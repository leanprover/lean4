// Lean compiler output
// Module: Lean.Elab.BuiltinDo.If
// Imports: public import Lean.Elab.Do.Basic meta import Lean.Parser.Do import Lean.Elab.BuiltinDo.Basic
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
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doIfLet"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(181, 227, 73, 225, 0, 143, 195, 11)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIfProp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(55, 147, 210, 58, 86, 191, 41, 151)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__11_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doIfLetPure"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__15_value),LEAN_SCALAR_PTR_LITERAL(30, 29, 142, 71, 96, 53, 139, 191)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doIfLetBind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__17_value),LEAN_SCALAR_PTR_LITERAL(251, 203, 116, 140, 48, 138, 26, 199)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__19_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__19_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__22_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__22_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "liftMethod"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__24_value),LEAN_SCALAR_PTR_LITERAL(217, 228, 135, 132, 46, 84, 105, 88)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__28_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__30_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__34_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__37_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__39_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40_value;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__1_value;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_expandDoIf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__0 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__1 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_expandDoIf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__2 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__3 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_expandDoIf___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__4 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__4_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l_Lean_Elab_Do_expandDoIf___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_expandDoIf___closed__5;
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__4_value),LEAN_SCALAR_PTR_LITERAL(182, 237, 62, 79, 212, 57, 236, 253)}};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__6 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_expandDoIf___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Pure"};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__7 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__7_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__7_value),LEAN_SCALAR_PTR_LITERAL(121, 135, 27, 238, 232, 181, 75, 85)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__4_value),LEAN_SCALAR_PTR_LITERAL(204, 106, 105, 165, 210, 13, 14, 1)}};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__8 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__9 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__10 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_expandDoIf___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "PUnit.unit"};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__11 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Do_expandDoIf___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_expandDoIf___closed__12;
static const lean_string_object l_Lean_Elab_Do_expandDoIf___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PUnit"};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__13 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__13_value;
static const lean_string_object l_Lean_Elab_Do_expandDoIf___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__14 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__13_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 158, 141, 176, 162, 235, 153)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__14_value),LEAN_SCALAR_PTR_LITERAL(146, 91, 82, 196, 249, 72, 203, 194)}};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__15 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__16 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__15_value)}};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__17 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__18 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__16_value),((lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__18_value)}};
static const lean_object* l_Lean_Elab_Do_expandDoIf___closed__19 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___closed__19_value;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "expandDoIf"};
static const lean_object* l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 129, 97, 131, 243, 145, 63, 99)}};
static const lean_object* l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3_value;
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 113, .m_capacity = 113, .m_length = 112, .m_data = "If the given syntax is a `doIf`, return an equivalent `doIf` that has an `else` but no `else if`s or\n`if let`s.\n"};
static const lean_object* l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___closed__0 = (const lean_object*)&l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___closed__0_value;
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termIfThenElse"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 209, 193, 165, 165, 31, 104, 198)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__1_value;
lean_object* l_Lean_Elab_Do_mkMonadicType___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "else branch of if with condition {cond}"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__1_value;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2;
lean_object* l_Lean_Elab_Do_elabDoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_doElabToSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "then branch of if with condition {cond}"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "termDepIfThenElse"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 94, 17, 11, 145, 108, 236, 173)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6_value;
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___lam__0___boxed(lean_object**);
lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_withDuplicableCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabDoIf"};
static const lean_object* l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 50, 230, 41, 148, 150, 129, 146)}};
static const lean_object* l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1_value;
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_SourceInfo_fromRef(x_2, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(x_5, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_4, x_3);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_151; 
x_18 = lean_array_uget(x_2, x_4);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_5, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_24 = x_5;
} else {
 lean_dec_ref(x_5);
 x_24 = lean_box(0);
}
x_25 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_unsigned_to_nat(2u);
x_151 = lean_unbox(x_23);
lean_dec(x_23);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_6, 5);
x_153 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(x_1, x_152, x_6, x_7);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
x_156 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
x_157 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
x_158 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40));
x_159 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc(x_154);
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_154);
lean_ctor_set(x_160, 1, x_157);
lean_ctor_set(x_160, 2, x_159);
lean_inc(x_154);
x_161 = l_Lean_Syntax_node2(x_154, x_158, x_22, x_160);
lean_inc(x_154);
x_162 = l_Lean_Syntax_node1(x_154, x_157, x_161);
x_163 = l_Lean_Syntax_node1(x_154, x_156, x_162);
x_28 = x_163;
x_29 = x_6;
x_30 = x_155;
goto block_150;
}
else
{
uint8_t x_164; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_164 = !lean_is_exclusive(x_153);
if (x_164 == 0)
{
return x_153;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_153, 0);
x_166 = lean_ctor_get(x_153, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_153);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
x_28 = x_22;
x_29 = x_6;
x_30 = x_7;
goto block_150;
}
block_150:
{
lean_object* x_31; uint8_t x_32; 
x_31 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6));
lean_inc(x_19);
x_32 = l_Lean_Syntax_isOfKind(x_19, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
lean_inc(x_19);
x_34 = l_Lean_Syntax_isOfKind(x_19, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_35 = l_Lean_Macro_throwUnsupported___redArg(x_30);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_8 = x_36;
x_9 = x_37;
goto block_15;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_42 = lean_ctor_get(x_29, 5);
x_43 = l_Lean_SourceInfo_fromRef(x_42, x_1);
x_44 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc(x_43);
if (lean_is_scalar(x_24)) {
 x_45 = lean_alloc_ctor(2, 2, 0);
} else {
 x_45 = x_24;
 lean_ctor_set_tag(x_45, 2);
}
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
lean_inc(x_43);
if (lean_is_scalar(x_21)) {
 x_47 = lean_alloc_ctor(2, 2, 0);
} else {
 x_47 = x_21;
 lean_ctor_set_tag(x_47, 2);
}
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
x_48 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
x_49 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc(x_43);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_50, 2, x_49);
x_51 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
lean_inc(x_43);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_43);
x_53 = l_Lean_Syntax_node2(x_43, x_48, x_52, x_28);
x_54 = l_Lean_Syntax_node6(x_43, x_25, x_45, x_19, x_47, x_20, x_50, x_53);
x_8 = x_54;
x_9 = x_30;
goto block_15;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = l_Lean_Syntax_getArg(x_19, x_26);
x_56 = l_Lean_Syntax_getArg(x_19, x_27);
lean_dec(x_19);
x_57 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16));
lean_inc(x_56);
x_58 = l_Lean_Syntax_isOfKind(x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18));
lean_inc(x_56);
x_60 = l_Lean_Syntax_isOfKind(x_56, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
x_61 = l_Lean_Macro_throwUnsupported___redArg(x_30);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_8 = x_62;
x_9 = x_63;
goto block_15;
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_61);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_29, 5);
x_69 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(x_1, x_68, x_29, x_30);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = l_Lean_Syntax_getArg(x_56, x_26);
lean_dec(x_56);
x_73 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
x_74 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
lean_inc(x_70);
if (lean_is_scalar(x_24)) {
 x_75 = lean_alloc_ctor(2, 2, 0);
} else {
 x_75 = x_24;
 lean_ctor_set_tag(x_75, 2);
}
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_74);
x_76 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
x_77 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc(x_70);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 2, x_77);
x_79 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
x_80 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25));
x_81 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26));
lean_inc(x_70);
if (lean_is_scalar(x_21)) {
 x_82 = lean_alloc_ctor(2, 2, 0);
} else {
 x_82 = x_21;
 lean_ctor_set_tag(x_82, 2);
}
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_81);
lean_inc(x_70);
x_83 = l_Lean_Syntax_node2(x_70, x_80, x_82, x_72);
lean_inc_ref(x_78);
lean_inc(x_70);
x_84 = l_Lean_Syntax_node2(x_70, x_79, x_78, x_83);
lean_inc(x_70);
x_85 = l_Lean_Syntax_node1(x_70, x_76, x_84);
x_86 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27));
lean_inc(x_70);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_70);
lean_ctor_set(x_87, 1, x_86);
x_88 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
x_89 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
x_90 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32));
lean_inc(x_70);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_70);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_70);
x_92 = l_Lean_Syntax_node1(x_70, x_76, x_55);
lean_inc(x_70);
x_93 = l_Lean_Syntax_node1(x_70, x_76, x_92);
x_94 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
lean_inc(x_70);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_70);
lean_ctor_set(x_95, 1, x_94);
lean_inc_ref(x_95);
lean_inc_ref(x_91);
lean_inc(x_70);
x_96 = l_Lean_Syntax_node4(x_70, x_89, x_91, x_93, x_95, x_20);
x_97 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
x_98 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36));
lean_inc(x_70);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_70);
lean_ctor_set(x_99, 1, x_98);
lean_inc(x_70);
x_100 = l_Lean_Syntax_node1(x_70, x_97, x_99);
lean_inc(x_70);
x_101 = l_Lean_Syntax_node1(x_70, x_76, x_100);
lean_inc(x_70);
x_102 = l_Lean_Syntax_node1(x_70, x_76, x_101);
lean_inc(x_70);
x_103 = l_Lean_Syntax_node4(x_70, x_89, x_91, x_102, x_95, x_28);
lean_inc(x_70);
x_104 = l_Lean_Syntax_node2(x_70, x_76, x_96, x_103);
lean_inc(x_70);
x_105 = l_Lean_Syntax_node1(x_70, x_88, x_104);
lean_inc_ref_n(x_78, 2);
x_106 = l_Lean_Syntax_node7(x_70, x_73, x_75, x_78, x_78, x_78, x_85, x_87, x_105);
x_8 = x_106;
x_9 = x_71;
goto block_15;
}
else
{
uint8_t x_107; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
x_107 = !lean_is_exclusive(x_69);
if (x_107 == 0)
{
return x_69;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_69, 0);
x_109 = lean_ctor_get(x_69, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_69);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_29, 5);
x_112 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___lam__0(x_1, x_111, x_29, x_30);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec_ref(x_112);
x_115 = l_Lean_Syntax_getArg(x_56, x_26);
lean_dec(x_56);
x_116 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
x_117 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
lean_inc(x_113);
if (lean_is_scalar(x_24)) {
 x_118 = lean_alloc_ctor(2, 2, 0);
} else {
 x_118 = x_24;
 lean_ctor_set_tag(x_118, 2);
}
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_117);
x_119 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
x_120 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc(x_113);
x_121 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_119);
lean_ctor_set(x_121, 2, x_120);
x_122 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
lean_inc_ref(x_121);
lean_inc(x_113);
x_123 = l_Lean_Syntax_node2(x_113, x_122, x_121, x_115);
lean_inc(x_113);
x_124 = l_Lean_Syntax_node1(x_113, x_119, x_123);
x_125 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27));
lean_inc(x_113);
if (lean_is_scalar(x_21)) {
 x_126 = lean_alloc_ctor(2, 2, 0);
} else {
 x_126 = x_21;
 lean_ctor_set_tag(x_126, 2);
}
lean_ctor_set(x_126, 0, x_113);
lean_ctor_set(x_126, 1, x_125);
x_127 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
x_128 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
x_129 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32));
lean_inc(x_113);
x_130 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_130, 0, x_113);
lean_ctor_set(x_130, 1, x_129);
lean_inc(x_113);
x_131 = l_Lean_Syntax_node1(x_113, x_119, x_55);
lean_inc(x_113);
x_132 = l_Lean_Syntax_node1(x_113, x_119, x_131);
x_133 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
lean_inc(x_113);
x_134 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_134, 0, x_113);
lean_ctor_set(x_134, 1, x_133);
lean_inc_ref(x_134);
lean_inc_ref(x_130);
lean_inc(x_113);
x_135 = l_Lean_Syntax_node4(x_113, x_128, x_130, x_132, x_134, x_20);
x_136 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
x_137 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36));
lean_inc(x_113);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_113);
lean_ctor_set(x_138, 1, x_137);
lean_inc(x_113);
x_139 = l_Lean_Syntax_node1(x_113, x_136, x_138);
lean_inc(x_113);
x_140 = l_Lean_Syntax_node1(x_113, x_119, x_139);
lean_inc(x_113);
x_141 = l_Lean_Syntax_node1(x_113, x_119, x_140);
lean_inc(x_113);
x_142 = l_Lean_Syntax_node4(x_113, x_128, x_130, x_141, x_134, x_28);
lean_inc(x_113);
x_143 = l_Lean_Syntax_node2(x_113, x_119, x_135, x_142);
lean_inc(x_113);
x_144 = l_Lean_Syntax_node1(x_113, x_127, x_143);
lean_inc_ref_n(x_121, 2);
x_145 = l_Lean_Syntax_node7(x_113, x_116, x_118, x_121, x_121, x_121, x_124, x_126, x_144);
x_8 = x_145;
x_9 = x_114;
goto block_15;
}
else
{
uint8_t x_146; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
x_146 = !lean_is_exclusive(x_112);
if (x_146 == 0)
{
return x_112;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_112, 0);
x_148 = lean_ctor_get(x_112, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_112);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
}
}
}
block_15:
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_box(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_4, x_12);
x_4 = x_13;
x_5 = x_11;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(x_8, x_2, x_9, x_10, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = l_Lean_SourceInfo_fromRef(x_1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_3, x_2);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_151; 
x_18 = lean_array_uget(x_1, x_3);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_24 = x_4;
} else {
 lean_dec_ref(x_4);
 x_24 = lean_box(0);
}
x_25 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_unsigned_to_nat(2u);
x_151 = lean_unbox(x_23);
lean_dec(x_23);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_5, 5);
x_153 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(x_152, x_5, x_6);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
x_156 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
x_157 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
x_158 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40));
x_159 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc(x_154);
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_154);
lean_ctor_set(x_160, 1, x_157);
lean_ctor_set(x_160, 2, x_159);
lean_inc(x_154);
x_161 = l_Lean_Syntax_node2(x_154, x_158, x_22, x_160);
lean_inc(x_154);
x_162 = l_Lean_Syntax_node1(x_154, x_157, x_161);
x_163 = l_Lean_Syntax_node1(x_154, x_156, x_162);
x_28 = x_163;
x_29 = x_5;
x_30 = x_155;
goto block_150;
}
else
{
uint8_t x_164; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_164 = !lean_is_exclusive(x_153);
if (x_164 == 0)
{
return x_153;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_153, 0);
x_166 = lean_ctor_get(x_153, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_153);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
x_28 = x_22;
x_29 = x_5;
x_30 = x_6;
goto block_150;
}
block_150:
{
lean_object* x_31; uint8_t x_32; 
x_31 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__6));
lean_inc(x_19);
x_32 = l_Lean_Syntax_isOfKind(x_19, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
lean_inc(x_19);
x_34 = l_Lean_Syntax_isOfKind(x_19, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_35 = l_Lean_Macro_throwUnsupported___redArg(x_30);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_7 = x_36;
x_8 = x_37;
goto block_15;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_42 = lean_ctor_get(x_29, 5);
x_43 = l_Lean_SourceInfo_fromRef(x_42, x_32);
x_44 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc(x_43);
if (lean_is_scalar(x_24)) {
 x_45 = lean_alloc_ctor(2, 2, 0);
} else {
 x_45 = x_24;
 lean_ctor_set_tag(x_45, 2);
}
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
lean_inc(x_43);
if (lean_is_scalar(x_21)) {
 x_47 = lean_alloc_ctor(2, 2, 0);
} else {
 x_47 = x_21;
 lean_ctor_set_tag(x_47, 2);
}
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
x_48 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
x_49 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc(x_43);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_50, 2, x_49);
x_51 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
lean_inc(x_43);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_43);
x_53 = l_Lean_Syntax_node2(x_43, x_48, x_52, x_28);
x_54 = l_Lean_Syntax_node6(x_43, x_25, x_45, x_19, x_47, x_20, x_50, x_53);
x_7 = x_54;
x_8 = x_30;
goto block_15;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = l_Lean_Syntax_getArg(x_19, x_26);
x_56 = l_Lean_Syntax_getArg(x_19, x_27);
lean_dec(x_19);
x_57 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__16));
lean_inc(x_56);
x_58 = l_Lean_Syntax_isOfKind(x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__18));
lean_inc(x_56);
x_60 = l_Lean_Syntax_isOfKind(x_56, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
x_61 = l_Lean_Macro_throwUnsupported___redArg(x_30);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_7 = x_62;
x_8 = x_63;
goto block_15;
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_61);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_29, 5);
x_69 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(x_68, x_29, x_30);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = l_Lean_Syntax_getArg(x_56, x_26);
lean_dec(x_56);
x_73 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
x_74 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
lean_inc(x_70);
if (lean_is_scalar(x_24)) {
 x_75 = lean_alloc_ctor(2, 2, 0);
} else {
 x_75 = x_24;
 lean_ctor_set_tag(x_75, 2);
}
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_74);
x_76 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
x_77 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc(x_70);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 2, x_77);
x_79 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
x_80 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__25));
x_81 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__26));
lean_inc(x_70);
if (lean_is_scalar(x_21)) {
 x_82 = lean_alloc_ctor(2, 2, 0);
} else {
 x_82 = x_21;
 lean_ctor_set_tag(x_82, 2);
}
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_81);
lean_inc(x_70);
x_83 = l_Lean_Syntax_node2(x_70, x_80, x_82, x_72);
lean_inc_ref(x_78);
lean_inc(x_70);
x_84 = l_Lean_Syntax_node2(x_70, x_79, x_78, x_83);
lean_inc(x_70);
x_85 = l_Lean_Syntax_node1(x_70, x_76, x_84);
x_86 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27));
lean_inc(x_70);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_70);
lean_ctor_set(x_87, 1, x_86);
x_88 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
x_89 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
x_90 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32));
lean_inc(x_70);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_70);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_70);
x_92 = l_Lean_Syntax_node1(x_70, x_76, x_55);
lean_inc(x_70);
x_93 = l_Lean_Syntax_node1(x_70, x_76, x_92);
x_94 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
lean_inc(x_70);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_70);
lean_ctor_set(x_95, 1, x_94);
lean_inc_ref(x_95);
lean_inc_ref(x_91);
lean_inc(x_70);
x_96 = l_Lean_Syntax_node4(x_70, x_89, x_91, x_93, x_95, x_20);
x_97 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
x_98 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36));
lean_inc(x_70);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_70);
lean_ctor_set(x_99, 1, x_98);
lean_inc(x_70);
x_100 = l_Lean_Syntax_node1(x_70, x_97, x_99);
lean_inc(x_70);
x_101 = l_Lean_Syntax_node1(x_70, x_76, x_100);
lean_inc(x_70);
x_102 = l_Lean_Syntax_node1(x_70, x_76, x_101);
lean_inc(x_70);
x_103 = l_Lean_Syntax_node4(x_70, x_89, x_91, x_102, x_95, x_28);
lean_inc(x_70);
x_104 = l_Lean_Syntax_node2(x_70, x_76, x_96, x_103);
lean_inc(x_70);
x_105 = l_Lean_Syntax_node1(x_70, x_88, x_104);
lean_inc_ref_n(x_78, 2);
x_106 = l_Lean_Syntax_node7(x_70, x_73, x_75, x_78, x_78, x_78, x_85, x_87, x_105);
x_7 = x_106;
x_8 = x_71;
goto block_15;
}
else
{
uint8_t x_107; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
x_107 = !lean_is_exclusive(x_69);
if (x_107 == 0)
{
return x_69;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_69, 0);
x_109 = lean_ctor_get(x_69, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_69);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_29, 5);
x_112 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___lam__0(x_111, x_29, x_30);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec_ref(x_112);
x_115 = l_Lean_Syntax_getArg(x_56, x_26);
lean_dec(x_56);
x_116 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__20));
x_117 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__21));
lean_inc(x_113);
if (lean_is_scalar(x_24)) {
 x_118 = lean_alloc_ctor(2, 2, 0);
} else {
 x_118 = x_24;
 lean_ctor_set_tag(x_118, 2);
}
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_117);
x_119 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
x_120 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc(x_113);
x_121 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_119);
lean_ctor_set(x_121, 2, x_120);
x_122 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__23));
lean_inc_ref(x_121);
lean_inc(x_113);
x_123 = l_Lean_Syntax_node2(x_113, x_122, x_121, x_115);
lean_inc(x_113);
x_124 = l_Lean_Syntax_node1(x_113, x_119, x_123);
x_125 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__27));
lean_inc(x_113);
if (lean_is_scalar(x_21)) {
 x_126 = lean_alloc_ctor(2, 2, 0);
} else {
 x_126 = x_21;
 lean_ctor_set_tag(x_126, 2);
}
lean_ctor_set(x_126, 0, x_113);
lean_ctor_set(x_126, 1, x_125);
x_127 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__29));
x_128 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__31));
x_129 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__32));
lean_inc(x_113);
x_130 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_130, 0, x_113);
lean_ctor_set(x_130, 1, x_129);
lean_inc(x_113);
x_131 = l_Lean_Syntax_node1(x_113, x_119, x_55);
lean_inc(x_113);
x_132 = l_Lean_Syntax_node1(x_113, x_119, x_131);
x_133 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__33));
lean_inc(x_113);
x_134 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_134, 0, x_113);
lean_ctor_set(x_134, 1, x_133);
lean_inc_ref(x_134);
lean_inc_ref(x_130);
lean_inc(x_113);
x_135 = l_Lean_Syntax_node4(x_113, x_128, x_130, x_132, x_134, x_20);
x_136 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
x_137 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__36));
lean_inc(x_113);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_113);
lean_ctor_set(x_138, 1, x_137);
lean_inc(x_113);
x_139 = l_Lean_Syntax_node1(x_113, x_136, x_138);
lean_inc(x_113);
x_140 = l_Lean_Syntax_node1(x_113, x_119, x_139);
lean_inc(x_113);
x_141 = l_Lean_Syntax_node1(x_113, x_119, x_140);
lean_inc(x_113);
x_142 = l_Lean_Syntax_node4(x_113, x_128, x_130, x_141, x_134, x_28);
lean_inc(x_113);
x_143 = l_Lean_Syntax_node2(x_113, x_119, x_135, x_142);
lean_inc(x_113);
x_144 = l_Lean_Syntax_node1(x_113, x_127, x_143);
lean_inc_ref_n(x_121, 2);
x_145 = l_Lean_Syntax_node7(x_113, x_116, x_118, x_121, x_121, x_121, x_124, x_126, x_144);
x_7 = x_145;
x_8 = x_114;
goto block_15;
}
else
{
uint8_t x_146; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
x_146 = !lean_is_exclusive(x_112);
if (x_146 == 0)
{
return x_112;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_112, 0);
x_148 = lean_ctor_get(x_112, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_112);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
}
}
}
block_15:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_4 = x_11;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___closed__1));
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_3);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_6, x_10);
x_12 = l_Lean_Syntax_isOfKind(x_11, x_7);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec_ref(x_3);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_array_uset(x_3, x_2, x_10);
x_17 = l_Lean_Syntax_getArg(x_6, x_14);
x_18 = l_Lean_Syntax_getArg(x_6, x_15);
lean_dec(x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_16, x_2, x_19);
x_2 = x_21;
x_3 = x_22;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Do_expandDoIf___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__4));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Do_expandDoIf___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__11));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__8));
lean_inc(x_8);
x_10 = l_Lean_Syntax_isOfKind(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_14 = lean_array_size(x_13);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(x_14, x_15, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_17 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_unsigned_to_nat(3u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = lean_array_size(x_18);
lean_inc(x_18);
x_22 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(x_21, x_15, x_18);
x_23 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(x_21, x_15, x_18);
x_48 = lean_unsigned_to_nat(5u);
x_49 = l_Lean_Syntax_getArg(x_1, x_48);
lean_dec(x_1);
x_50 = l_Lean_Syntax_isNone(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_unsigned_to_nat(2u);
lean_inc(x_49);
x_52 = l_Lean_Syntax_matchesNull(x_49, x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_49);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_2);
x_53 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_53;
}
else
{
lean_object* x_54; 
x_54 = l_Lean_Syntax_getArg(x_49, x_7);
lean_dec(x_49);
x_24 = x_2;
x_25 = x_54;
x_26 = x_3;
goto block_47;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_49);
x_55 = lean_ctor_get(x_2, 1);
x_56 = lean_ctor_get(x_2, 2);
x_57 = lean_ctor_get(x_2, 5);
x_58 = l_Lean_SourceInfo_fromRef(x_57, x_10);
x_59 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
x_60 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
x_61 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40));
x_62 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__1));
x_63 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__3));
x_64 = lean_obj_once(&l_Lean_Elab_Do_expandDoIf___closed__5, &l_Lean_Elab_Do_expandDoIf___closed__5_once, _init_l_Lean_Elab_Do_expandDoIf___closed__5);
x_65 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__6));
lean_inc(x_56);
lean_inc(x_55);
x_66 = l_Lean_addMacroScope(x_55, x_65, x_56);
x_67 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__10));
lean_inc(x_58);
x_68 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_64);
lean_ctor_set(x_68, 2, x_66);
lean_ctor_set(x_68, 3, x_67);
x_69 = lean_obj_once(&l_Lean_Elab_Do_expandDoIf___closed__12, &l_Lean_Elab_Do_expandDoIf___closed__12_once, _init_l_Lean_Elab_Do_expandDoIf___closed__12);
x_70 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__15));
lean_inc(x_56);
lean_inc(x_55);
x_71 = l_Lean_addMacroScope(x_55, x_70, x_56);
x_72 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__19));
lean_inc(x_58);
x_73 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_73, 0, x_58);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set(x_73, 2, x_71);
lean_ctor_set(x_73, 3, x_72);
lean_inc(x_58);
x_74 = l_Lean_Syntax_node1(x_58, x_60, x_73);
lean_inc(x_58);
x_75 = l_Lean_Syntax_node2(x_58, x_63, x_68, x_74);
lean_inc(x_58);
x_76 = l_Lean_Syntax_node1(x_58, x_62, x_75);
x_77 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc(x_58);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_58);
lean_ctor_set(x_78, 1, x_60);
lean_ctor_set(x_78, 2, x_77);
lean_inc(x_58);
x_79 = l_Lean_Syntax_node2(x_58, x_61, x_76, x_78);
lean_inc(x_58);
x_80 = l_Lean_Syntax_node1(x_58, x_60, x_79);
x_81 = l_Lean_Syntax_node1(x_58, x_59, x_80);
x_24 = x_2;
x_25 = x_81;
x_26 = x_3;
goto block_47;
}
block_47:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; 
x_27 = l_Array_reverse___redArg(x_23);
x_28 = lean_array_push(x_27, x_8);
x_29 = l_Array_reverse___redArg(x_22);
x_30 = lean_array_push(x_29, x_20);
x_31 = l_Array_zip___redArg(x_28, x_30);
lean_dec_ref(x_30);
lean_dec_ref(x_28);
x_32 = lean_box(x_5);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_array_size(x_31);
x_35 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3(x_10, x_31, x_34, x_15, x_33, x_24, x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_31);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_35);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_unsigned_to_nat(2u);
x_84 = lean_unsigned_to_nat(3u);
x_85 = l_Lean_Syntax_getArg(x_1, x_84);
x_146 = lean_unsigned_to_nat(4u);
x_147 = l_Lean_Syntax_getArg(x_1, x_146);
lean_inc(x_147);
x_148 = l_Lean_Syntax_matchesNull(x_147, x_82);
if (x_148 == 0)
{
lean_object* x_149; size_t x_150; size_t x_151; lean_object* x_152; 
x_149 = l_Lean_Syntax_getArgs(x_147);
lean_dec(x_147);
x_150 = lean_array_size(x_149);
x_151 = 0;
x_152 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(x_150, x_151, x_149);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
lean_dec(x_85);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_153 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_153;
}
else
{
lean_object* x_154; size_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
lean_dec_ref(x_152);
x_155 = lean_array_size(x_154);
lean_inc(x_154);
x_156 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(x_155, x_151, x_154);
x_157 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(x_155, x_151, x_154);
x_158 = lean_unsigned_to_nat(5u);
x_159 = l_Lean_Syntax_getArg(x_1, x_158);
lean_dec(x_1);
x_160 = l_Lean_Syntax_isNone(x_159);
if (x_160 == 0)
{
uint8_t x_161; 
lean_inc(x_159);
x_161 = l_Lean_Syntax_matchesNull(x_159, x_83);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_159);
lean_dec_ref(x_157);
lean_dec_ref(x_156);
lean_dec(x_85);
lean_dec(x_8);
lean_dec_ref(x_2);
x_162 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_162;
}
else
{
lean_object* x_163; 
x_163 = l_Lean_Syntax_getArg(x_159, x_7);
lean_dec(x_159);
x_86 = x_157;
x_87 = x_2;
x_88 = x_156;
x_89 = x_163;
x_90 = x_3;
goto block_112;
}
}
else
{
lean_dec(x_159);
x_113 = x_157;
x_114 = x_156;
x_115 = x_2;
x_116 = x_3;
goto block_145;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_unsigned_to_nat(5u);
x_165 = l_Lean_Syntax_getArg(x_1, x_164);
lean_dec(x_1);
lean_inc(x_165);
x_166 = l_Lean_Syntax_matchesNull(x_165, x_83);
if (x_166 == 0)
{
lean_object* x_167; size_t x_168; size_t x_169; lean_object* x_170; 
x_167 = l_Lean_Syntax_getArgs(x_147);
lean_dec(x_147);
x_168 = lean_array_size(x_167);
x_169 = 0;
x_170 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__0(x_168, x_169, x_167);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
lean_dec(x_165);
lean_dec(x_85);
lean_dec(x_8);
lean_dec_ref(x_2);
x_171 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_171;
}
else
{
lean_object* x_172; size_t x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
lean_dec_ref(x_170);
x_173 = lean_array_size(x_172);
lean_inc(x_172);
x_174 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__1(x_173, x_169, x_172);
x_175 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_expandDoIf_spec__2(x_173, x_169, x_172);
x_176 = l_Lean_Syntax_isNone(x_165);
if (x_176 == 0)
{
if (x_166 == 0)
{
lean_object* x_177; 
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec(x_165);
lean_dec(x_85);
lean_dec(x_8);
lean_dec_ref(x_2);
x_177 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_177;
}
else
{
lean_object* x_178; 
x_178 = l_Lean_Syntax_getArg(x_165, x_7);
lean_dec(x_165);
x_86 = x_175;
x_87 = x_2;
x_88 = x_174;
x_89 = x_178;
x_90 = x_3;
goto block_112;
}
}
else
{
lean_dec(x_165);
x_113 = x_175;
x_114 = x_174;
x_115 = x_2;
x_116 = x_3;
goto block_145;
}
}
}
else
{
lean_object* x_179; 
lean_dec(x_165);
lean_dec(x_147);
lean_dec(x_85);
lean_dec(x_8);
lean_dec_ref(x_2);
x_179 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_179;
}
}
block_112:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; size_t x_98; size_t x_99; lean_object* x_100; 
x_91 = l_Array_reverse___redArg(x_86);
x_92 = lean_array_push(x_91, x_8);
x_93 = l_Array_reverse___redArg(x_88);
x_94 = lean_array_push(x_93, x_85);
x_95 = l_Array_zip___redArg(x_92, x_94);
lean_dec_ref(x_94);
lean_dec_ref(x_92);
x_96 = lean_box(x_5);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_89);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_array_size(x_95);
x_99 = 0;
x_100 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__4(x_95, x_98, x_99, x_97, x_87, x_90);
lean_dec_ref(x_87);
lean_dec_ref(x_95);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
lean_ctor_set(x_100, 0, x_103);
return x_100;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_100, 0);
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_100);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_100);
if (x_108 == 0)
{
return x_100;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_100, 0);
x_110 = lean_ctor_get(x_100, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_100);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
block_145:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_117 = lean_ctor_get(x_115, 1);
x_118 = lean_ctor_get(x_115, 2);
x_119 = lean_ctor_get(x_115, 5);
x_120 = 0;
x_121 = l_Lean_SourceInfo_fromRef(x_119, x_120);
x_122 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__38));
x_123 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__12));
x_124 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__40));
x_125 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__1));
x_126 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__3));
x_127 = lean_obj_once(&l_Lean_Elab_Do_expandDoIf___closed__5, &l_Lean_Elab_Do_expandDoIf___closed__5_once, _init_l_Lean_Elab_Do_expandDoIf___closed__5);
x_128 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__6));
lean_inc(x_118);
lean_inc(x_117);
x_129 = l_Lean_addMacroScope(x_117, x_128, x_118);
x_130 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__10));
lean_inc(x_121);
x_131 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_131, 0, x_121);
lean_ctor_set(x_131, 1, x_127);
lean_ctor_set(x_131, 2, x_129);
lean_ctor_set(x_131, 3, x_130);
x_132 = lean_obj_once(&l_Lean_Elab_Do_expandDoIf___closed__12, &l_Lean_Elab_Do_expandDoIf___closed__12_once, _init_l_Lean_Elab_Do_expandDoIf___closed__12);
x_133 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__15));
lean_inc(x_118);
lean_inc(x_117);
x_134 = l_Lean_addMacroScope(x_117, x_133, x_118);
x_135 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___closed__19));
lean_inc(x_121);
x_136 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_132);
lean_ctor_set(x_136, 2, x_134);
lean_ctor_set(x_136, 3, x_135);
lean_inc(x_121);
x_137 = l_Lean_Syntax_node1(x_121, x_123, x_136);
lean_inc(x_121);
x_138 = l_Lean_Syntax_node2(x_121, x_126, x_131, x_137);
lean_inc(x_121);
x_139 = l_Lean_Syntax_node1(x_121, x_125, x_138);
x_140 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__13);
lean_inc(x_121);
x_141 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_141, 0, x_121);
lean_ctor_set(x_141, 1, x_123);
lean_ctor_set(x_141, 2, x_140);
lean_inc(x_121);
x_142 = l_Lean_Syntax_node2(x_121, x_124, x_139, x_141);
lean_inc(x_121);
x_143 = l_Lean_Syntax_node1(x_121, x_123, x_142);
x_144 = l_Lean_Syntax_node1(x_121, x_122, x_143);
x_86 = x_113;
x_87 = x_115;
x_88 = x_114;
x_89 = x_144;
x_90 = x_116;
goto block_112;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
x_4 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoIf), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1___closed__3));
x_3 = ((lean_object*)(l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___closed__0));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_13);
x_14 = l_Lean_Elab_Do_mkMonadicType___redArg(x_13, x_5);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_10, 5);
x_17 = 0;
x_18 = l_Lean_SourceInfo_fromRef(x_16, x_17);
x_19 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__1));
x_20 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc(x_18);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
lean_inc(x_18);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
x_24 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
lean_inc(x_18);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Syntax_node6(x_18, x_19, x_21, x_1, x_23, x_2, x_25, x_4);
lean_ctor_set_tag(x_14, 1);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Term_elabTermEnsuringType(x_26, x_14, x_3, x_3, x_27, x_6, x_7, x_8, x_9, x_10, x_11);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_ctor_get(x_10, 5);
x_31 = 0;
x_32 = l_Lean_SourceInfo_fromRef(x_30, x_31);
x_33 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___closed__1));
x_34 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc(x_32);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
lean_inc(x_32);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
x_38 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
lean_inc(x_32);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Syntax_node6(x_32, x_33, x_35, x_1, x_37, x_2, x_39, x_4);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_29);
x_42 = lean_box(0);
x_43 = l_Lean_Elab_Term_elabTermEnsuringType(x_40, x_41, x_3, x_3, x_42, x_6, x_7, x_8, x_9, x_10, x_11);
return x_43;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_box(x_2);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__0___boxed), 12, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_14);
x_16 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2);
x_17 = lean_box(x_2);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_4);
lean_closure_set(x_18, 2, x_17);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Do_doElabToSyntax___redArg(x_16, x_18, x_15, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
x_15 = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2);
x_14 = 1;
x_15 = lean_box(x_14);
lean_inc_ref(x_4);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___boxed), 13, 4);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
x_17 = lean_box(x_14);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_4);
lean_closure_set(x_18, 2, x_17);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Do_doElabToSyntax___redArg(x_13, x_18, x_16, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = 1;
if (x_4 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = l_Lean_Elab_Do_elabDoSeq(x_1, x_2, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = l_Lean_Elab_Do_elabDoSeq(x_3, x_2, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
x_14 = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_14);
x_15 = l_Lean_Elab_Do_mkMonadicType___redArg(x_14, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
lean_inc(x_1);
x_19 = l_Lean_Syntax_isOfKind(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__1));
lean_inc(x_1);
x_21 = l_Lean_Syntax_isOfKind(x_1, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_23 = lean_ctor_get(x_11, 5);
x_24 = l_Lean_SourceInfo_fromRef(x_23, x_19);
x_25 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3));
x_26 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc(x_24);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5));
lean_inc(x_24);
x_29 = l_Lean_Syntax_node1(x_24, x_28, x_1);
x_30 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6));
lean_inc(x_24);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
x_32 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
lean_inc(x_24);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
x_34 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
lean_inc(x_24);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Syntax_node8(x_24, x_25, x_27, x_29, x_31, x_2, x_33, x_3, x_35, x_5);
lean_ctor_set_tag(x_15, 1);
x_37 = lean_box(0);
x_38 = l_Lean_Elab_Term_elabTermEnsuringType(x_36, x_15, x_4, x_4, x_37, x_7, x_8, x_9, x_10, x_11, x_12);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_39 = lean_ctor_get(x_11, 5);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_Syntax_getArg(x_1, x_40);
lean_dec(x_1);
x_42 = 0;
x_43 = l_Lean_SourceInfo_fromRef(x_39, x_42);
x_44 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3));
x_45 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc(x_43);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5));
lean_inc(x_43);
x_48 = l_Lean_Syntax_node1(x_43, x_47, x_41);
x_49 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6));
lean_inc(x_43);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
x_51 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
lean_inc(x_43);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_51);
x_53 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
lean_inc(x_43);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Syntax_node8(x_43, x_44, x_46, x_48, x_50, x_2, x_52, x_3, x_54, x_5);
lean_ctor_set_tag(x_15, 1);
x_56 = lean_box(0);
x_57 = l_Lean_Elab_Term_elabTermEnsuringType(x_55, x_15, x_4, x_4, x_56, x_7, x_8, x_9, x_10, x_11, x_12);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_15, 0);
lean_inc(x_58);
lean_dec(x_15);
x_59 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__35));
lean_inc(x_1);
x_60 = l_Lean_Syntax_isOfKind(x_1, x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__1));
lean_inc(x_1);
x_62 = l_Lean_Syntax_isOfKind(x_1, x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_58);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_64 = lean_ctor_get(x_11, 5);
x_65 = l_Lean_SourceInfo_fromRef(x_64, x_60);
x_66 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3));
x_67 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc(x_65);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_69 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5));
lean_inc(x_65);
x_70 = l_Lean_Syntax_node1(x_65, x_69, x_1);
x_71 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6));
lean_inc(x_65);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_65);
lean_ctor_set(x_72, 1, x_71);
x_73 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
lean_inc(x_65);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_73);
x_75 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
lean_inc(x_65);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_65);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Syntax_node8(x_65, x_66, x_68, x_70, x_72, x_2, x_74, x_3, x_76, x_5);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_58);
x_79 = lean_box(0);
x_80 = l_Lean_Elab_Term_elabTermEnsuringType(x_77, x_78, x_4, x_4, x_79, x_7, x_8, x_9, x_10, x_11, x_12);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_81 = lean_ctor_get(x_11, 5);
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Lean_Syntax_getArg(x_1, x_82);
lean_dec(x_1);
x_84 = 0;
x_85 = l_Lean_SourceInfo_fromRef(x_81, x_84);
x_86 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__3));
x_87 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__9));
lean_inc(x_85);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_87);
x_89 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__5));
lean_inc(x_85);
x_90 = l_Lean_Syntax_node1(x_85, x_89, x_83);
x_91 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___closed__6));
lean_inc(x_85);
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_91);
x_93 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__10));
lean_inc(x_85);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_85);
lean_ctor_set(x_94, 1, x_93);
x_95 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__14));
lean_inc(x_85);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_85);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Syntax_node8(x_85, x_86, x_88, x_90, x_92, x_2, x_94, x_3, x_96, x_5);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_58);
x_99 = lean_box(0);
x_100 = l_Lean_Elab_Term_elabTermEnsuringType(x_97, x_98, x_4, x_4, x_99, x_7, x_8, x_9, x_10, x_11, x_12);
return x_100;
}
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
x_15 = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_box(x_3);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__1___boxed), 13, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_14);
x_16 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___lam__1___closed__2);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_apply_1(x_4, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Do_doElabToSyntax___redArg(x_16, x_19, x_15, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
x_15 = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_3);
lean_inc_ref(x_5);
lean_inc(x_4);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed), 12, 3);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_5);
lean_closure_set(x_14, 2, x_3);
x_15 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2, &l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte___closed__2);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__2___boxed), 13, 4);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_17);
lean_closure_set(x_18, 3, x_14);
x_19 = lean_box(x_16);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___lam__0___boxed), 12, 4);
lean_closure_set(x_20, 0, x_4);
lean_closure_set(x_20, 1, x_5);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_19);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Do_doElabToSyntax___redArg(x_15, x_20, x_18, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__7));
x_20 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_19);
lean_inc(x_4);
x_21 = l_Lean_Syntax_isOfKind(x_4, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Syntax_getArg(x_4, x_5);
lean_inc(x_23);
x_24 = l_Lean_Syntax_matchesNull(x_23, x_5);
if (x_24 == 0)
{
uint8_t x_25; 
lean_inc(x_23);
x_25 = l_Lean_Syntax_matchesNull(x_23, x_6);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Lean_Syntax_getArg(x_23, x_5);
lean_dec(x_23);
x_28 = l_Lean_Syntax_getArg(x_4, x_7);
lean_dec(x_4);
x_29 = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite(x_27, x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
x_30 = l_Lean_Syntax_getArg(x_4, x_7);
lean_dec(x_4);
x_31 = l___private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabIte(x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l_Lean_Elab_Do_elabDoIf___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__0));
x_12 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__1));
x_13 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__2));
x_14 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(4u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_Syntax_matchesNull(x_19, x_17);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_21 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_unsigned_to_nat(5u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
lean_inc(x_24);
x_25 = l_Lean_Syntax_matchesNull(x_24, x_22);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_24);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_If_0__Lean_Elab_Do_elabDoIf_elabDite_spec__0___redArg();
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_unsigned_to_nat(3u);
x_28 = l_Lean_Syntax_getArg(x_1, x_27);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_28);
x_29 = l_Lean_Elab_Do_inferControlInfoSeq(x_28, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = l_Lean_Syntax_getArg(x_24, x_31);
lean_dec(x_24);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_32);
x_33 = l_Lean_Elab_Do_inferControlInfoSeq(x_32, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l_Lean_Syntax_getArg(x_1, x_31);
lean_dec(x_1);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoIf___lam__0___boxed), 18, 9);
lean_closure_set(x_36, 0, x_11);
lean_closure_set(x_36, 1, x_12);
lean_closure_set(x_36, 2, x_13);
lean_closure_set(x_36, 3, x_35);
lean_closure_set(x_36, 4, x_17);
lean_closure_set(x_36, 5, x_22);
lean_closure_set(x_36, 6, x_31);
lean_closure_set(x_36, 7, x_28);
lean_closure_set(x_36, 8, x_32);
x_37 = l_Lean_Elab_Do_ControlInfo_alternative(x_30, x_34);
x_38 = l_Lean_Elab_Do_DoElemCont_withDuplicableCont(x_2, x_37, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
return x_29;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_29, 0);
lean_inc(x_43);
lean_dec(x_29);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Do_elabDoIf(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Do_doElemElabAttribute;
x_3 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_expandDoIf_spec__3___closed__4));
x_4 = ((lean_object*)(l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___closed__1));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoIf___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1();
return x_2;
}
}
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_If(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Do_expandDoIf___regBuiltin_Lean_Elab_Do_expandDoIf_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Do_elabDoIf___regBuiltin_Lean_Elab_Do_elabDoIf__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
