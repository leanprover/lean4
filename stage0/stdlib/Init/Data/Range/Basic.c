// Lean compiler output
// Module: Init.Data.Range.Basic
// Imports: public import Init.Control.Basic public import Init.Grind.Tactics public meta import Init.Grind.Tactics import Init.Omega import Init.WFTactics
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
LEAN_EXPORT lean_object* l_Std_Legacy_instMembershipNatRange;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_size___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__3 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__6 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__8 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__10 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__14 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__16;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forIn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForMNatOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForMNatOfMonad(lean_object*, lean_object*);
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Legacy"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Range"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term[:_]"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__3 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__3_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_2),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 247, 114, 105, 22, 2, 212, 24)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__5 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__5_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__7 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__7_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__7_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__9 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__9_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__9_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__13 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__13_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__13_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__14 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__14_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__16 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__16_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__16_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__17 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__17_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__17_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__18 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__18_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__19 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__19_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__19_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__18_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__21 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__21_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__21_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__22 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__22_value;
LEAN_EXPORT const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__22_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term[_:_]"};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__0 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__0_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_2),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 227, 143, 95, 3, 88, 200, 110)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__2 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__2_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__2_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__3 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__3_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__3_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__4 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__4_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__4_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__5 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__5_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__5_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__6 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__6_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__6_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__7 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__7_value;
LEAN_EXPORT const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__7_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term[:_:_]"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__0 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__0_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_2),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 39, 16, 99, 27, 138, 138, 190)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__16_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__2 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__2_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__2_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__3 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__3_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__3_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__4 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__4_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__4_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__5 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__5_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__5_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__6 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__6_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__6_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__7 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__7_value;
LEAN_EXPORT const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__7_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term[_:_:_]"};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__0 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__0_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_2),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 172, 42, 253, 230, 203, 52, 54)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__3_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__2 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__2_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__2_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__3 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__3_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__3_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__4 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__4_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__4_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__5 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__5_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__5_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__6 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__6_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__6_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__7 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__7_value;
LEAN_EXPORT const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__7_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__1 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__1_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_1),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__5 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__5_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_1),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__7 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__7_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_1),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__9 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__9_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_1),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "stop"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(73, 89, 146, 127, 39, 212, 171, 73)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(244, 244, 197, 195, 27, 244, 67, 26)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__15 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__15_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__17 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__17_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_1),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "step_pos"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21_value;
static lean_once_cell_t l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(245, 121, 239, 198, 116, 70, 162, 77)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(160, 87, 147, 8, 30, 205, 161, 86)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__25 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__25_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Nat.zero_lt_one"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__27 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__27_value;
static lean_once_cell_t l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__29 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__29_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "zero_lt_one"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__30 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__30_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31_value_aux_0),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(185, 8, 170, 47, 200, 94, 239, 254)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__32 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__32_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__33 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__33_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__34 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__34_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_1),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value;
static lean_once_cell_t l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 104, 217, 143, 145, 181, 232, 169)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__39 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__39_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__40 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__40_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__40_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__41 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__41_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__39_value),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__41_value)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "start"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0_value;
static lean_once_cell_t l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 129, 58, 248, 205, 160, 234, 176)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__2 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__2_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 7, 44, 103, 11, 200, 166, 88)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__4 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__4_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__5 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__5_value;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "step"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0_value;
static lean_once_cell_t l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 177, 97, 197, 78, 128, 65, 7)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__2 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__2_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 65, 241, 97, 173, 114, 37, 17)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__4 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__4_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__5 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__5_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__6 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__6_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_1),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__8 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__8_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value;
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x3a___x5d__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "tacticGet_elem_tactic_extensible"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 80, 20, 121, 148, 193, 237, 106)}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "seq1"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 140, 137, 56, 141, 11, 143, 117)}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Membership.get_elem_helper"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value;
static lean_once_cell_t l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Membership"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "get_elem_helper"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(205, 217, 109, 94, 255, 55, 82, 109)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(137, 97, 88, 79, 176, 40, 72, 204)}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assumption"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(240, 50, 167, 190, 65, 82, 149, 231)}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value;
LEAN_EXPORT lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_Legacy_instMembershipNatRange(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_size(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_nat_sub(x_3, x_2);
x_6 = lean_nat_add(x_5, x_4);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = lean_nat_div(x_8, x_4);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_size___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Legacy_Range_size(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__10));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12);
x_2 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5);
x_2 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__16, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__16_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__16);
x_2 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17);
x_2 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18);
x_2 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19);
x_2 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20);
x_2 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21);
x_2 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22);
x_2 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23);
x_2 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24);
x_2 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25);
x_2 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_5);
x_14 = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_5);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_1);
lean_closure_set(x_14, 4, x_2);
lean_closure_set(x_14, 5, x_3);
x_15 = lean_apply_3(x_3, x_5, lean_box(0), x_4);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_2(x_9, lean_box(0), x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = lean_nat_add(x_2, x_3);
x_13 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(x_4, x_5, x_6, x_11, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forIn_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(x_1, x_2, x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forIn_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(x_3, x_4, x_6, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(x_1, x_3, x_5, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_2);
lean_closure_set(x_13, 4, x_3);
x_14 = lean_apply_1(x_3, x_4);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_nat_add(x_1, x_2);
x_8 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForMNatOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Legacy_Range_forM), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForMNatOfMonad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Legacy_Range_forM), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__27));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_10, x_13);
lean_dec(x_10);
x_15 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2));
x_16 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3));
lean_inc(x_14);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9));
x_19 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4);
lean_inc(x_14);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6));
x_22 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8));
x_23 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10));
x_24 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12);
x_25 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13));
lean_inc(x_9);
lean_inc(x_8);
x_26 = l_Lean_addMacroScope(x_8, x_25, x_9);
x_27 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16));
lean_inc(x_14);
x_28 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_27);
lean_inc_ref(x_20);
lean_inc(x_14);
x_29 = l_Lean_Syntax_node2(x_14, x_23, x_28, x_20);
x_30 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18));
x_31 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19));
lean_inc(x_14);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_31);
lean_inc_ref(x_20);
lean_inc_ref(x_32);
lean_inc(x_14);
x_33 = l_Lean_Syntax_node3(x_14, x_30, x_32, x_20, x_12);
lean_inc_ref_n(x_20, 2);
lean_inc(x_14);
x_34 = l_Lean_Syntax_node3(x_14, x_18, x_20, x_20, x_33);
lean_inc(x_14);
x_35 = l_Lean_Syntax_node2(x_14, x_22, x_29, x_34);
x_36 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20));
lean_inc(x_14);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_14);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22);
x_39 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23));
lean_inc(x_9);
lean_inc(x_8);
x_40 = l_Lean_addMacroScope(x_8, x_39, x_9);
x_41 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26));
lean_inc(x_14);
x_42 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_42, 0, x_14);
lean_ctor_set(x_42, 1, x_38);
lean_ctor_set(x_42, 2, x_40);
lean_ctor_set(x_42, 3, x_41);
lean_inc_ref(x_20);
lean_inc(x_14);
x_43 = l_Lean_Syntax_node2(x_14, x_23, x_42, x_20);
x_44 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28);
x_45 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31));
lean_inc(x_9);
lean_inc(x_8);
x_46 = l_Lean_addMacroScope(x_8, x_45, x_9);
x_47 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__33));
lean_inc(x_14);
x_48 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_48, 0, x_14);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set(x_48, 3, x_47);
lean_inc_ref(x_20);
lean_inc(x_14);
x_49 = l_Lean_Syntax_node3(x_14, x_30, x_32, x_20, x_48);
lean_inc_ref_n(x_20, 2);
lean_inc(x_14);
x_50 = l_Lean_Syntax_node3(x_14, x_18, x_20, x_20, x_49);
lean_inc(x_14);
x_51 = l_Lean_Syntax_node2(x_14, x_22, x_43, x_50);
lean_inc(x_14);
x_52 = l_Lean_Syntax_node3(x_14, x_18, x_35, x_37, x_51);
lean_inc(x_14);
x_53 = l_Lean_Syntax_node1(x_14, x_21, x_52);
x_54 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35));
lean_inc_ref(x_20);
lean_inc(x_14);
x_55 = l_Lean_Syntax_node1(x_14, x_54, x_20);
x_56 = ((lean_object*)(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11));
lean_inc(x_14);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_14);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36);
x_59 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37));
x_60 = l_Lean_addMacroScope(x_8, x_59, x_9);
x_61 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42));
lean_inc(x_14);
x_62 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_62, 0, x_14);
lean_ctor_set(x_62, 1, x_58);
lean_ctor_set(x_62, 2, x_60);
lean_ctor_set(x_62, 3, x_61);
lean_inc(x_14);
x_63 = l_Lean_Syntax_node2(x_14, x_18, x_57, x_62);
x_64 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43));
lean_inc(x_14);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_14);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_Syntax_node6(x_14, x_15, x_17, x_20, x_53, x_55, x_63, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_3);
return x_67;
}
}
}
static lean_object* _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_10, x_15);
lean_dec(x_10);
x_17 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2));
x_18 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3));
lean_inc(x_16);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9));
x_21 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4);
lean_inc(x_16);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6));
x_24 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8));
x_25 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10));
x_26 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1);
x_27 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__2));
lean_inc(x_9);
lean_inc(x_8);
x_28 = l_Lean_addMacroScope(x_8, x_27, x_9);
x_29 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__5));
lean_inc(x_16);
x_30 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_29);
lean_inc_ref(x_22);
lean_inc(x_16);
x_31 = l_Lean_Syntax_node2(x_16, x_25, x_30, x_22);
x_32 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18));
x_33 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19));
lean_inc(x_16);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_16);
lean_ctor_set(x_34, 1, x_33);
lean_inc_ref(x_22);
lean_inc_ref(x_34);
lean_inc(x_16);
x_35 = l_Lean_Syntax_node3(x_16, x_32, x_34, x_22, x_12);
lean_inc_ref_n(x_22, 2);
lean_inc(x_16);
x_36 = l_Lean_Syntax_node3(x_16, x_20, x_22, x_22, x_35);
lean_inc(x_16);
x_37 = l_Lean_Syntax_node2(x_16, x_24, x_31, x_36);
x_38 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20));
lean_inc(x_16);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12);
x_41 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13));
lean_inc(x_9);
lean_inc(x_8);
x_42 = l_Lean_addMacroScope(x_8, x_41, x_9);
x_43 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16));
lean_inc(x_16);
x_44 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_44, 0, x_16);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_42);
lean_ctor_set(x_44, 3, x_43);
lean_inc_ref(x_22);
lean_inc(x_16);
x_45 = l_Lean_Syntax_node2(x_16, x_25, x_44, x_22);
lean_inc_ref(x_22);
lean_inc_ref(x_34);
lean_inc(x_16);
x_46 = l_Lean_Syntax_node3(x_16, x_32, x_34, x_22, x_14);
lean_inc_ref_n(x_22, 2);
lean_inc(x_16);
x_47 = l_Lean_Syntax_node3(x_16, x_20, x_22, x_22, x_46);
lean_inc(x_16);
x_48 = l_Lean_Syntax_node2(x_16, x_24, x_45, x_47);
x_49 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22);
x_50 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23));
lean_inc(x_9);
lean_inc(x_8);
x_51 = l_Lean_addMacroScope(x_8, x_50, x_9);
x_52 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26));
lean_inc(x_16);
x_53 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_53, 0, x_16);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_51);
lean_ctor_set(x_53, 3, x_52);
lean_inc_ref(x_22);
lean_inc(x_16);
x_54 = l_Lean_Syntax_node2(x_16, x_25, x_53, x_22);
x_55 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28);
x_56 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31));
lean_inc(x_9);
lean_inc(x_8);
x_57 = l_Lean_addMacroScope(x_8, x_56, x_9);
x_58 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__33));
lean_inc(x_16);
x_59 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_59, 0, x_16);
lean_ctor_set(x_59, 1, x_55);
lean_ctor_set(x_59, 2, x_57);
lean_ctor_set(x_59, 3, x_58);
lean_inc_ref(x_22);
lean_inc(x_16);
x_60 = l_Lean_Syntax_node3(x_16, x_32, x_34, x_22, x_59);
lean_inc_ref_n(x_22, 2);
lean_inc(x_16);
x_61 = l_Lean_Syntax_node3(x_16, x_20, x_22, x_22, x_60);
lean_inc(x_16);
x_62 = l_Lean_Syntax_node2(x_16, x_24, x_54, x_61);
lean_inc_ref(x_39);
lean_inc(x_16);
x_63 = l_Lean_Syntax_node5(x_16, x_20, x_37, x_39, x_48, x_39, x_62);
lean_inc(x_16);
x_64 = l_Lean_Syntax_node1(x_16, x_23, x_63);
x_65 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35));
lean_inc_ref(x_22);
lean_inc(x_16);
x_66 = l_Lean_Syntax_node1(x_16, x_65, x_22);
x_67 = ((lean_object*)(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11));
lean_inc(x_16);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_16);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36);
x_70 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37));
x_71 = l_Lean_addMacroScope(x_8, x_70, x_9);
x_72 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42));
lean_inc(x_16);
x_73 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_73, 0, x_16);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set(x_73, 2, x_71);
lean_ctor_set(x_73, 3, x_72);
lean_inc(x_16);
x_74 = l_Lean_Syntax_node2(x_16, x_20, x_68, x_73);
x_75 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43));
lean_inc(x_16);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_16);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Syntax_node6(x_16, x_17, x_19, x_22, x_64, x_66, x_74, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_3);
return x_78;
}
}
}
static lean_object* _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(5u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = 0;
x_18 = l_Lean_SourceInfo_fromRef(x_10, x_17);
lean_dec(x_10);
x_19 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2));
x_20 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3));
lean_inc(x_18);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9));
x_23 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4);
lean_inc(x_18);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6));
x_26 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8));
x_27 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10));
x_28 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1);
x_29 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__2));
lean_inc(x_9);
lean_inc(x_8);
x_30 = l_Lean_addMacroScope(x_8, x_29, x_9);
x_31 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__5));
lean_inc(x_18);
x_32 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
lean_inc_ref(x_24);
lean_inc(x_18);
x_33 = l_Lean_Syntax_node2(x_18, x_27, x_32, x_24);
x_34 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18));
x_35 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19));
lean_inc(x_18);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_35);
lean_inc_ref(x_24);
lean_inc_ref(x_36);
lean_inc(x_18);
x_37 = l_Lean_Syntax_node3(x_18, x_34, x_36, x_24, x_12);
lean_inc_ref_n(x_24, 2);
lean_inc(x_18);
x_38 = l_Lean_Syntax_node3(x_18, x_22, x_24, x_24, x_37);
lean_inc(x_18);
x_39 = l_Lean_Syntax_node2(x_18, x_26, x_33, x_38);
x_40 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20));
lean_inc(x_18);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_18);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12);
x_43 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13));
lean_inc(x_9);
lean_inc(x_8);
x_44 = l_Lean_addMacroScope(x_8, x_43, x_9);
x_45 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16));
lean_inc(x_18);
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_18);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_44);
lean_ctor_set(x_46, 3, x_45);
lean_inc_ref(x_24);
lean_inc(x_18);
x_47 = l_Lean_Syntax_node2(x_18, x_27, x_46, x_24);
lean_inc_ref(x_24);
lean_inc_ref(x_36);
lean_inc(x_18);
x_48 = l_Lean_Syntax_node3(x_18, x_34, x_36, x_24, x_14);
lean_inc_ref_n(x_24, 2);
lean_inc(x_18);
x_49 = l_Lean_Syntax_node3(x_18, x_22, x_24, x_24, x_48);
lean_inc(x_18);
x_50 = l_Lean_Syntax_node2(x_18, x_26, x_47, x_49);
x_51 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1);
x_52 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__2));
lean_inc(x_9);
lean_inc(x_8);
x_53 = l_Lean_addMacroScope(x_8, x_52, x_9);
x_54 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__5));
lean_inc(x_18);
x_55 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_55, 0, x_18);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set(x_55, 3, x_54);
lean_inc_ref(x_24);
lean_inc(x_18);
x_56 = l_Lean_Syntax_node2(x_18, x_27, x_55, x_24);
lean_inc_ref(x_24);
lean_inc_ref(x_36);
lean_inc(x_18);
x_57 = l_Lean_Syntax_node3(x_18, x_34, x_36, x_24, x_16);
lean_inc_ref_n(x_24, 2);
lean_inc(x_18);
x_58 = l_Lean_Syntax_node3(x_18, x_22, x_24, x_24, x_57);
lean_inc(x_18);
x_59 = l_Lean_Syntax_node2(x_18, x_26, x_56, x_58);
x_60 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22);
x_61 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23));
lean_inc(x_9);
lean_inc(x_8);
x_62 = l_Lean_addMacroScope(x_8, x_61, x_9);
x_63 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26));
lean_inc(x_18);
x_64 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_64, 0, x_18);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_64, 2, x_62);
lean_ctor_set(x_64, 3, x_63);
lean_inc_ref(x_24);
lean_inc(x_18);
x_65 = l_Lean_Syntax_node2(x_18, x_27, x_64, x_24);
x_66 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7));
x_67 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__8));
lean_inc(x_18);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_18);
lean_ctor_set(x_68, 1, x_67);
x_69 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4));
x_70 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7));
x_71 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9));
x_72 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10));
lean_inc(x_18);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_18);
lean_ctor_set(x_73, 1, x_71);
x_74 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15));
lean_inc_ref(x_24);
lean_inc(x_18);
x_75 = l_Lean_Syntax_node1(x_18, x_74, x_24);
lean_inc(x_18);
x_76 = l_Lean_Syntax_node2(x_18, x_72, x_73, x_75);
lean_inc(x_18);
x_77 = l_Lean_Syntax_node1(x_18, x_22, x_76);
lean_inc(x_18);
x_78 = l_Lean_Syntax_node1(x_18, x_70, x_77);
lean_inc(x_18);
x_79 = l_Lean_Syntax_node1(x_18, x_69, x_78);
lean_inc(x_18);
x_80 = l_Lean_Syntax_node2(x_18, x_66, x_68, x_79);
lean_inc_ref(x_24);
lean_inc(x_18);
x_81 = l_Lean_Syntax_node3(x_18, x_34, x_36, x_24, x_80);
lean_inc_ref_n(x_24, 2);
lean_inc(x_18);
x_82 = l_Lean_Syntax_node3(x_18, x_22, x_24, x_24, x_81);
lean_inc(x_18);
x_83 = l_Lean_Syntax_node2(x_18, x_26, x_65, x_82);
lean_inc_ref_n(x_41, 2);
lean_inc(x_18);
x_84 = l_Lean_Syntax_node7(x_18, x_22, x_39, x_41, x_50, x_41, x_59, x_41, x_83);
lean_inc(x_18);
x_85 = l_Lean_Syntax_node1(x_18, x_25, x_84);
x_86 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35));
lean_inc_ref(x_24);
lean_inc(x_18);
x_87 = l_Lean_Syntax_node1(x_18, x_86, x_24);
x_88 = ((lean_object*)(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11));
lean_inc(x_18);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_18);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36);
x_91 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37));
x_92 = l_Lean_addMacroScope(x_8, x_91, x_9);
x_93 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42));
lean_inc(x_18);
x_94 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_94, 0, x_18);
lean_ctor_set(x_94, 1, x_90);
lean_ctor_set(x_94, 2, x_92);
lean_ctor_set(x_94, 3, x_93);
lean_inc(x_18);
x_95 = l_Lean_Syntax_node2(x_18, x_22, x_89, x_94);
x_96 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43));
lean_inc(x_18);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_18);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Syntax_node6(x_18, x_19, x_21, x_24, x_85, x_87, x_95, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_3);
return x_99;
}
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x3a___x5d__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(4u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_10, x_15);
lean_dec(x_10);
x_17 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2));
x_18 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3));
lean_inc(x_16);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9));
x_21 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4);
lean_inc(x_16);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6));
x_24 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8));
x_25 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10));
x_26 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12);
x_27 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13));
lean_inc(x_9);
lean_inc(x_8);
x_28 = l_Lean_addMacroScope(x_8, x_27, x_9);
x_29 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16));
lean_inc(x_16);
x_30 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_29);
lean_inc_ref(x_22);
lean_inc(x_16);
x_31 = l_Lean_Syntax_node2(x_16, x_25, x_30, x_22);
x_32 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18));
x_33 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19));
lean_inc(x_16);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_16);
lean_ctor_set(x_34, 1, x_33);
lean_inc_ref(x_22);
lean_inc_ref(x_34);
lean_inc(x_16);
x_35 = l_Lean_Syntax_node3(x_16, x_32, x_34, x_22, x_12);
lean_inc_ref_n(x_22, 2);
lean_inc(x_16);
x_36 = l_Lean_Syntax_node3(x_16, x_20, x_22, x_22, x_35);
lean_inc(x_16);
x_37 = l_Lean_Syntax_node2(x_16, x_24, x_31, x_36);
x_38 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20));
lean_inc(x_16);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1);
x_41 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__2));
lean_inc(x_9);
lean_inc(x_8);
x_42 = l_Lean_addMacroScope(x_8, x_41, x_9);
x_43 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__5));
lean_inc(x_16);
x_44 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_44, 0, x_16);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_42);
lean_ctor_set(x_44, 3, x_43);
lean_inc_ref(x_22);
lean_inc(x_16);
x_45 = l_Lean_Syntax_node2(x_16, x_25, x_44, x_22);
lean_inc_ref(x_22);
lean_inc_ref(x_34);
lean_inc(x_16);
x_46 = l_Lean_Syntax_node3(x_16, x_32, x_34, x_22, x_14);
lean_inc_ref_n(x_22, 2);
lean_inc(x_16);
x_47 = l_Lean_Syntax_node3(x_16, x_20, x_22, x_22, x_46);
lean_inc(x_16);
x_48 = l_Lean_Syntax_node2(x_16, x_24, x_45, x_47);
x_49 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22);
x_50 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23));
lean_inc(x_9);
lean_inc(x_8);
x_51 = l_Lean_addMacroScope(x_8, x_50, x_9);
x_52 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26));
lean_inc(x_16);
x_53 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_53, 0, x_16);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_51);
lean_ctor_set(x_53, 3, x_52);
lean_inc_ref(x_22);
lean_inc(x_16);
x_54 = l_Lean_Syntax_node2(x_16, x_25, x_53, x_22);
x_55 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7));
x_56 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__8));
lean_inc(x_16);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_16);
lean_ctor_set(x_57, 1, x_56);
x_58 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4));
x_59 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7));
x_60 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9));
x_61 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10));
lean_inc(x_16);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_16);
lean_ctor_set(x_62, 1, x_60);
x_63 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15));
lean_inc_ref(x_22);
lean_inc(x_16);
x_64 = l_Lean_Syntax_node1(x_16, x_63, x_22);
lean_inc(x_16);
x_65 = l_Lean_Syntax_node2(x_16, x_61, x_62, x_64);
lean_inc(x_16);
x_66 = l_Lean_Syntax_node1(x_16, x_20, x_65);
lean_inc(x_16);
x_67 = l_Lean_Syntax_node1(x_16, x_59, x_66);
lean_inc(x_16);
x_68 = l_Lean_Syntax_node1(x_16, x_58, x_67);
lean_inc(x_16);
x_69 = l_Lean_Syntax_node2(x_16, x_55, x_57, x_68);
lean_inc_ref(x_22);
lean_inc(x_16);
x_70 = l_Lean_Syntax_node3(x_16, x_32, x_34, x_22, x_69);
lean_inc_ref_n(x_22, 2);
lean_inc(x_16);
x_71 = l_Lean_Syntax_node3(x_16, x_20, x_22, x_22, x_70);
lean_inc(x_16);
x_72 = l_Lean_Syntax_node2(x_16, x_24, x_54, x_71);
lean_inc_ref(x_39);
lean_inc(x_16);
x_73 = l_Lean_Syntax_node5(x_16, x_20, x_37, x_39, x_48, x_39, x_72);
lean_inc(x_16);
x_74 = l_Lean_Syntax_node1(x_16, x_23, x_73);
x_75 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35));
lean_inc_ref(x_22);
lean_inc(x_16);
x_76 = l_Lean_Syntax_node1(x_16, x_75, x_22);
x_77 = ((lean_object*)(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11));
lean_inc(x_16);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_16);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36);
x_80 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37));
x_81 = l_Lean_addMacroScope(x_8, x_80, x_9);
x_82 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42));
lean_inc(x_16);
x_83 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_83, 0, x_16);
lean_ctor_set(x_83, 1, x_79);
lean_ctor_set(x_83, 2, x_81);
lean_ctor_set(x_83, 3, x_82);
lean_inc(x_16);
x_84 = l_Lean_Syntax_node2(x_16, x_20, x_78, x_83);
x_85 = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43));
lean_inc(x_16);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_16);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Syntax_node6(x_16, x_17, x_19, x_22, x_74, x_76, x_84, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_3);
return x_88;
}
}
}
static lean_object* _init_l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
lean_dec(x_10);
x_13 = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3));
x_14 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9));
x_15 = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4));
x_16 = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5));
lean_inc(x_12);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_obj_once(&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7, &l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_once, _init_l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7);
x_19 = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10));
x_20 = l_Lean_addMacroScope(x_8, x_19, x_9);
x_21 = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12));
lean_inc(x_12);
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
lean_inc(x_12);
x_23 = l_Lean_Syntax_node2(x_12, x_16, x_17, x_22);
x_24 = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13));
lean_inc(x_12);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14));
x_27 = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15));
lean_inc(x_12);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_26);
lean_inc(x_12);
x_29 = l_Lean_Syntax_node1(x_12, x_27, x_28);
x_30 = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17));
x_31 = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18));
lean_inc(x_12);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_12);
x_33 = l_Lean_Syntax_node1(x_12, x_30, x_32);
lean_inc_ref(x_25);
lean_inc(x_12);
x_34 = l_Lean_Syntax_node5(x_12, x_14, x_23, x_25, x_29, x_25, x_33);
x_35 = l_Lean_Syntax_node1(x_12, x_13, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
return x_36;
}
}
}
lean_object* initialize_Init_Control_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Legacy_instMembershipNatRange = _init_l_Std_Legacy_instMembershipNatRange();
lean_mark_persistent(l_Std_Legacy_instMembershipNatRange);
l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1 = _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1();
lean_mark_persistent(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
