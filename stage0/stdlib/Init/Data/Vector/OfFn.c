// Lean compiler output
// Module: Init.Data.Vector.OfFn
// Imports: import all Init.Data.Vector.Basic public import Init.Data.Array.OfFn public import Init.Data.Vector.Basic import Init.Data.Fin.Lemmas import Init.Data.Vector.Monadic import Init.TacticsExtra
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_ofFnM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_ofFnM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1_value;
static const lean_string_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2_value;
static const lean_string_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__3 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value;
static const lean_array_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5_value;
static const lean_string_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__6 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value;
static const lean_string_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__8 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__9 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__9_value;
static const lean_string_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__10 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__10_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12;
static lean_once_cell_t l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13;
static const lean_string_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__14 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value_aux_1),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value_aux_2),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__9_value),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5_value)}};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__16 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__16_value;
static lean_once_cell_t l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17;
static lean_once_cell_t l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18;
static lean_once_cell_t l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19;
static lean_once_cell_t l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20;
static lean_once_cell_t l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21;
static lean_once_cell_t l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22;
static lean_once_cell_t l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23;
static lean_once_cell_t l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24;
static lean_once_cell_t l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25;
static lean_once_cell_t l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26;
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0___boxed(lean_object* v_i_1_, lean_object* v_acc_2_, lean_object* v_n_3_, lean_object* v_inst_4_, lean_object* v_f_5_, lean_object* v_____do__lift_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0(v_i_1_, v_acc_2_, v_n_3_, v_inst_4_, v_f_5_, v_____do__lift_6_);
lean_dec(v_i_1_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg(lean_object* v_n_8_, lean_object* v_inst_9_, lean_object* v_f_10_, lean_object* v_i_11_, lean_object* v_acc_12_){
_start:
{
uint8_t v___x_13_; 
v___x_13_ = lean_nat_dec_lt(v_i_11_, v_n_8_);
if (v___x_13_ == 0)
{
lean_object* v_toApplicative_14_; lean_object* v_toPure_15_; lean_object* v___x_16_; 
lean_dec(v_i_11_);
lean_dec(v_f_10_);
lean_dec(v_n_8_);
v_toApplicative_14_ = lean_ctor_get(v_inst_9_, 0);
lean_inc_ref(v_toApplicative_14_);
lean_dec_ref(v_inst_9_);
v_toPure_15_ = lean_ctor_get(v_toApplicative_14_, 1);
lean_inc(v_toPure_15_);
lean_dec_ref(v_toApplicative_14_);
v___x_16_ = lean_apply_2(v_toPure_15_, lean_box(0), v_acc_12_);
return v___x_16_;
}
else
{
lean_object* v_toBind_17_; lean_object* v___f_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v_toBind_17_ = lean_ctor_get(v_inst_9_, 1);
lean_inc(v_toBind_17_);
lean_inc(v_f_10_);
lean_inc(v_i_11_);
v___f_18_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_18_, 0, v_i_11_);
lean_closure_set(v___f_18_, 1, v_acc_12_);
lean_closure_set(v___f_18_, 2, v_n_8_);
lean_closure_set(v___f_18_, 3, v_inst_9_);
lean_closure_set(v___f_18_, 4, v_f_10_);
v___x_19_ = lean_apply_1(v_f_10_, v_i_11_);
v___x_20_ = lean_apply_4(v_toBind_17_, lean_box(0), lean_box(0), v___x_19_, v___f_18_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0(lean_object* v_i_21_, lean_object* v_acc_22_, lean_object* v_n_23_, lean_object* v_inst_24_, lean_object* v_f_25_, lean_object* v_____do__lift_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_add(v_i_21_, v___x_27_);
v___x_29_ = lean_array_push(v_acc_22_, v_____do__lift_26_);
v___x_30_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg(v_n_23_, v_inst_24_, v_f_25_, v___x_28_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go(lean_object* v_m_31_, lean_object* v_00_u03b1_32_, lean_object* v_n_33_, lean_object* v_inst_34_, lean_object* v_f_35_, lean_object* v_i_36_, lean_object* v_h_x27_37_, lean_object* v_acc_38_, lean_object* v_w_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg(v_n_33_, v_inst_34_, v_f_35_, v_i_36_, v_acc_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFnM___redArg(lean_object* v_n_41_, lean_object* v_inst_42_, lean_object* v_f_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_mk_empty_array_with_capacity(v_n_41_);
v___x_46_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg(v_n_41_, v_inst_42_, v_f_43_, v___x_44_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFnM(lean_object* v_m_47_, lean_object* v_00_u03b1_48_, lean_object* v_n_49_, lean_object* v_inst_50_, lean_object* v_f_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Vector_ofFnM___redArg(v_n_49_, v_inst_50_, v_f_51_);
return v___x_52_;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__10));
v___x_80_ = l_Lean_mkAtom(v___x_79_);
return v___x_80_;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12);
v___x_82_ = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5));
v___x_83_ = lean_array_push(v___x_82_, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__16));
v___x_95_ = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5));
v___x_96_ = lean_array_push(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17);
v___x_98_ = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15));
v___x_99_ = lean_box(2);
v___x_100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
lean_ctor_set(v___x_100_, 2, v___x_97_);
return v___x_100_;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18);
v___x_102_ = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13);
v___x_103_ = lean_array_push(v___x_102_, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19);
v___x_105_ = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11));
v___x_106_ = lean_box(2);
v___x_107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
lean_ctor_set(v___x_107_, 2, v___x_104_);
return v___x_107_;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20);
v___x_109_ = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5));
v___x_110_ = lean_array_push(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_111_ = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21);
v___x_112_ = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__9));
v___x_113_ = lean_box(2);
v___x_114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_111_);
return v___x_114_;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22);
v___x_116_ = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5));
v___x_117_ = lean_array_push(v___x_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23);
v___x_119_ = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7));
v___x_120_ = lean_box(2);
v___x_121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___x_119_);
lean_ctor_set(v___x_121_, 2, v___x_118_);
return v___x_121_;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24);
v___x_123_ = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5));
v___x_124_ = lean_array_push(v___x_123_, v___x_122_);
return v___x_124_;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_125_ = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25);
v___x_126_ = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4));
v___x_127_ = lean_box(2);
v___x_128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
lean_ctor_set(v___x_128_, 2, v___x_125_);
return v___x_128_;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26);
return v___x_129_;
}
}
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_OfFn(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Monadic(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_OfFn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Vector_OfFn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5 = _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5();
lean_mark_persistent(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_OfFn(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Monadic(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_OfFn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Vector_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Vector_OfFn(builtin);
}
#ifdef __cplusplus
}
#endif
