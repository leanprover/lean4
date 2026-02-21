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
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5;
static const lean_string_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__6 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value;
static const lean_string_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__8 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__9 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__9_value;
static const lean_string_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__10 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__10_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11 = (const lean_object*)&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value;
lean_object* l_Lean_mkAtom(lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__16;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_1);
lean_closure_set(x_11, 3, x_2);
lean_closure_set(x_11, 4, x_3);
x_12 = lean_apply_1(x_3, x_4);
x_13 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = lean_array_push(x_2, x_6);
x_10 = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg(x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg(x_3, x_4, x_5, x_6, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFnM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_1);
x_6 = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFnM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Vector_ofFnM___redArg(x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__10));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12);
x_2 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5);
x_2 = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__16, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__16_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__16);
x_2 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17);
x_2 = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18);
x_2 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19);
x_2 = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20);
x_2 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21);
x_2 = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22);
x_2 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23);
x_2 = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24);
x_2 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25);
x_2 = ((lean_object*)(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26, &l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26_once, _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26);
return x_1;
}
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
l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5 = _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5();
lean_mark_persistent(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
