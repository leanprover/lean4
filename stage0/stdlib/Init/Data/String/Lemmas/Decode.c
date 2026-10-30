// Lean compiler output
// Module: Init.Data.String.Lemmas.Decode
// Imports: public import Init.Data.String.Defs public import Init.Data.Char.Basic public import Init.Data.Ord.Basic public import Init.Data.Ord.UInt public import Init.Data.ByteArray.Lex public import Init.Data.String.Basic import Init.Data.List.Lemmas import Init.Data.List.Basic import Init.Data.List.Lex import Init.Data.Order.Lemmas import Init.Data.Order.LemmasExtra import Init.Data.List.Sublist import Init.Data.String.Decode import Init.Omega import Init.Data.UInt.Lemmas import Init.Data.String.Basic import Init.Data.ByteArray.Lex import Init.Data.Char.Order import Init.Data.BitVec.Package import Init.Data.List.Package import Init.Data.Char.Lemmas import Init.Data.BitVec.Lemmas import all Init.Data.String.Decode
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
static const lean_string_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__0 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__0_value;
static const lean_string_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__1 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__1_value;
static const lean_string_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__2 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__2_value;
static const lean_string_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__3 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__4 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__4_value;
static const lean_array_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__5 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__5_value;
static const lean_string_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__6 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__6_value;
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__7 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__7_value;
static const lean_string_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__8 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__8_value;
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__9 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__9_value;
static const lean_string_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__10 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__10_value;
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__11 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__11_value;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__12;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__13;
static const lean_string_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__14 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__14_value;
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__15_value_aux_1),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__15_value_aux_2),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__15 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__15_value;
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__9_value),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__5_value)}};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__16 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__16_value;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__17;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__18;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__19;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__20;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__21;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__22;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__23;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__24;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__25;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__26;
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1;
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__3;
static const lean_string_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__0 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__0_value;
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__1 = (const lean_object*)&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__1_value;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__2;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__3;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__4;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__5;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__6;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__7;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__8;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__9;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__10;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__11;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__12;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__13;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__14;
static lean_once_cell_t l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__15;
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5;
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__12, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__12_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__17(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__16));
v___x_43_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__5));
v___x_44_ = lean_array_push(v___x_43_, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__18(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_45_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__17, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__17_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__17);
v___x_46_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__15));
v___x_47_ = lean_box(2);
v___x_48_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
lean_ctor_set(v___x_48_, 2, v___x_45_);
return v___x_48_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__19(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__18, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__18_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__18);
v___x_50_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__13, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__13_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__13);
v___x_51_ = lean_array_push(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__20(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__19, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__19_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__19);
v___x_53_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__11));
v___x_54_ = lean_box(2);
v___x_55_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
lean_ctor_set(v___x_55_, 2, v___x_52_);
return v___x_55_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__21(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__20, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__20_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__20);
v___x_57_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__5));
v___x_58_ = lean_array_push(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__22(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__21, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__21_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__21);
v___x_60_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__9));
v___x_61_ = lean_box(2);
v___x_62_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
lean_ctor_set(v___x_62_, 2, v___x_59_);
return v___x_62_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__23(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__22, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__22_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__22);
v___x_64_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__5));
v___x_65_ = lean_array_push(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__24(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__23, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__23_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__23);
v___x_67_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__7));
v___x_68_ = lean_box(2);
v___x_69_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
return v___x_69_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__25(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__24, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__24_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__24);
v___x_71_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__5));
v___x_72_ = lean_array_push(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__26(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__25, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__25_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__25);
v___x_74_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__4));
v___x_75_ = lean_box(2);
v___x_76_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_73_);
return v___x_76_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__26, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__26_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__26);
return v___x_77_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__3(void){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__26, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__26_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__26);
return v___x_78_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__2(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__0));
v___x_86_ = l_Lean_mkAtom(v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__3(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__2, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__2_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__2);
v___x_88_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__5));
v___x_89_ = lean_array_push(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__4(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__18, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__18_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__18);
v___x_91_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__3, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__3_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__3);
v___x_92_ = lean_array_push(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__5(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__16));
v___x_94_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__4, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__4_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__4);
v___x_95_ = lean_array_push(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__6(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__16));
v___x_97_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__5, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__5_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__5);
v___x_98_ = lean_array_push(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__7(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__16));
v___x_100_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__6, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__6_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__6);
v___x_101_ = lean_array_push(v___x_100_, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__8(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__16));
v___x_103_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__7, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__7_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__7);
v___x_104_ = lean_array_push(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__9(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_105_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__8, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__8_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__8);
v___x_106_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__1));
v___x_107_ = lean_box(2);
v___x_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
lean_ctor_set(v___x_108_, 2, v___x_105_);
return v___x_108_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__10(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__9, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__9_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__9);
v___x_110_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__5));
v___x_111_ = lean_array_push(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__11(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__10, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__10_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__10);
v___x_113_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__9));
v___x_114_ = lean_box(2);
v___x_115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
lean_ctor_set(v___x_115_, 2, v___x_112_);
return v___x_115_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__12(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__11, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__11_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__11);
v___x_117_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__5));
v___x_118_ = lean_array_push(v___x_117_, v___x_116_);
return v___x_118_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__13(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_119_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__12, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__12_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__12);
v___x_120_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__7));
v___x_121_ = lean_box(2);
v___x_122_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v___x_120_);
lean_ctor_set(v___x_122_, 2, v___x_119_);
return v___x_122_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__14(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_123_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__13, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__13_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__13);
v___x_124_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__5));
v___x_125_ = lean_array_push(v___x_124_, v___x_123_);
return v___x_125_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__15(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_126_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__14, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__14_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__14);
v___x_127_ = ((lean_object*)(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1___closed__4));
v___x_128_ = lean_box(2);
v___x_129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
lean_ctor_set(v___x_129_, 2, v___x_126_);
return v___x_129_;
}
}
static lean_object* _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5(void){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__15, &l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__15_once, _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5___closed__15);
return v___x_130_;
}
}
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Lex(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lex(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_LemmasExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Decode(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Lex(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Package(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Package(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Decode(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lemmas_Decode(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_LemmasExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Decode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Decode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Lemmas_Decode(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1 = _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1();
lean_mark_persistent(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__1);
l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__3 = _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__3();
lean_mark_persistent(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__3);
l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5 = _init_l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5();
lean_mark_persistent(l___private_Init_Data_String_Lemmas_Decode_0__String_helper___auto__5);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Lex(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lex(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Order_LemmasExtra(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_String_Decode(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Lex(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Order(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Package(uint8_t builtin);
lean_object* initialize_Init_Data_List_Package(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_Decode(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lemmas_Decode(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_LemmasExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Decode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Decode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Decode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Lemmas_Decode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Lemmas_Decode(builtin);
}
#ifdef __cplusplus
}
#endif
