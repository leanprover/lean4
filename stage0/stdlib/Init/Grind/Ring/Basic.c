// Lean compiler output
// Module: Init.Grind.Ring.Basic
// Imports: public import Init.Grind.Module.Basic import Init.ByCases import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.LemmasAux import Init.Data.Int.Pow import Init.Data.Nat.Div.Lemmas import Init.Data.Nat.Lemmas import Init.Omega import Init.RCases
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
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__3 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__3_value;
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value;
static const lean_array_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5_value;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__6 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__8 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__8_value;
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9_value;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "intros"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__10 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__10_value;
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(26, 175, 18, 116, 252, 50, 128, 45)}};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13;
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9_value),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5_value)}};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14_value;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__18 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__18_value;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__21 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__21_value;
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value_aux_0),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value_aux_1),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value_aux_2),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__21_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22_value;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__23 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__23_value;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31;
static lean_once_cell_t l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32;
LEAN_EXPORT lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam;
LEAN_EXPORT lean_object* l_Lean_Grind_Semiring_ofNat__eq__natCast___autoParam;
LEAN_EXPORT lean_object* l_Lean_Grind_Semiring_nsmul__eq__natCast__mul___autoParam;
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_zsmul__natCast__eq__nsmul___autoParam;
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_intCast__ofNat___autoParam;
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_intCast__neg___autoParam;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__0 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__0_value;
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value_aux_0),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value_aux_1),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value_aux_2),((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 145, 9, 18, 75, 146, 159, 78)}};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6;
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__7 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__7_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rwSeq"};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__15 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__15_value;
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value_aux_0),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value_aux_1),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value_aux_2),((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__15_value),LEAN_SCALAR_PTR_LITERAL(50, 16, 185, 246, 153, 187, 181, 153)}};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16_value;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "rw"};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__17 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__17_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__20 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__20_value;
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_0),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_1),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_2),((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__20_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rwRuleSeq"};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__25 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__25_value;
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value_aux_0),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value_aux_1),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value_aux_2),((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__25_value),LEAN_SCALAR_PTR_LITERAL(170, 212, 96, 120, 212, 17, 101, 100)}};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26_value;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__27 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__27_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rwRule"};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__30 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__30_value;
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value_aux_0),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value_aux_1),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value_aux_2),((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__30_value),LEAN_SCALAR_PTR_LITERAL(163, 12, 102, 31, 194, 63, 248, 122)}};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31_value;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mul_comm"};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__32 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__32_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34;
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__32_value),LEAN_SCALAR_PTR_LITERAL(208, 157, 4, 183, 17, 39, 221, 175)}};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__35 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__35_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__40 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__40_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mul_one"};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45;
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43_value),LEAN_SCALAR_PTR_LITERAL(185, 178, 196, 247, 70, 46, 81, 207)}};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__46 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__46_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__53 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__53_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64;
static lean_once_cell_t l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65;
LEAN_EXPORT lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam;
static const lean_string_object l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "zero_mul"};
static const lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0 = (const lean_object*)&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2;
static const lean_ctor_object l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 47, 112, 108, 82, 3, 108)}};
static const lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__3 = (const lean_object*)&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__3_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19;
static lean_once_cell_t l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20;
LEAN_EXPORT lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam;
static const lean_string_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0 = (const lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2;
static const lean_ctor_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__3 = (const lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__3_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5;
static const lean_string_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6 = (const lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8;
static const lean_ctor_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(38, 183, 255, 58, 84, 31, 100, 5)}};
static const lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__9 = (const lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__9_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16;
static const lean_string_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "left_distrib"};
static const lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17 = (const lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19;
static const lean_ctor_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17_value),LEAN_SCALAR_PTR_LITERAL(125, 89, 23, 115, 236, 84, 239, 248)}};
static const lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__20 = (const lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__20_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25;
static const lean_string_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__26 = (const lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__26_value;
static const lean_string_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__27 = (const lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__27_value;
static const lean_ctor_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value_aux_0),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value_aux_1),((lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value_aux_2),((lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__27_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28 = (const lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28_value;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50;
static lean_once_cell_t l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51;
LEAN_EXPORT lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_toCommSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_toCommSemiring___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_toCommSemiring(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_toCommSemiring___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Semiring_toNatModule___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Semiring_toNatModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_toAddCommGroup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_toAddCommGroup(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_toIntModule___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_toIntModule(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12);
v___x_30_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14));
v___x_37_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13);
v___x_38_ = lean_array_push(v___x_37_, v___x_36_);
return v___x_38_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_39_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15);
v___x_40_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11));
v___x_41_ = lean_box(2);
v___x_42_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_40_);
lean_ctor_set(v___x_42_, 2, v___x_39_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16);
v___x_44_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_45_ = lean_array_push(v___x_44_, v___x_43_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__18));
v___x_48_ = l_Lean_mkAtom(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19);
v___x_50_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17);
v___x_51_ = lean_array_push(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__23));
v___x_60_ = l_Lean_mkAtom(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24);
v___x_62_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_63_ = lean_array_push(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25);
v___x_65_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22));
v___x_66_ = lean_box(2);
v___x_67_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_64_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26);
v___x_69_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20);
v___x_70_ = lean_array_push(v___x_69_, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_71_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27);
v___x_72_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
v___x_73_ = lean_box(2);
v___x_74_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_72_);
lean_ctor_set(v___x_74_, 2, v___x_71_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28);
v___x_76_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_77_ = lean_array_push(v___x_76_, v___x_75_);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29);
v___x_79_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7));
v___x_80_ = lean_box(2);
v___x_81_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
lean_ctor_set(v___x_81_, 2, v___x_78_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30);
v___x_83_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_84_ = lean_array_push(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31);
v___x_86_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4));
v___x_87_ = lean_box(2);
v___x_88_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_85_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam(void){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__eq__natCast___autoParam(void){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_nsmul__eq__natCast__mul___autoParam(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Grind_Ring_zsmul__natCast__eq__nsmul___autoParam(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_Grind_Ring_intCast__ofNat___autoParam(void){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Grind_Ring_intCast__neg___autoParam(void){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__0));
v___x_102_ = l_Lean_mkAtom(v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2);
v___x_104_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_105_ = lean_array_push(v___x_104_, v___x_103_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4));
v___x_108_ = lean_string_utf8_byte_size(v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_109_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4));
v___x_112_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___x_110_);
lean_ctor_set(v___x_112_, 2, v___x_109_);
return v___x_112_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_115_ = lean_box(0);
v___x_116_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__7));
v___x_117_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6);
v___x_118_ = lean_box(2);
v___x_119_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_117_);
lean_ctor_set(v___x_119_, 2, v___x_116_);
lean_ctor_set(v___x_119_, 3, v___x_115_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8);
v___x_121_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_122_ = lean_array_push(v___x_121_, v___x_120_);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_123_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9);
v___x_124_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
v___x_125_ = lean_box(2);
v___x_126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_124_);
lean_ctor_set(v___x_126_, 2, v___x_123_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10);
v___x_128_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3);
v___x_129_ = lean_array_push(v___x_128_, v___x_127_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_130_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11);
v___x_131_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1));
v___x_132_ = lean_box(2);
v___x_133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_131_);
lean_ctor_set(v___x_133_, 2, v___x_130_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12);
v___x_135_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_136_ = lean_array_push(v___x_135_, v___x_134_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19);
v___x_138_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13);
v___x_139_ = lean_array_push(v___x_138_, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__17));
v___x_148_ = l_Lean_mkAtom(v___x_147_);
return v___x_148_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18);
v___x_150_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_151_ = lean_array_push(v___x_150_, v___x_149_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14));
v___x_159_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_160_ = lean_array_push(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22);
v___x_162_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21));
v___x_163_ = lean_box(2);
v___x_164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
lean_ctor_set(v___x_164_, 2, v___x_161_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23);
v___x_166_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19);
v___x_167_ = lean_array_push(v___x_166_, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__27));
v___x_176_ = l_Lean_mkAtom(v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28);
v___x_178_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_179_ = lean_array_push(v___x_178_, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__32));
v___x_188_ = lean_string_utf8_byte_size(v___x_187_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33);
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__32));
v___x_192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
lean_ctor_set(v___x_192_, 2, v___x_189_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_195_ = lean_box(0);
v___x_196_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__35));
v___x_197_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34);
v___x_198_ = lean_box(2);
v___x_199_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
lean_ctor_set(v___x_199_, 2, v___x_196_);
lean_ctor_set(v___x_199_, 3, v___x_195_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36);
v___x_201_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22);
v___x_202_ = lean_array_push(v___x_201_, v___x_200_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_203_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37);
v___x_204_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31));
v___x_205_ = lean_box(2);
v___x_206_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_204_);
lean_ctor_set(v___x_206_, 2, v___x_203_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38);
v___x_208_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_209_ = lean_array_push(v___x_208_, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__40));
v___x_212_ = l_Lean_mkAtom(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41);
v___x_214_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39);
v___x_215_ = lean_array_push(v___x_214_, v___x_213_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43));
v___x_218_ = lean_string_utf8_byte_size(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_219_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43));
v___x_222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_219_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_225_ = lean_box(0);
v___x_226_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__46));
v___x_227_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45);
v___x_228_ = lean_box(2);
v___x_229_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___x_227_);
lean_ctor_set(v___x_229_, 2, v___x_226_);
lean_ctor_set(v___x_229_, 3, v___x_225_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47);
v___x_231_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22);
v___x_232_ = lean_array_push(v___x_231_, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_233_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48);
v___x_234_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31));
v___x_235_ = lean_box(2);
v___x_236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___x_234_);
lean_ctor_set(v___x_236_, 2, v___x_233_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49);
v___x_238_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42);
v___x_239_ = lean_array_push(v___x_238_, v___x_237_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_240_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50);
v___x_241_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
v___x_242_ = lean_box(2);
v___x_243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
lean_ctor_set(v___x_243_, 2, v___x_240_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51);
v___x_245_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29);
v___x_246_ = lean_array_push(v___x_245_, v___x_244_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__53));
v___x_249_ = l_Lean_mkAtom(v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54);
v___x_251_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52);
v___x_252_ = lean_array_push(v___x_251_, v___x_250_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_253_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55);
v___x_254_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26));
v___x_255_ = lean_box(2);
v___x_256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v___x_254_);
lean_ctor_set(v___x_256_, 2, v___x_253_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56);
v___x_258_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24);
v___x_259_ = lean_array_push(v___x_258_, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14));
v___x_261_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57);
v___x_262_ = lean_array_push(v___x_261_, v___x_260_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_263_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58);
v___x_264_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16));
v___x_265_ = lean_box(2);
v___x_266_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_264_);
lean_ctor_set(v___x_266_, 2, v___x_263_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59);
v___x_268_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14);
v___x_269_ = lean_array_push(v___x_268_, v___x_267_);
return v___x_269_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_270_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60);
v___x_271_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
v___x_272_ = lean_box(2);
v___x_273_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_271_);
lean_ctor_set(v___x_273_, 2, v___x_270_);
return v___x_273_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61);
v___x_275_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_276_ = lean_array_push(v___x_275_, v___x_274_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_277_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62);
v___x_278_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7));
v___x_279_ = lean_box(2);
v___x_280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
lean_ctor_set(v___x_280_, 2, v___x_277_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63);
v___x_282_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_283_ = lean_array_push(v___x_282_, v___x_281_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_284_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64);
v___x_285_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4));
v___x_286_ = lean_box(2);
v___x_287_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___x_285_);
lean_ctor_set(v___x_287_, 2, v___x_284_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam(void){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0));
v___x_291_ = lean_string_utf8_byte_size(v___x_290_);
return v___x_291_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_292_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = ((lean_object*)(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0));
v___x_295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
lean_ctor_set(v___x_295_, 2, v___x_292_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_298_ = lean_box(0);
v___x_299_ = ((lean_object*)(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__3));
v___x_300_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2);
v___x_301_ = lean_box(2);
v___x_302_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
lean_ctor_set(v___x_302_, 2, v___x_299_);
lean_ctor_set(v___x_302_, 3, v___x_298_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4);
v___x_304_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22);
v___x_305_ = lean_array_push(v___x_304_, v___x_303_);
return v___x_305_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_306_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5);
v___x_307_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31));
v___x_308_ = lean_box(2);
v___x_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_307_);
lean_ctor_set(v___x_309_, 2, v___x_306_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6);
v___x_311_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42);
v___x_312_ = lean_array_push(v___x_311_, v___x_310_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7);
v___x_314_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
v___x_315_ = lean_box(2);
v___x_316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_313_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8);
v___x_318_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29);
v___x_319_ = lean_array_push(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54);
v___x_321_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9);
v___x_322_ = lean_array_push(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_323_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10);
v___x_324_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26));
v___x_325_ = lean_box(2);
v___x_326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_324_);
lean_ctor_set(v___x_326_, 2, v___x_323_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11);
v___x_328_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24);
v___x_329_ = lean_array_push(v___x_328_, v___x_327_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14));
v___x_331_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12);
v___x_332_ = lean_array_push(v___x_331_, v___x_330_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_333_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13);
v___x_334_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16));
v___x_335_ = lean_box(2);
v___x_336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
lean_ctor_set(v___x_336_, 2, v___x_333_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14);
v___x_338_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14);
v___x_339_ = lean_array_push(v___x_338_, v___x_337_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_340_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15);
v___x_341_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
v___x_342_ = lean_box(2);
v___x_343_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
lean_ctor_set(v___x_343_, 2, v___x_340_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16);
v___x_345_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_346_ = lean_array_push(v___x_345_, v___x_344_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_347_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17);
v___x_348_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7));
v___x_349_ = lean_box(2);
v___x_350_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_348_);
lean_ctor_set(v___x_350_, 2, v___x_347_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18);
v___x_352_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_353_ = lean_array_push(v___x_352_, v___x_351_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_354_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19);
v___x_355_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4));
v___x_356_ = lean_box(2);
v___x_357_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v___x_355_);
lean_ctor_set(v___x_357_, 2, v___x_354_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam(void){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = lean_obj_once(&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20, &l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20_once, _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0));
v___x_361_ = lean_string_utf8_byte_size(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_362_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1);
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0));
v___x_365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
lean_ctor_set(v___x_365_, 2, v___x_362_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_368_ = lean_box(0);
v___x_369_ = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__3));
v___x_370_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2);
v___x_371_ = lean_box(2);
v___x_372_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v___x_370_);
lean_ctor_set(v___x_372_, 2, v___x_369_);
lean_ctor_set(v___x_372_, 3, v___x_368_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4);
v___x_374_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9);
v___x_375_ = lean_array_push(v___x_374_, v___x_373_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6));
v___x_378_ = lean_string_utf8_byte_size(v___x_377_);
return v___x_378_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_379_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7);
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6));
v___x_382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___x_380_);
lean_ctor_set(v___x_382_, 2, v___x_379_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_385_ = lean_box(0);
v___x_386_ = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__9));
v___x_387_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8);
v___x_388_ = lean_box(2);
v___x_389_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_387_);
lean_ctor_set(v___x_389_, 2, v___x_386_);
lean_ctor_set(v___x_389_, 3, v___x_385_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10);
v___x_391_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5);
v___x_392_ = lean_array_push(v___x_391_, v___x_390_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_393_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11);
v___x_394_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
v___x_395_ = lean_box(2);
v___x_396_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_394_);
lean_ctor_set(v___x_396_, 2, v___x_393_);
return v___x_396_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12);
v___x_398_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3);
v___x_399_ = lean_array_push(v___x_398_, v___x_397_);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_400_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13);
v___x_401_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1));
v___x_402_ = lean_box(2);
v___x_403_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_401_);
lean_ctor_set(v___x_403_, 2, v___x_400_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14);
v___x_405_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_406_ = lean_array_push(v___x_405_, v___x_404_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = lean_obj_once(&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19, &l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19_once, _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19);
v___x_408_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15);
v___x_409_ = lean_array_push(v___x_408_, v___x_407_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17));
v___x_412_ = lean_string_utf8_byte_size(v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_413_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17));
v___x_416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
lean_ctor_set(v___x_416_, 2, v___x_413_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_419_ = lean_box(0);
v___x_420_ = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__20));
v___x_421_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19);
v___x_422_ = lean_box(2);
v___x_423_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_421_);
lean_ctor_set(v___x_423_, 2, v___x_420_);
lean_ctor_set(v___x_423_, 3, v___x_419_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21);
v___x_425_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22);
v___x_426_ = lean_array_push(v___x_425_, v___x_424_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_427_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22);
v___x_428_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31));
v___x_429_ = lean_box(2);
v___x_430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_428_);
lean_ctor_set(v___x_430_, 2, v___x_427_);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23);
v___x_432_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42);
v___x_433_ = lean_array_push(v___x_432_, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41);
v___x_435_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24);
v___x_436_ = lean_array_push(v___x_435_, v___x_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36);
v___x_445_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_446_ = lean_array_push(v___x_445_, v___x_444_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10);
v___x_448_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_449_ = lean_array_push(v___x_448_, v___x_447_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_450_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30);
v___x_451_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
v___x_452_ = lean_box(2);
v___x_453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
lean_ctor_set(v___x_453_, 2, v___x_450_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31);
v___x_455_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29);
v___x_456_ = lean_array_push(v___x_455_, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_457_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32);
v___x_458_ = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28));
v___x_459_ = lean_box(2);
v___x_460_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___x_458_);
lean_ctor_set(v___x_460_, 2, v___x_457_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33);
v___x_462_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22);
v___x_463_ = lean_array_push(v___x_462_, v___x_461_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_464_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34);
v___x_465_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31));
v___x_466_ = lean_box(2);
v___x_467_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
lean_ctor_set(v___x_467_, 2, v___x_464_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35);
v___x_469_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25);
v___x_470_ = lean_array_push(v___x_469_, v___x_468_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41);
v___x_472_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36);
v___x_473_ = lean_array_push(v___x_472_, v___x_471_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35);
v___x_475_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37);
v___x_476_ = lean_array_push(v___x_475_, v___x_474_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_477_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38);
v___x_478_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
v___x_479_ = lean_box(2);
v___x_480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_478_);
lean_ctor_set(v___x_480_, 2, v___x_477_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39);
v___x_482_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29);
v___x_483_ = lean_array_push(v___x_482_, v___x_481_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54);
v___x_485_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40);
v___x_486_ = lean_array_push(v___x_485_, v___x_484_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_487_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41);
v___x_488_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26));
v___x_489_ = lean_box(2);
v___x_490_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_488_);
lean_ctor_set(v___x_490_, 2, v___x_487_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42);
v___x_492_ = lean_obj_once(&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24, &l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24_once, _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24);
v___x_493_ = lean_array_push(v___x_492_, v___x_491_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_494_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14));
v___x_495_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43);
v___x_496_ = lean_array_push(v___x_495_, v___x_494_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_497_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44);
v___x_498_ = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16));
v___x_499_ = lean_box(2);
v___x_500_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v___x_498_);
lean_ctor_set(v___x_500_, 2, v___x_497_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45);
v___x_502_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16);
v___x_503_ = lean_array_push(v___x_502_, v___x_501_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_504_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46);
v___x_505_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
v___x_506_ = lean_box(2);
v___x_507_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v___x_505_);
lean_ctor_set(v___x_507_, 2, v___x_504_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47);
v___x_509_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_510_ = lean_array_push(v___x_509_, v___x_508_);
return v___x_510_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_511_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48);
v___x_512_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7));
v___x_513_ = lean_box(2);
v___x_514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v___x_512_);
lean_ctor_set(v___x_514_, 2, v___x_511_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49);
v___x_516_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5));
v___x_517_ = lean_array_push(v___x_516_, v___x_515_);
return v___x_517_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_518_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50);
v___x_519_ = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4));
v___x_520_ = lean_box(2);
v___x_521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
lean_ctor_set(v___x_521_, 1, v___x_519_);
lean_ctor_set(v___x_521_, 2, v___x_518_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam(void){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_obj_once(&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51, &l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51_once, _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_toCommSemiring___redArg(lean_object* v_self_523_){
_start:
{
lean_object* v_toSemiring_524_; 
v_toSemiring_524_ = lean_ctor_get(v_self_523_, 0);
lean_inc_ref(v_toSemiring_524_);
return v_toSemiring_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_toCommSemiring___redArg___boxed(lean_object* v_self_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_Grind_CommRing_toCommSemiring___redArg(v_self_525_);
lean_dec_ref(v_self_525_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_toCommSemiring(lean_object* v_00_u03b1_527_, lean_object* v_self_528_){
_start:
{
lean_object* v_toSemiring_529_; 
v_toSemiring_529_ = lean_ctor_get(v_self_528_, 0);
lean_inc_ref(v_toSemiring_529_);
return v_toSemiring_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_toCommSemiring___boxed(lean_object* v_00_u03b1_530_, lean_object* v_self_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Grind_CommRing_toCommSemiring(v_00_u03b1_530_, v_self_531_);
lean_dec_ref(v_self_531_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Semiring_toNatModule___redArg(lean_object* v_I_533_){
_start:
{
lean_object* v_toAdd_534_; lean_object* v_ofNat_535_; lean_object* v_nsmul_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_toAdd_534_ = lean_ctor_get(v_I_533_, 0);
lean_inc(v_toAdd_534_);
v_ofNat_535_ = lean_ctor_get(v_I_533_, 3);
lean_inc(v_ofNat_535_);
v_nsmul_536_ = lean_ctor_get(v_I_533_, 4);
lean_inc(v_nsmul_536_);
lean_dec_ref(v_I_533_);
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = lean_apply_1(v_ofNat_535_, v___x_537_);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v_toAdd_534_);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v_nsmul_536_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Semiring_toNatModule(lean_object* v_00_u03b1_541_, lean_object* v_I_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_Grind_Semiring_toNatModule___redArg(v_I_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_toAddCommGroup___redArg(lean_object* v_I_544_){
_start:
{
lean_object* v_toSemiring_545_; lean_object* v_toNeg_546_; lean_object* v_toSub_547_; lean_object* v_toAdd_548_; lean_object* v_ofNat_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_toSemiring_545_ = lean_ctor_get(v_I_544_, 0);
lean_inc_ref(v_toSemiring_545_);
v_toNeg_546_ = lean_ctor_get(v_I_544_, 1);
lean_inc(v_toNeg_546_);
v_toSub_547_ = lean_ctor_get(v_I_544_, 2);
lean_inc(v_toSub_547_);
lean_dec_ref(v_I_544_);
v_toAdd_548_ = lean_ctor_get(v_toSemiring_545_, 0);
lean_inc(v_toAdd_548_);
v_ofNat_549_ = lean_ctor_get(v_toSemiring_545_, 3);
lean_inc(v_ofNat_549_);
lean_dec_ref(v_toSemiring_545_);
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = lean_apply_1(v_ofNat_549_, v___x_550_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v_toAdd_548_);
v___x_553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v_toNeg_546_);
lean_ctor_set(v___x_553_, 2, v_toSub_547_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_toAddCommGroup(lean_object* v_00_u03b1_554_, lean_object* v_I_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Grind_Ring_toAddCommGroup___redArg(v_I_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_toIntModule___redArg(lean_object* v_I_557_){
_start:
{
lean_object* v_toSemiring_558_; lean_object* v_toNeg_559_; lean_object* v_toSub_560_; lean_object* v_zsmul_561_; lean_object* v___x_562_; lean_object* v_toAddCommMonoid_563_; lean_object* v_toZero_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_575_; 
v_toSemiring_558_ = lean_ctor_get(v_I_557_, 0);
lean_inc_ref_n(v_toSemiring_558_, 2);
v_toNeg_559_ = lean_ctor_get(v_I_557_, 1);
lean_inc(v_toNeg_559_);
v_toSub_560_ = lean_ctor_get(v_I_557_, 2);
lean_inc(v_toSub_560_);
v_zsmul_561_ = lean_ctor_get(v_I_557_, 4);
lean_inc(v_zsmul_561_);
lean_dec_ref(v_I_557_);
v___x_562_ = l_Lean_Grind_Semiring_toNatModule___redArg(v_toSemiring_558_);
v_toAddCommMonoid_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_toAddCommMonoid_563_);
lean_dec_ref(v___x_562_);
v_toZero_564_ = lean_ctor_get(v_toAddCommMonoid_563_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v_toAddCommMonoid_563_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v_toAddCommMonoid_563_, 1);
lean_dec(v_unused_576_);
v___x_566_ = v_toAddCommMonoid_563_;
v_isShared_567_ = v_isSharedCheck_575_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_toZero_564_);
lean_dec(v_toAddCommMonoid_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_575_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v_toAdd_568_; lean_object* v_nsmul_569_; lean_object* v___x_571_; 
v_toAdd_568_ = lean_ctor_get(v_toSemiring_558_, 0);
lean_inc(v_toAdd_568_);
v_nsmul_569_ = lean_ctor_get(v_toSemiring_558_, 4);
lean_inc(v_nsmul_569_);
lean_dec_ref(v_toSemiring_558_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 1, v_toAdd_568_);
v___x_571_ = v___x_566_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_toZero_564_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_toAdd_568_);
v___x_571_ = v_reuseFailAlloc_574_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_toNeg_559_);
lean_ctor_set(v___x_572_, 2, v_toSub_560_);
v___x_573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v_nsmul_569_);
lean_ctor_set(v___x_573_, 2, v_zsmul_561_);
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_toIntModule(lean_object* v_00_u03b1_577_, lean_object* v_I_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Grind_Ring_toIntModule___redArg(v_I_578_);
return v___x_579_;
}
}
lean_object* runtime_initialize_Init_Grind_Module_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Ring_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Module_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Ring_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Grind_Semiring_ofNat__succ___autoParam = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam);
l_Lean_Grind_Semiring_ofNat__eq__natCast___autoParam = _init_l_Lean_Grind_Semiring_ofNat__eq__natCast___autoParam();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__eq__natCast___autoParam);
l_Lean_Grind_Semiring_nsmul__eq__natCast__mul___autoParam = _init_l_Lean_Grind_Semiring_nsmul__eq__natCast__mul___autoParam();
lean_mark_persistent(l_Lean_Grind_Semiring_nsmul__eq__natCast__mul___autoParam);
l_Lean_Grind_Ring_zsmul__natCast__eq__nsmul___autoParam = _init_l_Lean_Grind_Ring_zsmul__natCast__eq__nsmul___autoParam();
lean_mark_persistent(l_Lean_Grind_Ring_zsmul__natCast__eq__nsmul___autoParam);
l_Lean_Grind_Ring_intCast__ofNat___autoParam = _init_l_Lean_Grind_Ring_intCast__ofNat___autoParam();
lean_mark_persistent(l_Lean_Grind_Ring_intCast__ofNat___autoParam);
l_Lean_Grind_Ring_intCast__neg___autoParam = _init_l_Lean_Grind_Ring_intCast__neg___autoParam();
lean_mark_persistent(l_Lean_Grind_Ring_intCast__neg___autoParam);
l_Lean_Grind_CommSemiring_one__mul___autoParam = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam);
l_Lean_Grind_CommSemiring_mul__zero___autoParam = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam);
l_Lean_Grind_CommSemiring_right__distrib___autoParam = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Module_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Module_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Ring_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
