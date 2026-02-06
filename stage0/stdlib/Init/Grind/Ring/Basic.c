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
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__3 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__6 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7_value;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__8 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9_value;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "intros"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__10 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__10_value;
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(26, 175, 18, 116, 252, 50, 128, 45)}};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11_value;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17;
static const lean_string_object l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__18 = (const lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__18_value;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19;
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
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30;
static lean_object* l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31;
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
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6;
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__7 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__7_value;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13;
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
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__20 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__20_value;
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_0),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_1),((lean_object*)&l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value_aux_2),((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__20_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21_value;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23;
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
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28;
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
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34;
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__32_value),LEAN_SCALAR_PTR_LITERAL(208, 157, 4, 183, 17, 39, 221, 175)}};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__35 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__35_value;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__40 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__40_value;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mul_one"};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43_value;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45;
static const lean_ctor_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43_value),LEAN_SCALAR_PTR_LITERAL(185, 178, 196, 247, 70, 46, 81, 207)}};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__46 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__46_value;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52;
static const lean_string_object l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__53 = (const lean_object*)&l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__53_value;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64;
static lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65;
LEAN_EXPORT lean_object* l_Lean_Grind_CommSemiring_one__mul___autoParam;
static const lean_string_object l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "zero_mul"};
static const lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0 = (const lean_object*)&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0_value;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2;
static const lean_ctor_object l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 47, 112, 108, 82, 3, 108)}};
static const lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__3 = (const lean_object*)&l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__3_value;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19;
static lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20;
LEAN_EXPORT lean_object* l_Lean_Grind_CommSemiring_mul__zero___autoParam;
static const lean_string_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0 = (const lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0_value;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2;
static const lean_ctor_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__3 = (const lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__3_value;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5;
static const lean_string_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6 = (const lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6_value;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8;
static const lean_ctor_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(38, 183, 255, 58, 84, 31, 100, 5)}};
static const lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__9 = (const lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__9_value;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16;
static const lean_string_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "left_distrib"};
static const lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17 = (const lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17_value;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19;
static const lean_ctor_object l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17_value),LEAN_SCALAR_PTR_LITERAL(125, 89, 23, 115, 236, 84, 239, 248)}};
static const lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__20 = (const lean_object*)&l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__20_value;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24;
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
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49;
static lean_object* l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50;
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
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__10));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__11));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__18));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__23));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__22));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_ofNat__eq__natCast___autoParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_Semiring_nsmul__eq__natCast__mul___autoParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_Ring_zsmul__natCast__eq__nsmul___autoParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_Ring_intCast__ofNat___autoParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_Ring_intCast__neg___autoParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__0));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__4));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__7));
x_3 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6;
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11;
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__17));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22;
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__21));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__27));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__32));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33;
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__32));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__35));
x_3 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34;
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37;
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__40));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44;
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__43));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__46));
x_3 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45;
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48;
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__53));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55;
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58;
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_one__mul___autoParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__0));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__3));
x_3 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2;
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5;
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54;
x_2 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10;
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14;
x_2 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13;
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__0));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__3));
x_3 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2;
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__6));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__9));
x_3 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8;
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10;
x_2 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13;
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__1));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19;
x_2 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18;
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__17));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__20));
x_3 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19;
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22;
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41;
x_2 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31;
x_2 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32;
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__28));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34;
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__31));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35;
x_2 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41;
x_2 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35;
x_2 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54;
x_2 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41;
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__26));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42;
x_2 = l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14;
x_2 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44;
x_2 = ((lean_object*)(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__16));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45;
x_2 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49;
x_2 = l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50;
x_2 = ((lean_object*)(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_toCommSemiring___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_toCommSemiring___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_CommRing_toCommSemiring___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_toCommSemiring(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_toCommSemiring___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_toCommSemiring(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Semiring_toNatModule___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Semiring_toNatModule(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_Semiring_toNatModule___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_toAddCommGroup___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_apply_1(x_6, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_toAddCommGroup(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_Ring_toAddCommGroup___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_toIntModule___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_6 = l_Lean_Grind_Semiring_toNatModule___redArg(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 4);
lean_inc(x_11);
lean_dec_ref(x_2);
lean_ctor_set(x_7, 1, x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_3);
lean_ctor_set(x_12, 2, x_4);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 4);
lean_inc(x_16);
lean_dec_ref(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_4);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_5);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_toIntModule(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_Ring_toIntModule___redArg(x_2);
return x_3;
}
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
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__5);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__12);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__13);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__14);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__15);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__16);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__17);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__19);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__20);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__24);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__25);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__26);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__27);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__28);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__29);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__30);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__31);
l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32 = _init_l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32();
lean_mark_persistent(l_Lean_Grind_Semiring_ofNat__succ___autoParam___closed__32);
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
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__2);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__3);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__5);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__6);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__8);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__9);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__10);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__11);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__12);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__13);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__14);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__18);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__19);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__22);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__23);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__24);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__28);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__29);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__33);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__34);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__36);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__37);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__38);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__39);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__41);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__42);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__44);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__45);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__47);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__48);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__49);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__50);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__51);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__52);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__54);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__55);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__56);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__57);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__58);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__59);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__60);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__61);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__62);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__63);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__64);
l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65 = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam___closed__65);
l_Lean_Grind_CommSemiring_one__mul___autoParam = _init_l_Lean_Grind_CommSemiring_one__mul___autoParam();
lean_mark_persistent(l_Lean_Grind_CommSemiring_one__mul___autoParam);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__1);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__2);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__4);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__5);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__6);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__7);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__8);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__9);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__10);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__11);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__12);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__13);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__14);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__15);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__16);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__17);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__18);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__19);
l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20 = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam___closed__20);
l_Lean_Grind_CommSemiring_mul__zero___autoParam = _init_l_Lean_Grind_CommSemiring_mul__zero___autoParam();
lean_mark_persistent(l_Lean_Grind_CommSemiring_mul__zero___autoParam);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__1);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__2);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__4);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__5);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__7);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__8);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__10);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__11);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__12);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__13);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__14);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__15);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__16);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__18);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__19);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__21);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__22);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__23);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__24);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__25);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__29);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__30);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__31);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__32);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__33);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__34);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__35);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__36);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__37);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__38);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__39);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__40);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__41);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__42);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__43);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__44);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__45);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__46);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__47);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__48);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__49);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__50);
l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51 = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam___closed__51);
l_Lean_Grind_CommSemiring_right__distrib___autoParam = _init_l_Lean_Grind_CommSemiring_right__distrib___autoParam();
lean_mark_persistent(l_Lean_Grind_CommSemiring_right__distrib___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
