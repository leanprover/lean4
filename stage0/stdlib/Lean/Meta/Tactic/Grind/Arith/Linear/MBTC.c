// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.MBTC
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.MBTC import Lean.Meta.Tactic.Grind.Arith.ModelUtil import Lean.Meta.Tactic.Grind.Arith.Linear.Model import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_mkRat(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_hasTermAtRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(lean_object*, lean_object*);
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isInterpretedTerm(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f_spec__1(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(172, 37, 33, 120, 251, 36, 203, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "One"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(19, 85, 184, 168, 121, 55, 74, 19)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(31, 134, 200, 93, 163, 253, 252, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__1_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__2_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mbtc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f_spec__1(lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_nat_to_int(v_a_3_);
v___x_5_ = l_Rat_ofInt(v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_unsigned_to_nat(1u);
v___x_32_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f_spec__1(v___x_31_);
return v___x_32_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15);
v___x_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f_spec__1(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17);
v___x_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(lean_object* v_a_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_40_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2));
v___x_41_ = lean_unsigned_to_nat(2u);
v___x_42_ = l_Lean_Expr_isAppOfArity(v_a_39_, v___x_40_, v___x_41_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5));
v___x_44_ = l_Lean_Expr_isAppOfArity(v_a_39_, v___x_43_, v___x_41_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_45_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8));
v___x_46_ = lean_unsigned_to_nat(3u);
v___x_47_ = l_Lean_Expr_isAppOfArity(v_a_39_, v___x_45_, v___x_46_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11));
v___x_49_ = l_Lean_Expr_isAppOfArity(v_a_39_, v___x_48_, v___x_46_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_50_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14));
v___x_51_ = lean_unsigned_to_nat(6u);
v___x_52_ = l_Lean_Expr_isAppOfArity(v_a_39_, v___x_50_, v___x_51_);
if (v___x_52_ == 0)
{
if (lean_obj_tag(v_a_39_) == 9)
{
lean_object* v_a_53_; 
v_a_53_ = lean_ctor_get(v_a_39_, 0);
lean_inc_ref(v_a_53_);
lean_dec_ref_known(v_a_39_, 1);
if (lean_obj_tag(v_a_53_) == 0)
{
lean_object* v_val_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_64_; 
v_val_54_ = lean_ctor_get(v_a_53_, 0);
v_isSharedCheck_64_ = !lean_is_exclusive(v_a_53_);
if (v_isSharedCheck_64_ == 0)
{
v___x_56_ = v_a_53_;
v_isShared_57_ = v_isSharedCheck_64_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_val_54_);
lean_dec(v_a_53_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_64_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_58_ = lean_nat_to_int(v_val_54_);
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = l_mkRat(v___x_58_, v___x_59_);
if (v_isShared_57_ == 0)
{
lean_ctor_set_tag(v___x_56_, 1);
lean_ctor_set(v___x_56_, 0, v___x_60_);
v___x_62_ = v___x_56_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_60_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
else
{
lean_object* v___x_65_; 
lean_dec_ref(v_a_53_);
v___x_65_ = lean_box(0);
return v___x_65_;
}
}
else
{
lean_object* v___x_66_; 
lean_dec_ref(v_a_39_);
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = l_Lean_Expr_appFn_x21(v_a_39_);
v___x_68_ = l_Lean_Expr_appArg_x21(v___x_67_);
lean_dec_ref(v___x_67_);
v___x_69_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v___x_68_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_dec_ref(v_a_39_);
return v___x_69_;
}
else
{
lean_object* v_val_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_val_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_val_70_);
lean_dec_ref_known(v___x_69_, 1);
v___x_71_ = l_Lean_Expr_appArg_x21(v_a_39_);
lean_dec_ref(v_a_39_);
v___x_72_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v___x_71_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_dec(v_val_70_);
return v___x_72_;
}
else
{
lean_object* v_val_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_81_; 
v_val_73_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_81_ == 0)
{
v___x_75_ = v___x_72_;
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_val_73_);
lean_dec(v___x_72_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_77_ = l_Rat_div(v_val_70_, v_val_73_);
lean_dec(v_val_70_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_77_);
v___x_79_ = v___x_75_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
}
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = l_Lean_Expr_appArg_x21(v_a_39_);
lean_dec_ref(v_a_39_);
v___x_83_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v___x_82_);
if (lean_obj_tag(v___x_83_) == 0)
{
return v___x_83_;
}
else
{
lean_object* v_val_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_92_; 
v_val_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_92_ == 0)
{
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_val_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___x_90_; 
v___x_88_ = l_Rat_neg(v_val_84_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_88_);
v___x_90_ = v___x_86_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = l_Lean_Expr_getAppNumArgs(v_a_39_);
v___x_95_ = lean_nat_sub(v___x_94_, v___x_93_);
lean_dec(v___x_94_);
v___x_96_ = lean_nat_sub(v___x_95_, v___x_93_);
lean_dec(v___x_95_);
v___x_97_ = l_Lean_Expr_getRevArg_x21(v_a_39_, v___x_96_);
lean_dec_ref(v_a_39_);
v_a_39_ = v___x_97_;
goto _start;
}
}
else
{
lean_object* v___x_99_; 
lean_dec_ref(v_a_39_);
v___x_99_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16);
return v___x_99_;
}
}
else
{
lean_object* v___x_100_; 
lean_dec_ref(v_a_39_);
v___x_100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f(lean_object* v_s_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v_s_101_, v_a_102_);
if (lean_obj_tag(v___x_103_) == 1)
{
lean_dec_ref(v_a_102_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; 
lean_dec(v___x_103_);
v___x_104_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v_a_102_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f___boxed(lean_object* v_s_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f(v_s_105_, v_a_106_);
lean_dec_ref(v_s_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg(lean_object* v_e_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_inc_ref(v_e_108_);
v___x_116_ = l_Lean_Meta_Grind_SolverExtension_hasTermAtRoot___redArg(v___x_115_, v_e_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; uint8_t v___x_118_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
v___x_118_ = lean_unbox(v_a_117_);
lean_dec(v_a_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; 
v___x_119_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v_e_108_);
if (lean_obj_tag(v___x_119_) == 0)
{
return v___x_116_;
}
else
{
lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_128_; 
lean_dec_ref_known(v___x_119_, 1);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; 
v_unused_129_ = lean_ctor_get(v___x_116_, 0);
lean_dec(v_unused_129_);
v___x_121_ = v___x_116_;
v_isShared_122_ = v_isSharedCheck_128_;
goto v_resetjp_120_;
}
else
{
lean_dec(v___x_116_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_128_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
uint8_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_123_ = 1;
v___x_124_ = lean_box(v___x_123_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_124_);
v___x_126_ = v___x_121_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
else
{
lean_dec_ref(v_e_108_);
return v___x_116_;
}
}
else
{
lean_dec_ref(v_e_108_);
return v___x_116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg___boxed(lean_object* v_e_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg(v_e_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar(lean_object* v_e_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg(v_e_138_, v_a_139_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___boxed(lean_object* v_e_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar(v_e_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec(v_a_152_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg(lean_object* v_e_179_){
_start:
{
uint8_t v___x_181_; uint8_t v___x_182_; 
lean_inc_ref(v_e_179_);
v___x_181_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_179_);
v___x_182_ = 1;
if (v___x_181_ == 0)
{
lean_object* v_f_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v_f_183_ = l_Lean_Expr_getAppFn(v_e_179_);
lean_dec_ref(v_e_179_);
v___x_184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2));
v___x_185_ = l_Lean_Expr_isConstOf(v_f_183_, v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5));
v___x_187_ = l_Lean_Expr_isConstOf(v_f_183_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8));
v___x_189_ = l_Lean_Expr_isConstOf(v_f_183_, v___x_188_);
lean_dec_ref(v_f_183_);
v___x_190_ = lean_box(v___x_189_);
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
else
{
lean_object* v___x_192_; lean_object* v___x_193_; 
lean_dec_ref(v_f_183_);
v___x_192_ = lean_box(v___x_182_);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec_ref(v_f_183_);
v___x_194_ = lean_box(v___x_182_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; 
lean_dec_ref(v_e_179_);
v___x_196_ = lean_box(v___x_182_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___boxed(lean_object* v_e_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg(v_e_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted(lean_object* v_e_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg(v_e_201_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___boxed(lean_object* v_e_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted(v_e_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec(v_a_215_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_227_, lean_object* v_vals_228_, lean_object* v_i_229_, lean_object* v_k_230_){
_start:
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_array_get_size(v_keys_227_);
v___x_232_ = lean_nat_dec_lt(v_i_229_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
lean_dec(v_i_229_);
v___x_233_ = lean_box(0);
return v___x_233_;
}
else
{
lean_object* v_k_x27_234_; size_t v___x_235_; size_t v___x_236_; uint8_t v___x_237_; 
v_k_x27_234_ = lean_array_fget_borrowed(v_keys_227_, v_i_229_);
v___x_235_ = lean_ptr_addr(v_k_230_);
v___x_236_ = lean_ptr_addr(v_k_x27_234_);
v___x_237_ = lean_usize_dec_eq(v___x_235_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_add(v_i_229_, v___x_238_);
lean_dec(v_i_229_);
v_i_229_ = v___x_239_;
goto _start;
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_array_fget_borrowed(v_vals_228_, v_i_229_);
lean_dec(v_i_229_);
lean_inc(v___x_241_);
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_243_, lean_object* v_vals_244_, lean_object* v_i_245_, lean_object* v_k_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(v_keys_243_, v_vals_244_, v_i_245_, v_k_246_);
lean_dec_ref(v_k_246_);
lean_dec_ref(v_vals_244_);
lean_dec_ref(v_keys_243_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(lean_object* v_x_248_, size_t v_x_249_, lean_object* v_x_250_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
lean_object* v_es_251_; lean_object* v___x_252_; size_t v___x_253_; size_t v___x_254_; lean_object* v_j_255_; lean_object* v___x_256_; 
v_es_251_ = lean_ctor_get(v_x_248_, 0);
v___x_252_ = lean_box(2);
v___x_253_ = ((size_t)31ULL);
v___x_254_ = lean_usize_land(v_x_249_, v___x_253_);
v_j_255_ = lean_usize_to_nat(v___x_254_);
v___x_256_ = lean_array_get_borrowed(v___x_252_, v_es_251_, v_j_255_);
lean_dec(v_j_255_);
switch(lean_obj_tag(v___x_256_))
{
case 0:
{
lean_object* v_key_257_; lean_object* v_val_258_; size_t v___x_259_; size_t v___x_260_; uint8_t v___x_261_; 
v_key_257_ = lean_ctor_get(v___x_256_, 0);
v_val_258_ = lean_ctor_get(v___x_256_, 1);
v___x_259_ = lean_ptr_addr(v_x_250_);
v___x_260_ = lean_ptr_addr(v_key_257_);
v___x_261_ = lean_usize_dec_eq(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
v___x_262_ = lean_box(0);
return v___x_262_;
}
else
{
lean_object* v___x_263_; 
lean_inc(v_val_258_);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v_val_258_);
return v___x_263_;
}
}
case 1:
{
lean_object* v_node_264_; size_t v___x_265_; size_t v___x_266_; 
v_node_264_ = lean_ctor_get(v___x_256_, 0);
v___x_265_ = ((size_t)5ULL);
v___x_266_ = lean_usize_shift_right(v_x_249_, v___x_265_);
v_x_248_ = v_node_264_;
v_x_249_ = v___x_266_;
goto _start;
}
default: 
{
lean_object* v___x_268_; 
v___x_268_ = lean_box(0);
return v___x_268_;
}
}
}
else
{
lean_object* v_ks_269_; lean_object* v_vs_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_ks_269_ = lean_ctor_get(v_x_248_, 0);
v_vs_270_ = lean_ctor_get(v_x_248_, 1);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(v_ks_269_, v_vs_270_, v___x_271_, v_x_250_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_x_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
size_t v_x_6480__boxed_276_; lean_object* v_res_277_; 
v_x_6480__boxed_276_ = lean_unbox_usize(v_x_274_);
lean_dec(v_x_274_);
v_res_277_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(v_x_273_, v_x_6480__boxed_276_, v_x_275_);
lean_dec_ref(v_x_275_);
lean_dec_ref(v_x_273_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(lean_object* v_x_278_, lean_object* v_x_279_){
_start:
{
size_t v___x_280_; size_t v___x_281_; size_t v___x_282_; uint64_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; 
v___x_280_ = lean_ptr_addr(v_x_279_);
v___x_281_ = ((size_t)3ULL);
v___x_282_ = lean_usize_shift_right(v___x_280_, v___x_281_);
v___x_283_ = lean_usize_to_uint64(v___x_282_);
v___x_284_ = lean_uint64_to_usize(v___x_283_);
v___x_285_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(v_x_278_, v___x_284_, v_x_279_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg___boxed(lean_object* v_x_286_, lean_object* v_x_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_x_286_, v_x_287_);
lean_dec_ref(v_x_287_);
lean_dec_ref(v_x_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg(lean_object* v_a_289_, lean_object* v_b_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_296_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v___x_294_, 1);
v___x_296_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_355_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_355_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_355_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_355_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v_exprToStructId_301_; lean_object* v___x_302_; lean_object* v___y_304_; lean_object* v___x_352_; 
v_exprToStructId_301_ = lean_ctor_get(v_a_295_, 2);
lean_inc_ref(v_exprToStructId_301_);
lean_dec(v_a_295_);
v___x_302_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v___x_352_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_exprToStructId_301_, v_a_289_);
lean_dec_ref(v_exprToStructId_301_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_exprToStructId_353_; lean_object* v___x_354_; 
v_exprToStructId_353_ = lean_ctor_get(v_a_297_, 2);
lean_inc_ref(v_exprToStructId_353_);
lean_dec(v_a_297_);
v___x_354_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_exprToStructId_353_, v_b_290_);
lean_dec_ref(v_exprToStructId_353_);
v___y_304_ = v___x_354_;
goto v___jp_303_;
}
else
{
lean_dec(v_a_297_);
v___y_304_ = v___x_352_;
goto v___jp_303_;
}
v___jp_303_:
{
if (lean_obj_tag(v___y_304_) == 1)
{
lean_object* v_val_305_; lean_object* v___x_306_; 
lean_del_object(v___x_299_);
v_val_305_ = lean_ctor_get(v___y_304_, 0);
lean_inc(v_val_305_);
lean_dec_ref_known(v___y_304_, 1);
v___x_306_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_338_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_338_ == 0)
{
v___x_309_ = v___x_306_;
v_isShared_310_ = v_isSharedCheck_338_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_338_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v_structs_311_; lean_object* v___x_312_; lean_object* v_isLinearInst_x3f_313_; 
v_structs_311_ = lean_ctor_get(v_a_307_, 0);
lean_inc_ref(v_structs_311_);
lean_dec(v_a_307_);
v___x_312_ = lean_array_get(v___x_302_, v_structs_311_, v_val_305_);
lean_dec(v_val_305_);
lean_dec_ref(v_structs_311_);
v_isLinearInst_x3f_313_ = lean_ctor_get(v___x_312_, 10);
if (lean_obj_tag(v_isLinearInst_x3f_313_) == 0)
{
uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
lean_dec(v___x_312_);
lean_dec_ref(v_b_290_);
lean_dec_ref(v_a_289_);
v___x_314_ = 0;
v___x_315_ = lean_box(v___x_314_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_315_);
v___x_317_ = v___x_309_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
else
{
lean_object* v___x_319_; 
v___x_319_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f(v___x_312_, v_a_289_);
if (lean_obj_tag(v___x_319_) == 1)
{
lean_object* v_val_320_; lean_object* v___x_321_; 
v_val_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_val_320_);
lean_dec_ref_known(v___x_319_, 1);
v___x_321_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f(v___x_312_, v_b_290_);
lean_dec(v___x_312_);
if (lean_obj_tag(v___x_321_) == 1)
{
lean_object* v_val_322_; uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v_val_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_val_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = l_instDecidableEqRat_decEq(v_val_320_, v_val_322_);
lean_dec(v_val_322_);
lean_dec(v_val_320_);
v___x_324_ = lean_box(v___x_323_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_324_);
v___x_326_ = v___x_309_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
else
{
uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
lean_dec(v___x_321_);
lean_dec(v_val_320_);
v___x_328_ = 0;
v___x_329_ = lean_box(v___x_328_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_329_);
v___x_331_ = v___x_309_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
else
{
uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
lean_dec(v___x_319_);
lean_dec(v___x_312_);
lean_dec_ref(v_b_290_);
v___x_333_ = 0;
v___x_334_ = lean_box(v___x_333_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_334_);
v___x_336_ = v___x_309_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec(v_val_305_);
lean_dec_ref(v_b_290_);
lean_dec_ref(v_a_289_);
v_a_339_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_306_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_306_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
uint8_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
lean_dec(v___y_304_);
lean_dec_ref(v_b_290_);
lean_dec_ref(v_a_289_);
v___x_347_ = 0;
v___x_348_ = lean_box(v___x_347_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_348_);
v___x_350_ = v___x_299_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec(v_a_295_);
lean_dec_ref(v_b_290_);
lean_dec_ref(v_a_289_);
v_a_356_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_296_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_296_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref(v_b_290_);
lean_dec_ref(v_a_289_);
v_a_364_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_294_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_294_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg___boxed(lean_object* v_a_372_, lean_object* v_b_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg(v_a_372_, v_b_373_, v_a_374_, v_a_375_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment(lean_object* v_a_378_, lean_object* v_b_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg(v_a_378_, v_b_379_, v_a_380_, v_a_388_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___boxed(lean_object* v_a_392_, lean_object* v_b_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment(v_a_392_, v_b_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec(v_a_394_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0(lean_object* v_00_u03b2_406_, lean_object* v_x_407_, lean_object* v_x_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_x_407_, v_x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___boxed(lean_object* v_00_u03b2_410_, lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0(v_00_u03b2_410_, v_x_411_, v_x_412_);
lean_dec_ref(v_x_412_);
lean_dec_ref(v_x_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0(lean_object* v_00_u03b2_414_, lean_object* v_x_415_, size_t v_x_416_, lean_object* v_x_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(v_x_415_, v_x_416_, v_x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_419_, lean_object* v_x_420_, lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
size_t v_x_6715__boxed_423_; lean_object* v_res_424_; 
v_x_6715__boxed_423_ = lean_unbox_usize(v_x_421_);
lean_dec(v_x_421_);
v_res_424_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0(v_00_u03b2_419_, v_x_420_, v_x_6715__boxed_423_, v_x_422_);
lean_dec_ref(v_x_422_);
lean_dec_ref(v_x_420_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_425_, lean_object* v_keys_426_, lean_object* v_vals_427_, lean_object* v_heq_428_, lean_object* v_i_429_, lean_object* v_k_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(v_keys_426_, v_vals_427_, v_i_429_, v_k_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_432_, lean_object* v_keys_433_, lean_object* v_vals_434_, lean_object* v_heq_435_, lean_object* v_i_436_, lean_object* v_k_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1(v_00_u03b2_432_, v_keys_433_, v_vals_434_, v_heq_435_, v_i_436_, v_k_437_);
lean_dec_ref(v_k_437_);
lean_dec_ref(v_vals_434_);
lean_dec_ref(v_keys_433_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mbtc(lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__3));
v___x_458_ = l_Lean_Meta_Grind_mbtc(v___x_457_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mbtc___boxed(lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Meta_Grind_Arith_Linear_mbtc(v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec(v_a_459_);
return v_res_470_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_MBTC(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(builtin);
}
#ifdef __cplusplus
}
#endif
