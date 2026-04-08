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
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1;
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
lean_dec_ref(v_a_39_);
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
lean_dec_ref(v___x_69_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg(lean_object* v_e_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_inc_ref(v_e_105_);
v___x_113_ = l_Lean_Meta_Grind_SolverExtension_hasTermAtRoot___redArg(v___x_112_, v_e_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; uint8_t v___x_115_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_a_114_);
v___x_115_ = lean_unbox(v_a_114_);
lean_dec(v_a_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; 
v___x_116_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v_e_105_);
if (lean_obj_tag(v___x_116_) == 0)
{
return v___x_113_;
}
else
{
lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_125_; 
lean_dec_ref(v___x_116_);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_125_ == 0)
{
lean_object* v_unused_126_; 
v_unused_126_ = lean_ctor_get(v___x_113_, 0);
lean_dec(v_unused_126_);
v___x_118_ = v___x_113_;
v_isShared_119_ = v_isSharedCheck_125_;
goto v_resetjp_117_;
}
else
{
lean_dec(v___x_113_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_125_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_120_ = 1;
v___x_121_ = lean_box(v___x_120_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_121_);
v___x_123_ = v___x_118_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
else
{
lean_dec_ref(v_e_105_);
return v___x_113_;
}
}
else
{
lean_dec_ref(v_e_105_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg___boxed(lean_object* v_e_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg(v_e_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar(lean_object* v_e_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg(v_e_135_, v_a_136_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___boxed(lean_object* v_e_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar(v_e_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec(v_a_149_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg(lean_object* v_e_176_){
_start:
{
uint8_t v___x_178_; uint8_t v___x_179_; 
lean_inc_ref(v_e_176_);
v___x_178_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_176_);
v___x_179_ = 1;
if (v___x_178_ == 0)
{
lean_object* v_f_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_f_180_ = l_Lean_Expr_getAppFn(v_e_176_);
lean_dec_ref(v_e_176_);
v___x_181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2));
v___x_182_ = l_Lean_Expr_isConstOf(v_f_180_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5));
v___x_184_ = l_Lean_Expr_isConstOf(v_f_180_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; uint8_t v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8));
v___x_186_ = l_Lean_Expr_isConstOf(v_f_180_, v___x_185_);
lean_dec_ref(v_f_180_);
v___x_187_ = lean_box(v___x_186_);
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec_ref(v_f_180_);
v___x_189_ = lean_box(v___x_179_);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec_ref(v_f_180_);
v___x_191_ = lean_box(v___x_179_);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
return v___x_192_;
}
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec_ref(v_e_176_);
v___x_193_ = lean_box(v___x_179_);
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___boxed(lean_object* v_e_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg(v_e_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted(lean_object* v_e_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg(v_e_198_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___boxed(lean_object* v_e_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted(v_e_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec(v_a_212_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_224_, lean_object* v_vals_225_, lean_object* v_i_226_, lean_object* v_k_227_){
_start:
{
lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_228_ = lean_array_get_size(v_keys_224_);
v___x_229_ = lean_nat_dec_lt(v_i_226_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
lean_dec(v_i_226_);
v___x_230_ = lean_box(0);
return v___x_230_;
}
else
{
lean_object* v_k_x27_231_; uint8_t v___x_232_; 
v_k_x27_231_ = lean_array_fget_borrowed(v_keys_224_, v_i_226_);
v___x_232_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_227_, v_k_x27_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_add(v_i_226_, v___x_233_);
lean_dec(v_i_226_);
v_i_226_ = v___x_234_;
goto _start;
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_array_fget_borrowed(v_vals_225_, v_i_226_);
lean_dec(v_i_226_);
lean_inc(v___x_236_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_238_, lean_object* v_vals_239_, lean_object* v_i_240_, lean_object* v_k_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(v_keys_238_, v_vals_239_, v_i_240_, v_k_241_);
lean_dec_ref(v_k_241_);
lean_dec_ref(v_vals_239_);
lean_dec_ref(v_keys_238_);
return v_res_242_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; 
v___x_243_ = ((size_t)5ULL);
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_shift_left(v___x_244_, v___x_243_);
return v___x_245_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; 
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0);
v___x_248_ = lean_usize_sub(v___x_247_, v___x_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(lean_object* v_x_249_, size_t v_x_250_, lean_object* v_x_251_){
_start:
{
if (lean_obj_tag(v_x_249_) == 0)
{
lean_object* v_es_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_273_; 
v_es_252_ = lean_ctor_get(v_x_249_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_249_);
if (v_isSharedCheck_273_ == 0)
{
v___x_254_ = v_x_249_;
v_isShared_255_ = v_isSharedCheck_273_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_es_252_);
lean_dec(v_x_249_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_273_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; lean_object* v_j_260_; lean_object* v___x_261_; 
v___x_256_ = lean_box(2);
v___x_257_ = ((size_t)5ULL);
v___x_258_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1);
v___x_259_ = lean_usize_land(v_x_250_, v___x_258_);
v_j_260_ = lean_usize_to_nat(v___x_259_);
v___x_261_ = lean_array_get(v___x_256_, v_es_252_, v_j_260_);
lean_dec(v_j_260_);
lean_dec_ref(v_es_252_);
switch(lean_obj_tag(v___x_261_))
{
case 0:
{
lean_object* v_key_262_; lean_object* v_val_263_; uint8_t v___x_264_; 
v_key_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_key_262_);
v_val_263_ = lean_ctor_get(v___x_261_, 1);
lean_inc(v_val_263_);
lean_dec_ref(v___x_261_);
v___x_264_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_251_, v_key_262_);
lean_dec(v_key_262_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec(v_val_263_);
lean_del_object(v___x_254_);
v___x_265_ = lean_box(0);
return v___x_265_;
}
else
{
lean_object* v___x_267_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 1);
lean_ctor_set(v___x_254_, 0, v_val_263_);
v___x_267_ = v___x_254_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_val_263_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
case 1:
{
lean_object* v_node_269_; size_t v___x_270_; 
lean_del_object(v___x_254_);
v_node_269_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_node_269_);
lean_dec_ref(v___x_261_);
v___x_270_ = lean_usize_shift_right(v_x_250_, v___x_257_);
v_x_249_ = v_node_269_;
v_x_250_ = v___x_270_;
goto _start;
}
default: 
{
lean_object* v___x_272_; 
lean_del_object(v___x_254_);
v___x_272_ = lean_box(0);
return v___x_272_;
}
}
}
}
else
{
lean_object* v_ks_274_; lean_object* v_vs_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_ks_274_ = lean_ctor_get(v_x_249_, 0);
lean_inc_ref(v_ks_274_);
v_vs_275_ = lean_ctor_get(v_x_249_, 1);
lean_inc_ref(v_vs_275_);
lean_dec_ref(v_x_249_);
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(v_ks_274_, v_vs_275_, v___x_276_, v_x_251_);
lean_dec_ref(v_vs_275_);
lean_dec_ref(v_ks_274_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___boxed(lean_object* v_x_278_, lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
size_t v_x_6397__boxed_281_; lean_object* v_res_282_; 
v_x_6397__boxed_281_ = lean_unbox_usize(v_x_279_);
lean_dec(v_x_279_);
v_res_282_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(v_x_278_, v_x_6397__boxed_281_, v_x_280_);
lean_dec_ref(v_x_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(lean_object* v_x_283_, lean_object* v_x_284_){
_start:
{
uint64_t v___x_285_; size_t v___x_286_; lean_object* v___x_287_; 
v___x_285_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_284_);
v___x_286_ = lean_uint64_to_usize(v___x_285_);
v___x_287_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(v_x_283_, v___x_286_, v_x_284_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg___boxed(lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_x_288_, v_x_289_);
lean_dec_ref(v_x_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg(lean_object* v_a_291_, lean_object* v_b_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_298_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_297_);
lean_dec_ref(v___x_296_);
v___x_298_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_357_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_357_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_357_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_357_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v_exprToStructId_303_; lean_object* v___x_304_; lean_object* v___y_306_; lean_object* v___x_354_; 
v_exprToStructId_303_ = lean_ctor_get(v_a_297_, 2);
lean_inc_ref(v_exprToStructId_303_);
lean_dec(v_a_297_);
v___x_304_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v___x_354_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_exprToStructId_303_, v_a_291_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_exprToStructId_355_; lean_object* v___x_356_; 
v_exprToStructId_355_ = lean_ctor_get(v_a_299_, 2);
lean_inc_ref(v_exprToStructId_355_);
lean_dec(v_a_299_);
v___x_356_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_exprToStructId_355_, v_b_292_);
v___y_306_ = v___x_356_;
goto v___jp_305_;
}
else
{
lean_dec(v_a_299_);
v___y_306_ = v___x_354_;
goto v___jp_305_;
}
v___jp_305_:
{
if (lean_obj_tag(v___y_306_) == 1)
{
lean_object* v_val_307_; lean_object* v___x_308_; 
lean_del_object(v___x_301_);
v_val_307_ = lean_ctor_get(v___y_306_, 0);
lean_inc(v_val_307_);
lean_dec_ref(v___y_306_);
v___x_308_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_340_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_340_ == 0)
{
v___x_311_ = v___x_308_;
v_isShared_312_ = v_isSharedCheck_340_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_340_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v_structs_313_; lean_object* v___x_314_; lean_object* v_isLinearInst_x3f_315_; 
v_structs_313_ = lean_ctor_get(v_a_309_, 0);
lean_inc_ref(v_structs_313_);
lean_dec(v_a_309_);
v___x_314_ = lean_array_get(v___x_304_, v_structs_313_, v_val_307_);
lean_dec(v_val_307_);
lean_dec_ref(v_structs_313_);
v_isLinearInst_x3f_315_ = lean_ctor_get(v___x_314_, 10);
if (lean_obj_tag(v_isLinearInst_x3f_315_) == 0)
{
uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
lean_dec(v___x_314_);
lean_dec_ref(v_b_292_);
lean_dec_ref(v_a_291_);
v___x_316_ = 0;
v___x_317_ = lean_box(v___x_316_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_317_);
v___x_319_ = v___x_311_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
else
{
lean_object* v___x_321_; 
lean_inc(v___x_314_);
v___x_321_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f(v___x_314_, v_a_291_);
if (lean_obj_tag(v___x_321_) == 1)
{
lean_object* v_val_322_; lean_object* v___x_323_; 
v_val_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_val_322_);
lean_dec_ref(v___x_321_);
v___x_323_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f(v___x_314_, v_b_292_);
if (lean_obj_tag(v___x_323_) == 1)
{
lean_object* v_val_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v_val_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_val_324_);
lean_dec_ref(v___x_323_);
v___x_325_ = l_instDecidableEqRat_decEq(v_val_322_, v_val_324_);
lean_dec(v_val_324_);
lean_dec(v_val_322_);
v___x_326_ = lean_box(v___x_325_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_326_);
v___x_328_ = v___x_311_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
else
{
uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
lean_dec(v___x_323_);
lean_dec(v_val_322_);
v___x_330_ = 0;
v___x_331_ = lean_box(v___x_330_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_331_);
v___x_333_ = v___x_311_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
else
{
uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
lean_dec(v___x_321_);
lean_dec(v___x_314_);
lean_dec_ref(v_b_292_);
v___x_335_ = 0;
v___x_336_ = lean_box(v___x_335_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_336_);
v___x_338_ = v___x_311_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec(v_val_307_);
lean_dec_ref(v_b_292_);
lean_dec_ref(v_a_291_);
v_a_341_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_308_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_308_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
else
{
uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
lean_dec(v___y_306_);
lean_dec_ref(v_b_292_);
lean_dec_ref(v_a_291_);
v___x_349_ = 0;
v___x_350_ = lean_box(v___x_349_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_350_);
v___x_352_ = v___x_301_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec(v_a_297_);
lean_dec_ref(v_b_292_);
lean_dec_ref(v_a_291_);
v_a_358_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_298_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_298_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref(v_b_292_);
lean_dec_ref(v_a_291_);
v_a_366_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_296_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_296_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg___boxed(lean_object* v_a_374_, lean_object* v_b_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg(v_a_374_, v_b_375_, v_a_376_, v_a_377_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment(lean_object* v_a_380_, lean_object* v_b_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg(v_a_380_, v_b_381_, v_a_382_, v_a_390_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___boxed(lean_object* v_a_394_, lean_object* v_b_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment(v_a_394_, v_b_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec(v_a_396_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0(lean_object* v_00_u03b2_408_, lean_object* v_x_409_, lean_object* v_x_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_x_409_, v_x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___boxed(lean_object* v_00_u03b2_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0(v_00_u03b2_412_, v_x_413_, v_x_414_);
lean_dec_ref(v_x_414_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0(lean_object* v_00_u03b2_416_, lean_object* v_x_417_, size_t v_x_418_, lean_object* v_x_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(v_x_417_, v_x_418_, v_x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___boxed(lean_object* v_00_u03b2_421_, lean_object* v_x_422_, lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
size_t v_x_6640__boxed_425_; lean_object* v_res_426_; 
v_x_6640__boxed_425_ = lean_unbox_usize(v_x_423_);
lean_dec(v_x_423_);
v_res_426_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0(v_00_u03b2_421_, v_x_422_, v_x_6640__boxed_425_, v_x_424_);
lean_dec_ref(v_x_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_427_, lean_object* v_keys_428_, lean_object* v_vals_429_, lean_object* v_heq_430_, lean_object* v_i_431_, lean_object* v_k_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(v_keys_428_, v_vals_429_, v_i_431_, v_k_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_434_, lean_object* v_keys_435_, lean_object* v_vals_436_, lean_object* v_heq_437_, lean_object* v_i_438_, lean_object* v_k_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1(v_00_u03b2_434_, v_keys_435_, v_vals_436_, v_heq_437_, v_i_438_, v_k_439_);
lean_dec_ref(v_k_439_);
lean_dec_ref(v_vals_436_);
lean_dec_ref(v_keys_435_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mbtc(lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__3));
v___x_460_ = l_Lean_Meta_Grind_mbtc(v___x_459_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mbtc___boxed(lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Meta_Grind_Arith_Linear_mbtc(v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec(v_a_461_);
return v_res_472_;
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
