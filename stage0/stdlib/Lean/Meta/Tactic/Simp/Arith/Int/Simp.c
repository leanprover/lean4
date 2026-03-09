// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Int.Simp
// Imports: public import Lean.Meta.Tactic.Simp.Arith.Util public import Lean.Meta.Tactic.Simp.Arith.Int.Basic
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "norm_eq_var_const"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(35, 112, 223, 250, 183, 82, 157, 139)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_eq_false_of_divCoeff"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(155, 236, 46, 169, 167, 124, 63, 211)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
lean_object* l_Lean_mkIntLit(lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "norm_eq_coeff"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_value),LEAN_SCALAR_PTR_LITERAL(85, 43, 120, 188, 118, 245, 143, 91)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "norm_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(44, 156, 243, 152, 103, 234, 174, 123)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30;
lean_object* lean_int_neg(lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "norm_eq_var"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_value),LEAN_SCALAR_PTR_LITERAL(135, 64, 142, 174, 60, 214, 97, 115)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eq_eq_true"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_value),LEAN_SCALAR_PTR_LITERAL(22, 67, 32, 138, 58, 105, 16, 18)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "eq_eq_false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_value),LEAN_SCALAR_PTR_LITERAL(235, 105, 48, 217, 98, 238, 131, 5)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44;
lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Int_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkIntEq(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatEq(lean_object*);
uint8_t l_Int_Linear_Poly_isValidEq(lean_object*);
lean_object* l_Int_Linear_Poly_toExpr(lean_object*);
uint8_t l_Int_Linear_instBEqExpr_beq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "norm_le_coeff"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 68, 185, 68, 63, 172, 180, 150)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "norm_le_coeff_tight"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 199, 217, 219, 136, 132, 30, 204)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "norm_le"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(232, 121, 64, 164, 96, 91, 136, 25)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "le_eq_true"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(168, 245, 170, 32, 204, 84, 255, 159)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "le_eq_false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(76, 250, 170, 64, 206, 9, 106, 135)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value;
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object*);
uint8_t l_Int_Linear_Poly_isValidLe(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value;
lean_object* l_Lean_Level_succ___override(lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
lean_object* l_Lean_mkSort(lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_le_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(77, 74, 162, 108, 148, 71, 165, 71)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_ge_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(87, 141, 152, 40, 61, 44, 151, 4)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_lt_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(214, 41, 233, 126, 147, 68, 29, 47)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_gt_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value),LEAN_SCALAR_PTR_LITERAL(250, 161, 48, 12, 204, 229, 102, 4)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "norm_dvd_gcd"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 243, 25, 22, 225, 48, 108, 155)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "norm_dvd"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(14, 102, 31, 143, 124, 229, 161, 52)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dvd_eq_false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 255, 101, 122, 145, 117, 61, 183)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8;
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntDvd(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "eq_of_norm_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 62, 222, 142, 91, 249, 126, 146)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(53, 220, 199, 2, 108, 141, 83, 34)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3;
lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_nat_abs(x_5);
x_7 = lean_nat_gcd(x_1, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_nat_abs(x_8);
x_11 = lean_nat_gcd(x_1, x_10);
lean_dec(x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_9;
goto _start;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_nat_abs(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_abs(x_4);
x_7 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(x_6, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_Poly_gcdAll(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_abs(x_5);
x_8 = lean_nat_gcd(x_1, x_7);
lean_dec(x_7);
lean_dec(x_1);
x_1 = x_8;
x_2 = x_6;
goto _start;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(1u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_nat_abs(x_3);
x_6 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(x_5, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_Poly_gcdCoeffs_x27(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_get_borrowed(x_1, x_2, x_3);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_380; 
x_8 = lean_ctor_get(x_7, 0);
x_380 = !lean_is_exclusive(x_7);
if (x_380 == 0)
{
x_9 = x_7;
x_10 = x_380;
goto block_379;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_380;
goto block_379;
}
block_379:
{
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_374; 
x_11 = lean_ctor_get(x_8, 0);
x_374 = !lean_is_exclusive(x_8);
if (x_374 == 0)
{
x_12 = x_8;
x_13 = x_374;
goto block_373;
}
else
{
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = x_374;
goto block_373;
}
block_373:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_372; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_11, 0);
x_372 = !lean_is_exclusive(x_11);
if (x_372 == 0)
{
x_16 = x_11;
x_17 = x_372;
goto block_371;
}
else
{
lean_inc(x_14);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_372;
goto block_371;
}
block_371:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_370; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
x_370 = !lean_is_exclusive(x_14);
if (x_370 == 0)
{
x_20 = x_14;
x_21 = x_370;
goto block_369;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = x_370;
goto block_369;
}
block_369:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_instInhabitedExpr;
lean_inc(x_19);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_19);
lean_inc(x_15);
lean_inc_ref(x_23);
x_24 = l_Int_Linear_Expr_denoteExpr___redArg(x_23, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_360; 
x_25 = lean_ctor_get(x_24, 0);
x_360 = !lean_is_exclusive(x_24);
if (x_360 == 0)
{
x_26 = x_24;
x_27 = x_360;
goto block_359;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_360;
goto block_359;
}
block_359:
{
lean_object* x_28; 
lean_inc(x_18);
lean_inc_ref(x_23);
x_28 = l_Int_Linear_Expr_denoteExpr___redArg(x_23, x_18);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_350; 
x_29 = lean_ctor_get(x_28, 0);
x_350 = !lean_is_exclusive(x_28);
if (x_350 == 0)
{
x_30 = x_28;
x_31 = x_350;
goto block_349;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_350;
goto block_349;
}
block_349:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_219; uint8_t x_289; 
x_32 = l_Lean_mkIntEq(x_25, x_29);
lean_inc(x_18);
lean_inc(x_15);
x_104 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_104, 0, x_15);
lean_ctor_set(x_104, 1, x_18);
x_105 = l_Int_Linear_Expr_norm(x_104);
lean_dec_ref(x_104);
x_289 = l_Int_Linear_Poly_isUnsatEq(x_105);
if (x_289 == 0)
{
uint8_t x_290; 
x_290 = l_Int_Linear_Poly_isValidEq(x_105);
if (x_290 == 0)
{
lean_object* x_291; uint8_t x_292; 
lean_inc_ref(x_105);
x_291 = l_Int_Linear_Poly_toExpr(x_105);
x_292 = l_Int_Linear_instBEqExpr_beq(x_291, x_15);
lean_dec_ref(x_291);
if (x_292 == 0)
{
x_219 = x_292;
goto block_288;
}
else
{
lean_object* x_293; uint8_t x_294; 
x_293 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35);
x_294 = l_Int_Linear_instBEqExpr_beq(x_18, x_293);
x_219 = x_294;
goto block_288;
}
}
else
{
lean_object* x_295; 
lean_dec_ref(x_105);
lean_del_object(x_30);
lean_del_object(x_26);
lean_dec_ref(x_23);
lean_del_object(x_20);
lean_del_object(x_16);
lean_del_object(x_12);
lean_del_object(x_9);
x_295 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; uint8_t x_313; 
x_296 = lean_ctor_get(x_295, 0);
x_313 = !lean_is_exclusive(x_295);
if (x_313 == 0)
{
x_297 = x_295;
x_298 = x_313;
goto block_312;
}
else
{
lean_inc(x_296);
lean_dec(x_295);
x_297 = lean_box(0);
x_298 = x_313;
goto block_312;
}
block_312:
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_299 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38);
x_300 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41);
x_301 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_302 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_18);
x_303 = l_Lean_eagerReflBoolTrue;
x_304 = l_Lean_mkApp4(x_300, x_296, x_301, x_302, x_303);
x_305 = l_Lean_mkPropEq(x_32, x_299);
x_306 = l_Lean_Meta_mkExpectedPropHint(x_304, x_305);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_299);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_307);
if (x_298 == 0)
{
lean_ctor_set(x_297, 0, x_308);
x_309 = x_297;
goto block_310;
}
else
{
lean_object* x_311; 
x_311 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_311, 0, x_308);
x_309 = x_311;
goto block_310;
}
block_310:
{
return x_309;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; uint8_t x_321; 
lean_dec_ref(x_32);
lean_dec(x_18);
lean_dec(x_15);
x_314 = lean_ctor_get(x_295, 0);
x_321 = !lean_is_exclusive(x_295);
if (x_321 == 0)
{
x_315 = x_295;
x_316 = x_321;
goto block_320;
}
else
{
lean_inc(x_314);
lean_dec(x_295);
x_315 = lean_box(0);
x_316 = x_321;
goto block_320;
}
block_320:
{
lean_object* x_317; 
if (x_316 == 0)
{
x_317 = x_315;
goto block_318;
}
else
{
lean_object* x_319; 
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_314);
x_317 = x_319;
goto block_318;
}
block_318:
{
return x_317;
}
}
}
}
}
else
{
lean_object* x_322; 
lean_dec_ref(x_105);
lean_del_object(x_30);
lean_del_object(x_26);
lean_dec_ref(x_23);
lean_del_object(x_20);
lean_del_object(x_16);
lean_del_object(x_12);
lean_del_object(x_9);
x_322 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; uint8_t x_325; uint8_t x_340; 
x_323 = lean_ctor_get(x_322, 0);
x_340 = !lean_is_exclusive(x_322);
if (x_340 == 0)
{
x_324 = x_322;
x_325 = x_340;
goto block_339;
}
else
{
lean_inc(x_323);
lean_dec(x_322);
x_324 = lean_box(0);
x_325 = x_340;
goto block_339;
}
block_339:
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_326 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8);
x_327 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44);
x_328 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_329 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_18);
x_330 = l_Lean_eagerReflBoolTrue;
x_331 = l_Lean_mkApp4(x_327, x_323, x_328, x_329, x_330);
x_332 = l_Lean_mkPropEq(x_32, x_326);
x_333 = l_Lean_Meta_mkExpectedPropHint(x_331, x_332);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_326);
lean_ctor_set(x_334, 1, x_333);
x_335 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_335, 0, x_334);
if (x_325 == 0)
{
lean_ctor_set(x_324, 0, x_335);
x_336 = x_324;
goto block_337;
}
else
{
lean_object* x_338; 
x_338 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_338, 0, x_335);
x_336 = x_338;
goto block_337;
}
block_337:
{
return x_336;
}
}
}
else
{
lean_object* x_341; lean_object* x_342; uint8_t x_343; uint8_t x_348; 
lean_dec_ref(x_32);
lean_dec(x_18);
lean_dec(x_15);
x_341 = lean_ctor_get(x_322, 0);
x_348 = !lean_is_exclusive(x_322);
if (x_348 == 0)
{
x_342 = x_322;
x_343 = x_348;
goto block_347;
}
else
{
lean_inc(x_341);
lean_dec(x_322);
x_342 = lean_box(0);
x_343 = x_348;
goto block_347;
}
block_347:
{
lean_object* x_344; 
if (x_343 == 0)
{
x_344 = x_342;
goto block_345;
}
else
{
lean_object* x_346; 
x_346 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_346, 0, x_341);
x_344 = x_346;
goto block_345;
}
block_345:
{
return x_344;
}
}
}
}
block_52:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = l_Lean_eagerReflBoolTrue;
x_40 = l_Lean_mkApp5(x_37, x_35, x_36, x_34, x_38, x_39);
lean_inc_ref(x_33);
x_41 = l_Lean_mkPropEq(x_32, x_33);
x_42 = l_Lean_Meta_mkExpectedPropHint(x_40, x_41);
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_42);
lean_ctor_set(x_20, 0, x_33);
x_43 = x_20;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_33);
lean_ctor_set(x_51, 1, x_42);
x_43 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_44; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_43);
x_44 = x_12;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_43);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_44);
x_45 = x_30;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
block_71:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = l_Lean_eagerReflBoolTrue;
x_61 = l_Lean_mkApp6(x_54, x_57, x_55, x_56, x_58, x_59, x_60);
lean_inc_ref(x_53);
x_62 = l_Lean_mkPropEq(x_32, x_53);
x_63 = l_Lean_Meta_mkExpectedPropHint(x_61, x_62);
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_63);
lean_ctor_set(x_16, 0, x_53);
x_64 = x_16;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_63);
x_64 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_65);
x_66 = x_26;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_65);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
block_103:
{
lean_object* x_75; 
x_75 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_94; 
x_76 = lean_ctor_get(x_75, 0);
x_94 = !lean_is_exclusive(x_75);
if (x_94 == 0)
{
x_77 = x_75;
x_78 = x_94;
goto block_93;
}
else
{
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_box(0);
x_78 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_inc_ref(x_74);
x_79 = l_Lean_mkIntEq(x_72, x_74);
x_80 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4);
x_81 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_82 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_18);
x_83 = l_Lean_mkNatLit(x_73);
x_84 = l_Lean_eagerReflBoolTrue;
x_85 = l_Lean_mkApp6(x_80, x_76, x_81, x_82, x_83, x_74, x_84);
lean_inc_ref(x_79);
x_86 = l_Lean_mkPropEq(x_32, x_79);
x_87 = l_Lean_Meta_mkExpectedPropHint(x_85, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_79);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
if (x_78 == 0)
{
lean_ctor_set(x_77, 0, x_89);
x_90 = x_77;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_89);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_102; 
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec_ref(x_32);
lean_dec(x_18);
lean_dec(x_15);
x_95 = lean_ctor_get(x_75, 0);
x_102 = !lean_is_exclusive(x_75);
if (x_102 == 0)
{
x_96 = x_75;
x_97 = x_102;
goto block_101;
}
else
{
lean_inc(x_95);
lean_dec(x_75);
x_96 = lean_box(0);
x_97 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_98; 
if (x_97 == 0)
{
x_98 = x_96;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_95);
x_98 = x_100;
goto block_99;
}
block_99:
{
return x_98;
}
}
}
}
block_218:
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_110 = l_Int_Linear_Poly_gcdCoeffs_x27(x_105);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_dec_eq(x_110, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_113 = l_Int_Linear_Poly_getConst(x_105);
x_114 = lean_nat_to_int(x_110);
x_115 = lean_int_emod(x_113, x_114);
lean_dec(x_113);
x_116 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
x_117 = lean_int_dec_eq(x_115, x_116);
lean_dec(x_115);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec_ref(x_105);
lean_del_object(x_26);
lean_dec_ref(x_23);
lean_del_object(x_16);
x_118 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_19, x_106, x_107, x_108, x_109);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_120 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8);
x_121 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11);
x_122 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_123 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_18);
x_124 = lean_int_dec_le(x_116, x_114);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_125 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
x_126 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_127 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_128 = lean_int_neg(x_114);
lean_dec(x_114);
x_129 = l_Int_toNat(x_128);
lean_dec(x_128);
x_130 = l_Lean_instToExprInt_mkNat(x_129);
x_131 = l_Lean_mkApp3(x_125, x_126, x_127, x_130);
x_33 = x_120;
x_34 = x_123;
x_35 = x_119;
x_36 = x_122;
x_37 = x_121;
x_38 = x_131;
goto block_52;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = l_Int_toNat(x_114);
lean_dec(x_114);
x_133 = l_Lean_instToExprInt_mkNat(x_132);
x_33 = x_120;
x_34 = x_123;
x_35 = x_119;
x_36 = x_122;
x_37 = x_121;
x_38 = x_133;
goto block_52;
}
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_141; 
lean_dec(x_114);
lean_dec_ref(x_32);
lean_del_object(x_30);
lean_del_object(x_20);
lean_dec(x_18);
lean_dec(x_15);
lean_del_object(x_12);
x_134 = lean_ctor_get(x_118, 0);
x_141 = !lean_is_exclusive(x_118);
if (x_141 == 0)
{
x_135 = x_118;
x_136 = x_141;
goto block_140;
}
else
{
lean_inc(x_134);
lean_dec(x_118);
x_135 = lean_box(0);
x_136 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_137; 
if (x_136 == 0)
{
x_137 = x_135;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_134);
x_137 = x_139;
goto block_138;
}
block_138:
{
return x_137;
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_del_object(x_30);
lean_del_object(x_20);
lean_del_object(x_12);
x_142 = l_Int_Linear_Poly_div(x_114, x_105);
lean_inc_ref(x_142);
x_143 = l_Int_Linear_Poly_denoteExpr___redArg(x_23, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
x_145 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_19, x_106, x_107, x_108, x_109);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
x_148 = l_Lean_mkIntEq(x_144, x_147);
x_149 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26);
x_150 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_151 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_18);
x_152 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_142);
x_153 = lean_int_dec_le(x_116, x_114);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_154 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
x_155 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_156 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_157 = lean_int_neg(x_114);
lean_dec(x_114);
x_158 = l_Int_toNat(x_157);
lean_dec(x_157);
x_159 = l_Lean_instToExprInt_mkNat(x_158);
x_160 = l_Lean_mkApp3(x_154, x_155, x_156, x_159);
x_53 = x_148;
x_54 = x_149;
x_55 = x_150;
x_56 = x_151;
x_57 = x_146;
x_58 = x_152;
x_59 = x_160;
goto block_71;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = l_Int_toNat(x_114);
lean_dec(x_114);
x_162 = l_Lean_instToExprInt_mkNat(x_161);
x_53 = x_148;
x_54 = x_149;
x_55 = x_150;
x_56 = x_151;
x_57 = x_146;
x_58 = x_152;
x_59 = x_162;
goto block_71;
}
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_170; 
lean_dec(x_144);
lean_dec_ref(x_142);
lean_dec(x_114);
lean_dec_ref(x_32);
lean_del_object(x_26);
lean_dec(x_18);
lean_del_object(x_16);
lean_dec(x_15);
x_163 = lean_ctor_get(x_145, 0);
x_170 = !lean_is_exclusive(x_145);
if (x_170 == 0)
{
x_164 = x_145;
x_165 = x_170;
goto block_169;
}
else
{
lean_inc(x_163);
lean_dec(x_145);
x_164 = lean_box(0);
x_165 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_166; 
if (x_165 == 0)
{
x_166 = x_164;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_163);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; uint8_t x_178; 
lean_dec_ref(x_142);
lean_dec(x_114);
lean_dec(x_109);
lean_dec_ref(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_32);
lean_del_object(x_26);
lean_dec(x_19);
lean_dec(x_18);
lean_del_object(x_16);
lean_dec(x_15);
x_171 = lean_ctor_get(x_143, 0);
x_178 = !lean_is_exclusive(x_143);
if (x_178 == 0)
{
x_172 = x_143;
x_173 = x_178;
goto block_177;
}
else
{
lean_inc(x_171);
lean_dec(x_143);
x_172 = lean_box(0);
x_173 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_174; 
if (x_173 == 0)
{
x_174 = x_172;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_171);
x_174 = x_176;
goto block_175;
}
block_175:
{
return x_174;
}
}
}
}
}
else
{
lean_object* x_179; 
lean_dec(x_110);
lean_del_object(x_30);
lean_del_object(x_26);
lean_del_object(x_20);
lean_del_object(x_16);
lean_del_object(x_12);
lean_inc_ref(x_105);
x_179 = l_Int_Linear_Poly_denoteExpr___redArg(x_23, x_105);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec_ref(x_179);
x_181 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_19, x_106, x_107, x_108, x_109);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_201; 
x_182 = lean_ctor_get(x_181, 0);
x_201 = !lean_is_exclusive(x_181);
if (x_201 == 0)
{
x_183 = x_181;
x_184 = x_201;
goto block_200;
}
else
{
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_box(0);
x_184 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_185 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
x_186 = l_Lean_mkIntEq(x_180, x_185);
x_187 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29);
x_188 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_189 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_18);
x_190 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_105);
x_191 = l_Lean_eagerReflBoolTrue;
x_192 = l_Lean_mkApp5(x_187, x_182, x_188, x_189, x_190, x_191);
lean_inc_ref(x_186);
x_193 = l_Lean_mkPropEq(x_32, x_186);
x_194 = l_Lean_Meta_mkExpectedPropHint(x_192, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_186);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_195);
if (x_184 == 0)
{
lean_ctor_set(x_183, 0, x_196);
x_197 = x_183;
goto block_198;
}
else
{
lean_object* x_199; 
x_199 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_199, 0, x_196);
x_197 = x_199;
goto block_198;
}
block_198:
{
return x_197;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; uint8_t x_209; 
lean_dec(x_180);
lean_dec_ref(x_105);
lean_dec_ref(x_32);
lean_dec(x_18);
lean_dec(x_15);
x_202 = lean_ctor_get(x_181, 0);
x_209 = !lean_is_exclusive(x_181);
if (x_209 == 0)
{
x_203 = x_181;
x_204 = x_209;
goto block_208;
}
else
{
lean_inc(x_202);
lean_dec(x_181);
x_203 = lean_box(0);
x_204 = x_209;
goto block_208;
}
block_208:
{
lean_object* x_205; 
if (x_204 == 0)
{
x_205 = x_203;
goto block_206;
}
else
{
lean_object* x_207; 
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_202);
x_205 = x_207;
goto block_206;
}
block_206:
{
return x_205;
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_217; 
lean_dec(x_109);
lean_dec_ref(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_105);
lean_dec_ref(x_32);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
x_210 = lean_ctor_get(x_179, 0);
x_217 = !lean_is_exclusive(x_179);
if (x_217 == 0)
{
x_211 = x_179;
x_212 = x_217;
goto block_216;
}
else
{
lean_inc(x_210);
lean_dec(x_179);
x_211 = lean_box(0);
x_212 = x_217;
goto block_216;
}
block_216:
{
lean_object* x_213; 
if (x_212 == 0)
{
x_213 = x_211;
goto block_214;
}
else
{
lean_object* x_215; 
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_210);
x_213 = x_215;
goto block_214;
}
block_214:
{
return x_213;
}
}
}
}
}
block_288:
{
if (x_219 == 0)
{
lean_del_object(x_9);
if (lean_obj_tag(x_105) == 1)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_220 = lean_ctor_get(x_105, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_105, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_105, 2);
lean_inc_ref(x_222);
x_223 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
x_224 = lean_int_dec_eq(x_220, x_223);
lean_dec(x_220);
if (x_224 == 0)
{
lean_dec_ref(x_222);
lean_dec(x_221);
x_106 = x_2;
x_107 = x_3;
x_108 = x_4;
x_109 = x_5;
goto block_218;
}
else
{
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
lean_dec_ref(x_105);
lean_del_object(x_30);
lean_del_object(x_26);
lean_dec_ref(x_23);
lean_del_object(x_20);
lean_del_object(x_16);
lean_del_object(x_12);
x_225 = lean_ctor_get(x_222, 0);
lean_inc(x_225);
lean_dec_ref(x_222);
x_226 = lean_array_get_borrowed(x_22, x_19, x_221);
x_227 = lean_int_neg(x_225);
lean_dec(x_225);
x_228 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
x_229 = lean_int_dec_le(x_228, x_227);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_230 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
x_231 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_232 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_233 = lean_int_neg(x_227);
lean_dec(x_227);
x_234 = l_Int_toNat(x_233);
lean_dec(x_233);
x_235 = l_Lean_instToExprInt_mkNat(x_234);
x_236 = l_Lean_mkApp3(x_230, x_231, x_232, x_235);
lean_inc(x_226);
x_72 = x_226;
x_73 = x_221;
x_74 = x_236;
goto block_103;
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = l_Int_toNat(x_227);
lean_dec(x_227);
x_238 = l_Lean_instToExprInt_mkNat(x_237);
lean_inc(x_226);
x_72 = x_226;
x_73 = x_221;
x_74 = x_238;
goto block_103;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_239 = lean_ctor_get(x_222, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_222, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_222, 2);
lean_inc_ref(x_241);
lean_dec_ref(x_222);
x_242 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31);
x_243 = lean_int_dec_eq(x_239, x_242);
lean_dec(x_239);
if (x_243 == 0)
{
lean_dec_ref(x_241);
lean_dec(x_240);
lean_dec(x_221);
x_106 = x_2;
x_107 = x_3;
x_108 = x_4;
x_109 = x_5;
goto block_218;
}
else
{
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_244; lean_object* x_245; uint8_t x_246; uint8_t x_283; 
x_244 = lean_ctor_get(x_241, 0);
x_283 = !lean_is_exclusive(x_241);
if (x_283 == 0)
{
x_245 = x_241;
x_246 = x_283;
goto block_282;
}
else
{
lean_inc(x_244);
lean_dec(x_241);
x_245 = lean_box(0);
x_246 = x_283;
goto block_282;
}
block_282:
{
lean_object* x_247; uint8_t x_248; 
x_247 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
x_248 = lean_int_dec_eq(x_244, x_247);
lean_dec(x_244);
if (x_248 == 0)
{
lean_del_object(x_245);
lean_dec(x_240);
lean_dec(x_221);
x_106 = x_2;
x_107 = x_3;
x_108 = x_4;
x_109 = x_5;
goto block_218;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec_ref(x_105);
lean_del_object(x_30);
lean_del_object(x_26);
lean_dec_ref(x_23);
lean_del_object(x_20);
lean_del_object(x_16);
lean_del_object(x_12);
x_249 = lean_array_get(x_22, x_19, x_221);
x_250 = lean_array_get(x_22, x_19, x_240);
x_251 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; uint8_t x_273; 
x_252 = lean_ctor_get(x_251, 0);
x_273 = !lean_is_exclusive(x_251);
if (x_273 == 0)
{
x_253 = x_251;
x_254 = x_273;
goto block_272;
}
else
{
lean_inc(x_252);
lean_dec(x_251);
x_253 = lean_box(0);
x_254 = x_273;
goto block_272;
}
block_272:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_255 = l_Lean_mkIntEq(x_249, x_250);
x_256 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34);
x_257 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_258 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_18);
x_259 = l_Lean_mkNatLit(x_221);
x_260 = l_Lean_mkNatLit(x_240);
x_261 = l_Lean_eagerReflBoolTrue;
x_262 = l_Lean_mkApp6(x_256, x_252, x_257, x_258, x_259, x_260, x_261);
lean_inc_ref(x_255);
x_263 = l_Lean_mkPropEq(x_32, x_255);
x_264 = l_Lean_Meta_mkExpectedPropHint(x_262, x_263);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_255);
lean_ctor_set(x_265, 1, x_264);
if (x_246 == 0)
{
lean_ctor_set_tag(x_245, 1);
lean_ctor_set(x_245, 0, x_265);
x_266 = x_245;
goto block_270;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_265);
x_266 = x_271;
goto block_270;
}
block_270:
{
lean_object* x_267; 
if (x_254 == 0)
{
lean_ctor_set(x_253, 0, x_266);
x_267 = x_253;
goto block_268;
}
else
{
lean_object* x_269; 
x_269 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_269, 0, x_266);
x_267 = x_269;
goto block_268;
}
block_268:
{
return x_267;
}
}
}
}
else
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; uint8_t x_281; 
lean_dec(x_250);
lean_dec(x_249);
lean_del_object(x_245);
lean_dec(x_240);
lean_dec(x_221);
lean_dec_ref(x_32);
lean_dec(x_18);
lean_dec(x_15);
x_274 = lean_ctor_get(x_251, 0);
x_281 = !lean_is_exclusive(x_251);
if (x_281 == 0)
{
x_275 = x_251;
x_276 = x_281;
goto block_280;
}
else
{
lean_inc(x_274);
lean_dec(x_251);
x_275 = lean_box(0);
x_276 = x_281;
goto block_280;
}
block_280:
{
lean_object* x_277; 
if (x_276 == 0)
{
x_277 = x_275;
goto block_278;
}
else
{
lean_object* x_279; 
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_274);
x_277 = x_279;
goto block_278;
}
block_278:
{
return x_277;
}
}
}
}
}
}
else
{
lean_dec_ref(x_241);
lean_dec(x_240);
lean_dec(x_221);
x_106 = x_2;
x_107 = x_3;
x_108 = x_4;
x_109 = x_5;
goto block_218;
}
}
}
}
}
else
{
x_106 = x_2;
x_107 = x_3;
x_108 = x_4;
x_109 = x_5;
goto block_218;
}
}
else
{
lean_object* x_284; lean_object* x_285; 
lean_dec_ref(x_105);
lean_dec_ref(x_32);
lean_del_object(x_30);
lean_del_object(x_26);
lean_dec_ref(x_23);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_del_object(x_16);
lean_dec(x_15);
lean_del_object(x_12);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_284 = lean_box(0);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_284);
x_285 = x_9;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_287, 0, x_284);
x_285 = x_287;
goto block_286;
}
block_286:
{
return x_285;
}
}
}
}
}
else
{
lean_object* x_351; lean_object* x_352; uint8_t x_353; uint8_t x_358; 
lean_del_object(x_26);
lean_dec(x_25);
lean_dec_ref(x_23);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_del_object(x_16);
lean_dec(x_15);
lean_del_object(x_12);
lean_del_object(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_351 = lean_ctor_get(x_28, 0);
x_358 = !lean_is_exclusive(x_28);
if (x_358 == 0)
{
x_352 = x_28;
x_353 = x_358;
goto block_357;
}
else
{
lean_inc(x_351);
lean_dec(x_28);
x_352 = lean_box(0);
x_353 = x_358;
goto block_357;
}
block_357:
{
lean_object* x_354; 
if (x_353 == 0)
{
x_354 = x_352;
goto block_355;
}
else
{
lean_object* x_356; 
x_356 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_356, 0, x_351);
x_354 = x_356;
goto block_355;
}
block_355:
{
return x_354;
}
}
}
}
}
else
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; uint8_t x_368; 
lean_dec_ref(x_23);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_del_object(x_16);
lean_dec(x_15);
lean_del_object(x_12);
lean_del_object(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_361 = lean_ctor_get(x_24, 0);
x_368 = !lean_is_exclusive(x_24);
if (x_368 == 0)
{
x_362 = x_24;
x_363 = x_368;
goto block_367;
}
else
{
lean_inc(x_361);
lean_dec(x_24);
x_362 = lean_box(0);
x_363 = x_368;
goto block_367;
}
block_367:
{
lean_object* x_364; 
if (x_363 == 0)
{
x_364 = x_362;
goto block_365;
}
else
{
lean_object* x_366; 
x_366 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_366, 0, x_361);
x_364 = x_366;
goto block_365;
}
block_365:
{
return x_364;
}
}
}
}
}
}
}
else
{
lean_object* x_375; lean_object* x_376; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_375 = lean_box(0);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_375);
x_376 = x_9;
goto block_377;
}
else
{
lean_object* x_378; 
x_378 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_378, 0, x_375);
x_376 = x_378;
goto block_377;
}
block_377:
{
return x_376;
}
}
}
}
else
{
lean_object* x_381; lean_object* x_382; uint8_t x_383; uint8_t x_388; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_381 = lean_ctor_get(x_7, 0);
x_388 = !lean_is_exclusive(x_7);
if (x_388 == 0)
{
x_382 = x_7;
x_383 = x_388;
goto block_387;
}
else
{
lean_inc(x_381);
lean_dec(x_7);
x_382 = lean_box(0);
x_383 = x_388;
goto block_387;
}
block_387:
{
lean_object* x_384; 
if (x_383 == 0)
{
x_384 = x_382;
goto block_385;
}
else
{
lean_object* x_386; 
x_386 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_386, 0, x_381);
x_384 = x_386;
goto block_385;
}
block_385:
{
return x_384;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_175; uint8_t x_176; lean_object* x_315; uint8_t x_316; 
x_175 = l_Lean_instInhabitedExpr;
x_315 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17));
x_316 = l_Lean_Expr_isAppOf(x_1, x_315);
if (x_316 == 0)
{
x_176 = x_316;
goto block_314;
}
else
{
x_176 = x_2;
goto block_314;
}
block_16:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_8);
x_11 = l_Lean_mkPropEq(x_9, x_8);
x_12 = l_Lean_Meta_mkExpectedPropHint(x_10, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_eagerReflBoolTrue;
x_26 = l_Lean_mkApp6(x_17, x_18, x_20, x_23, x_21, x_24, x_25);
x_8 = x_19;
x_9 = x_22;
x_10 = x_26;
goto block_16;
}
block_38:
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_eagerReflBoolTrue;
x_37 = l_Lean_mkApp6(x_34, x_29, x_31, x_28, x_33, x_35, x_36);
x_8 = x_30;
x_9 = x_32;
x_10 = x_37;
goto block_16;
}
block_118:
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Int_Linear_Poly_div(x_39, x_40);
lean_inc_ref(x_49);
x_50 = l_Int_Linear_Poly_denoteExpr___redArg(x_47, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = l_Lean_mkIntLit(x_46);
x_53 = l_Lean_mkIntLE(x_51, x_52);
if (x_48 == 0)
{
lean_object* x_54; 
x_54 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_41, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_box(0);
x_57 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2);
x_58 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_42);
x_59 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_45);
x_60 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_49);
x_61 = lean_int_dec_le(x_46, x_39);
lean_dec(x_46);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_62 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14));
x_63 = l_Lean_Level_ofNat(x_43);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_56);
x_65 = l_Lean_Expr_const___override(x_62, x_64);
x_66 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_67 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_68 = lean_int_neg(x_39);
lean_dec(x_39);
x_69 = l_Int_toNat(x_68);
lean_dec(x_68);
x_70 = l_Lean_instToExprInt_mkNat(x_69);
x_71 = l_Lean_mkApp3(x_65, x_66, x_67, x_70);
x_28 = x_59;
x_29 = x_55;
x_30 = x_53;
x_31 = x_58;
x_32 = x_44;
x_33 = x_60;
x_34 = x_57;
x_35 = x_71;
goto block_38;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Int_toNat(x_39);
lean_dec(x_39);
x_73 = l_Lean_instToExprInt_mkNat(x_72);
x_28 = x_59;
x_29 = x_55;
x_30 = x_53;
x_31 = x_58;
x_32 = x_44;
x_33 = x_60;
x_34 = x_57;
x_35 = x_73;
goto block_38;
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_dec_ref(x_53);
lean_dec_ref(x_49);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec_ref(x_42);
lean_dec(x_39);
x_74 = lean_ctor_get(x_54, 0);
x_81 = !lean_is_exclusive(x_54);
if (x_81 == 0)
{
x_75 = x_54;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_54);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
else
{
lean_object* x_82; 
x_82 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_41, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = lean_box(0);
x_85 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5);
x_86 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_42);
x_87 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_45);
x_88 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_49);
x_89 = lean_int_dec_le(x_46, x_39);
lean_dec(x_46);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_90 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14));
x_91 = l_Lean_Level_ofNat(x_43);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_84);
x_93 = l_Lean_Expr_const___override(x_90, x_92);
x_94 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_95 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_96 = lean_int_neg(x_39);
lean_dec(x_39);
x_97 = l_Int_toNat(x_96);
lean_dec(x_96);
x_98 = l_Lean_instToExprInt_mkNat(x_97);
x_99 = l_Lean_mkApp3(x_93, x_94, x_95, x_98);
x_17 = x_85;
x_18 = x_83;
x_19 = x_53;
x_20 = x_86;
x_21 = x_88;
x_22 = x_44;
x_23 = x_87;
x_24 = x_99;
goto block_27;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = l_Int_toNat(x_39);
lean_dec(x_39);
x_101 = l_Lean_instToExprInt_mkNat(x_100);
x_17 = x_85;
x_18 = x_83;
x_19 = x_53;
x_20 = x_86;
x_21 = x_88;
x_22 = x_44;
x_23 = x_87;
x_24 = x_101;
goto block_27;
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_109; 
lean_dec_ref(x_53);
lean_dec_ref(x_49);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec_ref(x_42);
lean_dec(x_39);
x_102 = lean_ctor_get(x_82, 0);
x_109 = !lean_is_exclusive(x_82);
if (x_109 == 0)
{
x_103 = x_82;
x_104 = x_109;
goto block_108;
}
else
{
lean_inc(x_102);
lean_dec(x_82);
x_103 = lean_box(0);
x_104 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_105; 
if (x_104 == 0)
{
x_105 = x_103;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_102);
x_105 = x_107;
goto block_106;
}
block_106:
{
return x_105;
}
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_117; 
lean_dec_ref(x_49);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec(x_39);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_110 = lean_ctor_get(x_50, 0);
x_117 = !lean_is_exclusive(x_50);
if (x_117 == 0)
{
x_111 = x_50;
x_112 = x_117;
goto block_116;
}
else
{
lean_inc(x_110);
lean_dec(x_50);
x_111 = lean_box(0);
x_112 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_113; 
if (x_112 == 0)
{
x_113 = x_111;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_110);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
}
block_174:
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = l_Int_Linear_Poly_gcdCoeffs_x27(x_119);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_nat_dec_eq(x_125, x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_128 = l_Int_Linear_Poly_getConst(x_119);
x_129 = lean_nat_to_int(x_125);
x_130 = lean_int_emod(x_128, x_129);
lean_dec(x_128);
x_131 = lean_unsigned_to_nat(0u);
x_132 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
x_133 = lean_int_dec_eq(x_130, x_132);
lean_dec(x_130);
if (x_133 == 0)
{
uint8_t x_134; 
x_134 = 1;
x_39 = x_129;
x_40 = x_119;
x_41 = x_120;
x_42 = x_121;
x_43 = x_131;
x_44 = x_122;
x_45 = x_124;
x_46 = x_132;
x_47 = x_123;
x_48 = x_134;
goto block_118;
}
else
{
x_39 = x_129;
x_40 = x_119;
x_41 = x_120;
x_42 = x_121;
x_43 = x_131;
x_44 = x_122;
x_45 = x_124;
x_46 = x_132;
x_47 = x_123;
x_48 = x_127;
goto block_118;
}
}
else
{
lean_object* x_135; 
lean_dec(x_125);
lean_inc_ref(x_119);
x_135 = l_Int_Linear_Poly_denoteExpr___redArg(x_123, x_119);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
x_137 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_120, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_157; 
x_138 = lean_ctor_get(x_137, 0);
x_157 = !lean_is_exclusive(x_137);
if (x_157 == 0)
{
x_139 = x_137;
x_140 = x_157;
goto block_156;
}
else
{
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_box(0);
x_140 = x_157;
goto block_156;
}
block_156:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_141 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
x_142 = l_Lean_mkIntLE(x_136, x_141);
x_143 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8);
x_144 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_121);
x_145 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_124);
x_146 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_119);
x_147 = l_Lean_eagerReflBoolTrue;
x_148 = l_Lean_mkApp5(x_143, x_138, x_144, x_145, x_146, x_147);
lean_inc_ref(x_142);
x_149 = l_Lean_mkPropEq(x_122, x_142);
x_150 = l_Lean_Meta_mkExpectedPropHint(x_148, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_142);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
if (x_140 == 0)
{
lean_ctor_set(x_139, 0, x_152);
x_153 = x_139;
goto block_154;
}
else
{
lean_object* x_155; 
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_152);
x_153 = x_155;
goto block_154;
}
block_154:
{
return x_153;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; uint8_t x_165; 
lean_dec(x_136);
lean_dec_ref(x_124);
lean_dec_ref(x_122);
lean_dec_ref(x_121);
lean_dec_ref(x_119);
x_158 = lean_ctor_get(x_137, 0);
x_165 = !lean_is_exclusive(x_137);
if (x_165 == 0)
{
x_159 = x_137;
x_160 = x_165;
goto block_164;
}
else
{
lean_inc(x_158);
lean_dec(x_137);
x_159 = lean_box(0);
x_160 = x_165;
goto block_164;
}
block_164:
{
lean_object* x_161; 
if (x_160 == 0)
{
x_161 = x_159;
goto block_162;
}
else
{
lean_object* x_163; 
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_158);
x_161 = x_163;
goto block_162;
}
block_162:
{
return x_161;
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_173; 
lean_dec_ref(x_124);
lean_dec_ref(x_122);
lean_dec_ref(x_121);
lean_dec_ref(x_120);
lean_dec_ref(x_119);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_166 = lean_ctor_get(x_135, 0);
x_173 = !lean_is_exclusive(x_135);
if (x_173 == 0)
{
x_167 = x_135;
x_168 = x_173;
goto block_172;
}
else
{
lean_inc(x_166);
lean_dec(x_135);
x_167 = lean_box(0);
x_168 = x_173;
goto block_172;
}
block_172:
{
lean_object* x_169; 
if (x_168 == 0)
{
x_169 = x_167;
goto block_170;
}
else
{
lean_object* x_171; 
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_166);
x_169 = x_171;
goto block_170;
}
block_170:
{
return x_169;
}
}
}
}
}
block_314:
{
lean_object* x_177; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_177 = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_305; 
x_178 = lean_ctor_get(x_177, 0);
x_305 = !lean_is_exclusive(x_177);
if (x_305 == 0)
{
x_179 = x_177;
x_180 = x_305;
goto block_304;
}
else
{
lean_inc(x_178);
lean_dec(x_177);
x_179 = lean_box(0);
x_180 = x_305;
goto block_304;
}
block_304:
{
if (lean_obj_tag(x_178) == 1)
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; uint8_t x_299; 
lean_del_object(x_179);
x_181 = lean_ctor_get(x_178, 0);
x_299 = !lean_is_exclusive(x_178);
if (x_299 == 0)
{
x_182 = x_178;
x_183 = x_299;
goto block_298;
}
else
{
lean_inc(x_181);
lean_dec(x_178);
x_182 = lean_box(0);
x_183 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_297; 
x_184 = lean_ctor_get(x_181, 1);
x_185 = lean_ctor_get(x_181, 0);
x_297 = !lean_is_exclusive(x_181);
if (x_297 == 0)
{
x_186 = x_181;
x_187 = x_297;
goto block_296;
}
else
{
lean_inc(x_184);
lean_inc(x_185);
lean_dec(x_181);
x_186 = lean_box(0);
x_187 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; uint8_t x_295; 
x_188 = lean_ctor_get(x_184, 0);
x_189 = lean_ctor_get(x_184, 1);
x_295 = !lean_is_exclusive(x_184);
if (x_295 == 0)
{
x_190 = x_184;
x_191 = x_295;
goto block_294;
}
else
{
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_184);
x_190 = lean_box(0);
x_191 = x_295;
goto block_294;
}
block_294:
{
lean_object* x_192; lean_object* x_193; 
lean_inc(x_189);
x_192 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_192, 0, x_175);
lean_closure_set(x_192, 1, x_189);
lean_inc(x_185);
lean_inc_ref(x_192);
x_193 = l_Int_Linear_Expr_denoteExpr___redArg(x_192, x_185);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec_ref(x_193);
lean_inc(x_188);
lean_inc_ref(x_192);
x_195 = l_Int_Linear_Expr_denoteExpr___redArg(x_192, x_188);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; uint8_t x_277; 
x_196 = lean_ctor_get(x_195, 0);
x_277 = !lean_is_exclusive(x_195);
if (x_277 == 0)
{
x_197 = x_195;
x_198 = x_277;
goto block_276;
}
else
{
lean_inc(x_196);
lean_dec(x_195);
x_197 = lean_box(0);
x_198 = x_277;
goto block_276;
}
block_276:
{
lean_object* x_199; lean_object* x_200; 
x_199 = l_Lean_mkIntLE(x_194, x_196);
lean_inc(x_188);
lean_inc(x_185);
if (x_187 == 0)
{
lean_ctor_set_tag(x_186, 3);
lean_ctor_set(x_186, 1, x_188);
x_200 = x_186;
goto block_274;
}
else
{
lean_object* x_275; 
x_275 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_275, 0, x_185);
lean_ctor_set(x_275, 1, x_188);
x_200 = x_275;
goto block_274;
}
block_274:
{
lean_object* x_201; uint8_t x_202; 
x_201 = l_Int_Linear_Expr_norm(x_200);
lean_dec_ref(x_200);
x_202 = l_Int_Linear_Poly_isUnsatLe(x_201);
if (x_202 == 0)
{
uint8_t x_203; 
x_203 = l_Int_Linear_Poly_isValidLe(x_201);
if (x_203 == 0)
{
lean_del_object(x_190);
lean_del_object(x_182);
if (x_176 == 0)
{
lean_del_object(x_197);
x_119 = x_201;
x_120 = x_189;
x_121 = x_185;
x_122 = x_199;
x_123 = x_192;
x_124 = x_188;
goto block_174;
}
else
{
lean_object* x_204; uint8_t x_205; 
lean_inc_ref(x_201);
x_204 = l_Int_Linear_Poly_toExpr(x_201);
x_205 = l_Int_Linear_instBEqExpr_beq(x_204, x_185);
lean_dec_ref(x_204);
if (x_205 == 0)
{
lean_del_object(x_197);
x_119 = x_201;
x_120 = x_189;
x_121 = x_185;
x_122 = x_199;
x_123 = x_192;
x_124 = x_188;
goto block_174;
}
else
{
lean_object* x_206; uint8_t x_207; 
x_206 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35);
x_207 = l_Int_Linear_instBEqExpr_beq(x_188, x_206);
if (x_207 == 0)
{
lean_del_object(x_197);
x_119 = x_201;
x_120 = x_189;
x_121 = x_185;
x_122 = x_199;
x_123 = x_192;
x_124 = x_188;
goto block_174;
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec_ref(x_201);
lean_dec_ref(x_199);
lean_dec_ref(x_192);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_185);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_208 = lean_box(0);
if (x_198 == 0)
{
lean_ctor_set(x_197, 0, x_208);
x_209 = x_197;
goto block_210;
}
else
{
lean_object* x_211; 
x_211 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_211, 0, x_208);
x_209 = x_211;
goto block_210;
}
block_210:
{
return x_209;
}
}
}
}
}
else
{
lean_object* x_212; 
lean_dec_ref(x_201);
lean_del_object(x_197);
lean_dec_ref(x_192);
x_212 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_189, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; uint8_t x_234; 
x_213 = lean_ctor_get(x_212, 0);
x_234 = !lean_is_exclusive(x_212);
if (x_234 == 0)
{
x_214 = x_212;
x_215 = x_234;
goto block_233;
}
else
{
lean_inc(x_213);
lean_dec(x_212);
x_214 = lean_box(0);
x_215 = x_234;
goto block_233;
}
block_233:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_216 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38);
x_217 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11);
x_218 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_185);
x_219 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_188);
x_220 = l_Lean_eagerReflBoolTrue;
x_221 = l_Lean_mkApp4(x_217, x_213, x_218, x_219, x_220);
x_222 = l_Lean_mkPropEq(x_199, x_216);
x_223 = l_Lean_Meta_mkExpectedPropHint(x_221, x_222);
if (x_191 == 0)
{
lean_ctor_set(x_190, 1, x_223);
lean_ctor_set(x_190, 0, x_216);
x_224 = x_190;
goto block_231;
}
else
{
lean_object* x_232; 
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_216);
lean_ctor_set(x_232, 1, x_223);
x_224 = x_232;
goto block_231;
}
block_231:
{
lean_object* x_225; 
if (x_183 == 0)
{
lean_ctor_set(x_182, 0, x_224);
x_225 = x_182;
goto block_229;
}
else
{
lean_object* x_230; 
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_224);
x_225 = x_230;
goto block_229;
}
block_229:
{
lean_object* x_226; 
if (x_215 == 0)
{
lean_ctor_set(x_214, 0, x_225);
x_226 = x_214;
goto block_227;
}
else
{
lean_object* x_228; 
x_228 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_228, 0, x_225);
x_226 = x_228;
goto block_227;
}
block_227:
{
return x_226;
}
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; uint8_t x_242; 
lean_dec_ref(x_199);
lean_del_object(x_190);
lean_dec(x_188);
lean_dec(x_185);
lean_del_object(x_182);
x_235 = lean_ctor_get(x_212, 0);
x_242 = !lean_is_exclusive(x_212);
if (x_242 == 0)
{
x_236 = x_212;
x_237 = x_242;
goto block_241;
}
else
{
lean_inc(x_235);
lean_dec(x_212);
x_236 = lean_box(0);
x_237 = x_242;
goto block_241;
}
block_241:
{
lean_object* x_238; 
if (x_237 == 0)
{
x_238 = x_236;
goto block_239;
}
else
{
lean_object* x_240; 
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_235);
x_238 = x_240;
goto block_239;
}
block_239:
{
return x_238;
}
}
}
}
}
else
{
lean_object* x_243; 
lean_dec_ref(x_201);
lean_del_object(x_197);
lean_dec_ref(x_192);
x_243 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_189, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; uint8_t x_246; uint8_t x_265; 
x_244 = lean_ctor_get(x_243, 0);
x_265 = !lean_is_exclusive(x_243);
if (x_265 == 0)
{
x_245 = x_243;
x_246 = x_265;
goto block_264;
}
else
{
lean_inc(x_244);
lean_dec(x_243);
x_245 = lean_box(0);
x_246 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_247 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8);
x_248 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14);
x_249 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_185);
x_250 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_188);
x_251 = l_Lean_eagerReflBoolTrue;
x_252 = l_Lean_mkApp4(x_248, x_244, x_249, x_250, x_251);
x_253 = l_Lean_mkPropEq(x_199, x_247);
x_254 = l_Lean_Meta_mkExpectedPropHint(x_252, x_253);
if (x_191 == 0)
{
lean_ctor_set(x_190, 1, x_254);
lean_ctor_set(x_190, 0, x_247);
x_255 = x_190;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_247);
lean_ctor_set(x_263, 1, x_254);
x_255 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_256; 
if (x_183 == 0)
{
lean_ctor_set(x_182, 0, x_255);
x_256 = x_182;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_261, 0, x_255);
x_256 = x_261;
goto block_260;
}
block_260:
{
lean_object* x_257; 
if (x_246 == 0)
{
lean_ctor_set(x_245, 0, x_256);
x_257 = x_245;
goto block_258;
}
else
{
lean_object* x_259; 
x_259 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_259, 0, x_256);
x_257 = x_259;
goto block_258;
}
block_258:
{
return x_257;
}
}
}
}
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; uint8_t x_273; 
lean_dec_ref(x_199);
lean_del_object(x_190);
lean_dec(x_188);
lean_dec(x_185);
lean_del_object(x_182);
x_266 = lean_ctor_get(x_243, 0);
x_273 = !lean_is_exclusive(x_243);
if (x_273 == 0)
{
x_267 = x_243;
x_268 = x_273;
goto block_272;
}
else
{
lean_inc(x_266);
lean_dec(x_243);
x_267 = lean_box(0);
x_268 = x_273;
goto block_272;
}
block_272:
{
lean_object* x_269; 
if (x_268 == 0)
{
x_269 = x_267;
goto block_270;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_266);
x_269 = x_271;
goto block_270;
}
block_270:
{
return x_269;
}
}
}
}
}
}
}
else
{
lean_object* x_278; lean_object* x_279; uint8_t x_280; uint8_t x_285; 
lean_dec(x_194);
lean_dec_ref(x_192);
lean_del_object(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_del_object(x_186);
lean_dec(x_185);
lean_del_object(x_182);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_278 = lean_ctor_get(x_195, 0);
x_285 = !lean_is_exclusive(x_195);
if (x_285 == 0)
{
x_279 = x_195;
x_280 = x_285;
goto block_284;
}
else
{
lean_inc(x_278);
lean_dec(x_195);
x_279 = lean_box(0);
x_280 = x_285;
goto block_284;
}
block_284:
{
lean_object* x_281; 
if (x_280 == 0)
{
x_281 = x_279;
goto block_282;
}
else
{
lean_object* x_283; 
x_283 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_283, 0, x_278);
x_281 = x_283;
goto block_282;
}
block_282:
{
return x_281;
}
}
}
}
else
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; uint8_t x_293; 
lean_dec_ref(x_192);
lean_del_object(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_del_object(x_186);
lean_dec(x_185);
lean_del_object(x_182);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_286 = lean_ctor_get(x_193, 0);
x_293 = !lean_is_exclusive(x_193);
if (x_293 == 0)
{
x_287 = x_193;
x_288 = x_293;
goto block_292;
}
else
{
lean_inc(x_286);
lean_dec(x_193);
x_287 = lean_box(0);
x_288 = x_293;
goto block_292;
}
block_292:
{
lean_object* x_289; 
if (x_288 == 0)
{
x_289 = x_287;
goto block_290;
}
else
{
lean_object* x_291; 
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_286);
x_289 = x_291;
goto block_290;
}
block_290:
{
return x_289;
}
}
}
}
}
}
}
else
{
lean_object* x_300; lean_object* x_301; 
lean_dec(x_178);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_300 = lean_box(0);
if (x_180 == 0)
{
lean_ctor_set(x_179, 0, x_300);
x_301 = x_179;
goto block_302;
}
else
{
lean_object* x_303; 
x_303 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_303, 0, x_300);
x_301 = x_303;
goto block_302;
}
block_302:
{
return x_301;
}
}
}
}
else
{
lean_object* x_306; lean_object* x_307; uint8_t x_308; uint8_t x_313; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_306 = lean_ctor_get(x_177, 0);
x_313 = !lean_is_exclusive(x_177);
if (x_313 == 0)
{
x_307 = x_177;
x_308 = x_313;
goto block_312;
}
else
{
lean_inc(x_306);
lean_dec(x_177);
x_307 = lean_box(0);
x_308 = x_313;
goto block_312;
}
block_312:
{
lean_object* x_309; 
if (x_308 == 0)
{
x_309 = x_307;
goto block_310;
}
else
{
lean_object* x_311; 
x_311 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_311, 0, x_306);
x_309 = x_311;
goto block_310;
}
block_310:
{
return x_309;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Level_succ___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8));
x_53 = lean_unsigned_to_nat(1u);
x_54 = l_Lean_Expr_isAppOfArity(x_1, x_52, x_53);
if (x_54 == 0)
{
uint8_t x_55; lean_object* x_56; 
x_55 = 1;
x_56 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_1, x_55, x_2, x_3, x_4, x_5);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_Expr_appArg_x21(x_1);
x_58 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_57, x_3);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = l_Lean_Expr_cleanupAnnotations(x_59);
x_61 = l_Lean_Expr_isApp(x_60);
if (x_61 == 0)
{
lean_dec_ref(x_60);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_9;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_62);
x_63 = l_Lean_Expr_appFnCleanup___redArg(x_60);
x_64 = l_Lean_Expr_isApp(x_63);
if (x_64 == 0)
{
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_9;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_65);
x_66 = l_Lean_Expr_appFnCleanup___redArg(x_63);
x_67 = l_Lean_Expr_isApp(x_66);
if (x_67 == 0)
{
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_62);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_9;
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = l_Lean_Expr_appFnCleanup___redArg(x_66);
x_69 = l_Lean_Expr_isApp(x_68);
if (x_69 == 0)
{
lean_dec_ref(x_68);
lean_dec_ref(x_65);
lean_dec_ref(x_62);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_9;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_68, 1);
lean_inc_ref(x_70);
x_71 = l_Lean_Expr_appFnCleanup___redArg(x_68);
x_72 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11));
x_73 = l_Lean_Expr_isConstOf(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14));
x_75 = l_Lean_Expr_isConstOf(x_71, x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17));
x_77 = l_Lean_Expr_isConstOf(x_71, x_76);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17));
x_79 = l_Lean_Expr_isConstOf(x_71, x_78);
lean_dec_ref(x_71);
if (x_79 == 0)
{
lean_dec_ref(x_70);
lean_dec_ref(x_65);
lean_dec_ref(x_62);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_9;
}
else
{
lean_object* x_80; 
x_80 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_70, x_3);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = l_Lean_Expr_cleanupAnnotations(x_81);
x_83 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18));
x_84 = l_Lean_Expr_isConstOf(x_82, x_83);
lean_dec_ref(x_82);
if (x_84 == 0)
{
lean_dec_ref(x_65);
lean_dec_ref(x_62);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_9;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
lean_inc_ref(x_62);
x_86 = l_Lean_mkIntAdd(x_62, x_85);
lean_inc_ref(x_65);
x_87 = l_Lean_mkIntLE(x_86, x_65);
x_88 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21);
x_89 = l_Lean_mkAppB(x_88, x_65, x_62);
x_10 = x_87;
x_11 = x_89;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
goto block_51;
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
lean_dec_ref(x_65);
lean_dec_ref(x_62);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_90 = lean_ctor_get(x_80, 0);
x_97 = !lean_is_exclusive(x_80);
if (x_97 == 0)
{
x_91 = x_80;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_80);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
}
else
{
lean_object* x_98; 
lean_dec_ref(x_71);
x_98 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_70, x_3);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = l_Lean_Expr_cleanupAnnotations(x_99);
x_101 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18));
x_102 = l_Lean_Expr_isConstOf(x_100, x_101);
lean_dec_ref(x_100);
if (x_102 == 0)
{
lean_dec_ref(x_65);
lean_dec_ref(x_62);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_9;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
lean_inc_ref(x_65);
x_104 = l_Lean_mkIntAdd(x_65, x_103);
lean_inc_ref(x_62);
x_105 = l_Lean_mkIntLE(x_104, x_62);
x_106 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24);
x_107 = l_Lean_mkAppB(x_106, x_65, x_62);
x_10 = x_105;
x_11 = x_107;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
goto block_51;
}
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_115; 
lean_dec_ref(x_65);
lean_dec_ref(x_62);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_108 = lean_ctor_get(x_98, 0);
x_115 = !lean_is_exclusive(x_98);
if (x_115 == 0)
{
x_109 = x_98;
x_110 = x_115;
goto block_114;
}
else
{
lean_inc(x_108);
lean_dec(x_98);
x_109 = lean_box(0);
x_110 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_111; 
if (x_110 == 0)
{
x_111 = x_109;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_108);
x_111 = x_113;
goto block_112;
}
block_112:
{
return x_111;
}
}
}
}
}
else
{
lean_object* x_116; 
lean_dec_ref(x_71);
x_116 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_70, x_3);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_118 = l_Lean_Expr_cleanupAnnotations(x_117);
x_119 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18));
x_120 = l_Lean_Expr_isConstOf(x_118, x_119);
lean_dec_ref(x_118);
if (x_120 == 0)
{
lean_dec_ref(x_65);
lean_dec_ref(x_62);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_9;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_inc_ref(x_65);
lean_inc_ref(x_62);
x_121 = l_Lean_mkIntLE(x_62, x_65);
x_122 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27);
x_123 = l_Lean_mkAppB(x_122, x_65, x_62);
x_10 = x_121;
x_11 = x_123;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
goto block_51;
}
}
else
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_131; 
lean_dec_ref(x_65);
lean_dec_ref(x_62);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_124 = lean_ctor_get(x_116, 0);
x_131 = !lean_is_exclusive(x_116);
if (x_131 == 0)
{
x_125 = x_116;
x_126 = x_131;
goto block_130;
}
else
{
lean_inc(x_124);
lean_dec(x_116);
x_125 = lean_box(0);
x_126 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_127; 
if (x_126 == 0)
{
x_127 = x_125;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_124);
x_127 = x_129;
goto block_128;
}
block_128:
{
return x_127;
}
}
}
}
}
else
{
lean_object* x_132; 
lean_dec_ref(x_71);
x_132 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_70, x_3);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = l_Lean_Expr_cleanupAnnotations(x_133);
x_135 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18));
x_136 = l_Lean_Expr_isConstOf(x_134, x_135);
lean_dec_ref(x_134);
if (x_136 == 0)
{
lean_dec_ref(x_65);
lean_dec_ref(x_62);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_9;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_inc_ref(x_62);
lean_inc_ref(x_65);
x_137 = l_Lean_mkIntLE(x_65, x_62);
x_138 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30);
x_139 = l_Lean_mkAppB(x_138, x_65, x_62);
x_10 = x_137;
x_11 = x_139;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
goto block_51;
}
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_147; 
lean_dec_ref(x_65);
lean_dec_ref(x_62);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_140 = lean_ctor_get(x_132, 0);
x_147 = !lean_is_exclusive(x_132);
if (x_147 == 0)
{
x_141 = x_132;
x_142 = x_147;
goto block_146;
}
else
{
lean_inc(x_140);
lean_dec(x_132);
x_141 = lean_box(0);
x_142 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_143; 
if (x_142 == 0)
{
x_143 = x_141;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_140);
x_143 = x_145;
goto block_144;
}
block_144:
{
return x_143;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_155; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_148 = lean_ctor_get(x_58, 0);
x_155 = !lean_is_exclusive(x_58);
if (x_155 == 0)
{
x_149 = x_58;
x_150 = x_155;
goto block_154;
}
else
{
lean_inc(x_148);
lean_dec(x_58);
x_149 = lean_box(0);
x_150 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_151; 
if (x_150 == 0)
{
x_151 = x_149;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_148);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_51:
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
lean_inc_ref(x_10);
x_17 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_10, x_16, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_50; 
x_18 = lean_ctor_get(x_17, 0);
x_50 = !lean_is_exclusive(x_17);
if (x_50 == 0)
{
x_19 = x_17;
x_20 = x_50;
goto block_49;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_50;
goto block_49;
}
block_49:
{
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_43; 
x_21 = lean_ctor_get(x_18, 0);
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
x_22 = x_18;
x_23 = x_43;
goto block_42;
}
else
{
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_41; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
x_26 = x_21;
x_27 = x_41;
goto block_40;
}
else
{
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5);
x_29 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6);
lean_inc(x_24);
x_30 = l_Lean_mkApp6(x_28, x_29, x_1, x_10, x_24, x_11, x_25);
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_30);
x_31 = x_26;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_30);
x_31 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_32; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_31);
x_32 = x_22;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_31);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_32);
x_33 = x_19;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_18);
lean_dec_ref(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_10);
lean_ctor_set(x_44, 1, x_11);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_45);
x_46 = x_19;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
else
{
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_28; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_28 = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_196; 
x_29 = lean_ctor_get(x_28, 0);
x_196 = !lean_is_exclusive(x_28);
if (x_196 == 0)
{
x_30 = x_28;
x_31 = x_196;
goto block_195;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_196;
goto block_195;
}
block_195:
{
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_190; 
x_32 = lean_ctor_get(x_29, 0);
x_190 = !lean_is_exclusive(x_29);
if (x_190 == 0)
{
x_33 = x_29;
x_34 = x_190;
goto block_189;
}
else
{
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(0);
x_34 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_188; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_188 = !lean_is_exclusive(x_35);
if (x_188 == 0)
{
x_39 = x_35;
x_40 = x_188;
goto block_187;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_box(0);
x_40 = x_188;
goto block_187;
}
block_187:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_90; 
x_41 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
x_90 = lean_int_dec_eq(x_36, x_41);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_del_object(x_30);
x_91 = l_Lean_instInhabitedExpr;
lean_inc(x_38);
x_92 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_92, 0, x_91);
lean_closure_set(x_92, 1, x_38);
lean_inc(x_37);
lean_inc_ref(x_92);
x_93 = l_Int_Linear_Expr_denoteExpr___redArg(x_92, x_37);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_174; 
x_94 = lean_ctor_get(x_93, 0);
x_174 = !lean_is_exclusive(x_93);
if (x_174 == 0)
{
x_95 = x_93;
x_96 = x_174;
goto block_173;
}
else
{
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_box(0);
x_96 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_97; uint8_t x_163; 
x_163 = lean_int_dec_le(x_41, x_36);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_164 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
x_165 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_166 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_167 = lean_int_neg(x_36);
x_168 = l_Int_toNat(x_167);
lean_dec(x_167);
x_169 = l_Lean_instToExprInt_mkNat(x_168);
x_170 = l_Lean_mkApp3(x_164, x_165, x_166, x_169);
x_97 = x_170;
goto block_162;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = l_Int_toNat(x_36);
x_172 = l_Lean_instToExprInt_mkNat(x_171);
x_97 = x_172;
goto block_162;
}
block_162:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_inc_ref(x_97);
x_98 = l_Lean_mkIntDvd(x_97, x_94);
x_99 = l_Int_Linear_Expr_norm(x_37);
lean_inc(x_36);
x_100 = l_Int_Linear_Poly_gcdCoeffs(x_99, x_36);
x_101 = l_Int_Linear_Poly_getConst(x_99);
x_102 = lean_int_emod(x_101, x_100);
lean_dec(x_101);
x_103 = lean_int_dec_eq(x_102, x_41);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
lean_dec(x_100);
lean_dec_ref(x_99);
lean_del_object(x_95);
lean_dec_ref(x_92);
lean_dec(x_36);
x_104 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_38, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_125; 
x_105 = lean_ctor_get(x_104, 0);
x_125 = !lean_is_exclusive(x_104);
if (x_125 == 0)
{
x_106 = x_104;
x_107 = x_125;
goto block_124;
}
else
{
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_box(0);
x_107 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_108 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8);
x_109 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8);
x_110 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_37);
x_111 = l_Lean_eagerReflBoolTrue;
x_112 = l_Lean_mkApp4(x_109, x_105, x_97, x_110, x_111);
x_113 = l_Lean_mkPropEq(x_98, x_108);
x_114 = l_Lean_Meta_mkExpectedPropHint(x_112, x_113);
if (x_40 == 0)
{
lean_ctor_set(x_39, 1, x_114);
lean_ctor_set(x_39, 0, x_108);
x_115 = x_39;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_108);
lean_ctor_set(x_123, 1, x_114);
x_115 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_116; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_115);
x_116 = x_33;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_115);
x_116 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_117; 
if (x_107 == 0)
{
lean_ctor_set(x_106, 0, x_116);
x_117 = x_106;
goto block_118;
}
else
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_116);
x_117 = x_119;
goto block_118;
}
block_118:
{
return x_117;
}
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_133; 
lean_dec_ref(x_98);
lean_dec_ref(x_97);
lean_del_object(x_39);
lean_dec(x_37);
lean_del_object(x_33);
x_126 = lean_ctor_get(x_104, 0);
x_133 = !lean_is_exclusive(x_104);
if (x_133 == 0)
{
x_127 = x_104;
x_128 = x_133;
goto block_132;
}
else
{
lean_inc(x_126);
lean_dec(x_104);
x_127 = lean_box(0);
x_128 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_129; 
if (x_128 == 0)
{
x_129 = x_127;
goto block_130;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_126);
x_129 = x_131;
goto block_130;
}
block_130:
{
return x_129;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_del_object(x_39);
lean_del_object(x_33);
x_134 = l_Int_Linear_Poly_div(x_100, x_99);
lean_inc_ref(x_134);
x_135 = l_Int_Linear_Poly_toExpr(x_134);
x_136 = l_Int_Linear_instBEqExpr_beq(x_37, x_135);
lean_dec_ref(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
lean_del_object(x_95);
lean_inc_ref(x_134);
x_137 = l_Int_Linear_Poly_denoteExpr___redArg(x_92, x_134);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = lean_int_ediv(x_36, x_100);
lean_dec(x_36);
x_140 = lean_int_dec_le(x_41, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
x_142 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_143 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_144 = lean_int_neg(x_139);
lean_dec(x_139);
x_145 = l_Int_toNat(x_144);
lean_dec(x_144);
x_146 = l_Lean_instToExprInt_mkNat(x_145);
x_147 = l_Lean_mkApp3(x_141, x_142, x_143, x_146);
x_42 = x_134;
x_43 = x_138;
x_44 = x_98;
x_45 = x_97;
x_46 = x_100;
x_47 = x_147;
goto block_89;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = l_Int_toNat(x_139);
lean_dec(x_139);
x_149 = l_Lean_instToExprInt_mkNat(x_148);
x_42 = x_134;
x_43 = x_138;
x_44 = x_98;
x_45 = x_97;
x_46 = x_100;
x_47 = x_149;
goto block_89;
}
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_157; 
lean_dec_ref(x_134);
lean_dec(x_100);
lean_dec_ref(x_98);
lean_dec_ref(x_97);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_150 = lean_ctor_get(x_137, 0);
x_157 = !lean_is_exclusive(x_137);
if (x_157 == 0)
{
x_151 = x_137;
x_152 = x_157;
goto block_156;
}
else
{
lean_inc(x_150);
lean_dec(x_137);
x_151 = lean_box(0);
x_152 = x_157;
goto block_156;
}
block_156:
{
lean_object* x_153; 
if (x_152 == 0)
{
x_153 = x_151;
goto block_154;
}
else
{
lean_object* x_155; 
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_150);
x_153 = x_155;
goto block_154;
}
block_154:
{
return x_153;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec_ref(x_134);
lean_dec(x_100);
lean_dec_ref(x_98);
lean_dec_ref(x_97);
lean_dec_ref(x_92);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_158 = lean_box(0);
if (x_96 == 0)
{
lean_ctor_set(x_95, 0, x_158);
x_159 = x_95;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_158);
x_159 = x_161;
goto block_160;
}
block_160:
{
return x_159;
}
}
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_182; 
lean_dec_ref(x_92);
lean_del_object(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_del_object(x_33);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_175 = lean_ctor_get(x_93, 0);
x_182 = !lean_is_exclusive(x_93);
if (x_182 == 0)
{
x_176 = x_93;
x_177 = x_182;
goto block_181;
}
else
{
lean_inc(x_175);
lean_dec(x_93);
x_176 = lean_box(0);
x_177 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_178; 
if (x_177 == 0)
{
x_178 = x_176;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_175);
x_178 = x_180;
goto block_179;
}
block_179:
{
return x_178;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_del_object(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_del_object(x_33);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_183 = lean_box(0);
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_183);
x_184 = x_30;
goto block_185;
}
else
{
lean_object* x_186; 
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_183);
x_184 = x_186;
goto block_185;
}
block_185:
{
return x_184;
}
}
block_89:
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc_ref(x_47);
x_48 = l_Lean_mkIntDvd(x_47, x_43);
x_49 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
x_50 = lean_int_dec_eq(x_46, x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_38, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2);
x_54 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_37);
x_55 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_42);
x_56 = lean_int_dec_le(x_41, x_46);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
x_58 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_59 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_60 = lean_int_neg(x_46);
lean_dec(x_46);
x_61 = l_Int_toNat(x_60);
lean_dec(x_60);
x_62 = l_Lean_instToExprInt_mkNat(x_61);
x_63 = l_Lean_mkApp3(x_57, x_58, x_59, x_62);
x_16 = x_52;
x_17 = x_55;
x_18 = x_54;
x_19 = x_44;
x_20 = x_45;
x_21 = x_47;
x_22 = x_48;
x_23 = x_53;
x_24 = x_63;
goto block_27;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Int_toNat(x_46);
lean_dec(x_46);
x_65 = l_Lean_instToExprInt_mkNat(x_64);
x_16 = x_52;
x_17 = x_55;
x_18 = x_54;
x_19 = x_44;
x_20 = x_45;
x_21 = x_47;
x_22 = x_48;
x_23 = x_53;
x_24 = x_65;
goto block_27;
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_73; 
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec_ref(x_42);
lean_dec(x_37);
x_66 = lean_ctor_get(x_51, 0);
x_73 = !lean_is_exclusive(x_51);
if (x_73 == 0)
{
x_67 = x_51;
x_68 = x_73;
goto block_72;
}
else
{
lean_inc(x_66);
lean_dec(x_51);
x_67 = lean_box(0);
x_68 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_69; 
if (x_68 == 0)
{
x_69 = x_67;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_66);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
else
{
lean_object* x_74; 
lean_dec_ref(x_47);
lean_dec(x_46);
x_74 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_38, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5);
x_77 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_37);
x_78 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_42);
x_79 = l_Lean_eagerReflBoolTrue;
x_80 = l_Lean_mkApp5(x_76, x_75, x_45, x_77, x_78, x_79);
x_7 = x_44;
x_8 = x_48;
x_9 = x_80;
goto block_15;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
lean_dec_ref(x_48);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec_ref(x_42);
lean_dec(x_37);
x_81 = lean_ctor_get(x_74, 0);
x_88 = !lean_is_exclusive(x_74);
if (x_88 == 0)
{
x_82 = x_74;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_74);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_191 = lean_box(0);
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_191);
x_192 = x_30;
goto block_193;
}
else
{
lean_object* x_194; 
x_194 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_194, 0, x_191);
x_192 = x_194;
goto block_193;
}
block_193:
{
return x_192;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_204; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_197 = lean_ctor_get(x_28, 0);
x_204 = !lean_is_exclusive(x_28);
if (x_204 == 0)
{
x_198 = x_28;
x_199 = x_204;
goto block_203;
}
else
{
lean_inc(x_197);
lean_dec(x_28);
x_198 = lean_box(0);
x_199 = x_204;
goto block_203;
}
block_203:
{
lean_object* x_200; 
if (x_199 == 0)
{
x_200 = x_198;
goto block_201;
}
else
{
lean_object* x_202; 
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_197);
x_200 = x_202;
goto block_201;
}
block_201:
{
return x_200;
}
}
}
block_15:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc_ref(x_8);
x_10 = l_Lean_mkPropEq(x_7, x_8);
x_11 = l_Lean_Meta_mkExpectedPropHint(x_9, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_eagerReflBoolTrue;
x_26 = l_Lean_mkApp7(x_23, x_16, x_20, x_18, x_21, x_17, x_24, x_25);
x_7 = x_19;
x_8 = x_22;
x_9 = x_26;
goto block_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_instInhabitedExpr;
x_4 = lean_array_get_borrowed(x_3, x_1, x_2);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_74; 
x_8 = lean_ctor_get(x_7, 0);
x_74 = !lean_is_exclusive(x_7);
if (x_74 == 0)
{
x_9 = x_7;
x_10 = x_74;
goto block_73;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_72; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_72 = !lean_is_exclusive(x_8);
if (x_72 == 0)
{
x_13 = x_8;
x_14 = x_72;
goto block_71;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Int_Linear_Expr_norm(x_11);
lean_inc_ref(x_15);
x_16 = l_Int_Linear_Poly_toExpr(x_15);
x_17 = l_Int_Linear_instBEqExpr_beq(x_11, x_16);
lean_dec_ref(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_del_object(x_9);
lean_inc(x_12);
x_18 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_12, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_20, 0, x_12);
lean_inc(x_11);
x_21 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_11);
lean_inc_ref(x_20);
x_22 = l_Int_Linear_Expr_denoteExpr___redArg(x_20, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc_ref(x_15);
x_24 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_15);
x_25 = l_Int_Linear_Poly_denoteExpr___redArg(x_20, x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_42; 
x_26 = lean_ctor_get(x_25, 0);
x_42 = !lean_is_exclusive(x_25);
if (x_42 == 0)
{
x_27 = x_25;
x_28 = x_42;
goto block_41;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3);
x_30 = l_Lean_eagerReflBoolTrue;
x_31 = l_Lean_mkApp4(x_29, x_19, x_21, x_24, x_30);
lean_inc(x_26);
x_32 = l_Lean_mkIntEq(x_23, x_26);
x_33 = l_Lean_Meta_mkExpectedPropHint(x_31, x_32);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_33);
lean_ctor_set(x_13, 0, x_26);
x_34 = x_13;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_33);
x_34 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_35);
x_36 = x_27;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec(x_19);
lean_del_object(x_13);
x_43 = lean_ctor_get(x_25, 0);
x_50 = !lean_is_exclusive(x_25);
if (x_50 == 0)
{
x_44 = x_25;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_25);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_15);
lean_del_object(x_13);
x_51 = lean_ctor_get(x_22, 0);
x_58 = !lean_is_exclusive(x_22);
if (x_58 == 0)
{
x_52 = x_22;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_22);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
lean_dec_ref(x_15);
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_59 = lean_ctor_get(x_18, 0);
x_66 = !lean_is_exclusive(x_18);
if (x_66 == 0)
{
x_60 = x_18;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_dec(x_18);
x_60 = lean_box(0);
x_61 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_62; 
if (x_61 == 0)
{
x_62 = x_60;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_59);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_15);
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_67 = lean_box(0);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_67);
x_68 = x_9;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_82; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_75 = lean_ctor_get(x_7, 0);
x_82 = !lean_is_exclusive(x_7);
if (x_82 == 0)
{
x_76 = x_7;
x_77 = x_82;
goto block_81;
}
else
{
lean_inc(x_75);
lean_dec(x_7);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
}
#ifdef __cplusplus
}
#endif
