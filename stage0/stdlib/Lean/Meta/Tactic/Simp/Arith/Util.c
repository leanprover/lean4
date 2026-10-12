// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Util
// Imports: public import Lean.Meta.Basic
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
extern lean_object* l_Lean_Nat_mkType;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__3_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__5_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__5_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__8_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isLinearTerm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__3_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__4_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__6_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__7_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__8_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__9_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__10_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__10_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__12_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__13_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__15_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isLinearPosCnstr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isLinearCnstr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearCnstr___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__2_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isDvdCnstr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isDvdCnstr___boxed(lean_object*);
uint8_t l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(lean_object* v_type_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_8_ = l_Lean_Expr_cleanupAnnotations(v_type_7_);
v___x_9_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__1));
v___x_10_ = l_Lean_Expr_isConstOf(v___x_8_, v___x_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__3));
v___x_12_ = l_Lean_Expr_isConstOf(v___x_8_, v___x_11_);
lean_dec_ref(v___x_8_);
return v___x_12_;
}
else
{
lean_dec_ref(v___x_8_);
return v___x_10_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_7_ = stack[0].m_obj;
uint8_t v_res_13_;
v_res_13_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_type_7_);
stack->m_num = v_res_13_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___boxed(lean_object* v_type_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_type_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType(lean_object* v_type_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_18_ = l_Lean_Expr_cleanupAnnotations(v_type_17_);
v___x_19_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__1));
v___x_20_ = l_Lean_Expr_isConstOf(v___x_18_, v___x_19_);
lean_dec_ref(v___x_18_);
return v___x_20_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_17_ = stack[0].m_obj;
uint8_t v_res_21_;
v_res_21_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType(v_type_17_);
stack->m_num = v_res_21_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType___boxed(lean_object* v_type_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType(v_type_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral(lean_object* v_e_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = l_Lean_Expr_isRawNatLit(v_e_35_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = l_Lean_Expr_cleanupAnnotations(v_e_35_);
v___x_38_ = l_Lean_Expr_isApp(v___x_37_);
if (v___x_38_ == 0)
{
lean_dec_ref(v___x_37_);
return v___x_36_;
}
else
{
lean_object* v_arg_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v_arg_39_ = lean_ctor_get(v___x_37_, 1);
lean_inc_ref(v_arg_39_);
v___x_40_ = l_Lean_Expr_appFnCleanup___redArg(v___x_37_);
v___x_41_ = l_Lean_Expr_isApp(v___x_40_);
if (v___x_41_ == 0)
{
lean_dec_ref(v___x_40_);
lean_dec_ref(v_arg_39_);
return v___x_36_;
}
else
{
lean_object* v_arg_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v_arg_42_ = lean_ctor_get(v___x_40_, 1);
lean_inc_ref(v_arg_42_);
v___x_43_ = l_Lean_Expr_appFnCleanup___redArg(v___x_40_);
v___x_44_ = l_Lean_Expr_isApp(v___x_43_);
if (v___x_44_ == 0)
{
lean_dec_ref(v___x_43_);
lean_dec_ref(v_arg_42_);
lean_dec_ref(v_arg_39_);
return v___x_36_;
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_45_ = l_Lean_Expr_appFnCleanup___redArg(v___x_43_);
v___x_46_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__2));
v___x_47_ = l_Lean_Expr_isConstOf(v___x_45_, v___x_46_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; uint8_t v___x_49_; 
lean_dec_ref(v_arg_39_);
v___x_48_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__5));
v___x_49_ = l_Lean_Expr_isConstOf(v___x_45_, v___x_48_);
lean_dec_ref(v___x_45_);
if (v___x_49_ == 0)
{
lean_dec_ref(v_arg_42_);
return v___x_36_;
}
else
{
uint8_t v___x_50_; 
v___x_50_ = l_Lean_Expr_isRawNatLit(v_arg_42_);
lean_dec_ref(v_arg_42_);
return v___x_50_;
}
}
else
{
lean_object* v___x_51_; uint8_t v___x_52_; 
lean_dec_ref(v___x_45_);
lean_dec_ref(v_arg_42_);
v___x_51_ = l_Lean_Expr_cleanupAnnotations(v_arg_39_);
v___x_52_ = l_Lean_Expr_isApp(v___x_51_);
if (v___x_52_ == 0)
{
lean_dec_ref(v___x_51_);
return v___x_36_;
}
else
{
lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_53_ = l_Lean_Expr_appFnCleanup___redArg(v___x_51_);
v___x_54_ = l_Lean_Expr_isApp(v___x_53_);
if (v___x_54_ == 0)
{
lean_dec_ref(v___x_53_);
return v___x_36_;
}
else
{
lean_object* v_arg_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v_arg_55_ = lean_ctor_get(v___x_53_, 1);
lean_inc_ref(v_arg_55_);
v___x_56_ = l_Lean_Expr_appFnCleanup___redArg(v___x_53_);
v___x_57_ = l_Lean_Expr_isApp(v___x_56_);
if (v___x_57_ == 0)
{
lean_dec_ref(v___x_56_);
lean_dec_ref(v_arg_55_);
return v___x_36_;
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_58_ = l_Lean_Expr_appFnCleanup___redArg(v___x_56_);
v___x_59_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__5));
v___x_60_ = l_Lean_Expr_isConstOf(v___x_58_, v___x_59_);
lean_dec_ref(v___x_58_);
if (v___x_60_ == 0)
{
lean_dec_ref(v_arg_55_);
return v___x_36_;
}
else
{
uint8_t v___x_61_; 
v___x_61_ = l_Lean_Expr_isRawNatLit(v_arg_55_);
lean_dec_ref(v_arg_55_);
return v___x_61_;
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
lean_dec_ref(v_e_35_);
return v___x_36_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_35_ = stack[0].m_obj;
uint8_t v_res_62_;
v_res_62_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral(v_e_35_);
stack->m_num = v_res_62_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___boxed(lean_object* v_e_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral(v_e_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = l_Lean_Nat_mkType;
v___x_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f(lean_object* v_e_87_){
_start:
{
lean_object* v_00_u03b1_89_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = l_Lean_Expr_cleanupAnnotations(v_e_87_);
v___x_94_ = l_Lean_Expr_isApp(v___x_93_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; 
lean_dec_ref(v___x_93_);
v___x_95_ = lean_box(0);
return v___x_95_;
}
else
{
lean_object* v_arg_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_arg_96_ = lean_ctor_get(v___x_93_, 1);
lean_inc_ref(v_arg_96_);
v___x_97_ = l_Lean_Expr_appFnCleanup___redArg(v___x_93_);
v___x_98_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1));
v___x_99_ = l_Lean_Expr_isConstOf(v___x_97_, v___x_98_);
if (v___x_99_ == 0)
{
uint8_t v___x_100_; 
v___x_100_ = l_Lean_Expr_isApp(v___x_97_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
lean_dec_ref(v___x_97_);
lean_dec_ref(v_arg_96_);
v___x_101_ = lean_box(0);
return v___x_101_;
}
else
{
lean_object* v_arg_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_arg_102_ = lean_ctor_get(v___x_97_, 1);
lean_inc_ref(v_arg_102_);
v___x_103_ = l_Lean_Expr_appFnCleanup___redArg(v___x_97_);
v___x_104_ = l_Lean_Expr_isApp(v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; 
lean_dec_ref(v___x_103_);
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_arg_96_);
v___x_105_ = lean_box(0);
return v___x_105_;
}
else
{
lean_object* v_arg_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v_arg_106_ = lean_ctor_get(v___x_103_, 1);
lean_inc_ref(v_arg_106_);
v___x_107_ = l_Lean_Expr_appFnCleanup___redArg(v___x_103_);
v___x_108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__2));
v___x_109_ = l_Lean_Expr_isConstOf(v___x_107_, v___x_108_);
if (v___x_109_ == 0)
{
uint8_t v___x_110_; 
lean_dec_ref(v_arg_106_);
v___x_110_ = l_Lean_Expr_isApp(v___x_107_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
lean_dec_ref(v___x_107_);
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_arg_96_);
v___x_111_ = lean_box(0);
return v___x_111_;
}
else
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = l_Lean_Expr_appFnCleanup___redArg(v___x_107_);
v___x_113_ = l_Lean_Expr_isApp(v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; 
lean_dec_ref(v___x_112_);
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_arg_96_);
v___x_114_ = lean_box(0);
return v___x_114_;
}
else
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = l_Lean_Expr_appFnCleanup___redArg(v___x_112_);
v___x_116_ = l_Lean_Expr_isApp(v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
lean_dec_ref(v___x_115_);
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_arg_96_);
v___x_117_ = lean_box(0);
return v___x_117_;
}
else
{
lean_object* v_arg_118_; uint8_t v___y_120_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_arg_118_ = lean_ctor_get(v___x_115_, 1);
lean_inc_ref(v_arg_118_);
v___x_125_ = l_Lean_Expr_appFnCleanup___redArg(v___x_115_);
v___x_126_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4));
v___x_127_ = l_Lean_Expr_isConstOf(v___x_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7));
v___x_129_ = l_Lean_Expr_isConstOf(v___x_125_, v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; uint8_t v___x_131_; 
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_arg_96_);
v___x_130_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10));
v___x_131_ = l_Lean_Expr_isConstOf(v___x_125_, v___x_130_);
lean_dec_ref(v___x_125_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
lean_dec_ref(v_arg_118_);
v___x_132_ = lean_box(0);
return v___x_132_;
}
else
{
uint8_t v___x_133_; 
lean_inc_ref(v_arg_118_);
v___x_133_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_118_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; 
lean_dec_ref(v_arg_118_);
v___x_134_ = lean_box(0);
return v___x_134_;
}
else
{
lean_object* v___x_135_; 
v___x_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_135_, 0, v_arg_118_);
return v___x_135_;
}
}
}
else
{
uint8_t v___x_136_; 
lean_dec_ref(v___x_125_);
v___x_136_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral(v_arg_102_);
if (v___x_136_ == 0)
{
uint8_t v___x_137_; 
v___x_137_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral(v_arg_96_);
v___y_120_ = v___x_137_;
goto v___jp_119_;
}
else
{
lean_dec_ref(v_arg_96_);
v___y_120_ = v___x_136_;
goto v___jp_119_;
}
}
}
else
{
lean_dec_ref(v___x_125_);
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_arg_96_);
v_00_u03b1_89_ = v_arg_118_;
goto v___jp_88_;
}
v___jp_119_:
{
if (v___y_120_ == 0)
{
lean_object* v___x_121_; 
lean_dec_ref(v_arg_118_);
v___x_121_ = lean_box(0);
return v___x_121_;
}
else
{
uint8_t v___x_122_; 
lean_inc_ref(v_arg_118_);
v___x_122_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_118_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
lean_dec_ref(v_arg_118_);
v___x_123_ = lean_box(0);
return v___x_123_;
}
else
{
lean_object* v___x_124_; 
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v_arg_118_);
return v___x_124_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_107_);
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_arg_96_);
v_00_u03b1_89_ = v_arg_106_;
goto v___jp_88_;
}
}
}
}
else
{
lean_object* v___x_138_; 
lean_dec_ref(v___x_97_);
lean_dec_ref(v_arg_96_);
v___x_138_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11, &l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11_once, _init_l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11);
return v___x_138_;
}
}
v___jp_88_:
{
uint8_t v___x_90_; 
lean_inc_ref(v_00_u03b1_89_);
v___x_90_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType(v_00_u03b1_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; 
lean_dec_ref(v_00_u03b1_89_);
v___x_91_ = lean_box(0);
return v___x_91_;
}
else
{
lean_object* v___x_92_; 
v___x_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_92_, 0, v_00_u03b1_89_);
return v___x_92_;
}
}
}
}
uint8_t l_Lean_Meta_Simp_Arith_isLinearTerm(lean_object* v_e_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_Meta_Simp_Arith_isLinearTerm_x3f(v_e_139_);
if (lean_obj_tag(v___x_140_) == 0)
{
uint8_t v___x_141_; 
v___x_141_ = 0;
return v___x_141_;
}
else
{
uint8_t v___x_142_; 
lean_dec_ref_known(v___x_140_, 1);
v___x_142_ = 1;
return v___x_142_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_isLinearTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_139_ = stack[0].m_obj;
uint8_t v_res_143_;
v_res_143_ = l_Lean_Meta_Simp_Arith_isLinearTerm(v_e_139_);
stack->m_num = v_res_143_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm___boxed(lean_object* v_e_144_){
_start:
{
uint8_t v_res_145_; lean_object* v_r_146_; 
v_res_145_ = l_Lean_Meta_Simp_Arith_isLinearTerm(v_e_144_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
uint8_t l_Lean_Meta_Simp_Arith_isLinearPosCnstr(lean_object* v_e_173_){
_start:
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = l_Lean_Expr_cleanupAnnotations(v_e_173_);
v___x_175_ = l_Lean_Expr_isApp(v___x_174_);
if (v___x_175_ == 0)
{
lean_dec_ref(v___x_174_);
return v___x_175_;
}
else
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = l_Lean_Expr_appFnCleanup___redArg(v___x_174_);
v___x_177_ = l_Lean_Expr_isApp(v___x_176_);
if (v___x_177_ == 0)
{
lean_dec_ref(v___x_176_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = l_Lean_Expr_appFnCleanup___redArg(v___x_176_);
v___x_179_ = l_Lean_Expr_isApp(v___x_178_);
if (v___x_179_ == 0)
{
lean_dec_ref(v___x_178_);
return v___x_179_;
}
else
{
lean_object* v_arg_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_arg_180_ = lean_ctor_get(v___x_178_, 1);
lean_inc_ref(v_arg_180_);
v___x_181_ = l_Lean_Expr_appFnCleanup___redArg(v___x_178_);
v___x_182_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__1));
v___x_183_ = l_Lean_Expr_isConstOf(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__3));
v___x_185_ = l_Lean_Expr_isConstOf(v___x_181_, v___x_184_);
if (v___x_185_ == 0)
{
uint8_t v___x_186_; 
lean_dec_ref(v_arg_180_);
v___x_186_ = l_Lean_Expr_isApp(v___x_181_);
if (v___x_186_ == 0)
{
lean_dec_ref(v___x_181_);
return v___x_186_;
}
else
{
lean_object* v_arg_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_arg_187_ = lean_ctor_get(v___x_181_, 1);
lean_inc_ref(v_arg_187_);
v___x_188_ = l_Lean_Expr_appFnCleanup___redArg(v___x_181_);
v___x_189_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__6));
v___x_190_ = l_Lean_Expr_isConstOf(v___x_188_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__9));
v___x_192_ = l_Lean_Expr_isConstOf(v___x_188_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__12));
v___x_194_ = l_Lean_Expr_isConstOf(v___x_188_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__15));
v___x_196_ = l_Lean_Expr_isConstOf(v___x_188_, v___x_195_);
lean_dec_ref(v___x_188_);
if (v___x_196_ == 0)
{
lean_dec_ref(v_arg_187_);
return v___x_196_;
}
else
{
uint8_t v___x_197_; 
v___x_197_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_187_);
return v___x_197_;
}
}
else
{
uint8_t v___x_198_; 
lean_dec_ref(v___x_188_);
v___x_198_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_187_);
return v___x_198_;
}
}
else
{
uint8_t v___x_199_; 
lean_dec_ref(v___x_188_);
v___x_199_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_187_);
return v___x_199_;
}
}
else
{
uint8_t v___x_200_; 
lean_dec_ref(v___x_188_);
v___x_200_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_187_);
return v___x_200_;
}
}
}
else
{
uint8_t v___x_201_; 
lean_dec_ref(v___x_181_);
v___x_201_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_180_);
return v___x_201_;
}
}
else
{
uint8_t v___x_202_; 
lean_dec_ref(v___x_181_);
v___x_202_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_180_);
return v___x_202_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_isLinearPosCnstr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_173_ = stack[0].m_obj;
uint8_t v_res_203_;
v_res_203_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_173_);
stack->m_num = v_res_203_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___boxed(lean_object* v_e_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
uint8_t l_Lean_Meta_Simp_Arith_isLinearCnstr(lean_object* v_e_210_){
_start:
{
lean_object* v___x_211_; uint8_t v___x_212_; 
lean_inc_ref(v_e_210_);
v___x_211_ = l_Lean_Expr_cleanupAnnotations(v_e_210_);
v___x_212_ = l_Lean_Expr_isApp(v___x_211_);
if (v___x_212_ == 0)
{
uint8_t v___x_213_; 
lean_dec_ref(v___x_211_);
v___x_213_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_210_);
return v___x_213_;
}
else
{
lean_object* v_arg_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_arg_214_ = lean_ctor_get(v___x_211_, 1);
lean_inc_ref(v_arg_214_);
v___x_215_ = l_Lean_Expr_appFnCleanup___redArg(v___x_211_);
v___x_216_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__1));
v___x_217_ = l_Lean_Expr_isConstOf(v___x_215_, v___x_216_);
lean_dec_ref(v___x_215_);
if (v___x_217_ == 0)
{
uint8_t v___x_218_; 
lean_dec_ref(v_arg_214_);
v___x_218_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_210_);
return v___x_218_;
}
else
{
uint8_t v___x_219_; 
lean_dec_ref(v_e_210_);
v___x_219_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_arg_214_);
return v___x_219_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_isLinearCnstr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_210_ = stack[0].m_obj;
uint8_t v_res_220_;
v_res_220_ = l_Lean_Meta_Simp_Arith_isLinearCnstr(v_e_210_);
stack->m_num = v_res_220_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearCnstr___boxed(lean_object* v_e_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Lean_Meta_Simp_Arith_isLinearCnstr(v_e_221_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
uint8_t l_Lean_Meta_Simp_Arith_isDvdCnstr(lean_object* v_e_229_){
_start:
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = l_Lean_Expr_cleanupAnnotations(v_e_229_);
v___x_231_ = l_Lean_Expr_isApp(v___x_230_);
if (v___x_231_ == 0)
{
lean_dec_ref(v___x_230_);
return v___x_231_;
}
else
{
lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = l_Lean_Expr_appFnCleanup___redArg(v___x_230_);
v___x_233_ = l_Lean_Expr_isApp(v___x_232_);
if (v___x_233_ == 0)
{
lean_dec_ref(v___x_232_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_234_ = l_Lean_Expr_appFnCleanup___redArg(v___x_232_);
v___x_235_ = l_Lean_Expr_isApp(v___x_234_);
if (v___x_235_ == 0)
{
lean_dec_ref(v___x_234_);
return v___x_235_;
}
else
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = l_Lean_Expr_appFnCleanup___redArg(v___x_234_);
v___x_237_ = l_Lean_Expr_isApp(v___x_236_);
if (v___x_237_ == 0)
{
lean_dec_ref(v___x_236_);
return v___x_237_;
}
else
{
lean_object* v_arg_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_arg_238_ = lean_ctor_get(v___x_236_, 1);
lean_inc_ref(v_arg_238_);
v___x_239_ = l_Lean_Expr_appFnCleanup___redArg(v___x_236_);
v___x_240_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__2));
v___x_241_ = l_Lean_Expr_isConstOf(v___x_239_, v___x_240_);
lean_dec_ref(v___x_239_);
if (v___x_241_ == 0)
{
lean_dec_ref(v_arg_238_);
return v___x_241_;
}
else
{
uint8_t v___x_242_; 
v___x_242_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_238_);
return v___x_242_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_isDvdCnstr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_229_ = stack[0].m_obj;
uint8_t v_res_243_;
v_res_243_ = l_Lean_Meta_Simp_Arith_isDvdCnstr(v_e_229_);
stack->m_num = v_res_243_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isDvdCnstr___boxed(lean_object* v_e_244_){
_start:
{
uint8_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_Lean_Meta_Simp_Arith_isDvdCnstr(v_e_244_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
}
#ifdef __cplusplus
}
#endif
