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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(lean_object* v_type_7_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___boxed(lean_object* v_type_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_type_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType(lean_object* v_type_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_17_ = l_Lean_Expr_cleanupAnnotations(v_type_16_);
v___x_18_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__1));
v___x_19_ = l_Lean_Expr_isConstOf(v___x_17_, v___x_18_);
lean_dec_ref(v___x_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType___boxed(lean_object* v_type_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType(v_type_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral(lean_object* v_e_33_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = l_Lean_Expr_isRawNatLit(v_e_33_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_35_ = l_Lean_Expr_cleanupAnnotations(v_e_33_);
v___x_36_ = l_Lean_Expr_isApp(v___x_35_);
if (v___x_36_ == 0)
{
lean_dec_ref(v___x_35_);
return v___x_36_;
}
else
{
lean_object* v_arg_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v_arg_37_ = lean_ctor_get(v___x_35_, 1);
lean_inc_ref(v_arg_37_);
v___x_38_ = l_Lean_Expr_appFnCleanup___redArg(v___x_35_);
v___x_39_ = l_Lean_Expr_isApp(v___x_38_);
if (v___x_39_ == 0)
{
lean_dec_ref(v___x_38_);
lean_dec_ref(v_arg_37_);
return v___x_39_;
}
else
{
lean_object* v_arg_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v_arg_40_ = lean_ctor_get(v___x_38_, 1);
lean_inc_ref(v_arg_40_);
v___x_41_ = l_Lean_Expr_appFnCleanup___redArg(v___x_38_);
v___x_42_ = l_Lean_Expr_isApp(v___x_41_);
if (v___x_42_ == 0)
{
lean_dec_ref(v___x_41_);
lean_dec_ref(v_arg_40_);
lean_dec_ref(v_arg_37_);
return v___x_42_;
}
else
{
lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_43_ = l_Lean_Expr_appFnCleanup___redArg(v___x_41_);
v___x_44_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__2));
v___x_45_ = l_Lean_Expr_isConstOf(v___x_43_, v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; uint8_t v___x_47_; 
lean_dec_ref(v_arg_37_);
v___x_46_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__5));
v___x_47_ = l_Lean_Expr_isConstOf(v___x_43_, v___x_46_);
lean_dec_ref(v___x_43_);
if (v___x_47_ == 0)
{
lean_dec_ref(v_arg_40_);
return v___x_47_;
}
else
{
uint8_t v___x_48_; 
v___x_48_ = l_Lean_Expr_isRawNatLit(v_arg_40_);
lean_dec_ref(v_arg_40_);
return v___x_48_;
}
}
else
{
lean_object* v___x_49_; uint8_t v___x_50_; 
lean_dec_ref(v___x_43_);
lean_dec_ref(v_arg_40_);
v___x_49_ = l_Lean_Expr_cleanupAnnotations(v_arg_37_);
v___x_50_ = l_Lean_Expr_isApp(v___x_49_);
if (v___x_50_ == 0)
{
lean_dec_ref(v___x_49_);
return v___x_50_;
}
else
{
lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_51_ = l_Lean_Expr_appFnCleanup___redArg(v___x_49_);
v___x_52_ = l_Lean_Expr_isApp(v___x_51_);
if (v___x_52_ == 0)
{
lean_dec_ref(v___x_51_);
return v___x_52_;
}
else
{
lean_object* v_arg_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v_arg_53_ = lean_ctor_get(v___x_51_, 1);
lean_inc_ref(v_arg_53_);
v___x_54_ = l_Lean_Expr_appFnCleanup___redArg(v___x_51_);
v___x_55_ = l_Lean_Expr_isApp(v___x_54_);
if (v___x_55_ == 0)
{
lean_dec_ref(v___x_54_);
lean_dec_ref(v_arg_53_);
return v___x_55_;
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_56_ = l_Lean_Expr_appFnCleanup___redArg(v___x_54_);
v___x_57_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__5));
v___x_58_ = l_Lean_Expr_isConstOf(v___x_56_, v___x_57_);
lean_dec_ref(v___x_56_);
if (v___x_58_ == 0)
{
lean_dec_ref(v_arg_53_);
return v___x_58_;
}
else
{
uint8_t v___x_59_; 
v___x_59_ = l_Lean_Expr_isRawNatLit(v_arg_53_);
lean_dec_ref(v_arg_53_);
return v___x_59_;
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
lean_dec_ref(v_e_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___boxed(lean_object* v_e_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral(v_e_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = l_Lean_Nat_mkType;
v___x_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f(lean_object* v_e_84_){
_start:
{
lean_object* v_00_u03b1_86_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_90_ = l_Lean_Expr_cleanupAnnotations(v_e_84_);
v___x_91_ = l_Lean_Expr_isApp(v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; 
lean_dec_ref(v___x_90_);
v___x_92_ = lean_box(0);
return v___x_92_;
}
else
{
lean_object* v_arg_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v_arg_93_ = lean_ctor_get(v___x_90_, 1);
lean_inc_ref(v_arg_93_);
v___x_94_ = l_Lean_Expr_appFnCleanup___redArg(v___x_90_);
v___x_95_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1));
v___x_96_ = l_Lean_Expr_isConstOf(v___x_94_, v___x_95_);
if (v___x_96_ == 0)
{
uint8_t v___x_97_; 
v___x_97_ = l_Lean_Expr_isApp(v___x_94_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
lean_dec_ref(v___x_94_);
lean_dec_ref(v_arg_93_);
v___x_98_ = lean_box(0);
return v___x_98_;
}
else
{
lean_object* v_arg_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v_arg_99_ = lean_ctor_get(v___x_94_, 1);
lean_inc_ref(v_arg_99_);
v___x_100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_94_);
v___x_101_ = l_Lean_Expr_isApp(v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
lean_dec_ref(v___x_100_);
lean_dec_ref(v_arg_99_);
lean_dec_ref(v_arg_93_);
v___x_102_ = lean_box(0);
return v___x_102_;
}
else
{
lean_object* v_arg_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v_arg_103_ = lean_ctor_get(v___x_100_, 1);
lean_inc_ref(v_arg_103_);
v___x_104_ = l_Lean_Expr_appFnCleanup___redArg(v___x_100_);
v___x_105_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__2));
v___x_106_ = l_Lean_Expr_isConstOf(v___x_104_, v___x_105_);
if (v___x_106_ == 0)
{
uint8_t v___x_107_; 
lean_dec_ref(v_arg_103_);
v___x_107_ = l_Lean_Expr_isApp(v___x_104_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
lean_dec_ref(v___x_104_);
lean_dec_ref(v_arg_99_);
lean_dec_ref(v_arg_93_);
v___x_108_ = lean_box(0);
return v___x_108_;
}
else
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = l_Lean_Expr_appFnCleanup___redArg(v___x_104_);
v___x_110_ = l_Lean_Expr_isApp(v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
lean_dec_ref(v___x_109_);
lean_dec_ref(v_arg_99_);
lean_dec_ref(v_arg_93_);
v___x_111_ = lean_box(0);
return v___x_111_;
}
else
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = l_Lean_Expr_appFnCleanup___redArg(v___x_109_);
v___x_113_ = l_Lean_Expr_isApp(v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; 
lean_dec_ref(v___x_112_);
lean_dec_ref(v_arg_99_);
lean_dec_ref(v_arg_93_);
v___x_114_ = lean_box(0);
return v___x_114_;
}
else
{
lean_object* v_arg_115_; uint8_t v___y_117_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_arg_115_ = lean_ctor_get(v___x_112_, 1);
lean_inc_ref(v_arg_115_);
v___x_122_ = l_Lean_Expr_appFnCleanup___redArg(v___x_112_);
v___x_123_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4));
v___x_124_ = l_Lean_Expr_isConstOf(v___x_122_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7));
v___x_126_ = l_Lean_Expr_isConstOf(v___x_122_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; uint8_t v___x_128_; 
lean_dec_ref(v_arg_99_);
lean_dec_ref(v_arg_93_);
v___x_127_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10));
v___x_128_ = l_Lean_Expr_isConstOf(v___x_122_, v___x_127_);
lean_dec_ref(v___x_122_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
lean_dec_ref(v_arg_115_);
v___x_129_ = lean_box(0);
return v___x_129_;
}
else
{
uint8_t v___x_130_; 
lean_inc_ref(v_arg_115_);
v___x_130_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_115_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
lean_dec_ref(v_arg_115_);
v___x_131_ = lean_box(0);
return v___x_131_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_132_, 0, v_arg_115_);
return v___x_132_;
}
}
}
else
{
uint8_t v___x_133_; 
lean_dec_ref(v___x_122_);
v___x_133_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral(v_arg_99_);
if (v___x_133_ == 0)
{
uint8_t v___x_134_; 
v___x_134_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral(v_arg_93_);
v___y_117_ = v___x_134_;
goto v___jp_116_;
}
else
{
lean_dec_ref(v_arg_93_);
v___y_117_ = v___x_133_;
goto v___jp_116_;
}
}
}
else
{
lean_dec_ref(v___x_122_);
lean_dec_ref(v_arg_99_);
lean_dec_ref(v_arg_93_);
v_00_u03b1_86_ = v_arg_115_;
goto v___jp_85_;
}
v___jp_116_:
{
if (v___y_117_ == 0)
{
lean_object* v___x_118_; 
lean_dec_ref(v_arg_115_);
v___x_118_ = lean_box(0);
return v___x_118_;
}
else
{
uint8_t v___x_119_; 
lean_inc_ref(v_arg_115_);
v___x_119_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_115_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
lean_dec_ref(v_arg_115_);
v___x_120_ = lean_box(0);
return v___x_120_;
}
else
{
lean_object* v___x_121_; 
v___x_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_121_, 0, v_arg_115_);
return v___x_121_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_104_);
lean_dec_ref(v_arg_99_);
lean_dec_ref(v_arg_93_);
v_00_u03b1_86_ = v_arg_103_;
goto v___jp_85_;
}
}
}
}
else
{
lean_object* v___x_135_; 
lean_dec_ref(v___x_94_);
lean_dec_ref(v_arg_93_);
v___x_135_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11, &l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11_once, _init_l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11);
return v___x_135_;
}
}
v___jp_85_:
{
uint8_t v___x_87_; 
lean_inc_ref(v_00_u03b1_86_);
v___x_87_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType(v_00_u03b1_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; 
lean_dec_ref(v_00_u03b1_86_);
v___x_88_ = lean_box(0);
return v___x_88_;
}
else
{
lean_object* v___x_89_; 
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v_00_u03b1_86_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isLinearTerm(lean_object* v_e_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Meta_Simp_Arith_isLinearTerm_x3f(v_e_136_);
if (lean_obj_tag(v___x_137_) == 0)
{
uint8_t v___x_138_; 
v___x_138_ = 0;
return v___x_138_;
}
else
{
uint8_t v___x_139_; 
lean_dec_ref_known(v___x_137_, 1);
v___x_139_ = 1;
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm___boxed(lean_object* v_e_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l_Lean_Meta_Simp_Arith_isLinearTerm(v_e_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isLinearPosCnstr(lean_object* v_e_169_){
_start:
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = l_Lean_Expr_cleanupAnnotations(v_e_169_);
v___x_171_ = l_Lean_Expr_isApp(v___x_170_);
if (v___x_171_ == 0)
{
lean_dec_ref(v___x_170_);
return v___x_171_;
}
else
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = l_Lean_Expr_appFnCleanup___redArg(v___x_170_);
v___x_173_ = l_Lean_Expr_isApp(v___x_172_);
if (v___x_173_ == 0)
{
lean_dec_ref(v___x_172_);
return v___x_173_;
}
else
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = l_Lean_Expr_appFnCleanup___redArg(v___x_172_);
v___x_175_ = l_Lean_Expr_isApp(v___x_174_);
if (v___x_175_ == 0)
{
lean_dec_ref(v___x_174_);
return v___x_175_;
}
else
{
lean_object* v_arg_176_; lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v_arg_176_ = lean_ctor_get(v___x_174_, 1);
lean_inc_ref(v_arg_176_);
v___x_177_ = l_Lean_Expr_appFnCleanup___redArg(v___x_174_);
v___x_178_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__1));
v___x_179_ = l_Lean_Expr_isConstOf(v___x_177_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__3));
v___x_181_ = l_Lean_Expr_isConstOf(v___x_177_, v___x_180_);
if (v___x_181_ == 0)
{
uint8_t v___x_182_; 
lean_dec_ref(v_arg_176_);
v___x_182_ = l_Lean_Expr_isApp(v___x_177_);
if (v___x_182_ == 0)
{
lean_dec_ref(v___x_177_);
return v___x_182_;
}
else
{
lean_object* v_arg_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_arg_183_ = lean_ctor_get(v___x_177_, 1);
lean_inc_ref(v_arg_183_);
v___x_184_ = l_Lean_Expr_appFnCleanup___redArg(v___x_177_);
v___x_185_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__6));
v___x_186_ = l_Lean_Expr_isConstOf(v___x_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__9));
v___x_188_ = l_Lean_Expr_isConstOf(v___x_184_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__12));
v___x_190_ = l_Lean_Expr_isConstOf(v___x_184_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__15));
v___x_192_ = l_Lean_Expr_isConstOf(v___x_184_, v___x_191_);
lean_dec_ref(v___x_184_);
if (v___x_192_ == 0)
{
lean_dec_ref(v_arg_183_);
return v___x_192_;
}
else
{
uint8_t v___x_193_; 
v___x_193_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_183_);
return v___x_193_;
}
}
else
{
uint8_t v___x_194_; 
lean_dec_ref(v___x_184_);
v___x_194_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_183_);
return v___x_194_;
}
}
else
{
uint8_t v___x_195_; 
lean_dec_ref(v___x_184_);
v___x_195_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_183_);
return v___x_195_;
}
}
else
{
uint8_t v___x_196_; 
lean_dec_ref(v___x_184_);
v___x_196_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_183_);
return v___x_196_;
}
}
}
else
{
uint8_t v___x_197_; 
lean_dec_ref(v___x_177_);
v___x_197_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_176_);
return v___x_197_;
}
}
else
{
uint8_t v___x_198_; 
lean_dec_ref(v___x_177_);
v___x_198_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_176_);
return v___x_198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___boxed(lean_object* v_e_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_199_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isLinearCnstr(lean_object* v_e_205_){
_start:
{
lean_object* v___x_206_; uint8_t v___x_207_; 
lean_inc_ref(v_e_205_);
v___x_206_ = l_Lean_Expr_cleanupAnnotations(v_e_205_);
v___x_207_ = l_Lean_Expr_isApp(v___x_206_);
if (v___x_207_ == 0)
{
uint8_t v___x_208_; 
lean_dec_ref(v___x_206_);
v___x_208_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_205_);
return v___x_208_;
}
else
{
lean_object* v_arg_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_arg_209_ = lean_ctor_get(v___x_206_, 1);
lean_inc_ref(v_arg_209_);
v___x_210_ = l_Lean_Expr_appFnCleanup___redArg(v___x_206_);
v___x_211_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__1));
v___x_212_ = l_Lean_Expr_isConstOf(v___x_210_, v___x_211_);
lean_dec_ref(v___x_210_);
if (v___x_212_ == 0)
{
uint8_t v___x_213_; 
lean_dec_ref(v_arg_209_);
v___x_213_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_205_);
return v___x_213_;
}
else
{
uint8_t v___x_214_; 
lean_dec_ref(v_e_205_);
v___x_214_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_arg_209_);
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearCnstr___boxed(lean_object* v_e_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l_Lean_Meta_Simp_Arith_isLinearCnstr(v_e_215_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isDvdCnstr(lean_object* v_e_223_){
_start:
{
lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_224_ = l_Lean_Expr_cleanupAnnotations(v_e_223_);
v___x_225_ = l_Lean_Expr_isApp(v___x_224_);
if (v___x_225_ == 0)
{
lean_dec_ref(v___x_224_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_226_ = l_Lean_Expr_appFnCleanup___redArg(v___x_224_);
v___x_227_ = l_Lean_Expr_isApp(v___x_226_);
if (v___x_227_ == 0)
{
lean_dec_ref(v___x_226_);
return v___x_227_;
}
else
{
lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_228_ = l_Lean_Expr_appFnCleanup___redArg(v___x_226_);
v___x_229_ = l_Lean_Expr_isApp(v___x_228_);
if (v___x_229_ == 0)
{
lean_dec_ref(v___x_228_);
return v___x_229_;
}
else
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = l_Lean_Expr_appFnCleanup___redArg(v___x_228_);
v___x_231_ = l_Lean_Expr_isApp(v___x_230_);
if (v___x_231_ == 0)
{
lean_dec_ref(v___x_230_);
return v___x_231_;
}
else
{
lean_object* v_arg_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v_arg_232_ = lean_ctor_get(v___x_230_, 1);
lean_inc_ref(v_arg_232_);
v___x_233_ = l_Lean_Expr_appFnCleanup___redArg(v___x_230_);
v___x_234_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__2));
v___x_235_ = l_Lean_Expr_isConstOf(v___x_233_, v___x_234_);
lean_dec_ref(v___x_233_);
if (v___x_235_ == 0)
{
lean_dec_ref(v_arg_232_);
return v___x_235_;
}
else
{
uint8_t v___x_236_; 
v___x_236_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_232_);
return v___x_236_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isDvdCnstr___boxed(lean_object* v_e_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l_Lean_Meta_Simp_Arith_isDvdCnstr(v_e_237_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
