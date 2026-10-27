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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___boxed(lean_object*);
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
lean_dec_ref(v_type_13_);
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
lean_dec_ref(v_type_20_);
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
return v___x_34_;
}
else
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = l_Lean_Expr_appFnCleanup___redArg(v___x_35_);
v___x_38_ = l_Lean_Expr_isApp(v___x_37_);
if (v___x_38_ == 0)
{
lean_dec_ref(v___x_37_);
lean_dec_ref(v___x_35_);
return v___x_34_;
}
else
{
lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_39_ = l_Lean_Expr_appFnCleanup___redArg(v___x_37_);
v___x_40_ = l_Lean_Expr_isApp(v___x_39_);
if (v___x_40_ == 0)
{
lean_dec_ref(v___x_39_);
lean_dec_ref(v___x_37_);
lean_dec_ref(v___x_35_);
return v___x_34_;
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_41_ = l_Lean_Expr_appFnCleanup___redArg(v___x_39_);
lean_dec_ref(v___x_39_);
v___x_42_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__2));
v___x_43_ = l_Lean_Expr_isConstOf(v___x_41_, v___x_42_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; uint8_t v___x_45_; 
lean_dec_ref(v___x_35_);
v___x_44_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__5));
v___x_45_ = l_Lean_Expr_isConstOf(v___x_41_, v___x_44_);
lean_dec_ref(v___x_41_);
if (v___x_45_ == 0)
{
lean_dec_ref(v___x_37_);
return v___x_34_;
}
else
{
lean_object* v_arg_46_; uint8_t v___x_47_; 
v_arg_46_ = lean_ctor_get(v___x_37_, 1);
lean_inc_ref(v_arg_46_);
lean_dec_ref(v___x_37_);
v___x_47_ = l_Lean_Expr_isRawNatLit(v_arg_46_);
lean_dec_ref(v_arg_46_);
return v___x_47_;
}
}
else
{
lean_object* v_arg_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
lean_dec_ref(v___x_41_);
lean_dec_ref(v___x_37_);
v_arg_48_ = lean_ctor_get(v___x_35_, 1);
lean_inc_ref(v_arg_48_);
lean_dec_ref(v___x_35_);
v___x_49_ = l_Lean_Expr_cleanupAnnotations(v_arg_48_);
lean_dec_ref(v_arg_48_);
v___x_50_ = l_Lean_Expr_isApp(v___x_49_);
if (v___x_50_ == 0)
{
lean_dec_ref(v___x_49_);
return v___x_34_;
}
else
{
lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_51_ = l_Lean_Expr_appFnCleanup___redArg(v___x_49_);
lean_dec_ref(v___x_49_);
v___x_52_ = l_Lean_Expr_isApp(v___x_51_);
if (v___x_52_ == 0)
{
lean_dec_ref(v___x_51_);
return v___x_34_;
}
else
{
lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_53_ = l_Lean_Expr_appFnCleanup___redArg(v___x_51_);
v___x_54_ = l_Lean_Expr_isApp(v___x_53_);
if (v___x_54_ == 0)
{
lean_dec_ref(v___x_53_);
lean_dec_ref(v___x_51_);
return v___x_34_;
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_55_ = l_Lean_Expr_appFnCleanup___redArg(v___x_53_);
lean_dec_ref(v___x_53_);
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__5));
v___x_57_ = l_Lean_Expr_isConstOf(v___x_55_, v___x_56_);
lean_dec_ref(v___x_55_);
if (v___x_57_ == 0)
{
lean_dec_ref(v___x_51_);
return v___x_34_;
}
else
{
lean_object* v_arg_58_; uint8_t v___x_59_; 
v_arg_58_ = lean_ctor_get(v___x_51_, 1);
lean_inc_ref(v_arg_58_);
lean_dec_ref(v___x_51_);
v___x_59_ = l_Lean_Expr_isRawNatLit(v_arg_58_);
lean_dec_ref(v_arg_58_);
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
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___boxed(lean_object* v_e_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral(v_e_60_);
lean_dec_ref(v_e_60_);
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
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_93_ = l_Lean_Expr_appFnCleanup___redArg(v___x_90_);
v___x_94_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1));
v___x_95_ = l_Lean_Expr_isConstOf(v___x_93_, v___x_94_);
if (v___x_95_ == 0)
{
uint8_t v___x_96_; 
v___x_96_ = l_Lean_Expr_isApp(v___x_93_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec_ref(v___x_93_);
lean_dec_ref(v___x_90_);
v___x_97_ = lean_box(0);
return v___x_97_;
}
else
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = l_Lean_Expr_appFnCleanup___redArg(v___x_93_);
v___x_99_ = l_Lean_Expr_isApp(v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec_ref(v___x_98_);
lean_dec_ref(v___x_93_);
lean_dec_ref(v___x_90_);
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_101_ = l_Lean_Expr_appFnCleanup___redArg(v___x_98_);
v___x_102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral___closed__2));
v___x_103_ = l_Lean_Expr_isConstOf(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
uint8_t v___x_104_; 
lean_dec_ref(v___x_98_);
v___x_104_ = l_Lean_Expr_isApp(v___x_101_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; 
lean_dec_ref(v___x_101_);
lean_dec_ref(v___x_93_);
lean_dec_ref(v___x_90_);
v___x_105_ = lean_box(0);
return v___x_105_;
}
else
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = l_Lean_Expr_appFnCleanup___redArg(v___x_101_);
lean_dec_ref(v___x_101_);
v___x_107_ = l_Lean_Expr_isApp(v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
lean_dec_ref(v___x_106_);
lean_dec_ref(v___x_93_);
lean_dec_ref(v___x_90_);
v___x_108_ = lean_box(0);
return v___x_108_;
}
else
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = l_Lean_Expr_appFnCleanup___redArg(v___x_106_);
lean_dec_ref(v___x_106_);
v___x_110_ = l_Lean_Expr_isApp(v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
lean_dec_ref(v___x_109_);
lean_dec_ref(v___x_93_);
lean_dec_ref(v___x_90_);
v___x_111_ = lean_box(0);
return v___x_111_;
}
else
{
lean_object* v_arg_112_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v_arg_112_ = lean_ctor_get(v___x_109_, 1);
lean_inc_ref(v_arg_112_);
v___x_117_ = l_Lean_Expr_appFnCleanup___redArg(v___x_109_);
lean_dec_ref(v___x_109_);
v___x_118_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4));
v___x_119_ = l_Lean_Expr_isConstOf(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7));
v___x_121_ = l_Lean_Expr_isConstOf(v___x_117_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; uint8_t v___x_123_; 
lean_dec_ref(v___x_93_);
lean_dec_ref(v___x_90_);
v___x_122_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10));
v___x_123_ = l_Lean_Expr_isConstOf(v___x_117_, v___x_122_);
lean_dec_ref(v___x_117_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; 
lean_dec_ref(v_arg_112_);
v___x_124_ = lean_box(0);
return v___x_124_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_112_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
lean_dec_ref(v_arg_112_);
v___x_126_ = lean_box(0);
return v___x_126_;
}
else
{
lean_object* v___x_127_; 
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v_arg_112_);
return v___x_127_;
}
}
}
else
{
lean_object* v_arg_128_; uint8_t v___x_129_; 
lean_dec_ref(v___x_117_);
v_arg_128_ = lean_ctor_get(v___x_93_, 1);
lean_inc_ref(v_arg_128_);
lean_dec_ref(v___x_93_);
v___x_129_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral(v_arg_128_);
lean_dec_ref(v_arg_128_);
if (v___x_129_ == 0)
{
lean_object* v_arg_130_; uint8_t v___x_131_; 
v_arg_130_ = lean_ctor_get(v___x_90_, 1);
lean_inc_ref(v_arg_130_);
lean_dec_ref(v___x_90_);
v___x_131_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isNumeral(v_arg_130_);
lean_dec_ref(v_arg_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
lean_dec_ref(v_arg_112_);
v___x_132_ = lean_box(0);
return v___x_132_;
}
else
{
goto v___jp_113_;
}
}
else
{
lean_dec_ref(v___x_90_);
goto v___jp_113_;
}
}
}
else
{
lean_dec_ref(v___x_117_);
lean_dec_ref(v___x_93_);
lean_dec_ref(v___x_90_);
v_00_u03b1_86_ = v_arg_112_;
goto v___jp_85_;
}
v___jp_113_:
{
uint8_t v___x_114_; 
v___x_114_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_112_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
lean_dec_ref(v_arg_112_);
v___x_115_ = lean_box(0);
return v___x_115_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v_arg_112_);
return v___x_116_;
}
}
}
}
}
}
else
{
lean_object* v_arg_133_; 
lean_dec_ref(v___x_101_);
lean_dec_ref(v___x_93_);
lean_dec_ref(v___x_90_);
v_arg_133_ = lean_ctor_get(v___x_98_, 1);
lean_inc_ref(v_arg_133_);
lean_dec_ref(v___x_98_);
v_00_u03b1_86_ = v_arg_133_;
goto v___jp_85_;
}
}
}
}
else
{
lean_object* v___x_134_; 
lean_dec_ref(v___x_93_);
lean_dec_ref(v___x_90_);
v___x_134_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11, &l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11_once, _init_l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11);
return v___x_134_;
}
}
v___jp_85_:
{
uint8_t v___x_87_; 
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___boxed(lean_object* v_e_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Meta_Simp_Arith_isLinearTerm_x3f(v_e_135_);
lean_dec_ref(v_e_135_);
return v_res_136_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isLinearTerm(lean_object* v_e_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Simp_Arith_isLinearTerm_x3f(v_e_137_);
if (lean_obj_tag(v___x_138_) == 0)
{
uint8_t v___x_139_; 
v___x_139_ = 0;
return v___x_139_;
}
else
{
uint8_t v___x_140_; 
lean_dec_ref_known(v___x_138_, 1);
v___x_140_ = 1;
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm___boxed(lean_object* v_e_141_){
_start:
{
uint8_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = l_Lean_Meta_Simp_Arith_isLinearTerm(v_e_141_);
lean_dec_ref(v_e_141_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isLinearPosCnstr(lean_object* v_e_170_){
_start:
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = l_Lean_Expr_cleanupAnnotations(v_e_170_);
v___x_172_ = l_Lean_Expr_isApp(v___x_171_);
if (v___x_172_ == 0)
{
lean_dec_ref(v___x_171_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = l_Lean_Expr_appFnCleanup___redArg(v___x_171_);
lean_dec_ref(v___x_171_);
v___x_174_ = l_Lean_Expr_isApp(v___x_173_);
if (v___x_174_ == 0)
{
lean_dec_ref(v___x_173_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = l_Lean_Expr_appFnCleanup___redArg(v___x_173_);
lean_dec_ref(v___x_173_);
v___x_176_ = l_Lean_Expr_isApp(v___x_175_);
if (v___x_176_ == 0)
{
lean_dec_ref(v___x_175_);
return v___x_176_;
}
else
{
lean_object* v_arg_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_arg_177_ = lean_ctor_get(v___x_175_, 1);
lean_inc_ref(v_arg_177_);
v___x_178_ = l_Lean_Expr_appFnCleanup___redArg(v___x_175_);
lean_dec_ref(v___x_175_);
v___x_179_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__1));
v___x_180_ = l_Lean_Expr_isConstOf(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__3));
v___x_182_ = l_Lean_Expr_isConstOf(v___x_178_, v___x_181_);
if (v___x_182_ == 0)
{
uint8_t v___x_183_; 
lean_dec_ref(v_arg_177_);
v___x_183_ = l_Lean_Expr_isApp(v___x_178_);
if (v___x_183_ == 0)
{
lean_dec_ref(v___x_178_);
return v___x_183_;
}
else
{
lean_object* v_arg_184_; lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_arg_184_ = lean_ctor_get(v___x_178_, 1);
lean_inc_ref(v_arg_184_);
v___x_185_ = l_Lean_Expr_appFnCleanup___redArg(v___x_178_);
lean_dec_ref(v___x_178_);
v___x_186_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__6));
v___x_187_ = l_Lean_Expr_isConstOf(v___x_185_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__9));
v___x_189_ = l_Lean_Expr_isConstOf(v___x_185_, v___x_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_190_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__12));
v___x_191_ = l_Lean_Expr_isConstOf(v___x_185_, v___x_190_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__15));
v___x_193_ = l_Lean_Expr_isConstOf(v___x_185_, v___x_192_);
lean_dec_ref(v___x_185_);
if (v___x_193_ == 0)
{
lean_dec_ref(v_arg_184_);
return v___x_193_;
}
else
{
uint8_t v___x_194_; 
v___x_194_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_184_);
lean_dec_ref(v_arg_184_);
return v___x_194_;
}
}
else
{
uint8_t v___x_195_; 
lean_dec_ref(v___x_185_);
v___x_195_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_184_);
lean_dec_ref(v_arg_184_);
return v___x_195_;
}
}
else
{
uint8_t v___x_196_; 
lean_dec_ref(v___x_185_);
v___x_196_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_184_);
lean_dec_ref(v_arg_184_);
return v___x_196_;
}
}
else
{
uint8_t v___x_197_; 
lean_dec_ref(v___x_185_);
v___x_197_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_184_);
lean_dec_ref(v_arg_184_);
return v___x_197_;
}
}
}
else
{
uint8_t v___x_198_; 
lean_dec_ref(v___x_178_);
v___x_198_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_177_);
lean_dec_ref(v_arg_177_);
return v___x_198_;
}
}
else
{
uint8_t v___x_199_; 
lean_dec_ref(v___x_178_);
v___x_199_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_177_);
lean_dec_ref(v_arg_177_);
return v___x_199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___boxed(lean_object* v_e_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_200_);
lean_dec_ref(v_e_200_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isLinearCnstr(lean_object* v_e_206_){
_start:
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = l_Lean_Expr_cleanupAnnotations(v_e_206_);
v___x_208_ = l_Lean_Expr_isApp(v___x_207_);
if (v___x_208_ == 0)
{
uint8_t v___x_209_; 
lean_dec_ref(v___x_207_);
v___x_209_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_206_);
return v___x_209_;
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_210_ = l_Lean_Expr_appFnCleanup___redArg(v___x_207_);
v___x_211_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__1));
v___x_212_ = l_Lean_Expr_isConstOf(v___x_210_, v___x_211_);
lean_dec_ref(v___x_210_);
if (v___x_212_ == 0)
{
uint8_t v___x_213_; 
lean_dec_ref(v___x_207_);
v___x_213_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_206_);
return v___x_213_;
}
else
{
lean_object* v_arg_214_; uint8_t v___x_215_; 
v_arg_214_ = lean_ctor_get(v___x_207_, 1);
lean_inc_ref(v_arg_214_);
lean_dec_ref(v___x_207_);
v___x_215_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_arg_214_);
lean_dec_ref(v_arg_214_);
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearCnstr___boxed(lean_object* v_e_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l_Lean_Meta_Simp_Arith_isLinearCnstr(v_e_216_);
lean_dec_ref(v_e_216_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isDvdCnstr(lean_object* v_e_224_){
_start:
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = l_Lean_Expr_cleanupAnnotations(v_e_224_);
v___x_226_ = l_Lean_Expr_isApp(v___x_225_);
if (v___x_226_ == 0)
{
lean_dec_ref(v___x_225_);
return v___x_226_;
}
else
{
lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_227_ = l_Lean_Expr_appFnCleanup___redArg(v___x_225_);
lean_dec_ref(v___x_225_);
v___x_228_ = l_Lean_Expr_isApp(v___x_227_);
if (v___x_228_ == 0)
{
lean_dec_ref(v___x_227_);
return v___x_228_;
}
else
{
lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_229_ = l_Lean_Expr_appFnCleanup___redArg(v___x_227_);
lean_dec_ref(v___x_227_);
v___x_230_ = l_Lean_Expr_isApp(v___x_229_);
if (v___x_230_ == 0)
{
lean_dec_ref(v___x_229_);
return v___x_230_;
}
else
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = l_Lean_Expr_appFnCleanup___redArg(v___x_229_);
lean_dec_ref(v___x_229_);
v___x_232_ = l_Lean_Expr_isApp(v___x_231_);
if (v___x_232_ == 0)
{
lean_dec_ref(v___x_231_);
return v___x_232_;
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_233_ = l_Lean_Expr_appFnCleanup___redArg(v___x_231_);
v___x_234_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__2));
v___x_235_ = l_Lean_Expr_isConstOf(v___x_233_, v___x_234_);
lean_dec_ref(v___x_233_);
if (v___x_235_ == 0)
{
lean_dec_ref(v___x_231_);
return v___x_235_;
}
else
{
lean_object* v_arg_236_; uint8_t v___x_237_; 
v_arg_236_ = lean_ctor_get(v___x_231_, 1);
lean_inc_ref(v_arg_236_);
lean_dec_ref(v___x_231_);
v___x_237_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_236_);
lean_dec_ref(v_arg_236_);
return v___x_237_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isDvdCnstr___boxed(lean_object* v_e_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Lean_Meta_Simp_Arith_isDvdCnstr(v_e_238_);
lean_dec_ref(v_e_238_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
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
