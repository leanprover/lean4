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
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__5_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__8_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__14;
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__14(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = l_Lean_Nat_mkType;
v___x_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm_x3f(lean_object* v_e_49_){
_start:
{
lean_object* v_00_u03b1_51_; lean_object* v_00_u03b1_56_; lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = l_Lean_Expr_cleanupAnnotations(v_e_49_);
v___x_61_ = l_Lean_Expr_isApp(v___x_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; 
lean_dec_ref(v___x_60_);
v___x_62_ = lean_box(0);
return v___x_62_;
}
else
{
lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_63_ = l_Lean_Expr_appFnCleanup___redArg(v___x_60_);
v___x_64_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1));
v___x_65_ = l_Lean_Expr_isConstOf(v___x_63_, v___x_64_);
if (v___x_65_ == 0)
{
uint8_t v___x_66_; 
v___x_66_ = l_Lean_Expr_isApp(v___x_63_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; 
lean_dec_ref(v___x_63_);
v___x_67_ = lean_box(0);
return v___x_67_;
}
else
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = l_Lean_Expr_appFnCleanup___redArg(v___x_63_);
v___x_69_ = l_Lean_Expr_isApp(v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; 
lean_dec_ref(v___x_68_);
v___x_70_ = lean_box(0);
return v___x_70_;
}
else
{
lean_object* v_arg_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v_arg_71_ = lean_ctor_get(v___x_68_, 1);
lean_inc_ref(v_arg_71_);
v___x_72_ = l_Lean_Expr_appFnCleanup___redArg(v___x_68_);
v___x_73_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4));
v___x_74_ = l_Lean_Expr_isConstOf(v___x_72_, v___x_73_);
if (v___x_74_ == 0)
{
uint8_t v___x_75_; 
lean_dec_ref(v_arg_71_);
v___x_75_ = l_Lean_Expr_isApp(v___x_72_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; 
lean_dec_ref(v___x_72_);
v___x_76_ = lean_box(0);
return v___x_76_;
}
else
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = l_Lean_Expr_appFnCleanup___redArg(v___x_72_);
v___x_78_ = l_Lean_Expr_isApp(v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
lean_dec_ref(v___x_77_);
v___x_79_ = lean_box(0);
return v___x_79_;
}
else
{
lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = l_Lean_Expr_appFnCleanup___redArg(v___x_77_);
v___x_81_ = l_Lean_Expr_isApp(v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; 
lean_dec_ref(v___x_80_);
v___x_82_ = lean_box(0);
return v___x_82_;
}
else
{
lean_object* v_arg_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v_arg_83_ = lean_ctor_get(v___x_80_, 1);
lean_inc_ref(v_arg_83_);
v___x_84_ = l_Lean_Expr_appFnCleanup___redArg(v___x_80_);
v___x_85_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7));
v___x_86_ = l_Lean_Expr_isConstOf(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10));
v___x_88_ = l_Lean_Expr_isConstOf(v___x_84_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__13));
v___x_90_ = l_Lean_Expr_isConstOf(v___x_84_, v___x_89_);
lean_dec_ref(v___x_84_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; 
lean_dec_ref(v_arg_83_);
v___x_91_ = lean_box(0);
return v___x_91_;
}
else
{
v_00_u03b1_56_ = v_arg_83_;
goto v___jp_55_;
}
}
else
{
lean_dec_ref(v___x_84_);
v_00_u03b1_56_ = v_arg_83_;
goto v___jp_55_;
}
}
else
{
lean_dec_ref(v___x_84_);
v_00_u03b1_51_ = v_arg_83_;
goto v___jp_50_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_72_);
v_00_u03b1_51_ = v_arg_71_;
goto v___jp_50_;
}
}
}
}
else
{
lean_object* v___x_92_; 
lean_dec_ref(v___x_63_);
v___x_92_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__14, &l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__14);
return v___x_92_;
}
}
v___jp_50_:
{
uint8_t v___x_52_; 
lean_inc_ref(v_00_u03b1_51_);
v___x_52_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType(v_00_u03b1_51_);
if (v___x_52_ == 0)
{
lean_object* v___x_53_; 
lean_dec_ref(v_00_u03b1_51_);
v___x_53_ = lean_box(0);
return v___x_53_;
}
else
{
lean_object* v___x_54_; 
v___x_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_54_, 0, v_00_u03b1_51_);
return v___x_54_;
}
}
v___jp_55_:
{
uint8_t v___x_57_; 
lean_inc_ref(v_00_u03b1_56_);
v___x_57_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_00_u03b1_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; 
lean_dec_ref(v_00_u03b1_56_);
v___x_58_ = lean_box(0);
return v___x_58_;
}
else
{
lean_object* v___x_59_; 
v___x_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_59_, 0, v_00_u03b1_56_);
return v___x_59_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isLinearTerm(lean_object* v_e_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_Meta_Simp_Arith_isLinearTerm_x3f(v_e_93_);
if (lean_obj_tag(v___x_94_) == 0)
{
uint8_t v___x_95_; 
v___x_95_ = 0;
return v___x_95_;
}
else
{
uint8_t v___x_96_; 
lean_dec_ref(v___x_94_);
v___x_96_ = 1;
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearTerm___boxed(lean_object* v_e_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_Lean_Meta_Simp_Arith_isLinearTerm(v_e_97_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isLinearPosCnstr(lean_object* v_e_126_){
_start:
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = l_Lean_Expr_cleanupAnnotations(v_e_126_);
v___x_128_ = l_Lean_Expr_isApp(v___x_127_);
if (v___x_128_ == 0)
{
lean_dec_ref(v___x_127_);
return v___x_128_;
}
else
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = l_Lean_Expr_appFnCleanup___redArg(v___x_127_);
v___x_130_ = l_Lean_Expr_isApp(v___x_129_);
if (v___x_130_ == 0)
{
lean_dec_ref(v___x_129_);
return v___x_130_;
}
else
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = l_Lean_Expr_appFnCleanup___redArg(v___x_129_);
v___x_132_ = l_Lean_Expr_isApp(v___x_131_);
if (v___x_132_ == 0)
{
lean_dec_ref(v___x_131_);
return v___x_132_;
}
else
{
lean_object* v_arg_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_arg_133_ = lean_ctor_get(v___x_131_, 1);
lean_inc_ref(v_arg_133_);
v___x_134_ = l_Lean_Expr_appFnCleanup___redArg(v___x_131_);
v___x_135_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__1));
v___x_136_ = l_Lean_Expr_isConstOf(v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__3));
v___x_138_ = l_Lean_Expr_isConstOf(v___x_134_, v___x_137_);
if (v___x_138_ == 0)
{
uint8_t v___x_139_; 
lean_dec_ref(v_arg_133_);
v___x_139_ = l_Lean_Expr_isApp(v___x_134_);
if (v___x_139_ == 0)
{
lean_dec_ref(v___x_134_);
return v___x_139_;
}
else
{
lean_object* v_arg_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_arg_140_ = lean_ctor_get(v___x_134_, 1);
lean_inc_ref(v_arg_140_);
v___x_141_ = l_Lean_Expr_appFnCleanup___redArg(v___x_134_);
v___x_142_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__6));
v___x_143_ = l_Lean_Expr_isConstOf(v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__9));
v___x_145_ = l_Lean_Expr_isConstOf(v___x_141_, v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__12));
v___x_147_ = l_Lean_Expr_isConstOf(v___x_141_, v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__15));
v___x_149_ = l_Lean_Expr_isConstOf(v___x_141_, v___x_148_);
lean_dec_ref(v___x_141_);
if (v___x_149_ == 0)
{
lean_dec_ref(v_arg_140_);
return v___x_149_;
}
else
{
uint8_t v___x_150_; 
v___x_150_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_140_);
return v___x_150_;
}
}
else
{
uint8_t v___x_151_; 
lean_dec_ref(v___x_141_);
v___x_151_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_140_);
return v___x_151_;
}
}
else
{
uint8_t v___x_152_; 
lean_dec_ref(v___x_141_);
v___x_152_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_140_);
return v___x_152_;
}
}
else
{
uint8_t v___x_153_; 
lean_dec_ref(v___x_141_);
v___x_153_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_140_);
return v___x_153_;
}
}
}
else
{
uint8_t v___x_154_; 
lean_dec_ref(v___x_134_);
v___x_154_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_133_);
return v___x_154_;
}
}
else
{
uint8_t v___x_155_; 
lean_dec_ref(v___x_134_);
v___x_155_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_133_);
return v___x_155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearPosCnstr___boxed(lean_object* v_e_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_156_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isLinearCnstr(lean_object* v_e_162_){
_start:
{
lean_object* v___x_163_; uint8_t v___x_164_; 
lean_inc_ref(v_e_162_);
v___x_163_ = l_Lean_Expr_cleanupAnnotations(v_e_162_);
v___x_164_ = l_Lean_Expr_isApp(v___x_163_);
if (v___x_164_ == 0)
{
uint8_t v___x_165_; 
lean_dec_ref(v___x_163_);
v___x_165_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_162_);
return v___x_165_;
}
else
{
lean_object* v_arg_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_arg_166_ = lean_ctor_get(v___x_163_, 1);
lean_inc_ref(v_arg_166_);
v___x_167_ = l_Lean_Expr_appFnCleanup___redArg(v___x_163_);
v___x_168_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__1));
v___x_169_ = l_Lean_Expr_isConstOf(v___x_167_, v___x_168_);
lean_dec_ref(v___x_167_);
if (v___x_169_ == 0)
{
uint8_t v___x_170_; 
lean_dec_ref(v_arg_166_);
v___x_170_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_162_);
return v___x_170_;
}
else
{
uint8_t v___x_171_; 
lean_dec_ref(v_e_162_);
v___x_171_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_arg_166_);
return v___x_171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isLinearCnstr___boxed(lean_object* v_e_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Lean_Meta_Simp_Arith_isLinearCnstr(v_e_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_isDvdCnstr(lean_object* v_e_180_){
_start:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = l_Lean_Expr_cleanupAnnotations(v_e_180_);
v___x_182_ = l_Lean_Expr_isApp(v___x_181_);
if (v___x_182_ == 0)
{
lean_dec_ref(v___x_181_);
return v___x_182_;
}
else
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = l_Lean_Expr_appFnCleanup___redArg(v___x_181_);
v___x_184_ = l_Lean_Expr_isApp(v___x_183_);
if (v___x_184_ == 0)
{
lean_dec_ref(v___x_183_);
return v___x_184_;
}
else
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = l_Lean_Expr_appFnCleanup___redArg(v___x_183_);
v___x_186_ = l_Lean_Expr_isApp(v___x_185_);
if (v___x_186_ == 0)
{
lean_dec_ref(v___x_185_);
return v___x_186_;
}
else
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = l_Lean_Expr_appFnCleanup___redArg(v___x_185_);
v___x_188_ = l_Lean_Expr_isApp(v___x_187_);
if (v___x_188_ == 0)
{
lean_dec_ref(v___x_187_);
return v___x_188_;
}
else
{
lean_object* v_arg_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_arg_189_ = lean_ctor_get(v___x_187_, 1);
lean_inc_ref(v_arg_189_);
v___x_190_ = l_Lean_Expr_appFnCleanup___redArg(v___x_187_);
v___x_191_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__2));
v___x_192_ = l_Lean_Expr_isConstOf(v___x_190_, v___x_191_);
lean_dec_ref(v___x_190_);
if (v___x_192_ == 0)
{
lean_dec_ref(v_arg_189_);
return v___x_192_;
}
else
{
uint8_t v___x_193_; 
v___x_193_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_189_);
return v___x_193_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_isDvdCnstr___boxed(lean_object* v_e_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Lean_Meta_Simp_Arith_isDvdCnstr(v_e_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
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
