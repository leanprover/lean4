// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.Internalize
// Imports: public import Lean.Meta.Tactic.Grind.Order.OrderM import Init.Data.Int.OfNat import Init.Grind.Module.Envelope import Init.Grind.Order import Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr import Lean.Meta.Tactic.Grind.Arith.CommRing.Proof import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat import Lean.Meta.Tactic.Grind.Order.StructId import Lean.Meta.Tactic.Grind.Order.Util import Lean.Meta.Tactic.Grind.Order.Assert import Lean.Meta.Tactic.Grind.Order.Proof
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__3_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__16_value;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isArithTerm(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "IntModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OfNatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "toQ"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__4_value;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__3_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__4_value),LEAN_SCALAR_PTR_LITERAL(100, 80, 29, 215, 2, 174, 123, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__6_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__9_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__10_value),LEAN_SCALAR_PTR_LITERAL(19, 237, 167, 212, 100, 179, 19, 112)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__12_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__13_value),LEAN_SCALAR_PTR_LITERAL(23, 127, 6, 115, 121, 139, 223, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__14_value;
uint8_t l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__1;
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "le_norm0"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__1_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(58, 137, 199, 7, 196, 32, 237, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__2_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lt_norm0"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 38, 13, 200, 139, 5, 129, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "eq_norm0"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 168, 25, 138, 204, 93, 116, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0___closed__1_value;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCnstrNorm0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCnstrNorm0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0___closed__0;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 189, 244, 99, 68, 50, 19, 202)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(190, 203, 124, 26, 63, 107, 241, 61)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__10_value),LEAN_SCALAR_PTR_LITERAL(181, 4, 252, 84, 28, 16, 24, 6)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__7_value;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___lam__0(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "`grind` failed to find instance"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(7, 205, 186, 60, 7, 38, 135, 75)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__1_value;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "npow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__3_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__5_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__6_value;
extern lean_object* l_Lean_Nat_mkType;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3_spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__0_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__7_value),LEAN_SCALAR_PTR_LITERAL(84, 97, 73, 37, 143, 22, 233, 204)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__6_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 49, 23, 61, 125, 46, 165, 129)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__1_value;
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__6_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(8, 241, 181, 204, 215, 46, 40, 252)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkLeIffProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkLtIffProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3_spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNonCommLeIffProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNonCommLtIffProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Expr_toPoly__nc(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCnstr_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__2;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Order_orderExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___lam__0(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___closed__2_value;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "order"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "internalize"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__1_value),LEAN_SCALAR_PTR_LITERAL(40, 139, 28, 5, 248, 187, 127, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__2_value),LEAN_SCALAR_PTR_LITERAL(201, 111, 26, 150, 112, 124, 18, 136)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 231, 27, 63, 201, 183, 177, 76)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = " ↦ #"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__6;
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__1_value),LEAN_SCALAR_PTR_LITERAL(40, 139, 28, 5, 248, 187, 127, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__2_value),LEAN_SCALAR_PTR_LITERAL(201, 111, 26, 150, 112, 124, 18, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__3_value;
lean_object* l_Lean_Meta_Grind_Order_getDist_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Order_Weight_isNeg(lean_object*);
lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object*);
uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_getConst(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkTermEqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNonCommTermEqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTerm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTerm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "le_of_offset_eq_2_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "le_of_offset_eq_1_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(73, 223, 161, 173, 94, 131, 29, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__4;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__5;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__8_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__10;
lean_object* l_Lean_Meta_Grind_Order_addEdge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkOrdRingPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ToInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "le_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__9_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(174, 62, 213, 17, 103, 229, 239, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lt_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__9_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(228, 229, 32, 71, 94, 156, 254, 214)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__4_value;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adapt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adapt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_hasLt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_9);
x_10 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_11 = l_Lean_Expr_isApp(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_13);
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_10);
x_19 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__2));
x_20 = l_Lean_Expr_isConstOf(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__4));
x_22 = l_Lean_Expr_isConstOf(x_18, x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec_ref(x_13);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
x_23 = l_Lean_Expr_isApp(x_18);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec_ref(x_18);
x_24 = lean_box(0);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_25);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_27 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__7));
x_28 = l_Lean_Expr_isConstOf(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__10));
x_30 = l_Lean_Expr_isConstOf(x_26, x_29);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec_ref(x_25);
x_31 = l_Lean_Expr_isApp(x_26);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec_ref(x_26);
x_32 = lean_box(0);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_34 = l_Lean_Expr_isApp(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec_ref(x_33);
x_35 = lean_box(0);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_36);
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_33);
x_38 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__13));
x_39 = l_Lean_Expr_isConstOf(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__16));
x_41 = l_Lean_Expr_isConstOf(x_37, x_40);
lean_dec_ref(x_37);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec_ref(x_36);
x_42 = lean_box(0);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_36);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec_ref(x_37);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_36);
return x_44;
}
}
}
}
else
{
lean_object* x_45; 
lean_dec_ref(x_26);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_25);
return x_45;
}
}
else
{
lean_object* x_46; 
lean_dec_ref(x_26);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_25);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec_ref(x_18);
x_47 = l_Lean_Meta_Grind_Arith_isArithTerm(x_9);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Meta_Grind_Arith_isArithTerm(x_5);
x_14 = x_48;
goto block_17;
}
else
{
lean_dec_ref(x_5);
x_14 = x_47;
goto block_17;
}
}
}
else
{
lean_object* x_49; 
lean_dec_ref(x_18);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_13);
return x_49;
}
block_17:
{
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_13);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(x_1);
x_3 = 1;
if (x_2 == 0)
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_Expr_isEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Expr_cleanupAnnotations(x_4);
x_8 = l_Lean_Expr_isApp(x_7);
if (x_8 == 0)
{
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_7);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_dec_ref(x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec_ref(x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_14 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__5));
x_15 = l_Lean_Expr_isConstOf(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__8));
x_17 = l_Lean_Expr_isConstOf(x_13, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__11));
x_19 = l_Lean_Expr_isConstOf(x_13, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Expr_isApp(x_13);
if (x_20 == 0)
{
lean_dec_ref(x_13);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_13);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__14));
x_27 = l_Lean_Expr_isConstOf(x_25, x_26);
lean_dec_ref(x_25);
if (x_27 == 0)
{
return x_27;
}
else
{
return x_3;
}
}
}
}
}
else
{
lean_dec_ref(x_13);
return x_3;
}
}
else
{
lean_dec_ref(x_13);
return x_3;
}
}
else
{
lean_dec_ref(x_13);
return x_3;
}
}
}
}
}
else
{
lean_dec_ref(x_6);
lean_dec(x_4);
return x_3;
}
}
else
{
lean_dec(x_4);
return x_2;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__1);
x_4 = lean_int_neg(x_2);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_46; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_46 = !lean_is_exclusive(x_1);
if (x_46 == 0)
{
x_10 = x_1;
x_11 = x_46;
goto block_45;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_44; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split(x_9);
x_13 = lean_ctor_get(x_12, 1);
x_14 = lean_ctor_get(x_12, 0);
x_44 = !lean_is_exclusive(x_12);
if (x_44 == 0)
{
x_15 = x_12;
x_16 = x_44;
goto block_43;
}
else
{
lean_inc(x_13);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
x_19 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0);
x_20 = lean_int_dec_lt(x_7, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 2, x_14);
x_21 = x_10;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_8);
lean_ctor_set(x_26, 2, x_14);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_21);
x_22 = x_15;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_13);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
else
{
lean_object* x_27; uint8_t x_28; uint8_t x_40; 
lean_inc(x_18);
lean_inc(x_17);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_13, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_13, 0);
lean_dec(x_42);
x_27 = x_13;
x_28 = x_40;
goto block_39;
}
else
{
lean_dec(x_13);
x_27 = lean_box(0);
x_28 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_int_neg(x_7);
lean_dec(x_7);
if (x_11 == 0)
{
lean_ctor_set(x_10, 2, x_17);
lean_ctor_set(x_10, 0, x_29);
x_30 = x_10;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_8);
lean_ctor_set(x_38, 2, x_17);
x_30 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_31; 
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_30);
x_31 = x_27;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_18);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_31);
x_32 = x_15;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__2));
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(22u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_2 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 12);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = l_Lean_mkAppB(x_5, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 13);
lean_inc(x_7);
lean_dec_ref(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3);
x_9 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel_spec__0(x_8);
x_10 = l_Lean_mkAppB(x_9, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = l_Lean_mkAppB(x_11, x_3, x_4);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0___closed__2));
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_mkConst(x_8, x_10);
x_12 = l_Lean_mkApp5(x_11, x_5, x_2, x_7, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 5);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0___closed__1));
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_mkConst(x_8, x_10);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3);
x_13 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel_spec__0(x_12);
x_14 = l_Lean_mkApp5(x_11, x_5, x_2, x_13, x_3, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec_ref(x_7);
x_16 = l_Lean_mkApp5(x_11, x_5, x_2, x_15, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkEqNorm0___closed__1));
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_mkConst(x_7, x_9);
x_11 = l_Lean_mkApp4(x_10, x_5, x_2, x_3, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCnstrNorm0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_3 == 0)
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLeNorm0(x_1, x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkLtNorm0(x_1, x_2, x_4, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCnstrNorm0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCnstrNorm0(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0);
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0___closed__0);
x_9 = l_Lean_Expr_app___override(x_7, x_8);
x_10 = l_Lean_mkAppB(x_1, x_2, x_9);
x_11 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel(x_3, x_4, x_5, x_10);
x_12 = lean_apply_2(x_6, lean_box(0), x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
x_9 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_box(x_3);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0___boxed), 7, 6);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_5);
x_14 = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(x_6, x_7, x_8, x_9);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_14, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__1(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
x_13 = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(x_1, x_2, x_3, x_4, x_5);
x_14 = lean_box(x_7);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__1___boxed), 11, 10);
lean_closure_set(x_15, 0, x_9);
lean_closure_set(x_15, 1, x_6);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_8);
lean_closure_set(x_15, 4, x_12);
lean_closure_set(x_15, 5, x_1);
lean_closure_set(x_15, 6, x_3);
lean_closure_set(x_15, 7, x_4);
lean_closure_set(x_15, 8, x_5);
lean_closure_set(x_15, 9, x_11);
x_16 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_13, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_7);
x_11 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_8);
x_12 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_51; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_ctor_get(x_2, 6);
x_10 = lean_ctor_get(x_2, 7);
x_11 = lean_ctor_get(x_2, 8);
x_12 = lean_ctor_get(x_2, 9);
x_13 = lean_ctor_get(x_2, 10);
x_14 = lean_ctor_get(x_2, 11);
x_15 = lean_ctor_get(x_2, 12);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*15);
x_17 = lean_ctor_get(x_2, 13);
x_18 = lean_ctor_get(x_2, 14);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*15 + 1);
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
x_20 = x_2;
x_21 = x_51;
goto block_50;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_48; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 3);
x_26 = lean_ctor_get(x_3, 4);
x_27 = lean_ctor_get(x_3, 5);
x_28 = lean_ctor_get(x_3, 6);
x_29 = lean_ctor_get(x_3, 7);
x_30 = lean_ctor_get(x_3, 8);
x_31 = lean_ctor_get(x_3, 9);
x_32 = lean_ctor_get(x_3, 10);
x_33 = lean_ctor_get(x_3, 12);
x_34 = lean_ctor_get(x_3, 13);
x_35 = lean_ctor_get(x_3, 14);
x_36 = lean_ctor_get(x_3, 15);
x_37 = lean_ctor_get(x_3, 16);
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_3, 11);
lean_dec(x_49);
x_38 = x_3;
x_39 = x_48;
goto block_47;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_38 = lean_box(0);
x_39 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_1);
if (x_39 == 0)
{
lean_ctor_set(x_38, 11, x_40);
x_41 = x_38;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_46, 0, x_22);
lean_ctor_set(x_46, 1, x_23);
lean_ctor_set(x_46, 2, x_24);
lean_ctor_set(x_46, 3, x_25);
lean_ctor_set(x_46, 4, x_26);
lean_ctor_set(x_46, 5, x_27);
lean_ctor_set(x_46, 6, x_28);
lean_ctor_set(x_46, 7, x_29);
lean_ctor_set(x_46, 8, x_30);
lean_ctor_set(x_46, 9, x_31);
lean_ctor_set(x_46, 10, x_32);
lean_ctor_set(x_46, 11, x_40);
lean_ctor_set(x_46, 12, x_33);
lean_ctor_set(x_46, 13, x_34);
lean_ctor_set(x_46, 14, x_35);
lean_ctor_set(x_46, 15, x_36);
lean_ctor_set(x_46, 16, x_37);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_41);
x_42 = x_20;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_4);
lean_ctor_set(x_44, 2, x_5);
lean_ctor_set(x_44, 3, x_6);
lean_ctor_set(x_44, 4, x_7);
lean_ctor_set(x_44, 5, x_8);
lean_ctor_set(x_44, 6, x_9);
lean_ctor_set(x_44, 7, x_10);
lean_ctor_set(x_44, 8, x_11);
lean_ctor_set(x_44, 9, x_12);
lean_ctor_set(x_44, 10, x_13);
lean_ctor_set(x_44, 11, x_14);
lean_ctor_set(x_44, 12, x_15);
lean_ctor_set(x_44, 13, x_17);
lean_ctor_set(x_44, 14, x_18);
lean_ctor_set_uint8(x_44, sizeof(void*)*15, x_16);
lean_ctor_set_uint8(x_44, sizeof(void*)*15 + 1, x_19);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_36; 
x_36 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_99; 
x_37 = lean_ctor_get(x_36, 0);
x_99 = !lean_is_exclusive(x_36);
if (x_99 == 0)
{
x_38 = x_36;
x_39 = x_99;
goto block_98;
}
else
{
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_40, 11);
if (lean_obj_tag(x_41) == 1)
{
lean_object* x_42; lean_object* x_43; 
lean_inc_ref(x_41);
lean_dec_ref(x_40);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_42);
x_43 = x_38;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_del_object(x_38);
x_46 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_40, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_40, 3);
lean_inc_ref(x_48);
lean_dec_ref(x_40);
x_49 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__2));
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
lean_inc_ref(x_51);
x_52 = l_Lean_mkConst(x_49, x_51);
lean_inc_ref(x_46);
x_53 = l_Lean_mkAppB(x_52, x_46, x_48);
x_74 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__5));
lean_inc_ref(x_51);
x_75 = l_Lean_mkConst(x_74, x_51);
lean_inc_ref(x_46);
x_76 = l_Lean_Expr_app___override(x_75, x_46);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_77 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_76, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
if (lean_obj_tag(x_78) == 0)
{
x_54 = x_53;
x_55 = x_1;
x_56 = x_2;
x_57 = x_3;
x_58 = x_4;
x_59 = x_5;
x_60 = x_6;
x_61 = x_7;
x_62 = x_8;
x_63 = x_9;
x_64 = x_10;
x_65 = x_11;
x_66 = lean_box(0);
goto block_73;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__7));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_79);
x_81 = l_Lean_Meta_Grind_Arith_CommRing_checkInst(x_80, x_79, x_53, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_81);
x_54 = x_79;
x_55 = x_1;
x_56 = x_2;
x_57 = x_3;
x_58 = x_4;
x_59 = x_5;
x_60 = x_6;
x_61 = x_7;
x_62 = x_8;
x_63 = x_9;
x_64 = x_10;
x_65 = x_11;
x_66 = lean_box(0);
goto block_73;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_dec(x_79);
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_82 = lean_ctor_get(x_81, 0);
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
x_83 = x_81;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
lean_dec_ref(x_53);
lean_dec_ref(x_51);
lean_dec_ref(x_46);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_90 = lean_ctor_get(x_77, 0);
x_97 = !lean_is_exclusive(x_77);
if (x_97 == 0)
{
x_91 = x_77;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_77);
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
block_73:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__4));
x_68 = l_Lean_mkConst(x_67, x_51);
x_69 = l_Lean_mkAppB(x_68, x_46, x_54);
lean_inc(x_61);
lean_inc(x_56);
x_70 = lean_grind_canon(x_69, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_63, x_64, x_65);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = l_Lean_Meta_Sym_shareCommon___redArg(x_71, x_61);
lean_dec(x_61);
x_13 = x_56;
x_14 = x_55;
x_15 = x_72;
goto block_35;
}
else
{
lean_dec(x_61);
x_13 = x_56;
x_14 = x_55;
x_15 = x_70;
goto block_35;
}
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_107; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_100 = lean_ctor_get(x_36, 0);
x_107 = !lean_is_exclusive(x_36);
if (x_107 == 0)
{
x_101 = x_36;
x_102 = x_107;
goto block_106;
}
else
{
lean_inc(x_100);
lean_dec(x_36);
x_101 = lean_box(0);
x_102 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_103; 
if (x_102 == 0)
{
x_103 = x_101;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_100);
x_103 = x_105;
goto block_104;
}
block_104:
{
return x_103;
}
}
}
block_35:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___lam__0), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(x_17, x_14, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; uint8_t x_25; 
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_19 = x_18;
x_20 = x_25;
goto block_24;
}
else
{
lean_dec(x_18);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_16);
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_16);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec(x_16);
x_27 = lean_ctor_get(x_18, 0);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
x_28 = x_18;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_dec_ref(x_14);
lean_dec(x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_51; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_ctor_get(x_2, 6);
x_10 = lean_ctor_get(x_2, 7);
x_11 = lean_ctor_get(x_2, 8);
x_12 = lean_ctor_get(x_2, 9);
x_13 = lean_ctor_get(x_2, 10);
x_14 = lean_ctor_get(x_2, 11);
x_15 = lean_ctor_get(x_2, 12);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*15);
x_17 = lean_ctor_get(x_2, 13);
x_18 = lean_ctor_get(x_2, 14);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*15 + 1);
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
x_20 = x_2;
x_21 = x_51;
goto block_50;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_48; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 3);
x_26 = lean_ctor_get(x_3, 4);
x_27 = lean_ctor_get(x_3, 5);
x_28 = lean_ctor_get(x_3, 7);
x_29 = lean_ctor_get(x_3, 8);
x_30 = lean_ctor_get(x_3, 9);
x_31 = lean_ctor_get(x_3, 10);
x_32 = lean_ctor_get(x_3, 11);
x_33 = lean_ctor_get(x_3, 12);
x_34 = lean_ctor_get(x_3, 13);
x_35 = lean_ctor_get(x_3, 14);
x_36 = lean_ctor_get(x_3, 15);
x_37 = lean_ctor_get(x_3, 16);
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_3, 6);
lean_dec(x_49);
x_38 = x_3;
x_39 = x_48;
goto block_47;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_38 = lean_box(0);
x_39 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_1);
if (x_39 == 0)
{
lean_ctor_set(x_38, 6, x_40);
x_41 = x_38;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_46, 0, x_22);
lean_ctor_set(x_46, 1, x_23);
lean_ctor_set(x_46, 2, x_24);
lean_ctor_set(x_46, 3, x_25);
lean_ctor_set(x_46, 4, x_26);
lean_ctor_set(x_46, 5, x_27);
lean_ctor_set(x_46, 6, x_40);
lean_ctor_set(x_46, 7, x_28);
lean_ctor_set(x_46, 8, x_29);
lean_ctor_set(x_46, 9, x_30);
lean_ctor_set(x_46, 10, x_31);
lean_ctor_set(x_46, 11, x_32);
lean_ctor_set(x_46, 12, x_33);
lean_ctor_set(x_46, 13, x_34);
lean_ctor_set(x_46, 14, x_35);
lean_ctor_set(x_46, 15, x_36);
lean_ctor_set(x_46, 16, x_37);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_41);
x_42 = x_20;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_4);
lean_ctor_set(x_44, 2, x_5);
lean_ctor_set(x_44, 3, x_6);
lean_ctor_set(x_44, 4, x_7);
lean_ctor_set(x_44, 5, x_8);
lean_ctor_set(x_44, 6, x_9);
lean_ctor_set(x_44, 7, x_10);
lean_ctor_set(x_44, 8, x_11);
lean_ctor_set(x_44, 9, x_12);
lean_ctor_set(x_44, 10, x_13);
lean_ctor_set(x_44, 11, x_14);
lean_ctor_set(x_44, 12, x_15);
lean_ctor_set(x_44, 13, x_17);
lean_ctor_set(x_44, 14, x_18);
lean_ctor_set_uint8(x_44, sizeof(void*)*15, x_16);
lean_ctor_set_uint8(x_44, sizeof(void*)*15 + 1, x_19);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15_spec__16(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15_spec__16(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
x_14 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_1, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_27; 
x_15 = lean_ctor_get(x_14, 0);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
x_16 = x_14;
x_17 = x_27;
goto block_26;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_27;
goto block_26;
}
block_26:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_del_object(x_16);
lean_dec(x_15);
x_22 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___closed__1);
x_23 = l_Lean_indentExpr(x_1);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___redArg(x_24, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_25;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_28 = lean_ctor_get(x_14, 0);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
x_29 = x_14;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_box(0);
lean_inc(x_2);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
lean_inc_ref(x_21);
x_22 = l_Lean_mkConst(x_3, x_21);
lean_inc_ref_n(x_1, 3);
x_23 = l_Lean_mkApp3(x_22, x_1, x_1, x_1);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_24 = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14(x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_25);
lean_inc(x_4);
x_26 = l_Lean_Meta_Grind_Arith_CommRing_checkInst(x_4, x_25, x_5, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_26);
x_27 = l_Lean_mkConst(x_4, x_21);
lean_inc_ref_n(x_1, 2);
x_28 = l_Lean_mkApp4(x_27, x_1, x_1, x_1, x_25);
lean_inc(x_12);
x_29 = lean_grind_canon(x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_Meta_Sym_shareCommon___redArg(x_30, x_12);
lean_dec(x_12);
return x_31;
}
else
{
lean_dec(x_12);
return x_29;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec(x_25);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_26, 0);
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
x_33 = x_26;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_57; 
x_14 = lean_ctor_get(x_13, 0);
x_57 = !lean_is_exclusive(x_13);
if (x_57 == 0)
{
x_15 = x_13;
x_16 = x_57;
goto block_56;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_17, 6);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; 
lean_inc_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_19);
x_20 = x_15;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_del_object(x_15);
x_23 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_17, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 4);
lean_inc_ref(x_25);
lean_dec_ref(x_17);
x_26 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__1));
x_27 = lean_box(0);
lean_inc(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
lean_inc_ref(x_28);
x_29 = l_Lean_mkConst(x_26, x_28);
x_30 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__4));
x_31 = l_Lean_mkConst(x_30, x_28);
lean_inc_ref(x_23);
x_32 = l_Lean_mkAppB(x_31, x_23, x_25);
lean_inc_ref(x_23);
x_33 = l_Lean_mkAppB(x_29, x_23, x_32);
x_34 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__5));
x_35 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__16));
lean_inc(x_2);
x_36 = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9(x_23, x_24, x_34, x_35, x_33, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc(x_37);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___lam__0), 2, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(x_38, x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_46; 
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_39, 0);
lean_dec(x_47);
x_40 = x_39;
x_41 = x_46;
goto block_45;
}
else
{
lean_dec(x_39);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_37);
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_37);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_dec(x_37);
x_48 = lean_ctor_get(x_39, 0);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
x_49 = x_39;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_36;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_58 = lean_ctor_get(x_13, 0);
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
x_59 = x_13;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_13);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_17 = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_31; 
x_20 = lean_ctor_get(x_19, 0);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
x_21 = x_19;
x_22 = x_31;
goto block_30;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0___closed__0);
x_24 = l_Lean_Expr_app___override(x_20, x_23);
x_25 = l_Lean_mkAppB(x_18, x_4, x_24);
x_26 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel(x_1, x_2, x_3, x_25);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_26);
x_27 = x_21;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_dec(x_18);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_19;
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_2);
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 14);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_4, 2);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_4);
x_7 = l_outOfBounds___redArg(x_2);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_get_x21___redArg(x_2, x_4, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__1));
x_17 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__2);
x_18 = lean_box(0);
lean_inc(x_1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
lean_inc_ref(x_19);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
lean_inc_ref(x_21);
x_22 = l_Lean_mkConst(x_16, x_21);
x_23 = l_Lean_Nat_mkType;
lean_inc_ref_n(x_2, 2);
x_24 = l_Lean_mkApp3(x_22, x_2, x_23, x_2);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_25 = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14(x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__4));
x_28 = l_Lean_mkConst(x_27, x_19);
lean_inc_ref(x_2);
x_29 = l_Lean_mkAppB(x_28, x_2, x_3);
x_30 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__6));
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_26);
x_31 = l_Lean_Meta_Grind_Arith_CommRing_checkInst(x_30, x_26, x_29, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_31);
x_32 = l_Lean_mkConst(x_30, x_21);
lean_inc_ref(x_2);
x_33 = l_Lean_mkApp4(x_32, x_2, x_23, x_2, x_26);
lean_inc(x_10);
x_34 = lean_grind_canon(x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_Meta_Sym_shareCommon___redArg(x_35, x_10);
lean_dec(x_10);
return x_36;
}
else
{
lean_dec(x_10);
return x_34;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_26);
lean_dec_ref(x_21);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_37 = lean_ctor_get(x_31, 0);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
x_38 = x_31;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_51; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_ctor_get(x_2, 6);
x_10 = lean_ctor_get(x_2, 7);
x_11 = lean_ctor_get(x_2, 8);
x_12 = lean_ctor_get(x_2, 9);
x_13 = lean_ctor_get(x_2, 10);
x_14 = lean_ctor_get(x_2, 11);
x_15 = lean_ctor_get(x_2, 12);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*15);
x_17 = lean_ctor_get(x_2, 13);
x_18 = lean_ctor_get(x_2, 14);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*15 + 1);
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
x_20 = x_2;
x_21 = x_51;
goto block_50;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_48; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 3);
x_26 = lean_ctor_get(x_3, 4);
x_27 = lean_ctor_get(x_3, 5);
x_28 = lean_ctor_get(x_3, 6);
x_29 = lean_ctor_get(x_3, 7);
x_30 = lean_ctor_get(x_3, 8);
x_31 = lean_ctor_get(x_3, 9);
x_32 = lean_ctor_get(x_3, 11);
x_33 = lean_ctor_get(x_3, 12);
x_34 = lean_ctor_get(x_3, 13);
x_35 = lean_ctor_get(x_3, 14);
x_36 = lean_ctor_get(x_3, 15);
x_37 = lean_ctor_get(x_3, 16);
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_3, 10);
lean_dec(x_49);
x_38 = x_3;
x_39 = x_48;
goto block_47;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_38 = lean_box(0);
x_39 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_1);
if (x_39 == 0)
{
lean_ctor_set(x_38, 10, x_40);
x_41 = x_38;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_46, 0, x_22);
lean_ctor_set(x_46, 1, x_23);
lean_ctor_set(x_46, 2, x_24);
lean_ctor_set(x_46, 3, x_25);
lean_ctor_set(x_46, 4, x_26);
lean_ctor_set(x_46, 5, x_27);
lean_ctor_set(x_46, 6, x_28);
lean_ctor_set(x_46, 7, x_29);
lean_ctor_set(x_46, 8, x_30);
lean_ctor_set(x_46, 9, x_31);
lean_ctor_set(x_46, 10, x_40);
lean_ctor_set(x_46, 11, x_32);
lean_ctor_set(x_46, 12, x_33);
lean_ctor_set(x_46, 13, x_34);
lean_ctor_set(x_46, 14, x_35);
lean_ctor_set(x_46, 15, x_36);
lean_ctor_set(x_46, 16, x_37);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_41);
x_42 = x_20;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_4);
lean_ctor_set(x_44, 2, x_5);
lean_ctor_set(x_44, 3, x_6);
lean_ctor_set(x_44, 4, x_7);
lean_ctor_set(x_44, 5, x_8);
lean_ctor_set(x_44, 6, x_9);
lean_ctor_set(x_44, 7, x_10);
lean_ctor_set(x_44, 8, x_11);
lean_ctor_set(x_44, 9, x_12);
lean_ctor_set(x_44, 10, x_13);
lean_ctor_set(x_44, 11, x_14);
lean_ctor_set(x_44, 12, x_15);
lean_ctor_set(x_44, 13, x_17);
lean_ctor_set(x_44, 14, x_18);
lean_ctor_set_uint8(x_44, sizeof(void*)*15, x_16);
lean_ctor_set_uint8(x_44, sizeof(void*)*15 + 1, x_19);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_47; 
x_14 = lean_ctor_get(x_13, 0);
x_47 = !lean_is_exclusive(x_13);
if (x_47 == 0)
{
x_15 = x_13;
x_16 = x_47;
goto block_46;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_17, 10);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; 
lean_inc_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_19);
x_20 = x_15;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_del_object(x_15);
x_23 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_17, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 4);
lean_inc_ref(x_25);
lean_dec_ref(x_17);
lean_inc(x_2);
x_26 = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11(x_24, x_23, x_25, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_inc(x_27);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6___lam__0), 2, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(x_28, x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; uint8_t x_36; 
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_29, 0);
lean_dec(x_37);
x_30 = x_29;
x_31 = x_36;
goto block_35;
}
else
{
lean_dec(x_29);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_27);
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_27);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec(x_27);
x_38 = lean_ctor_get(x_29, 0);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
x_39 = x_29;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_26;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_13, 0);
x_55 = !lean_is_exclusive(x_13);
if (x_55 == 0)
{
x_49 = x_13;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_13);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
lean_inc_ref(x_19);
x_20 = l_Lean_mkConst(x_3, x_19);
lean_inc_ref(x_1);
x_21 = l_Lean_Expr_app___override(x_20, x_1);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_22 = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14(x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_23);
lean_inc(x_4);
x_24 = l_Lean_Meta_Grind_Arith_CommRing_checkInst(x_4, x_23, x_5, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_24);
x_25 = l_Lean_mkConst(x_4, x_19);
x_26 = l_Lean_mkAppB(x_25, x_1, x_23);
lean_inc(x_12);
x_27 = lean_grind_canon(x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_Meta_Sym_shareCommon___redArg(x_28, x_12);
lean_dec(x_12);
return x_29;
}
else
{
lean_dec(x_12);
return x_27;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_23);
lean_dec_ref(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_1);
x_30 = lean_ctor_get(x_24, 0);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
x_31 = x_24;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
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
else
{
lean_dec_ref(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3_spec__7___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_51; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_ctor_get(x_2, 6);
x_10 = lean_ctor_get(x_2, 7);
x_11 = lean_ctor_get(x_2, 8);
x_12 = lean_ctor_get(x_2, 9);
x_13 = lean_ctor_get(x_2, 10);
x_14 = lean_ctor_get(x_2, 11);
x_15 = lean_ctor_get(x_2, 12);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*15);
x_17 = lean_ctor_get(x_2, 13);
x_18 = lean_ctor_get(x_2, 14);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*15 + 1);
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
x_20 = x_2;
x_21 = x_51;
goto block_50;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_48; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 3);
x_26 = lean_ctor_get(x_3, 4);
x_27 = lean_ctor_get(x_3, 5);
x_28 = lean_ctor_get(x_3, 6);
x_29 = lean_ctor_get(x_3, 7);
x_30 = lean_ctor_get(x_3, 8);
x_31 = lean_ctor_get(x_3, 10);
x_32 = lean_ctor_get(x_3, 11);
x_33 = lean_ctor_get(x_3, 12);
x_34 = lean_ctor_get(x_3, 13);
x_35 = lean_ctor_get(x_3, 14);
x_36 = lean_ctor_get(x_3, 15);
x_37 = lean_ctor_get(x_3, 16);
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_3, 9);
lean_dec(x_49);
x_38 = x_3;
x_39 = x_48;
goto block_47;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_38 = lean_box(0);
x_39 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_1);
if (x_39 == 0)
{
lean_ctor_set(x_38, 9, x_40);
x_41 = x_38;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_46, 0, x_22);
lean_ctor_set(x_46, 1, x_23);
lean_ctor_set(x_46, 2, x_24);
lean_ctor_set(x_46, 3, x_25);
lean_ctor_set(x_46, 4, x_26);
lean_ctor_set(x_46, 5, x_27);
lean_ctor_set(x_46, 6, x_28);
lean_ctor_set(x_46, 7, x_29);
lean_ctor_set(x_46, 8, x_30);
lean_ctor_set(x_46, 9, x_40);
lean_ctor_set(x_46, 10, x_31);
lean_ctor_set(x_46, 11, x_32);
lean_ctor_set(x_46, 12, x_33);
lean_ctor_set(x_46, 13, x_34);
lean_ctor_set(x_46, 14, x_35);
lean_ctor_set(x_46, 15, x_36);
lean_ctor_set(x_46, 16, x_37);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_41);
x_42 = x_20;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_4);
lean_ctor_set(x_44, 2, x_5);
lean_ctor_set(x_44, 3, x_6);
lean_ctor_set(x_44, 4, x_7);
lean_ctor_set(x_44, 5, x_8);
lean_ctor_set(x_44, 6, x_9);
lean_ctor_set(x_44, 7, x_10);
lean_ctor_set(x_44, 8, x_11);
lean_ctor_set(x_44, 9, x_12);
lean_ctor_set(x_44, 10, x_13);
lean_ctor_set(x_44, 11, x_14);
lean_ctor_set(x_44, 12, x_15);
lean_ctor_set(x_44, 13, x_17);
lean_ctor_set(x_44, 14, x_18);
lean_ctor_set_uint8(x_44, sizeof(void*)*15, x_16);
lean_ctor_set_uint8(x_44, sizeof(void*)*15 + 1, x_19);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_54; 
x_14 = lean_ctor_get(x_13, 0);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
x_15 = x_13;
x_16 = x_54;
goto block_53;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_17, 9);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; 
lean_inc_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_19);
x_20 = x_15;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_del_object(x_15);
x_23 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_17, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 3);
lean_inc_ref(x_25);
lean_dec_ref(x_17);
x_26 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__1));
x_27 = lean_box(0);
lean_inc(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_mkConst(x_26, x_28);
lean_inc_ref(x_23);
x_30 = l_Lean_mkAppB(x_29, x_23, x_25);
x_31 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__3));
x_32 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__5));
lean_inc(x_2);
x_33 = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3_spec__7(x_23, x_24, x_31, x_32, x_30, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
lean_inc(x_34);
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___lam__0), 2, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(x_35, x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; uint8_t x_43; 
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_36, 0);
lean_dec(x_44);
x_37 = x_36;
x_38 = x_43;
goto block_42;
}
else
{
lean_dec(x_36);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
lean_ctor_set(x_37, 0, x_34);
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_34);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_dec(x_34);
x_45 = lean_ctor_get(x_36, 0);
x_52 = !lean_is_exclusive(x_36);
if (x_52 == 0)
{
x_46 = x_36;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_33;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_55 = lean_ctor_get(x_13, 0);
x_62 = !lean_is_exclusive(x_13);
if (x_62 == 0)
{
x_56 = x_13;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_13);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_51; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_ctor_get(x_2, 6);
x_10 = lean_ctor_get(x_2, 7);
x_11 = lean_ctor_get(x_2, 8);
x_12 = lean_ctor_get(x_2, 9);
x_13 = lean_ctor_get(x_2, 10);
x_14 = lean_ctor_get(x_2, 11);
x_15 = lean_ctor_get(x_2, 12);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*15);
x_17 = lean_ctor_get(x_2, 13);
x_18 = lean_ctor_get(x_2, 14);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*15 + 1);
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
x_20 = x_2;
x_21 = x_51;
goto block_50;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_48; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 3);
x_26 = lean_ctor_get(x_3, 4);
x_27 = lean_ctor_get(x_3, 5);
x_28 = lean_ctor_get(x_3, 6);
x_29 = lean_ctor_get(x_3, 7);
x_30 = lean_ctor_get(x_3, 8);
x_31 = lean_ctor_get(x_3, 9);
x_32 = lean_ctor_get(x_3, 10);
x_33 = lean_ctor_get(x_3, 11);
x_34 = lean_ctor_get(x_3, 13);
x_35 = lean_ctor_get(x_3, 14);
x_36 = lean_ctor_get(x_3, 15);
x_37 = lean_ctor_get(x_3, 16);
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_3, 12);
lean_dec(x_49);
x_38 = x_3;
x_39 = x_48;
goto block_47;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_38 = lean_box(0);
x_39 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_1);
if (x_39 == 0)
{
lean_ctor_set(x_38, 12, x_40);
x_41 = x_38;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_46, 0, x_22);
lean_ctor_set(x_46, 1, x_23);
lean_ctor_set(x_46, 2, x_24);
lean_ctor_set(x_46, 3, x_25);
lean_ctor_set(x_46, 4, x_26);
lean_ctor_set(x_46, 5, x_27);
lean_ctor_set(x_46, 6, x_28);
lean_ctor_set(x_46, 7, x_29);
lean_ctor_set(x_46, 8, x_30);
lean_ctor_set(x_46, 9, x_31);
lean_ctor_set(x_46, 10, x_32);
lean_ctor_set(x_46, 11, x_33);
lean_ctor_set(x_46, 12, x_40);
lean_ctor_set(x_46, 13, x_34);
lean_ctor_set(x_46, 14, x_35);
lean_ctor_set(x_46, 15, x_36);
lean_ctor_set(x_46, 16, x_37);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_41);
x_42 = x_20;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_4);
lean_ctor_set(x_44, 2, x_5);
lean_ctor_set(x_44, 3, x_6);
lean_ctor_set(x_44, 4, x_7);
lean_ctor_set(x_44, 5, x_8);
lean_ctor_set(x_44, 6, x_9);
lean_ctor_set(x_44, 7, x_10);
lean_ctor_set(x_44, 8, x_11);
lean_ctor_set(x_44, 9, x_12);
lean_ctor_set(x_44, 10, x_13);
lean_ctor_set(x_44, 11, x_14);
lean_ctor_set(x_44, 12, x_15);
lean_ctor_set(x_44, 13, x_17);
lean_ctor_set(x_44, 14, x_18);
lean_ctor_set_uint8(x_44, sizeof(void*)*15, x_16);
lean_ctor_set_uint8(x_44, sizeof(void*)*15 + 1, x_19);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_15 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__0));
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
lean_inc_ref(x_17);
x_18 = l_Lean_mkConst(x_15, x_17);
lean_inc_ref(x_2);
x_19 = l_Lean_mkAppB(x_18, x_2, x_3);
x_39 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__1));
lean_inc_ref(x_17);
x_40 = l_Lean_mkConst(x_39, x_17);
lean_inc_ref(x_2);
x_41 = l_Lean_Expr_app___override(x_40, x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_42 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_41, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
if (lean_obj_tag(x_43) == 0)
{
x_20 = x_19;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_11;
x_29 = x_12;
x_30 = x_13;
x_31 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__8));
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_44);
x_46 = l_Lean_Meta_Grind_Arith_CommRing_checkInst(x_45, x_44, x_19, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_46) == 0)
{
lean_dec_ref(x_46);
x_20 = x_44;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_11;
x_29 = x_12;
x_30 = x_13;
x_31 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_44);
lean_dec_ref(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_47 = lean_ctor_get(x_46, 0);
x_54 = !lean_is_exclusive(x_46);
if (x_54 == 0)
{
x_48 = x_46;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec_ref(x_19);
lean_dec_ref(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_55 = lean_ctor_get(x_42, 0);
x_62 = !lean_is_exclusive(x_42);
if (x_62 == 0)
{
x_56 = x_42;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_42);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
block_38:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__8));
x_33 = l_Lean_mkConst(x_32, x_17);
x_34 = l_Lean_mkAppB(x_33, x_2, x_20);
lean_inc(x_26);
x_35 = lean_grind_canon(x_34, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_Meta_Sym_shareCommon___redArg(x_36, x_26);
lean_dec(x_26);
return x_37;
}
else
{
lean_dec(x_26);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_47; 
x_14 = lean_ctor_get(x_13, 0);
x_47 = !lean_is_exclusive(x_13);
if (x_47 == 0)
{
x_15 = x_13;
x_16 = x_47;
goto block_46;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_17, 12);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; 
lean_inc_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_19);
x_20 = x_15;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_del_object(x_15);
x_23 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_17, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 4);
lean_inc_ref(x_25);
lean_dec_ref(x_17);
lean_inc(x_2);
x_26 = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg(x_24, x_23, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_inc(x_27);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2___lam__0), 2, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(x_28, x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; uint8_t x_36; 
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_29, 0);
lean_dec(x_37);
x_30 = x_29;
x_31 = x_36;
goto block_35;
}
else
{
lean_dec(x_29);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_27);
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_27);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec(x_27);
x_38 = lean_ctor_get(x_29, 0);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
x_39 = x_29;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_26;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_13, 0);
x_55 = !lean_is_exclusive(x_13);
if (x_55 == 0)
{
x_49 = x_13;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_13);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_19);
lean_dec_ref(x_16);
x_20 = lean_nat_abs(x_1);
x_21 = l_Lean_mkRawNatLit(x_20);
x_22 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__0));
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
lean_inc_ref(x_24);
x_25 = l_Lean_mkConst(x_22, x_24);
lean_inc_ref(x_21);
lean_inc_ref(x_17);
x_26 = l_Lean_mkAppB(x_25, x_17, x_21);
x_27 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_28 = l_Lean_Meta_synthInstance_x3f(x_26, x_27, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_68; 
x_29 = lean_ctor_get(x_28, 0);
x_68 = !lean_is_exclusive(x_28);
if (x_68 == 0)
{
x_30 = x_28;
x_31 = x_68;
goto block_67;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_63; 
lean_dec_ref(x_19);
x_63 = lean_ctor_get(x_29, 0);
lean_inc(x_63);
lean_dec_ref(x_29);
x_32 = x_63;
x_33 = x_2;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
x_37 = x_6;
x_38 = x_7;
x_39 = x_8;
x_40 = x_9;
x_41 = x_10;
x_42 = x_11;
x_43 = x_12;
goto block_62;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_29);
x_64 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__1));
lean_inc_ref(x_24);
x_65 = l_Lean_mkConst(x_64, x_24);
lean_inc_ref(x_21);
lean_inc_ref(x_17);
x_66 = l_Lean_mkApp3(x_65, x_17, x_19, x_21);
x_32 = x_66;
x_33 = x_2;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
x_37 = x_6;
x_38 = x_7;
x_39 = x_8;
x_40 = x_9;
x_41 = x_10;
x_42 = x_11;
x_43 = x_12;
goto block_62;
}
block_62:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__2));
x_45 = l_Lean_mkConst(x_44, x_24);
x_46 = l_Lean_mkApp3(x_45, x_17, x_21, x_32);
x_47 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0);
x_48 = lean_int_dec_lt(x_1, x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_46);
x_49 = x_30;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
else
{
lean_object* x_52; 
lean_del_object(x_30);
x_52 = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3(x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_41, x_42, x_43);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_61; 
x_53 = lean_ctor_get(x_52, 0);
x_61 = !lean_is_exclusive(x_52);
if (x_61 == 0)
{
x_54 = x_52;
x_55 = x_61;
goto block_60;
}
else
{
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_box(0);
x_55 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Lean_Expr_app___override(x_53, x_46);
if (x_55 == 0)
{
lean_ctor_set(x_54, 0, x_56);
x_57 = x_54;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
else
{
lean_dec_ref(x_46);
return x_52;
}
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_76; 
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec_ref(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_69 = lean_ctor_get(x_28, 0);
x_76 = !lean_is_exclusive(x_28);
if (x_76 == 0)
{
x_70 = x_28;
x_71 = x_76;
goto block_75;
}
else
{
lean_inc(x_69);
lean_dec(x_28);
x_70 = lean_box(0);
x_71 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_72; 
if (x_71 == 0)
{
x_72 = x_70;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_69);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_77 = lean_ctor_get(x_14, 0);
x_84 = !lean_is_exclusive(x_14);
if (x_84 == 0)
{
x_78 = x_14;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_14);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_51; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_ctor_get(x_2, 6);
x_10 = lean_ctor_get(x_2, 7);
x_11 = lean_ctor_get(x_2, 8);
x_12 = lean_ctor_get(x_2, 9);
x_13 = lean_ctor_get(x_2, 10);
x_14 = lean_ctor_get(x_2, 11);
x_15 = lean_ctor_get(x_2, 12);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*15);
x_17 = lean_ctor_get(x_2, 13);
x_18 = lean_ctor_get(x_2, 14);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*15 + 1);
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
x_20 = x_2;
x_21 = x_51;
goto block_50;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_48; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 3);
x_26 = lean_ctor_get(x_3, 4);
x_27 = lean_ctor_get(x_3, 5);
x_28 = lean_ctor_get(x_3, 6);
x_29 = lean_ctor_get(x_3, 8);
x_30 = lean_ctor_get(x_3, 9);
x_31 = lean_ctor_get(x_3, 10);
x_32 = lean_ctor_get(x_3, 11);
x_33 = lean_ctor_get(x_3, 12);
x_34 = lean_ctor_get(x_3, 13);
x_35 = lean_ctor_get(x_3, 14);
x_36 = lean_ctor_get(x_3, 15);
x_37 = lean_ctor_get(x_3, 16);
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_3, 7);
lean_dec(x_49);
x_38 = x_3;
x_39 = x_48;
goto block_47;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_38 = lean_box(0);
x_39 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_1);
if (x_39 == 0)
{
lean_ctor_set(x_38, 7, x_40);
x_41 = x_38;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_46, 0, x_22);
lean_ctor_set(x_46, 1, x_23);
lean_ctor_set(x_46, 2, x_24);
lean_ctor_set(x_46, 3, x_25);
lean_ctor_set(x_46, 4, x_26);
lean_ctor_set(x_46, 5, x_27);
lean_ctor_set(x_46, 6, x_28);
lean_ctor_set(x_46, 7, x_40);
lean_ctor_set(x_46, 8, x_29);
lean_ctor_set(x_46, 9, x_30);
lean_ctor_set(x_46, 10, x_31);
lean_ctor_set(x_46, 11, x_32);
lean_ctor_set(x_46, 12, x_33);
lean_ctor_set(x_46, 13, x_34);
lean_ctor_set(x_46, 14, x_35);
lean_ctor_set(x_46, 15, x_36);
lean_ctor_set(x_46, 16, x_37);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_41);
x_42 = x_20;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_4);
lean_ctor_set(x_44, 2, x_5);
lean_ctor_set(x_44, 3, x_6);
lean_ctor_set(x_44, 4, x_7);
lean_ctor_set(x_44, 5, x_8);
lean_ctor_set(x_44, 6, x_9);
lean_ctor_set(x_44, 7, x_10);
lean_ctor_set(x_44, 8, x_11);
lean_ctor_set(x_44, 9, x_12);
lean_ctor_set(x_44, 10, x_13);
lean_ctor_set(x_44, 11, x_14);
lean_ctor_set(x_44, 12, x_15);
lean_ctor_set(x_44, 13, x_17);
lean_ctor_set(x_44, 14, x_18);
lean_ctor_set_uint8(x_44, sizeof(void*)*15, x_16);
lean_ctor_set_uint8(x_44, sizeof(void*)*15 + 1, x_19);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_57; 
x_14 = lean_ctor_get(x_13, 0);
x_57 = !lean_is_exclusive(x_13);
if (x_57 == 0)
{
x_15 = x_13;
x_16 = x_57;
goto block_56;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_17, 7);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; 
lean_inc_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_19);
x_20 = x_15;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_del_object(x_15);
x_23 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_17, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 4);
lean_inc_ref(x_25);
lean_dec_ref(x_17);
x_26 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__1));
x_27 = lean_box(0);
lean_inc(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
lean_inc_ref(x_28);
x_29 = l_Lean_mkConst(x_26, x_28);
x_30 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__3));
x_31 = l_Lean_mkConst(x_30, x_28);
lean_inc_ref(x_23);
x_32 = l_Lean_mkAppB(x_31, x_23, x_25);
lean_inc_ref(x_23);
x_33 = l_Lean_mkAppB(x_29, x_23, x_32);
x_34 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__5));
x_35 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__7));
lean_inc(x_2);
x_36 = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9(x_23, x_24, x_34, x_35, x_33, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc(x_37);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___lam__0), 2, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(x_38, x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_46; 
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_39, 0);
lean_dec(x_47);
x_40 = x_39;
x_41 = x_46;
goto block_45;
}
else
{
lean_dec(x_39);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_37);
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_37);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_dec(x_37);
x_48 = lean_ctor_get(x_39, 0);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
x_49 = x_39;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_36;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_58 = lean_ctor_get(x_13, 0);
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
x_59 = x_13;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_13);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_51; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_ctor_get(x_2, 6);
x_10 = lean_ctor_get(x_2, 7);
x_11 = lean_ctor_get(x_2, 8);
x_12 = lean_ctor_get(x_2, 9);
x_13 = lean_ctor_get(x_2, 10);
x_14 = lean_ctor_get(x_2, 11);
x_15 = lean_ctor_get(x_2, 12);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*15);
x_17 = lean_ctor_get(x_2, 13);
x_18 = lean_ctor_get(x_2, 14);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*15 + 1);
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
x_20 = x_2;
x_21 = x_51;
goto block_50;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_48; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 3);
x_26 = lean_ctor_get(x_3, 4);
x_27 = lean_ctor_get(x_3, 5);
x_28 = lean_ctor_get(x_3, 6);
x_29 = lean_ctor_get(x_3, 7);
x_30 = lean_ctor_get(x_3, 9);
x_31 = lean_ctor_get(x_3, 10);
x_32 = lean_ctor_get(x_3, 11);
x_33 = lean_ctor_get(x_3, 12);
x_34 = lean_ctor_get(x_3, 13);
x_35 = lean_ctor_get(x_3, 14);
x_36 = lean_ctor_get(x_3, 15);
x_37 = lean_ctor_get(x_3, 16);
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_3, 8);
lean_dec(x_49);
x_38 = x_3;
x_39 = x_48;
goto block_47;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_38 = lean_box(0);
x_39 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_1);
if (x_39 == 0)
{
lean_ctor_set(x_38, 8, x_40);
x_41 = x_38;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_46, 0, x_22);
lean_ctor_set(x_46, 1, x_23);
lean_ctor_set(x_46, 2, x_24);
lean_ctor_set(x_46, 3, x_25);
lean_ctor_set(x_46, 4, x_26);
lean_ctor_set(x_46, 5, x_27);
lean_ctor_set(x_46, 6, x_28);
lean_ctor_set(x_46, 7, x_29);
lean_ctor_set(x_46, 8, x_40);
lean_ctor_set(x_46, 9, x_30);
lean_ctor_set(x_46, 10, x_31);
lean_ctor_set(x_46, 11, x_32);
lean_ctor_set(x_46, 12, x_33);
lean_ctor_set(x_46, 13, x_34);
lean_ctor_set(x_46, 14, x_35);
lean_ctor_set(x_46, 15, x_36);
lean_ctor_set(x_46, 16, x_37);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_41);
x_42 = x_20;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_4);
lean_ctor_set(x_44, 2, x_5);
lean_ctor_set(x_44, 3, x_6);
lean_ctor_set(x_44, 4, x_7);
lean_ctor_set(x_44, 5, x_8);
lean_ctor_set(x_44, 6, x_9);
lean_ctor_set(x_44, 7, x_10);
lean_ctor_set(x_44, 8, x_11);
lean_ctor_set(x_44, 9, x_12);
lean_ctor_set(x_44, 10, x_13);
lean_ctor_set(x_44, 11, x_14);
lean_ctor_set(x_44, 12, x_15);
lean_ctor_set(x_44, 13, x_17);
lean_ctor_set(x_44, 14, x_18);
lean_ctor_set_uint8(x_44, sizeof(void*)*15, x_16);
lean_ctor_set_uint8(x_44, sizeof(void*)*15 + 1, x_19);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_57; 
x_14 = lean_ctor_get(x_13, 0);
x_57 = !lean_is_exclusive(x_13);
if (x_57 == 0)
{
x_15 = x_13;
x_16 = x_57;
goto block_56;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_17, 8);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; 
lean_inc_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_19);
x_20 = x_15;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_del_object(x_15);
x_23 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_17, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 3);
lean_inc_ref(x_25);
lean_dec_ref(x_17);
x_26 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__1));
x_27 = lean_box(0);
lean_inc(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
lean_inc_ref(x_28);
x_29 = l_Lean_mkConst(x_26, x_28);
x_30 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__3));
x_31 = l_Lean_mkConst(x_30, x_28);
lean_inc_ref(x_23);
x_32 = l_Lean_mkAppB(x_31, x_23, x_25);
lean_inc_ref(x_23);
x_33 = l_Lean_mkAppB(x_29, x_23, x_32);
x_34 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__4));
x_35 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__13));
lean_inc(x_2);
x_36 = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9(x_23, x_24, x_34, x_35, x_33, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc(x_37);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___lam__0), 2, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(x_38, x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_46; 
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_39, 0);
lean_dec(x_47);
x_40 = x_39;
x_41 = x_46;
goto block_45;
}
else
{
lean_dec(x_39);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_37);
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_37);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_dec(x_37);
x_48 = lean_ctor_get(x_39, 0);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
x_49 = x_39;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_36;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_58 = lean_ctor_get(x_13, 0);
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
x_59 = x_13;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_13);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec_ref(x_2);
x_16 = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_15);
return x_16;
}
case 1:
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec_ref(x_2);
x_18 = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_28; 
x_19 = lean_ctor_get(x_18, 0);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
x_20 = x_18;
x_21 = x_28;
goto block_27;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_mkNatLit(x_17);
x_23 = l_Lean_Expr_app___override(x_19, x_22);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_23);
x_24 = x_20;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
else
{
lean_dec(x_17);
return x_18;
}
}
case 2:
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_1);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
lean_dec_ref(x_2);
x_30 = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_40; 
x_31 = lean_ctor_get(x_30, 0);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
x_32 = x_30;
x_33 = x_40;
goto block_39;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Lean_mkIntLit(x_29);
lean_dec(x_29);
x_35 = l_Lean_Expr_app___override(x_31, x_34);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_35);
x_36 = x_32;
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
else
{
lean_dec(x_29);
return x_30;
}
}
case 3:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_49; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_41 = lean_ctor_get(x_2, 0);
x_49 = !lean_is_exclusive(x_2);
if (x_49 == 0)
{
x_42 = x_2;
x_43 = x_49;
goto block_48;
}
else
{
lean_inc(x_41);
lean_dec(x_2);
x_42 = lean_box(0);
x_43 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_apply_1(x_1, x_41);
if (x_43 == 0)
{
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_44);
x_45 = x_42;
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
case 4:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_50);
lean_dec_ref(x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_51 = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0(x_1, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_62; 
x_54 = lean_ctor_get(x_53, 0);
x_62 = !lean_is_exclusive(x_53);
if (x_62 == 0)
{
x_55 = x_53;
x_56 = x_62;
goto block_61;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_Expr_app___override(x_52, x_54);
if (x_56 == 0)
{
lean_ctor_set(x_55, 0, x_57);
x_58 = x_55;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_57);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
else
{
lean_dec(x_52);
return x_53;
}
}
else
{
lean_dec_ref(x_50);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_51;
}
}
case 5:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_64);
lean_dec_ref(x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_65 = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0(x_1, x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0(x_1, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_78; 
x_70 = lean_ctor_get(x_69, 0);
x_78 = !lean_is_exclusive(x_69);
if (x_78 == 0)
{
x_71 = x_69;
x_72 = x_78;
goto block_77;
}
else
{
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_box(0);
x_72 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Lean_mkAppB(x_66, x_68, x_70);
if (x_72 == 0)
{
lean_ctor_set(x_71, 0, x_73);
x_74 = x_71;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_73);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
else
{
lean_dec(x_68);
lean_dec(x_66);
return x_69;
}
}
else
{
lean_dec(x_66);
lean_dec_ref(x_64);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_67;
}
}
else
{
lean_dec_ref(x_64);
lean_dec_ref(x_63);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_65;
}
}
case 6:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_80);
lean_dec_ref(x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_81 = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_83 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0(x_1, x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0(x_1, x_80, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_94; 
x_86 = lean_ctor_get(x_85, 0);
x_94 = !lean_is_exclusive(x_85);
if (x_94 == 0)
{
x_87 = x_85;
x_88 = x_94;
goto block_93;
}
else
{
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_box(0);
x_88 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Lean_mkAppB(x_82, x_84, x_86);
if (x_88 == 0)
{
lean_ctor_set(x_87, 0, x_89);
x_90 = x_87;
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
lean_dec(x_84);
lean_dec(x_82);
return x_85;
}
}
else
{
lean_dec(x_82);
lean_dec_ref(x_80);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_83;
}
}
else
{
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_81;
}
}
case 7:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_96);
lean_dec_ref(x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_97 = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_99 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0(x_1, x_95, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0(x_1, x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_110; 
x_102 = lean_ctor_get(x_101, 0);
x_110 = !lean_is_exclusive(x_101);
if (x_110 == 0)
{
x_103 = x_101;
x_104 = x_110;
goto block_109;
}
else
{
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_box(0);
x_104 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_105; lean_object* x_106; 
x_105 = l_Lean_mkAppB(x_98, x_100, x_102);
if (x_104 == 0)
{
lean_ctor_set(x_103, 0, x_105);
x_106 = x_103;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_105);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
else
{
lean_dec(x_100);
lean_dec(x_98);
return x_101;
}
}
else
{
lean_dec(x_98);
lean_dec_ref(x_96);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_99;
}
}
else
{
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_97;
}
}
default: 
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_2, 1);
lean_inc(x_112);
lean_dec_ref(x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_113 = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0(x_1, x_111, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_125; 
x_116 = lean_ctor_get(x_115, 0);
x_125 = !lean_is_exclusive(x_115);
if (x_125 == 0)
{
x_117 = x_115;
x_118 = x_125;
goto block_124;
}
else
{
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_box(0);
x_118 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = l_Lean_mkNatLit(x_112);
x_120 = l_Lean_mkAppB(x_114, x_116, x_119);
if (x_118 == 0)
{
lean_ctor_set(x_117, 0, x_120);
x_121 = x_117;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_120);
x_121 = x_123;
goto block_122;
}
block_122:
{
return x_121;
}
}
}
else
{
lean_dec(x_114);
lean_dec(x_112);
return x_115;
}
}
else
{
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_113;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = l_Lean_instInhabitedExpr;
x_18 = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0(x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_20 = lean_ctor_get(x_14, 0);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
x_21 = x_14;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_297; 
lean_inc_ref(x_3);
x_297 = l_Lean_Meta_Grind_Arith_isArithTerm(x_3);
if (x_297 == 0)
{
uint8_t x_298; 
lean_inc_ref(x_4);
x_298 = l_Lean_Meta_Grind_Arith_isArithTerm(x_4);
if (x_298 == 0)
{
lean_object* x_299; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_299 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
lean_dec_ref(x_299);
x_301 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; uint8_t x_304; uint8_t x_316; 
x_302 = lean_ctor_get(x_301, 0);
x_316 = !lean_is_exclusive(x_301);
if (x_316 == 0)
{
x_303 = x_301;
x_304 = x_316;
goto block_315;
}
else
{
lean_inc(x_302);
lean_dec(x_301);
x_303 = lean_box(0);
x_304 = x_316;
goto block_315;
}
block_315:
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_305 = lean_ctor_get(x_302, 0);
lean_inc_ref(x_305);
lean_dec(x_302);
x_306 = lean_ctor_get(x_305, 3);
lean_inc_ref(x_306);
lean_dec_ref(x_305);
x_307 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_308 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCnstrNorm0(x_1, x_306, x_2, x_3, x_4);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_308);
x_310 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_310, 0, x_3);
lean_ctor_set(x_310, 1, x_4);
lean_ctor_set(x_310, 2, x_307);
lean_ctor_set(x_310, 3, x_300);
lean_ctor_set(x_310, 4, x_309);
lean_ctor_set_uint8(x_310, sizeof(void*)*5, x_2);
x_311 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_311, 0, x_310);
if (x_304 == 0)
{
lean_ctor_set(x_303, 0, x_311);
x_312 = x_303;
goto block_313;
}
else
{
lean_object* x_314; 
x_314 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_314, 0, x_311);
x_312 = x_314;
goto block_313;
}
block_313:
{
return x_312;
}
}
}
else
{
lean_object* x_317; lean_object* x_318; uint8_t x_319; uint8_t x_324; 
lean_dec(x_300);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_317 = lean_ctor_get(x_301, 0);
x_324 = !lean_is_exclusive(x_301);
if (x_324 == 0)
{
x_318 = x_301;
x_319 = x_324;
goto block_323;
}
else
{
lean_inc(x_317);
lean_dec(x_301);
x_318 = lean_box(0);
x_319 = x_324;
goto block_323;
}
block_323:
{
lean_object* x_320; 
if (x_319 == 0)
{
x_320 = x_318;
goto block_321;
}
else
{
lean_object* x_322; 
x_322 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_322, 0, x_317);
x_320 = x_322;
goto block_321;
}
block_321:
{
return x_320;
}
}
}
}
else
{
lean_object* x_325; lean_object* x_326; uint8_t x_327; uint8_t x_332; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_325 = lean_ctor_get(x_299, 0);
x_332 = !lean_is_exclusive(x_299);
if (x_332 == 0)
{
x_326 = x_299;
x_327 = x_332;
goto block_331;
}
else
{
lean_inc(x_325);
lean_dec(x_299);
x_326 = lean_box(0);
x_327 = x_332;
goto block_331;
}
block_331:
{
lean_object* x_328; 
if (x_327 == 0)
{
x_328 = x_326;
goto block_329;
}
else
{
lean_object* x_330; 
x_330 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_330, 0, x_325);
x_328 = x_330;
goto block_329;
}
block_329:
{
return x_328;
}
}
}
}
else
{
goto block_296;
}
}
else
{
goto block_296;
}
block_55:
{
lean_object* x_34; 
x_34 = l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0(x_18, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_46; 
x_35 = lean_ctor_get(x_34, 0);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
x_36 = x_34;
x_37 = x_46;
goto block_45;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_inc_ref(x_17);
x_38 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel(x_1, x_2, x_17, x_35);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_21);
x_40 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_40, 0, x_17);
lean_ctor_set(x_40, 1, x_19);
lean_ctor_set(x_40, 2, x_20);
lean_ctor_set(x_40, 3, x_38);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*5, x_2);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_41);
x_42 = x_36;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_1);
x_47 = lean_ctor_get(x_34, 0);
x_54 = !lean_is_exclusive(x_34);
if (x_54 == 0)
{
x_48 = x_34;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_34);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
block_78:
{
lean_object* x_68; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_62);
x_68 = l_Lean_Meta_Grind_Arith_CommRing_mkLeIffProof(x_65, x_58, x_63, x_67, x_57, x_56, x_61, x_62, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_17 = x_59;
x_18 = x_62;
x_19 = x_64;
x_20 = x_66;
x_21 = x_69;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_11;
x_29 = x_12;
x_30 = x_13;
x_31 = x_14;
x_32 = x_15;
x_33 = lean_box(0);
goto block_55;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_77; 
lean_dec(x_66);
lean_dec_ref(x_64);
lean_dec_ref(x_62);
lean_dec_ref(x_59);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_70 = lean_ctor_get(x_68, 0);
x_77 = !lean_is_exclusive(x_68);
if (x_77 == 0)
{
x_71 = x_68;
x_72 = x_77;
goto block_76;
}
else
{
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_box(0);
x_72 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_73; 
if (x_72 == 0)
{
x_73 = x_71;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_70);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
block_94:
{
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3);
x_92 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel_spec__0(x_91);
x_56 = x_80;
x_57 = x_79;
x_58 = x_90;
x_59 = x_81;
x_60 = lean_box(0);
x_61 = x_83;
x_62 = x_85;
x_63 = x_84;
x_64 = x_87;
x_65 = x_86;
x_66 = x_88;
x_67 = x_92;
goto block_78;
}
else
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
lean_dec_ref(x_89);
x_56 = x_80;
x_57 = x_79;
x_58 = x_90;
x_59 = x_81;
x_60 = lean_box(0);
x_61 = x_83;
x_62 = x_85;
x_63 = x_84;
x_64 = x_87;
x_65 = x_86;
x_66 = x_88;
x_67 = x_93;
goto block_78;
}
}
block_118:
{
lean_object* x_108; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_101);
x_108 = l_Lean_Meta_Grind_Arith_CommRing_mkLtIffProof(x_106, x_105, x_98, x_103, x_107, x_96, x_95, x_100, x_101, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_17 = x_97;
x_18 = x_101;
x_19 = x_102;
x_20 = x_104;
x_21 = x_109;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_11;
x_29 = x_12;
x_30 = x_13;
x_31 = x_14;
x_32 = x_15;
x_33 = lean_box(0);
goto block_55;
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_117; 
lean_dec(x_104);
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_97);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_110 = lean_ctor_get(x_108, 0);
x_117 = !lean_is_exclusive(x_108);
if (x_117 == 0)
{
x_111 = x_108;
x_112 = x_117;
goto block_116;
}
else
{
lean_inc(x_110);
lean_dec(x_108);
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
block_135:
{
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3);
x_133 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel_spec__0(x_132);
x_95 = x_120;
x_96 = x_119;
x_97 = x_121;
x_98 = x_131;
x_99 = lean_box(0);
x_100 = x_123;
x_101 = x_124;
x_102 = x_126;
x_103 = x_125;
x_104 = x_128;
x_105 = x_127;
x_106 = x_130;
x_107 = x_133;
goto block_118;
}
else
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_129, 0);
lean_inc(x_134);
lean_dec_ref(x_129);
x_95 = x_120;
x_96 = x_119;
x_97 = x_121;
x_98 = x_131;
x_99 = lean_box(0);
x_100 = x_123;
x_101 = x_124;
x_102 = x_126;
x_103 = x_125;
x_104 = x_128;
x_105 = x_127;
x_106 = x_130;
x_107 = x_134;
goto block_118;
}
}
block_152:
{
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3);
x_150 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel_spec__0(x_149);
x_119 = x_137;
x_120 = x_136;
x_121 = x_138;
x_122 = lean_box(0);
x_123 = x_140;
x_124 = x_141;
x_125 = x_143;
x_126 = x_142;
x_127 = x_148;
x_128 = x_144;
x_129 = x_145;
x_130 = x_147;
x_131 = x_150;
goto block_135;
}
else
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_146, 0);
lean_inc(x_151);
lean_dec_ref(x_146);
x_119 = x_137;
x_120 = x_136;
x_121 = x_138;
x_122 = lean_box(0);
x_123 = x_140;
x_124 = x_141;
x_125 = x_143;
x_126 = x_142;
x_127 = x_148;
x_128 = x_144;
x_129 = x_145;
x_130 = x_147;
x_131 = x_151;
goto block_135;
}
}
block_296:
{
uint8_t x_153; lean_object* x_154; lean_object* x_155; 
x_153 = 0;
x_154 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_155 = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(x_3, x_153, x_154, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_287; 
x_156 = lean_ctor_get(x_155, 0);
x_287 = !lean_is_exclusive(x_155);
if (x_287 == 0)
{
x_157 = x_155;
x_158 = x_287;
goto block_286;
}
else
{
lean_inc(x_156);
lean_dec(x_155);
x_157 = lean_box(0);
x_158 = x_287;
goto block_286;
}
block_286:
{
if (lean_obj_tag(x_156) == 1)
{
lean_object* x_159; lean_object* x_160; 
lean_del_object(x_157);
x_159 = lean_ctor_get(x_156, 0);
lean_inc(x_159);
lean_dec_ref(x_156);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_160 = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(x_4, x_153, x_154, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_273; 
x_161 = lean_ctor_get(x_160, 0);
x_273 = !lean_is_exclusive(x_160);
if (x_273 == 0)
{
x_162 = x_160;
x_163 = x_273;
goto block_272;
}
else
{
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_box(0);
x_163 = x_273;
goto block_272;
}
block_272:
{
if (lean_obj_tag(x_161) == 1)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_del_object(x_162);
x_164 = lean_ctor_get(x_161, 0);
lean_inc(x_164);
lean_dec_ref(x_161);
lean_inc(x_164);
lean_inc(x_159);
x_165 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_165, 0, x_159);
lean_ctor_set(x_165, 1, x_164);
lean_inc_ref(x_14);
x_166 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_165, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_259; 
x_167 = lean_ctor_get(x_166, 0);
x_259 = !lean_is_exclusive(x_166);
if (x_259 == 0)
{
x_168 = x_166;
x_169 = x_259;
goto block_258;
}
else
{
lean_inc(x_167);
lean_dec(x_166);
x_168 = lean_box(0);
x_169 = x_259;
goto block_258;
}
block_258:
{
if (lean_obj_tag(x_167) == 1)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_253; 
lean_del_object(x_168);
x_170 = lean_ctor_get(x_167, 0);
x_253 = !lean_is_exclusive(x_167);
if (x_253 == 0)
{
x_171 = x_167;
x_172 = x_253;
goto block_252;
}
else
{
lean_inc(x_170);
lean_dec(x_167);
x_171 = lean_box(0);
x_172 = x_253;
goto block_252;
}
block_252:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_251; 
x_173 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split(x_170);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
lean_dec_ref(x_173);
x_176 = lean_ctor_get(x_174, 0);
x_177 = lean_ctor_get(x_174, 1);
x_251 = !lean_is_exclusive(x_174);
if (x_251 == 0)
{
x_178 = x_174;
x_179 = x_251;
goto block_250;
}
else
{
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_174);
x_178 = lean_box(0);
x_179 = x_251;
goto block_250;
}
block_250:
{
lean_object* x_180; lean_object* x_181; 
x_180 = l_Lean_Grind_CommRing_Poly_toExpr(x_175);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_180);
x_181 = l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0(x_180, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec_ref(x_181);
x_183 = l_Lean_Meta_Sym_shareCommon___redArg(x_182, x_11);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
x_185 = l_Lean_Grind_CommRing_Poly_toExpr(x_176);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_185);
x_186 = l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0(x_185, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
lean_dec_ref(x_186);
x_188 = l_Lean_Meta_Sym_shareCommon___redArg(x_187, x_11);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
lean_dec_ref(x_188);
lean_inc(x_177);
if (x_172 == 0)
{
lean_ctor_set_tag(x_171, 2);
lean_ctor_set(x_171, 0, x_177);
x_190 = x_171;
goto block_216;
}
else
{
lean_object* x_217; 
x_217 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_217, 0, x_177);
x_190 = x_217;
goto block_216;
}
block_216:
{
lean_object* x_191; 
if (x_179 == 0)
{
lean_ctor_set_tag(x_178, 5);
lean_ctor_set(x_178, 1, x_190);
lean_ctor_set(x_178, 0, x_185);
x_191 = x_178;
goto block_214;
}
else
{
lean_object* x_215; 
x_215 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_215, 0, x_185);
lean_ctor_set(x_215, 1, x_190);
x_191 = x_215;
goto block_214;
}
block_214:
{
if (x_2 == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_1, 5);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_193 = lean_ctor_get(x_1, 3);
x_194 = lean_ctor_get(x_1, 4);
x_195 = lean_ctor_get(x_1, 11);
x_196 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3);
x_197 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel_spec__0(x_196);
lean_inc(x_195);
lean_inc_ref(x_194);
lean_inc_ref(x_193);
x_79 = x_159;
x_80 = x_164;
x_81 = x_184;
x_82 = lean_box(0);
x_83 = x_180;
x_84 = x_193;
x_85 = x_191;
x_86 = x_194;
x_87 = x_189;
x_88 = x_177;
x_89 = x_195;
x_90 = x_197;
goto block_94;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_1, 3);
x_199 = lean_ctor_get(x_1, 4);
x_200 = lean_ctor_get(x_1, 11);
x_201 = lean_ctor_get(x_192, 0);
lean_inc(x_201);
lean_inc(x_200);
lean_inc_ref(x_199);
lean_inc_ref(x_198);
x_79 = x_159;
x_80 = x_164;
x_81 = x_184;
x_82 = lean_box(0);
x_83 = x_180;
x_84 = x_198;
x_85 = x_191;
x_86 = x_199;
x_87 = x_189;
x_88 = x_177;
x_89 = x_200;
x_90 = x_201;
goto block_94;
}
}
else
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_1, 5);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_203 = lean_ctor_get(x_1, 3);
x_204 = lean_ctor_get(x_1, 4);
x_205 = lean_ctor_get(x_1, 8);
x_206 = lean_ctor_get(x_1, 11);
x_207 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3);
x_208 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel_spec__0(x_207);
lean_inc_ref(x_204);
lean_inc(x_205);
lean_inc(x_206);
lean_inc_ref(x_203);
x_136 = x_164;
x_137 = x_159;
x_138 = x_184;
x_139 = lean_box(0);
x_140 = x_180;
x_141 = x_191;
x_142 = x_189;
x_143 = x_203;
x_144 = x_177;
x_145 = x_206;
x_146 = x_205;
x_147 = x_204;
x_148 = x_208;
goto block_152;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_209 = lean_ctor_get(x_1, 3);
x_210 = lean_ctor_get(x_1, 4);
x_211 = lean_ctor_get(x_1, 8);
x_212 = lean_ctor_get(x_1, 11);
x_213 = lean_ctor_get(x_202, 0);
lean_inc(x_213);
lean_inc_ref(x_210);
lean_inc(x_211);
lean_inc(x_212);
lean_inc_ref(x_209);
x_136 = x_164;
x_137 = x_159;
x_138 = x_184;
x_139 = lean_box(0);
x_140 = x_180;
x_141 = x_191;
x_142 = x_189;
x_143 = x_209;
x_144 = x_177;
x_145 = x_212;
x_146 = x_211;
x_147 = x_210;
x_148 = x_213;
goto block_152;
}
}
}
}
}
else
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; uint8_t x_225; 
lean_dec_ref(x_185);
lean_dec(x_184);
lean_dec_ref(x_180);
lean_del_object(x_178);
lean_dec(x_177);
lean_del_object(x_171);
lean_dec(x_164);
lean_dec(x_159);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_218 = lean_ctor_get(x_188, 0);
x_225 = !lean_is_exclusive(x_188);
if (x_225 == 0)
{
x_219 = x_188;
x_220 = x_225;
goto block_224;
}
else
{
lean_inc(x_218);
lean_dec(x_188);
x_219 = lean_box(0);
x_220 = x_225;
goto block_224;
}
block_224:
{
lean_object* x_221; 
if (x_220 == 0)
{
x_221 = x_219;
goto block_222;
}
else
{
lean_object* x_223; 
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_218);
x_221 = x_223;
goto block_222;
}
block_222:
{
return x_221;
}
}
}
}
else
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_233; 
lean_dec_ref(x_185);
lean_dec(x_184);
lean_dec_ref(x_180);
lean_del_object(x_178);
lean_dec(x_177);
lean_del_object(x_171);
lean_dec(x_164);
lean_dec(x_159);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_226 = lean_ctor_get(x_186, 0);
x_233 = !lean_is_exclusive(x_186);
if (x_233 == 0)
{
x_227 = x_186;
x_228 = x_233;
goto block_232;
}
else
{
lean_inc(x_226);
lean_dec(x_186);
x_227 = lean_box(0);
x_228 = x_233;
goto block_232;
}
block_232:
{
lean_object* x_229; 
if (x_228 == 0)
{
x_229 = x_227;
goto block_230;
}
else
{
lean_object* x_231; 
x_231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_231, 0, x_226);
x_229 = x_231;
goto block_230;
}
block_230:
{
return x_229;
}
}
}
}
else
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; uint8_t x_241; 
lean_dec_ref(x_180);
lean_del_object(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_del_object(x_171);
lean_dec(x_164);
lean_dec(x_159);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_234 = lean_ctor_get(x_183, 0);
x_241 = !lean_is_exclusive(x_183);
if (x_241 == 0)
{
x_235 = x_183;
x_236 = x_241;
goto block_240;
}
else
{
lean_inc(x_234);
lean_dec(x_183);
x_235 = lean_box(0);
x_236 = x_241;
goto block_240;
}
block_240:
{
lean_object* x_237; 
if (x_236 == 0)
{
x_237 = x_235;
goto block_238;
}
else
{
lean_object* x_239; 
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_234);
x_237 = x_239;
goto block_238;
}
block_238:
{
return x_237;
}
}
}
}
else
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_249; 
lean_dec_ref(x_180);
lean_del_object(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_del_object(x_171);
lean_dec(x_164);
lean_dec(x_159);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_242 = lean_ctor_get(x_181, 0);
x_249 = !lean_is_exclusive(x_181);
if (x_249 == 0)
{
x_243 = x_181;
x_244 = x_249;
goto block_248;
}
else
{
lean_inc(x_242);
lean_dec(x_181);
x_243 = lean_box(0);
x_244 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_245; 
if (x_244 == 0)
{
x_245 = x_243;
goto block_246;
}
else
{
lean_object* x_247; 
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_242);
x_245 = x_247;
goto block_246;
}
block_246:
{
return x_245;
}
}
}
}
}
}
else
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_167);
lean_dec(x_164);
lean_dec(x_159);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_254 = lean_box(0);
if (x_169 == 0)
{
lean_ctor_set(x_168, 0, x_254);
x_255 = x_168;
goto block_256;
}
else
{
lean_object* x_257; 
x_257 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_257, 0, x_254);
x_255 = x_257;
goto block_256;
}
block_256:
{
return x_255;
}
}
}
}
else
{
lean_object* x_260; lean_object* x_261; uint8_t x_262; uint8_t x_267; 
lean_dec(x_164);
lean_dec(x_159);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_260 = lean_ctor_get(x_166, 0);
x_267 = !lean_is_exclusive(x_166);
if (x_267 == 0)
{
x_261 = x_166;
x_262 = x_267;
goto block_266;
}
else
{
lean_inc(x_260);
lean_dec(x_166);
x_261 = lean_box(0);
x_262 = x_267;
goto block_266;
}
block_266:
{
lean_object* x_263; 
if (x_262 == 0)
{
x_263 = x_261;
goto block_264;
}
else
{
lean_object* x_265; 
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_260);
x_263 = x_265;
goto block_264;
}
block_264:
{
return x_263;
}
}
}
}
else
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_268 = lean_box(0);
if (x_163 == 0)
{
lean_ctor_set(x_162, 0, x_268);
x_269 = x_162;
goto block_270;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_271, 0, x_268);
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
else
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; uint8_t x_281; 
lean_dec(x_159);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_274 = lean_ctor_get(x_160, 0);
x_281 = !lean_is_exclusive(x_160);
if (x_281 == 0)
{
x_275 = x_160;
x_276 = x_281;
goto block_280;
}
else
{
lean_inc(x_274);
lean_dec(x_160);
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
else
{
lean_object* x_282; lean_object* x_283; 
lean_dec(x_156);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_282 = lean_box(0);
if (x_158 == 0)
{
lean_ctor_set(x_157, 0, x_282);
x_283 = x_157;
goto block_284;
}
else
{
lean_object* x_285; 
x_285 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_285, 0, x_282);
x_283 = x_285;
goto block_284;
}
block_284:
{
return x_283;
}
}
}
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; uint8_t x_295; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_288 = lean_ctor_get(x_155, 0);
x_295 = !lean_is_exclusive(x_155);
if (x_295 == 0)
{
x_289 = x_155;
x_290 = x_295;
goto block_294;
}
else
{
lean_inc(x_288);
lean_dec(x_155);
x_289 = lean_box(0);
x_290 = x_295;
goto block_294;
}
block_294:
{
lean_object* x_291; 
if (x_290 == 0)
{
x_291 = x_289;
goto block_292;
}
else
{
lean_object* x_293; 
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_288);
x_291 = x_293;
goto block_292;
}
block_292:
{
return x_291;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_2);
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___redArg(x_2, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15_spec__16(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
x_14 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_1, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_27; 
x_15 = lean_ctor_get(x_14, 0);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
x_16 = x_14;
x_17 = x_27;
goto block_26;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_27;
goto block_26;
}
block_26:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_del_object(x_16);
lean_dec(x_15);
x_22 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___closed__1);
x_23 = l_Lean_indentExpr(x_1);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___redArg(x_24, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_25;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_28 = lean_ctor_get(x_14, 0);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
x_29 = x_14;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_box(0);
lean_inc(x_2);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
lean_inc_ref(x_21);
x_22 = l_Lean_mkConst(x_3, x_21);
lean_inc_ref_n(x_1, 3);
x_23 = l_Lean_mkApp3(x_22, x_1, x_1, x_1);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_24 = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14(x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_25);
lean_inc(x_4);
x_26 = l_Lean_Meta_Grind_Arith_CommRing_checkInst(x_4, x_25, x_5, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_26);
x_27 = l_Lean_mkConst(x_4, x_21);
lean_inc_ref_n(x_1, 2);
x_28 = l_Lean_mkApp4(x_27, x_1, x_1, x_1, x_25);
lean_inc(x_12);
x_29 = lean_grind_canon(x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_Meta_Sym_shareCommon___redArg(x_30, x_12);
lean_dec(x_12);
return x_31;
}
else
{
lean_dec(x_12);
return x_29;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec(x_25);
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_26, 0);
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
x_33 = x_26;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_dec_ref(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_26; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_ctor_get(x_2, 7);
x_10 = lean_ctor_get(x_2, 8);
x_11 = lean_ctor_get(x_2, 9);
x_12 = lean_ctor_get(x_2, 10);
x_13 = lean_ctor_get(x_2, 11);
x_14 = lean_ctor_get(x_2, 12);
x_15 = lean_ctor_get(x_2, 13);
x_16 = lean_ctor_get(x_2, 14);
x_17 = lean_ctor_get(x_2, 15);
x_18 = lean_ctor_get(x_2, 16);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_2, 6);
lean_dec(x_27);
x_19 = x_2;
x_20 = x_26;
goto block_25;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
if (x_20 == 0)
{
lean_ctor_set(x_19, 6, x_21);
x_22 = x_19;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_5);
lean_ctor_set(x_24, 3, x_6);
lean_ctor_set(x_24, 4, x_7);
lean_ctor_set(x_24, 5, x_8);
lean_ctor_set(x_24, 6, x_21);
lean_ctor_set(x_24, 7, x_9);
lean_ctor_set(x_24, 8, x_10);
lean_ctor_set(x_24, 9, x_11);
lean_ctor_set(x_24, 10, x_12);
lean_ctor_set(x_24, 11, x_13);
lean_ctor_set(x_24, 12, x_14);
lean_ctor_set(x_24, 13, x_15);
lean_ctor_set(x_24, 14, x_16);
lean_ctor_set(x_24, 15, x_17);
lean_ctor_set(x_24, 16, x_18);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_56; 
x_14 = lean_ctor_get(x_13, 0);
x_56 = !lean_is_exclusive(x_13);
if (x_56 == 0)
{
x_15 = x_13;
x_16 = x_56;
goto block_55;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 6);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
lean_inc_ref(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_del_object(x_15);
x_22 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_14, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_14, 4);
lean_inc_ref(x_24);
lean_dec(x_14);
x_25 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__1));
x_26 = lean_box(0);
lean_inc(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
lean_inc_ref(x_27);
x_28 = l_Lean_mkConst(x_25, x_27);
x_29 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__4));
x_30 = l_Lean_mkConst(x_29, x_27);
lean_inc_ref(x_22);
x_31 = l_Lean_mkAppB(x_30, x_22, x_24);
lean_inc_ref(x_22);
x_32 = l_Lean_mkAppB(x_28, x_22, x_31);
x_33 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2___closed__5));
x_34 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__16));
lean_inc(x_2);
x_35 = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9(x_22, x_23, x_33, x_34, x_32, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_36);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2___lam__0), 2, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(x_37, x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; uint8_t x_45; 
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_38, 0);
lean_dec(x_46);
x_39 = x_38;
x_40 = x_45;
goto block_44;
}
else
{
lean_dec(x_38);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
lean_ctor_set(x_39, 0, x_36);
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_36);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_36);
x_47 = lean_ctor_get(x_38, 0);
x_54 = !lean_is_exclusive(x_38);
if (x_54 == 0)
{
x_48 = x_38;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_38);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_35;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_ctor_get(x_13, 0);
x_64 = !lean_is_exclusive(x_13);
if (x_64 == 0)
{
x_58 = x_13;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_dec(x_13);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__3___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_26; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_ctor_get(x_2, 6);
x_10 = lean_ctor_get(x_2, 7);
x_11 = lean_ctor_get(x_2, 8);
x_12 = lean_ctor_get(x_2, 9);
x_13 = lean_ctor_get(x_2, 10);
x_14 = lean_ctor_get(x_2, 12);
x_15 = lean_ctor_get(x_2, 13);
x_16 = lean_ctor_get(x_2, 14);
x_17 = lean_ctor_get(x_2, 15);
x_18 = lean_ctor_get(x_2, 16);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_2, 11);
lean_dec(x_27);
x_19 = x_2;
x_20 = x_26;
goto block_25;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
if (x_20 == 0)
{
lean_ctor_set(x_19, 11, x_21);
x_22 = x_19;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_5);
lean_ctor_set(x_24, 3, x_6);
lean_ctor_set(x_24, 4, x_7);
lean_ctor_set(x_24, 5, x_8);
lean_ctor_set(x_24, 6, x_9);
lean_ctor_set(x_24, 7, x_10);
lean_ctor_set(x_24, 8, x_11);
lean_ctor_set(x_24, 9, x_12);
lean_ctor_set(x_24, 10, x_13);
lean_ctor_set(x_24, 11, x_21);
lean_ctor_set(x_24, 12, x_14);
lean_ctor_set(x_24, 13, x_15);
lean_ctor_set(x_24, 14, x_16);
lean_ctor_set(x_24, 15, x_17);
lean_ctor_set(x_24, 16, x_18);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_36; 
x_36 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_98; 
x_37 = lean_ctor_get(x_36, 0);
x_98 = !lean_is_exclusive(x_36);
if (x_98 == 0)
{
x_38 = x_36;
x_39 = x_98;
goto block_97;
}
else
{
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_37, 11);
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_41; lean_object* x_42; 
lean_inc_ref(x_40);
lean_dec(x_37);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_41);
x_42 = x_38;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_del_object(x_38);
x_45 = lean_ctor_get(x_37, 1);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_37, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_37, 3);
lean_inc_ref(x_47);
lean_dec(x_37);
x_48 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__2));
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
lean_inc_ref(x_50);
x_51 = l_Lean_mkConst(x_48, x_50);
lean_inc_ref(x_45);
x_52 = l_Lean_mkAppB(x_51, x_45, x_47);
x_73 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__5));
lean_inc_ref(x_50);
x_74 = l_Lean_mkConst(x_73, x_50);
lean_inc_ref(x_45);
x_75 = l_Lean_Expr_app___override(x_74, x_45);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_76 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_75, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
if (lean_obj_tag(x_77) == 0)
{
x_53 = x_52;
x_54 = x_1;
x_55 = x_2;
x_56 = x_3;
x_57 = x_4;
x_58 = x_5;
x_59 = x_6;
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_10;
x_64 = x_11;
x_65 = lean_box(0);
goto block_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__7));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_78);
x_80 = l_Lean_Meta_Grind_Arith_CommRing_checkInst(x_79, x_78, x_52, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_80) == 0)
{
lean_dec_ref(x_80);
x_53 = x_78;
x_54 = x_1;
x_55 = x_2;
x_56 = x_3;
x_57 = x_4;
x_58 = x_5;
x_59 = x_6;
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_10;
x_64 = x_11;
x_65 = lean_box(0);
goto block_72;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
lean_dec(x_78);
lean_dec_ref(x_50);
lean_dec_ref(x_45);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = lean_ctor_get(x_80, 0);
x_88 = !lean_is_exclusive(x_80);
if (x_88 == 0)
{
x_82 = x_80;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_80);
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
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
lean_dec_ref(x_52);
lean_dec_ref(x_50);
lean_dec_ref(x_45);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_ctor_get(x_76, 0);
x_96 = !lean_is_exclusive(x_76);
if (x_96 == 0)
{
x_90 = x_76;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_dec(x_76);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
block_72:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__3___closed__4));
x_67 = l_Lean_mkConst(x_66, x_50);
x_68 = l_Lean_mkAppB(x_67, x_45, x_53);
lean_inc(x_60);
lean_inc(x_55);
x_69 = lean_grind_canon(x_68, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = l_Lean_Meta_Sym_shareCommon___redArg(x_70, x_60);
lean_dec(x_60);
x_13 = x_54;
x_14 = x_55;
x_15 = x_71;
goto block_35;
}
else
{
lean_dec(x_60);
x_13 = x_54;
x_14 = x_55;
x_15 = x_69;
goto block_35;
}
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_106; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_ctor_get(x_36, 0);
x_106 = !lean_is_exclusive(x_36);
if (x_106 == 0)
{
x_100 = x_36;
x_101 = x_106;
goto block_105;
}
else
{
lean_inc(x_99);
lean_dec(x_36);
x_100 = lean_box(0);
x_101 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_102; 
if (x_101 == 0)
{
x_102 = x_100;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_99);
x_102 = x_104;
goto block_103;
}
block_103:
{
return x_102;
}
}
}
block_35:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__3___lam__0), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(x_17, x_13, x_14);
lean_dec(x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; uint8_t x_25; 
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_19 = x_18;
x_20 = x_25;
goto block_24;
}
else
{
lean_dec(x_18);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_16);
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_16);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec(x_16);
x_27 = lean_ctor_get(x_18, 0);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
x_28 = x_18;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_31; 
x_20 = lean_ctor_get(x_19, 0);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
x_21 = x_19;
x_22 = x_31;
goto block_30;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___redArg___lam__0___closed__0);
x_24 = l_Lean_Expr_app___override(x_20, x_23);
x_25 = l_Lean_mkAppB(x_18, x_4, x_24);
x_26 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel(x_1, x_2, x_3, x_25);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_26);
x_27 = x_21;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_dec(x_18);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_19;
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_2);
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__1));
x_17 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__2);
x_18 = lean_box(0);
lean_inc(x_1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
lean_inc_ref(x_19);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
lean_inc_ref(x_21);
x_22 = l_Lean_mkConst(x_16, x_21);
x_23 = l_Lean_Nat_mkType;
lean_inc_ref_n(x_2, 2);
x_24 = l_Lean_mkApp3(x_22, x_2, x_23, x_2);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_25 = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14(x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__4));
x_28 = l_Lean_mkConst(x_27, x_19);
lean_inc_ref(x_2);
x_29 = l_Lean_mkAppB(x_28, x_2, x_3);
x_30 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__6));
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_26);
x_31 = l_Lean_Meta_Grind_Arith_CommRing_checkInst(x_30, x_26, x_29, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_31);
x_32 = l_Lean_mkConst(x_30, x_21);
lean_inc_ref(x_2);
x_33 = l_Lean_mkApp4(x_32, x_2, x_23, x_2, x_26);
lean_inc(x_10);
x_34 = lean_grind_canon(x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_Meta_Sym_shareCommon___redArg(x_35, x_10);
lean_dec(x_10);
return x_36;
}
else
{
lean_dec(x_10);
return x_34;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_26);
lean_dec_ref(x_21);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_37 = lean_ctor_get(x_31, 0);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
x_38 = x_31;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_26; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_ctor_get(x_2, 6);
x_10 = lean_ctor_get(x_2, 7);
x_11 = lean_ctor_get(x_2, 8);
x_12 = lean_ctor_get(x_2, 9);
x_13 = lean_ctor_get(x_2, 11);
x_14 = lean_ctor_get(x_2, 12);
x_15 = lean_ctor_get(x_2, 13);
x_16 = lean_ctor_get(x_2, 14);
x_17 = lean_ctor_get(x_2, 15);
x_18 = lean_ctor_get(x_2, 16);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_2, 10);
lean_dec(x_27);
x_19 = x_2;
x_20 = x_26;
goto block_25;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
if (x_20 == 0)
{
lean_ctor_set(x_19, 10, x_21);
x_22 = x_19;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_5);
lean_ctor_set(x_24, 3, x_6);
lean_ctor_set(x_24, 4, x_7);
lean_ctor_set(x_24, 5, x_8);
lean_ctor_set(x_24, 6, x_9);
lean_ctor_set(x_24, 7, x_10);
lean_ctor_set(x_24, 8, x_11);
lean_ctor_set(x_24, 9, x_12);
lean_ctor_set(x_24, 10, x_21);
lean_ctor_set(x_24, 11, x_13);
lean_ctor_set(x_24, 12, x_14);
lean_ctor_set(x_24, 13, x_15);
lean_ctor_set(x_24, 14, x_16);
lean_ctor_set(x_24, 15, x_17);
lean_ctor_set(x_24, 16, x_18);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_46; 
x_14 = lean_ctor_get(x_13, 0);
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
x_15 = x_13;
x_16 = x_46;
goto block_45;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 10);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
lean_inc_ref(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_del_object(x_15);
x_22 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_14, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_14, 4);
lean_inc_ref(x_24);
lean_dec(x_14);
lean_inc(x_2);
x_25 = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11(x_23, x_22, x_24, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc(x_26);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6___lam__0), 2, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(x_27, x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; uint8_t x_35; 
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
x_29 = x_28;
x_30 = x_35;
goto block_34;
}
else
{
lean_dec(x_28);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_26);
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_26);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_26);
x_37 = lean_ctor_get(x_28, 0);
x_44 = !lean_is_exclusive(x_28);
if (x_44 == 0)
{
x_38 = x_28;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_25;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_13, 0);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
x_48 = x_13;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_13);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
lean_inc_ref(x_19);
x_20 = l_Lean_mkConst(x_3, x_19);
lean_inc_ref(x_1);
x_21 = l_Lean_Expr_app___override(x_20, x_1);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_22 = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14(x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_23);
lean_inc(x_4);
x_24 = l_Lean_Meta_Grind_Arith_CommRing_checkInst(x_4, x_23, x_5, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_24);
x_25 = l_Lean_mkConst(x_4, x_19);
x_26 = l_Lean_mkAppB(x_25, x_1, x_23);
lean_inc(x_12);
x_27 = lean_grind_canon(x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_Meta_Sym_shareCommon___redArg(x_28, x_12);
lean_dec(x_12);
return x_29;
}
else
{
lean_dec(x_12);
return x_27;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_23);
lean_dec_ref(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_1);
x_30 = lean_ctor_get(x_24, 0);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
x_31 = x_24;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
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
else
{
lean_dec_ref(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3_spec__7___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_26; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_ctor_get(x_2, 6);
x_10 = lean_ctor_get(x_2, 7);
x_11 = lean_ctor_get(x_2, 8);
x_12 = lean_ctor_get(x_2, 10);
x_13 = lean_ctor_get(x_2, 11);
x_14 = lean_ctor_get(x_2, 12);
x_15 = lean_ctor_get(x_2, 13);
x_16 = lean_ctor_get(x_2, 14);
x_17 = lean_ctor_get(x_2, 15);
x_18 = lean_ctor_get(x_2, 16);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_2, 9);
lean_dec(x_27);
x_19 = x_2;
x_20 = x_26;
goto block_25;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
if (x_20 == 0)
{
lean_ctor_set(x_19, 9, x_21);
x_22 = x_19;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_5);
lean_ctor_set(x_24, 3, x_6);
lean_ctor_set(x_24, 4, x_7);
lean_ctor_set(x_24, 5, x_8);
lean_ctor_set(x_24, 6, x_9);
lean_ctor_set(x_24, 7, x_10);
lean_ctor_set(x_24, 8, x_11);
lean_ctor_set(x_24, 9, x_21);
lean_ctor_set(x_24, 10, x_12);
lean_ctor_set(x_24, 11, x_13);
lean_ctor_set(x_24, 12, x_14);
lean_ctor_set(x_24, 13, x_15);
lean_ctor_set(x_24, 14, x_16);
lean_ctor_set(x_24, 15, x_17);
lean_ctor_set(x_24, 16, x_18);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_53; 
x_14 = lean_ctor_get(x_13, 0);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
x_15 = x_13;
x_16 = x_53;
goto block_52;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 9);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
lean_inc_ref(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_del_object(x_15);
x_22 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_14, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_14, 3);
lean_inc_ref(x_24);
lean_dec(x_14);
x_25 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__1));
x_26 = lean_box(0);
lean_inc(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_mkConst(x_25, x_27);
lean_inc_ref(x_22);
x_29 = l_Lean_mkAppB(x_28, x_22, x_24);
x_30 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__3));
x_31 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__5));
lean_inc(x_2);
x_32 = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3_spec__7(x_22, x_23, x_30, x_31, x_29, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
lean_inc(x_33);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3___lam__0), 2, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(x_34, x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; uint8_t x_42; 
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_35, 0);
lean_dec(x_43);
x_36 = x_35;
x_37 = x_42;
goto block_41;
}
else
{
lean_dec(x_35);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_33);
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_33);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
lean_dec(x_33);
x_44 = lean_ctor_get(x_35, 0);
x_51 = !lean_is_exclusive(x_35);
if (x_51 == 0)
{
x_45 = x_35;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_35);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_32;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_ctor_get(x_13, 0);
x_61 = !lean_is_exclusive(x_13);
if (x_61 == 0)
{
x_55 = x_13;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_13);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__4___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_26; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_ctor_get(x_2, 6);
x_10 = lean_ctor_get(x_2, 7);
x_11 = lean_ctor_get(x_2, 9);
x_12 = lean_ctor_get(x_2, 10);
x_13 = lean_ctor_get(x_2, 11);
x_14 = lean_ctor_get(x_2, 12);
x_15 = lean_ctor_get(x_2, 13);
x_16 = lean_ctor_get(x_2, 14);
x_17 = lean_ctor_get(x_2, 15);
x_18 = lean_ctor_get(x_2, 16);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_2, 8);
lean_dec(x_27);
x_19 = x_2;
x_20 = x_26;
goto block_25;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
if (x_20 == 0)
{
lean_ctor_set(x_19, 8, x_21);
x_22 = x_19;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_5);
lean_ctor_set(x_24, 3, x_6);
lean_ctor_set(x_24, 4, x_7);
lean_ctor_set(x_24, 5, x_8);
lean_ctor_set(x_24, 6, x_9);
lean_ctor_set(x_24, 7, x_10);
lean_ctor_set(x_24, 8, x_21);
lean_ctor_set(x_24, 9, x_11);
lean_ctor_set(x_24, 10, x_12);
lean_ctor_set(x_24, 11, x_13);
lean_ctor_set(x_24, 12, x_14);
lean_ctor_set(x_24, 13, x_15);
lean_ctor_set(x_24, 14, x_16);
lean_ctor_set(x_24, 15, x_17);
lean_ctor_set(x_24, 16, x_18);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_56; 
x_14 = lean_ctor_get(x_13, 0);
x_56 = !lean_is_exclusive(x_13);
if (x_56 == 0)
{
x_15 = x_13;
x_16 = x_56;
goto block_55;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 8);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
lean_inc_ref(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_del_object(x_15);
x_22 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_14, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_14, 3);
lean_inc_ref(x_24);
lean_dec(x_14);
x_25 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__1));
x_26 = lean_box(0);
lean_inc(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
lean_inc_ref(x_27);
x_28 = l_Lean_mkConst(x_25, x_27);
x_29 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__3));
x_30 = l_Lean_mkConst(x_29, x_27);
lean_inc_ref(x_22);
x_31 = l_Lean_mkAppB(x_30, x_22, x_24);
lean_inc_ref(x_22);
x_32 = l_Lean_mkAppB(x_28, x_22, x_31);
x_33 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__4___closed__4));
x_34 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__13));
lean_inc(x_2);
x_35 = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9(x_22, x_23, x_33, x_34, x_32, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_36);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__4___lam__0), 2, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(x_37, x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; uint8_t x_45; 
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_38, 0);
lean_dec(x_46);
x_39 = x_38;
x_40 = x_45;
goto block_44;
}
else
{
lean_dec(x_38);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
lean_ctor_set(x_39, 0, x_36);
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_36);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_36);
x_47 = lean_ctor_get(x_38, 0);
x_54 = !lean_is_exclusive(x_38);
if (x_54 == 0)
{
x_48 = x_38;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_38);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_35;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_ctor_get(x_13, 0);
x_64 = !lean_is_exclusive(x_13);
if (x_64 == 0)
{
x_58 = x_13;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_dec(x_13);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__5___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_26; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_ctor_get(x_2, 6);
x_10 = lean_ctor_get(x_2, 8);
x_11 = lean_ctor_get(x_2, 9);
x_12 = lean_ctor_get(x_2, 10);
x_13 = lean_ctor_get(x_2, 11);
x_14 = lean_ctor_get(x_2, 12);
x_15 = lean_ctor_get(x_2, 13);
x_16 = lean_ctor_get(x_2, 14);
x_17 = lean_ctor_get(x_2, 15);
x_18 = lean_ctor_get(x_2, 16);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_2, 7);
lean_dec(x_27);
x_19 = x_2;
x_20 = x_26;
goto block_25;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
if (x_20 == 0)
{
lean_ctor_set(x_19, 7, x_21);
x_22 = x_19;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_5);
lean_ctor_set(x_24, 3, x_6);
lean_ctor_set(x_24, 4, x_7);
lean_ctor_set(x_24, 5, x_8);
lean_ctor_set(x_24, 6, x_9);
lean_ctor_set(x_24, 7, x_21);
lean_ctor_set(x_24, 8, x_10);
lean_ctor_set(x_24, 9, x_11);
lean_ctor_set(x_24, 10, x_12);
lean_ctor_set(x_24, 11, x_13);
lean_ctor_set(x_24, 12, x_14);
lean_ctor_set(x_24, 13, x_15);
lean_ctor_set(x_24, 14, x_16);
lean_ctor_set(x_24, 15, x_17);
lean_ctor_set(x_24, 16, x_18);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_56; 
x_14 = lean_ctor_get(x_13, 0);
x_56 = !lean_is_exclusive(x_13);
if (x_56 == 0)
{
x_15 = x_13;
x_16 = x_56;
goto block_55;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 7);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
lean_inc_ref(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_del_object(x_15);
x_22 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_14, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_14, 4);
lean_inc_ref(x_24);
lean_dec(x_14);
x_25 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__1));
x_26 = lean_box(0);
lean_inc(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
lean_inc_ref(x_27);
x_28 = l_Lean_mkConst(x_25, x_27);
x_29 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__3));
x_30 = l_Lean_mkConst(x_29, x_27);
lean_inc_ref(x_22);
x_31 = l_Lean_mkAppB(x_30, x_22, x_24);
lean_inc_ref(x_22);
x_32 = l_Lean_mkAppB(x_28, x_22, x_31);
x_33 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__5));
x_34 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5___closed__7));
lean_inc(x_2);
x_35 = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9(x_22, x_23, x_33, x_34, x_32, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_36);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__5___lam__0), 2, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(x_37, x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; uint8_t x_45; 
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_38, 0);
lean_dec(x_46);
x_39 = x_38;
x_40 = x_45;
goto block_44;
}
else
{
lean_dec(x_38);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
lean_ctor_set(x_39, 0, x_36);
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_36);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_36);
x_47 = lean_ctor_get(x_38, 0);
x_54 = !lean_is_exclusive(x_38);
if (x_54 == 0)
{
x_48 = x_38;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_38);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_35;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_ctor_get(x_13, 0);
x_64 = !lean_is_exclusive(x_13);
if (x_64 == 0)
{
x_58 = x_13;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_dec(x_13);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 4);
lean_inc_ref(x_18);
lean_dec(x_15);
x_19 = lean_nat_abs(x_1);
x_20 = l_Lean_mkRawNatLit(x_19);
x_21 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__0));
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
lean_inc_ref(x_23);
x_24 = l_Lean_mkConst(x_21, x_23);
lean_inc_ref(x_20);
lean_inc_ref(x_16);
x_25 = l_Lean_mkAppB(x_24, x_16, x_20);
x_26 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_27 = l_Lean_Meta_synthInstance_x3f(x_25, x_26, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_67; 
x_28 = lean_ctor_get(x_27, 0);
x_67 = !lean_is_exclusive(x_27);
if (x_67 == 0)
{
x_29 = x_27;
x_30 = x_67;
goto block_66;
}
else
{
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_62; 
lean_dec_ref(x_18);
x_62 = lean_ctor_get(x_28, 0);
lean_inc(x_62);
lean_dec_ref(x_28);
x_31 = x_62;
x_32 = x_2;
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_10;
x_41 = x_11;
x_42 = x_12;
goto block_61;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_28);
x_63 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1___closed__1));
lean_inc_ref(x_23);
x_64 = l_Lean_mkConst(x_63, x_23);
lean_inc_ref(x_20);
lean_inc_ref(x_16);
x_65 = l_Lean_mkApp3(x_64, x_16, x_18, x_20);
x_31 = x_65;
x_32 = x_2;
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_10;
x_41 = x_11;
x_42 = x_12;
goto block_61;
}
block_61:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__2));
x_44 = l_Lean_mkConst(x_43, x_23);
x_45 = l_Lean_mkApp3(x_44, x_16, x_20, x_31);
x_46 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0);
x_47 = lean_int_dec_lt(x_1, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_45);
x_48 = x_29;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
else
{
lean_object* x_51; 
lean_del_object(x_29);
x_51 = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3(x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_60; 
x_52 = lean_ctor_get(x_51, 0);
x_60 = !lean_is_exclusive(x_51);
if (x_60 == 0)
{
x_53 = x_51;
x_54 = x_60;
goto block_59;
}
else
{
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_box(0);
x_54 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Lean_Expr_app___override(x_52, x_45);
if (x_54 == 0)
{
lean_ctor_set(x_53, 0, x_55);
x_56 = x_53;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_55);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
else
{
lean_dec_ref(x_45);
return x_51;
}
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_75; 
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_ctor_get(x_27, 0);
x_75 = !lean_is_exclusive(x_27);
if (x_75 == 0)
{
x_69 = x_27;
x_70 = x_75;
goto block_74;
}
else
{
lean_inc(x_68);
lean_dec(x_27);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = lean_ctor_get(x_14, 0);
x_83 = !lean_is_exclusive(x_14);
if (x_83 == 0)
{
x_77 = x_14;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_14);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_26; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_ctor_get(x_2, 6);
x_10 = lean_ctor_get(x_2, 7);
x_11 = lean_ctor_get(x_2, 8);
x_12 = lean_ctor_get(x_2, 9);
x_13 = lean_ctor_get(x_2, 10);
x_14 = lean_ctor_get(x_2, 11);
x_15 = lean_ctor_get(x_2, 13);
x_16 = lean_ctor_get(x_2, 14);
x_17 = lean_ctor_get(x_2, 15);
x_18 = lean_ctor_get(x_2, 16);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_2, 12);
lean_dec(x_27);
x_19 = x_2;
x_20 = x_26;
goto block_25;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
if (x_20 == 0)
{
lean_ctor_set(x_19, 12, x_21);
x_22 = x_19;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_5);
lean_ctor_set(x_24, 3, x_6);
lean_ctor_set(x_24, 4, x_7);
lean_ctor_set(x_24, 5, x_8);
lean_ctor_set(x_24, 6, x_9);
lean_ctor_set(x_24, 7, x_10);
lean_ctor_set(x_24, 8, x_11);
lean_ctor_set(x_24, 9, x_12);
lean_ctor_set(x_24, 10, x_13);
lean_ctor_set(x_24, 11, x_14);
lean_ctor_set(x_24, 12, x_21);
lean_ctor_set(x_24, 13, x_15);
lean_ctor_set(x_24, 14, x_16);
lean_ctor_set(x_24, 15, x_17);
lean_ctor_set(x_24, 16, x_18);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_15 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__0));
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
lean_inc_ref(x_17);
x_18 = l_Lean_mkConst(x_15, x_17);
lean_inc_ref(x_2);
x_19 = l_Lean_mkAppB(x_18, x_2, x_3);
x_39 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___closed__1));
lean_inc_ref(x_17);
x_40 = l_Lean_mkConst(x_39, x_17);
lean_inc_ref(x_2);
x_41 = l_Lean_Expr_app___override(x_40, x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_42 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_41, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
if (lean_obj_tag(x_43) == 0)
{
x_20 = x_19;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_11;
x_29 = x_12;
x_30 = x_13;
x_31 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__8));
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_44);
x_46 = l_Lean_Meta_Grind_Arith_CommRing_checkInst(x_45, x_44, x_19, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_46) == 0)
{
lean_dec_ref(x_46);
x_20 = x_44;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_11;
x_29 = x_12;
x_30 = x_13;
x_31 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_44);
lean_dec_ref(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_47 = lean_ctor_get(x_46, 0);
x_54 = !lean_is_exclusive(x_46);
if (x_54 == 0)
{
x_48 = x_46;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec_ref(x_19);
lean_dec_ref(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_55 = lean_ctor_get(x_42, 0);
x_62 = !lean_is_exclusive(x_42);
if (x_62 == 0)
{
x_56 = x_42;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_42);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
block_38:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__8));
x_33 = l_Lean_mkConst(x_32, x_17);
x_34 = l_Lean_mkAppB(x_33, x_2, x_20);
lean_inc(x_26);
x_35 = lean_grind_canon(x_34, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_Meta_Sym_shareCommon___redArg(x_36, x_26);
lean_dec(x_26);
return x_37;
}
else
{
lean_dec(x_26);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_46; 
x_14 = lean_ctor_get(x_13, 0);
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
x_15 = x_13;
x_16 = x_46;
goto block_45;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 12);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
lean_inc_ref(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_del_object(x_15);
x_22 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_14, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_14, 4);
lean_inc_ref(x_24);
lean_dec(x_14);
lean_inc(x_2);
x_25 = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg(x_23, x_22, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc(x_26);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2___lam__0), 2, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(x_27, x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; uint8_t x_35; 
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
x_29 = x_28;
x_30 = x_35;
goto block_34;
}
else
{
lean_dec(x_28);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_26);
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_26);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_26);
x_37 = lean_ctor_get(x_28, 0);
x_44 = !lean_is_exclusive(x_28);
if (x_44 == 0)
{
x_38 = x_28;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_25;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_13, 0);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
x_48 = x_13;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_13);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec_ref(x_2);
x_16 = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__1(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_15);
return x_16;
}
case 1:
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec_ref(x_2);
x_18 = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_28; 
x_19 = lean_ctor_get(x_18, 0);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
x_20 = x_18;
x_21 = x_28;
goto block_27;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_mkNatLit(x_17);
x_23 = l_Lean_Expr_app___override(x_19, x_22);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_23);
x_24 = x_20;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
else
{
lean_dec(x_17);
return x_18;
}
}
case 2:
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_1);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
lean_dec_ref(x_2);
x_30 = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_40; 
x_31 = lean_ctor_get(x_30, 0);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
x_32 = x_30;
x_33 = x_40;
goto block_39;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Lean_mkIntLit(x_29);
lean_dec(x_29);
x_35 = l_Lean_Expr_app___override(x_31, x_34);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_35);
x_36 = x_32;
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
else
{
lean_dec(x_29);
return x_30;
}
}
case 3:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_49; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = lean_ctor_get(x_2, 0);
x_49 = !lean_is_exclusive(x_2);
if (x_49 == 0)
{
x_42 = x_2;
x_43 = x_49;
goto block_48;
}
else
{
lean_inc(x_41);
lean_dec(x_2);
x_42 = lean_box(0);
x_43 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_apply_1(x_1, x_41);
if (x_43 == 0)
{
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_44);
x_45 = x_42;
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
case 4:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_50);
lean_dec_ref(x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0(x_1, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_62; 
x_54 = lean_ctor_get(x_53, 0);
x_62 = !lean_is_exclusive(x_53);
if (x_62 == 0)
{
x_55 = x_53;
x_56 = x_62;
goto block_61;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_Expr_app___override(x_52, x_54);
if (x_56 == 0)
{
lean_ctor_set(x_55, 0, x_57);
x_58 = x_55;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_57);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
else
{
lean_dec(x_52);
return x_53;
}
}
else
{
lean_dec_ref(x_50);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_51;
}
}
case 5:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_64);
lean_dec_ref(x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_65 = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0(x_1, x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0(x_1, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_78; 
x_70 = lean_ctor_get(x_69, 0);
x_78 = !lean_is_exclusive(x_69);
if (x_78 == 0)
{
x_71 = x_69;
x_72 = x_78;
goto block_77;
}
else
{
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_box(0);
x_72 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Lean_mkAppB(x_66, x_68, x_70);
if (x_72 == 0)
{
lean_ctor_set(x_71, 0, x_73);
x_74 = x_71;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_73);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
else
{
lean_dec(x_68);
lean_dec(x_66);
return x_69;
}
}
else
{
lean_dec(x_66);
lean_dec_ref(x_64);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_67;
}
}
else
{
lean_dec_ref(x_64);
lean_dec_ref(x_63);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_65;
}
}
case 6:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_80);
lean_dec_ref(x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_81 = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__4(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_83 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0(x_1, x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0(x_1, x_80, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_94; 
x_86 = lean_ctor_get(x_85, 0);
x_94 = !lean_is_exclusive(x_85);
if (x_94 == 0)
{
x_87 = x_85;
x_88 = x_94;
goto block_93;
}
else
{
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_box(0);
x_88 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Lean_mkAppB(x_82, x_84, x_86);
if (x_88 == 0)
{
lean_ctor_set(x_87, 0, x_89);
x_90 = x_87;
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
lean_dec(x_84);
lean_dec(x_82);
return x_85;
}
}
else
{
lean_dec(x_82);
lean_dec_ref(x_80);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_83;
}
}
else
{
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_81;
}
}
case 7:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_96);
lean_dec_ref(x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_97 = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__5(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_99 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0(x_1, x_95, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0(x_1, x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_110; 
x_102 = lean_ctor_get(x_101, 0);
x_110 = !lean_is_exclusive(x_101);
if (x_110 == 0)
{
x_103 = x_101;
x_104 = x_110;
goto block_109;
}
else
{
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_box(0);
x_104 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_105; lean_object* x_106; 
x_105 = l_Lean_mkAppB(x_98, x_100, x_102);
if (x_104 == 0)
{
lean_ctor_set(x_103, 0, x_105);
x_106 = x_103;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_105);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
else
{
lean_dec(x_100);
lean_dec(x_98);
return x_101;
}
}
else
{
lean_dec(x_98);
lean_dec_ref(x_96);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_99;
}
}
else
{
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_97;
}
}
default: 
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_2, 1);
lean_inc(x_112);
lean_dec_ref(x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_113 = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0(x_1, x_111, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_125; 
x_116 = lean_ctor_get(x_115, 0);
x_125 = !lean_is_exclusive(x_115);
if (x_125 == 0)
{
x_117 = x_115;
x_118 = x_125;
goto block_124;
}
else
{
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_box(0);
x_118 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = l_Lean_mkNatLit(x_112);
x_120 = l_Lean_mkAppB(x_114, x_116, x_119);
if (x_118 == 0)
{
lean_ctor_set(x_117, 0, x_120);
x_121 = x_117;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_120);
x_121 = x_123;
goto block_122;
}
block_122:
{
return x_121;
}
}
}
else
{
lean_dec(x_114);
lean_dec(x_112);
return x_115;
}
}
else
{
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_113;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 14);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_4, 2);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_4);
x_7 = l_outOfBounds___redArg(x_2);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_get_x21___redArg(x_2, x_4, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_instInhabitedExpr;
x_17 = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0(x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_14, 0);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
x_20 = x_14;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_279; 
lean_inc_ref(x_3);
x_279 = l_Lean_Meta_Grind_Arith_isArithTerm(x_3);
if (x_279 == 0)
{
uint8_t x_280; 
lean_inc_ref(x_4);
x_280 = l_Lean_Meta_Grind_Arith_isArithTerm(x_4);
if (x_280 == 0)
{
lean_object* x_281; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_281 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
lean_dec_ref(x_281);
x_283 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; uint8_t x_286; uint8_t x_297; 
x_284 = lean_ctor_get(x_283, 0);
x_297 = !lean_is_exclusive(x_283);
if (x_297 == 0)
{
x_285 = x_283;
x_286 = x_297;
goto block_296;
}
else
{
lean_inc(x_284);
lean_dec(x_283);
x_285 = lean_box(0);
x_286 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_287 = lean_ctor_get(x_284, 3);
lean_inc_ref(x_287);
lean_dec(x_284);
x_288 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_289 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCnstrNorm0(x_1, x_287, x_2, x_3, x_4);
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_289);
x_291 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_291, 0, x_3);
lean_ctor_set(x_291, 1, x_4);
lean_ctor_set(x_291, 2, x_288);
lean_ctor_set(x_291, 3, x_282);
lean_ctor_set(x_291, 4, x_290);
lean_ctor_set_uint8(x_291, sizeof(void*)*5, x_2);
x_292 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_292, 0, x_291);
if (x_286 == 0)
{
lean_ctor_set(x_285, 0, x_292);
x_293 = x_285;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_295, 0, x_292);
x_293 = x_295;
goto block_294;
}
block_294:
{
return x_293;
}
}
}
else
{
lean_object* x_298; lean_object* x_299; uint8_t x_300; uint8_t x_305; 
lean_dec(x_282);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_298 = lean_ctor_get(x_283, 0);
x_305 = !lean_is_exclusive(x_283);
if (x_305 == 0)
{
x_299 = x_283;
x_300 = x_305;
goto block_304;
}
else
{
lean_inc(x_298);
lean_dec(x_283);
x_299 = lean_box(0);
x_300 = x_305;
goto block_304;
}
block_304:
{
lean_object* x_301; 
if (x_300 == 0)
{
x_301 = x_299;
goto block_302;
}
else
{
lean_object* x_303; 
x_303 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_303, 0, x_298);
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
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_306 = lean_ctor_get(x_281, 0);
x_313 = !lean_is_exclusive(x_281);
if (x_313 == 0)
{
x_307 = x_281;
x_308 = x_313;
goto block_312;
}
else
{
lean_inc(x_306);
lean_dec(x_281);
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
else
{
goto block_278;
}
}
else
{
goto block_278;
}
block_55:
{
lean_object* x_34; 
x_34 = l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0(x_17, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_46; 
x_35 = lean_ctor_get(x_34, 0);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
x_36 = x_34;
x_37 = x_46;
goto block_45;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_inc_ref(x_19);
x_38 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel(x_1, x_2, x_19, x_35);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_21);
x_40 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_40, 0, x_19);
lean_ctor_set(x_40, 1, x_20);
lean_ctor_set(x_40, 2, x_18);
lean_ctor_set(x_40, 3, x_38);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*5, x_2);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_41);
x_42 = x_36;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_1);
x_47 = lean_ctor_get(x_34, 0);
x_54 = !lean_is_exclusive(x_34);
if (x_54 == 0)
{
x_48 = x_34;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_34);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
block_78:
{
lean_object* x_68; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_56);
x_68 = l_Lean_Meta_Grind_Arith_CommRing_mkNonCommLeIffProof(x_63, x_62, x_58, x_67, x_64, x_66, x_61, x_56, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_17 = x_56;
x_18 = x_59;
x_19 = x_60;
x_20 = x_65;
x_21 = x_69;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_11;
x_29 = x_12;
x_30 = x_13;
x_31 = x_14;
x_32 = x_15;
x_33 = lean_box(0);
goto block_55;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_77; 
lean_dec_ref(x_65);
lean_dec_ref(x_60);
lean_dec(x_59);
lean_dec_ref(x_56);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_70 = lean_ctor_get(x_68, 0);
x_77 = !lean_is_exclusive(x_68);
if (x_77 == 0)
{
x_71 = x_68;
x_72 = x_77;
goto block_76;
}
else
{
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_box(0);
x_72 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_73; 
if (x_72 == 0)
{
x_73 = x_71;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_70);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
block_94:
{
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3);
x_92 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel_spec__0(x_91);
x_56 = x_79;
x_57 = lean_box(0);
x_58 = x_80;
x_59 = x_82;
x_60 = x_83;
x_61 = x_84;
x_62 = x_90;
x_63 = x_85;
x_64 = x_86;
x_65 = x_87;
x_66 = x_89;
x_67 = x_92;
goto block_78;
}
else
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_88, 0);
lean_inc(x_93);
lean_dec_ref(x_88);
x_56 = x_79;
x_57 = lean_box(0);
x_58 = x_80;
x_59 = x_82;
x_60 = x_83;
x_61 = x_84;
x_62 = x_90;
x_63 = x_85;
x_64 = x_86;
x_65 = x_87;
x_66 = x_89;
x_67 = x_93;
goto block_78;
}
}
block_118:
{
lean_object* x_108; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_95);
x_108 = l_Lean_Meta_Grind_Arith_CommRing_mkNonCommLtIffProof(x_103, x_100, x_97, x_105, x_107, x_102, x_106, x_101, x_95, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_17 = x_95;
x_18 = x_98;
x_19 = x_99;
x_20 = x_104;
x_21 = x_109;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_11;
x_29 = x_12;
x_30 = x_13;
x_31 = x_14;
x_32 = x_15;
x_33 = lean_box(0);
goto block_55;
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_117; 
lean_dec_ref(x_104);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec_ref(x_95);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_110 = lean_ctor_get(x_108, 0);
x_117 = !lean_is_exclusive(x_108);
if (x_117 == 0)
{
x_111 = x_108;
x_112 = x_117;
goto block_116;
}
else
{
lean_inc(x_110);
lean_dec(x_108);
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
block_135:
{
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3);
x_133 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel_spec__0(x_132);
x_95 = x_119;
x_96 = lean_box(0);
x_97 = x_131;
x_98 = x_121;
x_99 = x_124;
x_100 = x_123;
x_101 = x_125;
x_102 = x_126;
x_103 = x_127;
x_104 = x_129;
x_105 = x_128;
x_106 = x_130;
x_107 = x_133;
goto block_118;
}
else
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_122, 0);
lean_inc(x_134);
lean_dec_ref(x_122);
x_95 = x_119;
x_96 = lean_box(0);
x_97 = x_131;
x_98 = x_121;
x_99 = x_124;
x_100 = x_123;
x_101 = x_125;
x_102 = x_126;
x_103 = x_127;
x_104 = x_129;
x_105 = x_128;
x_106 = x_130;
x_107 = x_134;
goto block_118;
}
}
block_152:
{
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3);
x_150 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel_spec__0(x_149);
x_119 = x_136;
x_120 = lean_box(0);
x_121 = x_138;
x_122 = x_139;
x_123 = x_148;
x_124 = x_140;
x_125 = x_142;
x_126 = x_143;
x_127 = x_144;
x_128 = x_146;
x_129 = x_145;
x_130 = x_147;
x_131 = x_150;
goto block_135;
}
else
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_141, 0);
lean_inc(x_151);
lean_dec_ref(x_141);
x_119 = x_136;
x_120 = lean_box(0);
x_121 = x_138;
x_122 = x_139;
x_123 = x_148;
x_124 = x_140;
x_125 = x_142;
x_126 = x_143;
x_127 = x_144;
x_128 = x_146;
x_129 = x_145;
x_130 = x_147;
x_131 = x_151;
goto block_135;
}
}
block_278:
{
uint8_t x_153; lean_object* x_154; lean_object* x_155; 
x_153 = 0;
x_154 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_155 = l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(x_3, x_153, x_154, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_269; 
x_156 = lean_ctor_get(x_155, 0);
x_269 = !lean_is_exclusive(x_155);
if (x_269 == 0)
{
x_157 = x_155;
x_158 = x_269;
goto block_268;
}
else
{
lean_inc(x_156);
lean_dec(x_155);
x_157 = lean_box(0);
x_158 = x_269;
goto block_268;
}
block_268:
{
if (lean_obj_tag(x_156) == 1)
{
lean_object* x_159; lean_object* x_160; 
lean_del_object(x_157);
x_159 = lean_ctor_get(x_156, 0);
lean_inc(x_159);
lean_dec_ref(x_156);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_160 = l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(x_4, x_153, x_154, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_255; 
x_161 = lean_ctor_get(x_160, 0);
x_255 = !lean_is_exclusive(x_160);
if (x_255 == 0)
{
x_162 = x_160;
x_163 = x_255;
goto block_254;
}
else
{
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_box(0);
x_163 = x_255;
goto block_254;
}
block_254:
{
if (lean_obj_tag(x_161) == 1)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; uint8_t x_249; 
lean_del_object(x_162);
x_164 = lean_ctor_get(x_161, 0);
x_249 = !lean_is_exclusive(x_161);
if (x_249 == 0)
{
x_165 = x_161;
x_166 = x_249;
goto block_248;
}
else
{
lean_inc(x_164);
lean_dec(x_161);
x_165 = lean_box(0);
x_166 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_247; 
lean_inc(x_164);
lean_inc(x_159);
x_167 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_167, 0, x_159);
lean_ctor_set(x_167, 1, x_164);
x_168 = l_Lean_Grind_CommRing_Expr_toPoly__nc(x_167);
x_169 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split(x_168);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
lean_dec_ref(x_169);
x_172 = lean_ctor_get(x_170, 0);
x_173 = lean_ctor_get(x_170, 1);
x_247 = !lean_is_exclusive(x_170);
if (x_247 == 0)
{
x_174 = x_170;
x_175 = x_247;
goto block_246;
}
else
{
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_170);
x_174 = lean_box(0);
x_175 = x_247;
goto block_246;
}
block_246:
{
lean_object* x_176; lean_object* x_177; 
x_176 = l_Lean_Grind_CommRing_Poly_toExpr(x_171);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_176);
x_177 = l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0(x_176, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = l_Lean_Meta_Sym_shareCommon___redArg(x_178, x_11);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec_ref(x_179);
x_181 = l_Lean_Grind_CommRing_Poly_toExpr(x_172);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_181);
x_182 = l_Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0(x_181, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec_ref(x_182);
x_184 = l_Lean_Meta_Sym_shareCommon___redArg(x_183, x_11);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
lean_inc(x_173);
if (x_166 == 0)
{
lean_ctor_set_tag(x_165, 2);
lean_ctor_set(x_165, 0, x_173);
x_186 = x_165;
goto block_212;
}
else
{
lean_object* x_213; 
x_213 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_213, 0, x_173);
x_186 = x_213;
goto block_212;
}
block_212:
{
lean_object* x_187; 
if (x_175 == 0)
{
lean_ctor_set_tag(x_174, 5);
lean_ctor_set(x_174, 1, x_186);
lean_ctor_set(x_174, 0, x_181);
x_187 = x_174;
goto block_210;
}
else
{
lean_object* x_211; 
x_211 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_211, 0, x_181);
lean_ctor_set(x_211, 1, x_186);
x_187 = x_211;
goto block_210;
}
block_210:
{
if (x_2 == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_1, 5);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_1, 3);
x_190 = lean_ctor_get(x_1, 4);
x_191 = lean_ctor_get(x_1, 11);
x_192 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3);
x_193 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel_spec__0(x_192);
lean_inc(x_191);
lean_inc_ref(x_190);
lean_inc_ref(x_189);
x_79 = x_187;
x_80 = x_189;
x_81 = lean_box(0);
x_82 = x_173;
x_83 = x_180;
x_84 = x_176;
x_85 = x_190;
x_86 = x_159;
x_87 = x_185;
x_88 = x_191;
x_89 = x_164;
x_90 = x_193;
goto block_94;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_1, 3);
x_195 = lean_ctor_get(x_1, 4);
x_196 = lean_ctor_get(x_1, 11);
x_197 = lean_ctor_get(x_188, 0);
lean_inc(x_197);
lean_inc(x_196);
lean_inc_ref(x_195);
lean_inc_ref(x_194);
x_79 = x_187;
x_80 = x_194;
x_81 = lean_box(0);
x_82 = x_173;
x_83 = x_180;
x_84 = x_176;
x_85 = x_195;
x_86 = x_159;
x_87 = x_185;
x_88 = x_196;
x_89 = x_164;
x_90 = x_197;
goto block_94;
}
}
else
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_1, 5);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_199 = lean_ctor_get(x_1, 3);
x_200 = lean_ctor_get(x_1, 4);
x_201 = lean_ctor_get(x_1, 8);
x_202 = lean_ctor_get(x_1, 11);
x_203 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel___closed__3);
x_204 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkRel_spec__0(x_203);
lean_inc_ref(x_199);
lean_inc_ref(x_200);
lean_inc(x_201);
lean_inc(x_202);
x_136 = x_187;
x_137 = lean_box(0);
x_138 = x_173;
x_139 = x_202;
x_140 = x_180;
x_141 = x_201;
x_142 = x_176;
x_143 = x_159;
x_144 = x_200;
x_145 = x_185;
x_146 = x_199;
x_147 = x_164;
x_148 = x_204;
goto block_152;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_1, 3);
x_206 = lean_ctor_get(x_1, 4);
x_207 = lean_ctor_get(x_1, 8);
x_208 = lean_ctor_get(x_1, 11);
x_209 = lean_ctor_get(x_198, 0);
lean_inc(x_209);
lean_inc_ref(x_205);
lean_inc_ref(x_206);
lean_inc(x_207);
lean_inc(x_208);
x_136 = x_187;
x_137 = lean_box(0);
x_138 = x_173;
x_139 = x_208;
x_140 = x_180;
x_141 = x_207;
x_142 = x_176;
x_143 = x_159;
x_144 = x_206;
x_145 = x_185;
x_146 = x_205;
x_147 = x_164;
x_148 = x_209;
goto block_152;
}
}
}
}
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_221; 
lean_dec_ref(x_181);
lean_dec(x_180);
lean_dec_ref(x_176);
lean_del_object(x_174);
lean_dec(x_173);
lean_del_object(x_165);
lean_dec(x_164);
lean_dec(x_159);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_214 = lean_ctor_get(x_184, 0);
x_221 = !lean_is_exclusive(x_184);
if (x_221 == 0)
{
x_215 = x_184;
x_216 = x_221;
goto block_220;
}
else
{
lean_inc(x_214);
lean_dec(x_184);
x_215 = lean_box(0);
x_216 = x_221;
goto block_220;
}
block_220:
{
lean_object* x_217; 
if (x_216 == 0)
{
x_217 = x_215;
goto block_218;
}
else
{
lean_object* x_219; 
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_214);
x_217 = x_219;
goto block_218;
}
block_218:
{
return x_217;
}
}
}
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; uint8_t x_229; 
lean_dec_ref(x_181);
lean_dec(x_180);
lean_dec_ref(x_176);
lean_del_object(x_174);
lean_dec(x_173);
lean_del_object(x_165);
lean_dec(x_164);
lean_dec(x_159);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_222 = lean_ctor_get(x_182, 0);
x_229 = !lean_is_exclusive(x_182);
if (x_229 == 0)
{
x_223 = x_182;
x_224 = x_229;
goto block_228;
}
else
{
lean_inc(x_222);
lean_dec(x_182);
x_223 = lean_box(0);
x_224 = x_229;
goto block_228;
}
block_228:
{
lean_object* x_225; 
if (x_224 == 0)
{
x_225 = x_223;
goto block_226;
}
else
{
lean_object* x_227; 
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_222);
x_225 = x_227;
goto block_226;
}
block_226:
{
return x_225;
}
}
}
}
else
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; uint8_t x_237; 
lean_dec_ref(x_176);
lean_del_object(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_del_object(x_165);
lean_dec(x_164);
lean_dec(x_159);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_230 = lean_ctor_get(x_179, 0);
x_237 = !lean_is_exclusive(x_179);
if (x_237 == 0)
{
x_231 = x_179;
x_232 = x_237;
goto block_236;
}
else
{
lean_inc(x_230);
lean_dec(x_179);
x_231 = lean_box(0);
x_232 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_233; 
if (x_232 == 0)
{
x_233 = x_231;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_230);
x_233 = x_235;
goto block_234;
}
block_234:
{
return x_233;
}
}
}
}
else
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; uint8_t x_245; 
lean_dec_ref(x_176);
lean_del_object(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_del_object(x_165);
lean_dec(x_164);
lean_dec(x_159);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_238 = lean_ctor_get(x_177, 0);
x_245 = !lean_is_exclusive(x_177);
if (x_245 == 0)
{
x_239 = x_177;
x_240 = x_245;
goto block_244;
}
else
{
lean_inc(x_238);
lean_dec(x_177);
x_239 = lean_box(0);
x_240 = x_245;
goto block_244;
}
block_244:
{
lean_object* x_241; 
if (x_240 == 0)
{
x_241 = x_239;
goto block_242;
}
else
{
lean_object* x_243; 
x_243 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_243, 0, x_238);
x_241 = x_243;
goto block_242;
}
block_242:
{
return x_241;
}
}
}
}
}
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_250 = lean_box(0);
if (x_163 == 0)
{
lean_ctor_set(x_162, 0, x_250);
x_251 = x_162;
goto block_252;
}
else
{
lean_object* x_253; 
x_253 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_253, 0, x_250);
x_251 = x_253;
goto block_252;
}
block_252:
{
return x_251;
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; uint8_t x_263; 
lean_dec(x_159);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_256 = lean_ctor_get(x_160, 0);
x_263 = !lean_is_exclusive(x_160);
if (x_263 == 0)
{
x_257 = x_160;
x_258 = x_263;
goto block_262;
}
else
{
lean_inc(x_256);
lean_dec(x_160);
x_257 = lean_box(0);
x_258 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_259; 
if (x_258 == 0)
{
x_259 = x_257;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_261, 0, x_256);
x_259 = x_261;
goto block_260;
}
block_260:
{
return x_259;
}
}
}
}
else
{
lean_object* x_264; lean_object* x_265; 
lean_dec(x_156);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_264 = lean_box(0);
if (x_158 == 0)
{
lean_ctor_set(x_157, 0, x_264);
x_265 = x_157;
goto block_266;
}
else
{
lean_object* x_267; 
x_267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_267, 0, x_264);
x_265 = x_267;
goto block_266;
}
block_266:
{
return x_265;
}
}
}
}
else
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; uint8_t x_277; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_270 = lean_ctor_get(x_155, 0);
x_277 = !lean_is_exclusive(x_155);
if (x_277 == 0)
{
x_271 = x_155;
x_272 = x_277;
goto block_276;
}
else
{
lean_inc(x_270);
lean_dec(x_155);
x_271 = lean_box(0);
x_272 = x_277;
goto block_276;
}
block_276:
{
lean_object* x_273; 
if (x_272 == 0)
{
x_273 = x_271;
goto block_274;
}
else
{
lean_object* x_275; 
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_270);
x_273 = x_275;
goto block_274;
}
block_274:
{
return x_273;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_2);
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__2_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___redArg(x_2, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCnstr_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Order_getStruct(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_37; 
x_18 = lean_ctor_get(x_17, 0);
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
x_19 = x_17;
x_20 = x_37;
goto block_36;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 9);
if (lean_obj_tag(x_21) == 1)
{
uint8_t x_22; 
lean_del_object(x_19);
lean_dec_ref(x_1);
x_22 = lean_ctor_get_uint8(x_18, sizeof(void*)*22);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f(x_18, x_2, x_3, x_4, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = 0;
lean_inc(x_25);
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f(x_18, x_2, x_3, x_4, x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_29 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_4);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_1);
lean_ctor_set(x_31, 4, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*5, x_2);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
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
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_38 = lean_ctor_get(x_17, 0);
x_45 = !lean_is_exclusive(x_17);
if (x_45 == 0)
{
x_39 = x_17;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_17);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_2);
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCnstr_x3f(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_30; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
x_7 = x_1;
x_8 = x_30;
goto block_29;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_array_push(x_5, x_3);
x_12 = lean_array_push(x_6, x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_fget_borrowed(x_5, x_2);
x_17 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
if (x_8 == 0)
{
x_18 = x_7;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_array_fset(x_5, x_2, x_3);
x_25 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_24);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__2(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_1;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_50; 
lean_inc_ref(x_6);
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_14 = x_1;
x_15 = x_50;
goto block_49;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_6, x_11);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_11, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_27 = x_16;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_29; 
x_29 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_del_object(x_27);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_25, x_26, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_19 = x_31;
goto block_24;
}
else
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_4);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_19 = x_32;
goto block_24;
}
}
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; 
x_37 = lean_ctor_get(x_16, 0);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
x_38 = x_16;
x_39 = x_47;
goto block_46;
}
else
{
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = x_47;
goto block_46;
}
block_46:
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg(x_37, x_40, x_41, x_4, x_5);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_42);
x_43 = x_38;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
x_19 = x_43;
goto block_24;
}
}
}
default: 
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_19 = x_48;
goto block_24;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_11, x_19);
lean_dec(x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_73; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
x_54 = x_1;
x_55 = x_73;
goto block_72;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_53);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; uint8_t x_58; size_t x_65; uint8_t x_66; 
x_57 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__1___redArg(x_56, x_4, x_5);
x_65 = 7;
x_66 = lean_usize_dec_le(x_65, x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_57);
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_67);
x_58 = x_69;
goto block_64;
}
else
{
x_58 = x_66;
goto block_64;
}
block_64:
{
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_57);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__2);
x_63 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__2___redArg(x_3, x_59, x_60, x_61, x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
return x_63;
}
else
{
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__2___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__2___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_16; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
x_9 = x_3;
x_10 = x_16;
goto block_15;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0___redArg(x_6, x_1, x_2);
if (x_10 == 0)
{
lean_ctor_set(x_9, 2, x_11);
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_7);
lean_ctor_set(x_14, 4, x_8);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Meta_Grind_Order_orderExt;
x_7 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_6, x_5, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId___redArg(x_1, x_2, x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_20; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
x_10 = x_4;
x_11 = x_20;
goto block_19;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_inc_ref(x_3);
x_13 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0___redArg(x_8, x_3, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_2);
x_15 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0___redArg(x_9, x_1, x_14);
if (x_11 == 0)
{
lean_ctor_set(x_10, 4, x_15);
lean_ctor_set(x_10, 3, x_13);
x_16 = x_10;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_7);
lean_ctor_set(x_18, 3, x_13);
lean_ctor_set(x_18, 4, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap___redArg___lam__0), 4, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_1);
x_7 = l_Lean_Meta_Grind_Order_orderExt;
x_8 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_7, x_6, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap___redArg(x_1, x_2, x_3, x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_25; 
x_4 = lean_ctor_get(x_1, 0);
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
x_5 = x_1;
x_6 = x_25;
goto block_24;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_box(2);
x_8 = 5;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get(x_7, x_4, x_11);
lean_dec(x_11);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_del_object(x_5);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_14);
x_17 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
case 1:
{
lean_object* x_20; size_t x_21; 
lean_del_object(x_5);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec_ref(x_12);
x_21 = lean_usize_shift_right(x_2, x_8);
x_1 = x_20;
x_2 = x_21;
goto _start;
}
default: 
{
lean_object* x_23; 
lean_del_object(x_5);
x_23 = lean_box(0);
return x_23;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0_spec__1___redArg(x_26, x_27, x_28, x_3);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_2, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_88; 
x_13 = lean_ctor_get(x_12, 0);
x_88 = !lean_is_exclusive(x_12);
if (x_88 == 0)
{
x_14 = x_12;
x_15 = x_88;
goto block_87;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 4);
lean_inc_ref(x_16);
lean_dec(x_13);
x_17 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0___redArg(x_16, x_1);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_29; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_17, 0);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
x_19 = x_17;
x_20 = x_29;
goto block_28;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_21);
x_22 = x_19;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_21);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_22);
x_23 = x_14;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_30; uint8_t x_31; 
lean_dec(x_17);
lean_del_object(x_14);
lean_inc_ref(x_1);
x_30 = l_Lean_Expr_cleanupAnnotations(x_1);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec_ref(x_30);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc_ref(x_32);
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_34 = l_Lean_Expr_isApp(x_33);
if (x_34 == 0)
{
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Expr_appFnCleanup___redArg(x_33);
x_36 = l_Lean_Expr_isApp(x_35);
if (x_36 == 0)
{
lean_dec_ref(x_35);
lean_dec_ref(x_32);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_35);
x_38 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__8));
x_39 = l_Lean_Expr_isConstOf(x_37, x_38);
lean_dec_ref(x_37);
if (x_39 == 0)
{
lean_dec_ref(x_32);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_40; 
x_40 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_32, x_2);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_78; 
x_41 = lean_ctor_get(x_40, 0);
x_78 = !lean_is_exclusive(x_40);
if (x_78 == 0)
{
x_42 = x_40;
x_43 = x_78;
goto block_77;
}
else
{
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = x_78;
goto block_77;
}
block_77:
{
uint8_t x_44; 
x_44 = lean_unbox(x_41);
lean_dec(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_32);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_45 = lean_box(0);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_45);
x_46 = x_42;
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
else
{
lean_object* x_49; 
lean_del_object(x_42);
lean_inc_ref(x_1);
x_49 = l_Lean_Meta_mkEqRefl(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc_ref(x_32);
x_51 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap___redArg(x_32, x_1, x_50, x_2);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; uint8_t x_59; 
x_59 = !lean_is_exclusive(x_51);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_51, 0);
lean_dec(x_60);
x_52 = x_51;
x_53 = x_59;
goto block_58;
}
else
{
lean_dec(x_51);
x_52 = lean_box(0);
x_53 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_32);
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_54);
x_55 = x_52;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_54);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_dec_ref(x_32);
x_61 = lean_ctor_get(x_51, 0);
x_68 = !lean_is_exclusive(x_51);
if (x_68 == 0)
{
x_62 = x_51;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_51);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_76; 
lean_dec_ref(x_32);
lean_dec_ref(x_1);
x_69 = lean_ctor_get(x_49, 0);
x_76 = !lean_is_exclusive(x_49);
if (x_76 == 0)
{
x_70 = x_49;
x_71 = x_76;
goto block_75;
}
else
{
lean_inc(x_69);
lean_dec(x_49);
x_70 = lean_box(0);
x_71 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_72; 
if (x_71 == 0)
{
x_72 = x_70;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_69);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec_ref(x_32);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_79 = lean_ctor_get(x_40, 0);
x_86 = !lean_is_exclusive(x_40);
if (x_86 == 0)
{
x_80 = x_40;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_40);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
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
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_89 = lean_ctor_get(x_12, 0);
x_96 = !lean_is_exclusive(x_12);
if (x_96 == 0)
{
x_90 = x_12;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_dec(x_12);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg(x_1, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_39; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_ctor_get(x_3, 8);
x_13 = lean_ctor_get(x_3, 9);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*22);
x_15 = lean_ctor_get(x_3, 10);
x_16 = lean_ctor_get(x_3, 11);
x_17 = lean_ctor_get(x_3, 12);
x_18 = lean_ctor_get(x_3, 13);
x_19 = lean_ctor_get(x_3, 14);
x_20 = lean_ctor_get(x_3, 15);
x_21 = lean_ctor_get(x_3, 16);
x_22 = lean_ctor_get(x_3, 17);
x_23 = lean_ctor_get(x_3, 18);
x_24 = lean_ctor_get(x_3, 19);
x_25 = lean_ctor_get(x_3, 20);
x_26 = lean_ctor_get(x_3, 21);
x_39 = !lean_is_exclusive(x_3);
if (x_39 == 0)
{
x_27 = x_3;
x_28 = x_39;
goto block_38;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_27 = lean_box(0);
x_28 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc_ref(x_1);
x_29 = l_Lean_PersistentArray_push___redArg(x_19, x_1);
x_30 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0___redArg(x_20, x_1, x_2);
x_31 = lean_box(0);
x_32 = l_Lean_PersistentArray_push___redArg(x_23, x_31);
x_33 = l_Lean_PersistentArray_push___redArg(x_24, x_31);
x_34 = l_Lean_PersistentArray_push___redArg(x_25, x_31);
if (x_28 == 0)
{
lean_ctor_set(x_27, 20, x_34);
lean_ctor_set(x_27, 19, x_33);
lean_ctor_set(x_27, 18, x_32);
lean_ctor_set(x_27, 15, x_30);
lean_ctor_set(x_27, 14, x_29);
x_35 = x_27;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_5);
lean_ctor_set(x_37, 2, x_6);
lean_ctor_set(x_37, 3, x_7);
lean_ctor_set(x_37, 4, x_8);
lean_ctor_set(x_37, 5, x_9);
lean_ctor_set(x_37, 6, x_10);
lean_ctor_set(x_37, 7, x_11);
lean_ctor_set(x_37, 8, x_12);
lean_ctor_set(x_37, 9, x_13);
lean_ctor_set(x_37, 10, x_15);
lean_ctor_set(x_37, 11, x_16);
lean_ctor_set(x_37, 12, x_17);
lean_ctor_set(x_37, 13, x_18);
lean_ctor_set(x_37, 14, x_29);
lean_ctor_set(x_37, 15, x_30);
lean_ctor_set(x_37, 16, x_21);
lean_ctor_set(x_37, 17, x_22);
lean_ctor_set(x_37, 18, x_32);
lean_ctor_set(x_37, 19, x_33);
lean_ctor_set(x_37, 20, x_34);
lean_ctor_set(x_37, 21, x_26);
lean_ctor_set_uint8(x_37, sizeof(void*)*22, x_14);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2_spec__9_spec__14_spec__15_spec__16(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___closed__2));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_164; 
x_15 = lean_ctor_get(x_14, 0);
x_164 = !lean_is_exclusive(x_14);
if (x_164 == 0)
{
x_16 = x_14;
x_17 = x_164;
goto block_163;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 15);
lean_inc_ref(x_18);
lean_dec(x_15);
x_19 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0___redArg(x_18, x_1);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_20);
x_21 = x_16;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; 
lean_dec(x_19);
lean_del_object(x_16);
x_24 = l_Lean_Meta_Grind_Order_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_154; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__4));
x_27 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg(x_26, x_11);
x_28 = lean_ctor_get(x_25, 14);
lean_inc_ref(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_27, 0);
x_154 = !lean_is_exclusive(x_27);
if (x_154 == 0)
{
x_30 = x_27;
x_31 = x_154;
goto block_153;
}
else
{
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_134; 
x_32 = lean_ctor_get(x_28, 2);
lean_inc(x_32);
lean_dec_ref(x_28);
lean_inc(x_32);
lean_inc_ref(x_1);
x_81 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___lam__0), 3, 2);
lean_closure_set(x_81, 0, x_1);
lean_closure_set(x_81, 1, x_32);
x_134 = lean_unbox(x_29);
lean_dec(x_29);
if (x_134 == 0)
{
lean_del_object(x_30);
x_82 = x_2;
x_83 = x_3;
x_84 = x_4;
x_85 = x_5;
x_86 = x_6;
x_87 = x_7;
x_88 = x_8;
x_89 = x_9;
x_90 = x_10;
x_91 = x_11;
x_92 = x_12;
x_93 = lean_box(0);
goto block_133;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_inc_ref(x_1);
x_135 = l_Lean_MessageData_ofExpr(x_1);
x_136 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__6, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___closed__6);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
lean_inc(x_32);
x_138 = l_Nat_reprFast(x_32);
if (x_31 == 0)
{
lean_ctor_set_tag(x_30, 3);
lean_ctor_set(x_30, 0, x_138);
x_139 = x_30;
goto block_151;
}
else
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_152, 0, x_138);
x_139 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = l_Lean_MessageData_ofFormat(x_139);
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_137);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg(x_26, x_141, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_142) == 0)
{
lean_dec_ref(x_142);
x_82 = x_2;
x_83 = x_3;
x_84 = x_4;
x_85 = x_5;
x_86 = x_6;
x_87 = x_7;
x_88 = x_8;
x_89 = x_9;
x_90 = x_10;
x_91 = x_11;
x_92 = x_12;
x_93 = lean_box(0);
goto block_133;
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_150; 
lean_dec_ref(x_81);
lean_dec(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_143 = lean_ctor_get(x_142, 0);
x_150 = !lean_is_exclusive(x_142);
if (x_150 == 0)
{
x_144 = x_142;
x_145 = x_150;
goto block_149;
}
else
{
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_box(0);
x_145 = x_150;
goto block_149;
}
block_149:
{
lean_object* x_146; 
if (x_145 == 0)
{
x_146 = x_144;
goto block_147;
}
else
{
lean_object* x_148; 
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_143);
x_146 = x_148;
goto block_147;
}
block_147:
{
return x_146;
}
}
}
}
}
block_80:
{
lean_object* x_44; 
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
x_44 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f___redArg(x_1, x_33, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_71; 
x_45 = lean_ctor_get(x_44, 0);
x_71 = !lean_is_exclusive(x_44);
if (x_71 == 0)
{
x_46 = x_44;
x_47 = x_71;
goto block_70;
}
else
{
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = x_71;
goto block_70;
}
block_70:
{
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_del_object(x_46);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec_ref(x_45);
x_49 = l_Lean_Meta_Grind_Order_orderExt;
x_50 = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(x_49, x_48, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; uint8_t x_57; 
x_57 = !lean_is_exclusive(x_50);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_50, 0);
lean_dec(x_58);
x_51 = x_50;
x_52 = x_57;
goto block_56;
}
else
{
lean_dec(x_50);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
lean_ctor_set(x_51, 0, x_32);
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_32);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
lean_dec(x_32);
x_59 = lean_ctor_get(x_50, 0);
x_66 = !lean_is_exclusive(x_50);
if (x_66 == 0)
{
x_60 = x_50;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_dec(x_50);
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
lean_object* x_67; 
lean_dec(x_45);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec(x_33);
if (x_47 == 0)
{
lean_ctor_set(x_46, 0, x_32);
x_67 = x_46;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_32);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
x_72 = lean_ctor_get(x_44, 0);
x_79 = !lean_is_exclusive(x_44);
if (x_79 == 0)
{
x_73 = x_44;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_44);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
block_133:
{
lean_object* x_94; 
lean_inc(x_82);
x_94 = l_Lean_Meta_Grind_Order_modifyStruct___redArg(x_81, x_82, x_83);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
lean_dec_ref(x_94);
lean_inc_ref(x_1);
x_95 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId___redArg(x_1, x_82, x_83);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
lean_dec_ref(x_95);
x_96 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_1, x_83);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
x_33 = x_83;
x_34 = x_84;
x_35 = x_85;
x_36 = x_86;
x_37 = x_87;
x_38 = x_88;
x_39 = x_89;
x_40 = x_90;
x_41 = x_91;
x_42 = x_92;
x_43 = lean_box(0);
goto block_80;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Lean_Meta_Grind_Order_orderExt;
lean_inc(x_92);
lean_inc_ref(x_91);
lean_inc(x_90);
lean_inc_ref(x_89);
lean_inc(x_88);
lean_inc_ref(x_87);
lean_inc(x_86);
lean_inc_ref(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc_ref(x_1);
x_100 = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(x_99, x_1, x_83, x_84, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92);
if (lean_obj_tag(x_100) == 0)
{
lean_dec_ref(x_100);
x_33 = x_83;
x_34 = x_84;
x_35 = x_85;
x_36 = x_86;
x_37 = x_87;
x_38 = x_88;
x_39 = x_89;
x_40 = x_90;
x_41 = x_91;
x_42 = x_92;
x_43 = lean_box(0);
goto block_80;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_108; 
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_32);
lean_dec_ref(x_1);
x_101 = lean_ctor_get(x_100, 0);
x_108 = !lean_is_exclusive(x_100);
if (x_108 == 0)
{
x_102 = x_100;
x_103 = x_108;
goto block_107;
}
else
{
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_box(0);
x_103 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_104; 
if (x_103 == 0)
{
x_104 = x_102;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_116; 
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_32);
lean_dec_ref(x_1);
x_109 = lean_ctor_get(x_96, 0);
x_116 = !lean_is_exclusive(x_96);
if (x_116 == 0)
{
x_110 = x_96;
x_111 = x_116;
goto block_115;
}
else
{
lean_inc(x_109);
lean_dec(x_96);
x_110 = lean_box(0);
x_111 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_112; 
if (x_111 == 0)
{
x_112 = x_110;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_109);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_124; 
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_32);
lean_dec_ref(x_1);
x_117 = lean_ctor_get(x_95, 0);
x_124 = !lean_is_exclusive(x_95);
if (x_124 == 0)
{
x_118 = x_95;
x_119 = x_124;
goto block_123;
}
else
{
lean_inc(x_117);
lean_dec(x_95);
x_118 = lean_box(0);
x_119 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_120; 
if (x_119 == 0)
{
x_120 = x_118;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_117);
x_120 = x_122;
goto block_121;
}
block_121:
{
return x_120;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_132; 
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_32);
lean_dec_ref(x_1);
x_125 = lean_ctor_get(x_94, 0);
x_132 = !lean_is_exclusive(x_94);
if (x_132 == 0)
{
x_126 = x_94;
x_127 = x_132;
goto block_131;
}
else
{
lean_inc(x_125);
lean_dec(x_94);
x_126 = lean_box(0);
x_127 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_128; 
if (x_127 == 0)
{
x_128 = x_126;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_125);
x_128 = x_130;
goto block_129;
}
block_129:
{
return x_128;
}
}
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_162; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_155 = lean_ctor_get(x_24, 0);
x_162 = !lean_is_exclusive(x_24);
if (x_162 == 0)
{
x_156 = x_24;
x_157 = x_162;
goto block_161;
}
else
{
lean_inc(x_155);
lean_dec(x_24);
x_156 = lean_box(0);
x_157 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_158; 
if (x_157 == 0)
{
x_158 = x_156;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_155);
x_158 = x_160;
goto block_159;
}
block_159:
{
return x_158;
}
}
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_172; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_165 = lean_ctor_get(x_14, 0);
x_172 = !lean_is_exclusive(x_14);
if (x_172 == 0)
{
x_166 = x_14;
x_167 = x_172;
goto block_171;
}
else
{
lean_inc(x_165);
lean_dec(x_14);
x_166 = lean_box(0);
x_167 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_168; 
if (x_167 == 0)
{
x_168 = x_166;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_165);
x_168 = x_170;
goto block_169;
}
block_169:
{
return x_168;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg(x_1, x_2, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_array_fget_borrowed(x_1, x_3);
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_nat_dec_eq(x_15, x_18);
if (x_20 == 0)
{
x_5 = x_20;
goto block_11;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_eq(x_16, x_19);
x_5 = x_21;
goto block_11;
}
}
block_11:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_3);
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2_spec__5___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_32; 
x_4 = lean_ctor_get(x_1, 0);
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
x_5 = x_1;
x_6 = x_32;
goto block_31;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_box(2);
x_8 = 5;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get(x_7, x_4, x_11);
lean_dec(x_11);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_nat_dec_eq(x_21, x_23);
lean_dec(x_23);
if (x_25 == 0)
{
lean_dec(x_24);
x_15 = x_25;
goto block_20;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_eq(x_22, x_24);
lean_dec(x_24);
x_15 = x_26;
goto block_20;
}
block_20:
{
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_del_object(x_5);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_14);
x_17 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
case 1:
{
lean_object* x_27; size_t x_28; 
lean_del_object(x_5);
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
lean_dec_ref(x_12);
x_28 = lean_usize_shift_right(x_2, x_8);
x_1 = x_27;
x_2 = x_28;
goto _start;
}
default: 
{
lean_object* x_30; 
lean_del_object(x_5);
x_30 = lean_box(0);
return x_30;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_34);
lean_dec_ref(x_1);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2_spec__5___redArg(x_33, x_34, x_35, x_3);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; size_t x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_uint64_of_nat(x_3);
x_6 = lean_uint64_of_nat(x_4);
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_uint64_to_usize(x_7);
x_9 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2___redArg(x_1, x_8, x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_35; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_35 = !lean_is_exclusive(x_1);
if (x_35 == 0)
{
x_7 = x_1;
x_8 = x_35;
goto block_34;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_35;
goto block_34;
}
block_34:
{
uint8_t x_9; lean_object* x_22; uint8_t x_23; 
x_22 = lean_array_get_size(x_5);
x_23 = lean_nat_dec_lt(x_2, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_del_object(x_7);
lean_dec(x_2);
x_24 = lean_array_push(x_5, x_3);
x_25 = lean_array_push(x_6, x_4);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
x_29 = lean_array_fget_borrowed(x_5, x_2);
x_30 = lean_ctor_get(x_29, 0);
x_31 = lean_ctor_get(x_29, 1);
x_32 = lean_nat_dec_eq(x_27, x_30);
if (x_32 == 0)
{
x_9 = x_32;
goto block_21;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_eq(x_28, x_31);
x_9 = x_33;
goto block_21;
}
}
block_21:
{
if (x_9 == 0)
{
lean_object* x_10; 
if (x_8 == 0)
{
x_10 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fset(x_5, x_2, x_3);
x_17 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_17);
lean_ctor_set(x_7, 0, x_16);
x_18 = x_7;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__1_spec__3___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_1;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_57; 
lean_inc_ref(x_6);
x_57 = !lean_is_exclusive(x_1);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_1, 0);
lean_dec(x_58);
x_14 = x_1;
x_15 = x_57;
goto block_56;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_6, x_11);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_11, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_43; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_43 = !lean_is_exclusive(x_16);
if (x_43 == 0)
{
x_27 = x_16;
x_28 = x_43;
goto block_42;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_43;
goto block_42;
}
block_42:
{
uint8_t x_29; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
x_38 = lean_ctor_get(x_25, 0);
x_39 = lean_ctor_get(x_25, 1);
x_40 = lean_nat_dec_eq(x_36, x_38);
if (x_40 == 0)
{
x_29 = x_40;
goto block_35;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_eq(x_37, x_39);
x_29 = x_41;
goto block_35;
}
block_35:
{
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_del_object(x_27);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_25, x_26, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_19 = x_31;
goto block_24;
}
else
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_4);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_19 = x_32;
goto block_24;
}
}
}
}
}
case 1:
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_54; 
x_44 = lean_ctor_get(x_16, 0);
x_54 = !lean_is_exclusive(x_16);
if (x_54 == 0)
{
x_45 = x_16;
x_46 = x_54;
goto block_53;
}
else
{
lean_inc(x_44);
lean_dec(x_16);
x_45 = lean_box(0);
x_46 = x_54;
goto block_53;
}
block_53:
{
size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_usize_shift_right(x_2, x_7);
x_48 = lean_usize_add(x_3, x_8);
x_49 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___redArg(x_44, x_47, x_48, x_4, x_5);
if (x_46 == 0)
{
lean_ctor_set(x_45, 0, x_49);
x_50 = x_45;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_49);
x_50 = x_52;
goto block_51;
}
block_51:
{
x_19 = x_50;
goto block_24;
}
}
}
default: 
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_4);
lean_ctor_set(x_55, 1, x_5);
x_19 = x_55;
goto block_24;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_11, x_19);
lean_dec(x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_80; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
x_80 = !lean_is_exclusive(x_1);
if (x_80 == 0)
{
x_61 = x_1;
x_62 = x_80;
goto block_79;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_box(0);
x_62 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_63; 
if (x_62 == 0)
{
x_63 = x_61;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_59);
lean_ctor_set(x_78, 1, x_60);
x_63 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_64; uint8_t x_65; size_t x_72; uint8_t x_73; 
x_64 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__1___redArg(x_63, x_4, x_5);
x_72 = 7;
x_73 = lean_usize_dec_le(x_72, x_3);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_64);
x_75 = lean_unsigned_to_nat(4u);
x_76 = lean_nat_dec_lt(x_74, x_75);
lean_dec(x_74);
x_65 = x_76;
goto block_71;
}
else
{
x_65 = x_73;
goto block_71;
}
block_71:
{
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_67);
lean_dec_ref(x_64);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___redArg___closed__0);
x_70 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__2___redArg(x_3, x_66, x_67, x_68, x_69);
lean_dec_ref(x_67);
lean_dec_ref(x_66);
return x_70;
}
else
{
return x_64;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__2___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; lean_object* x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_array_fget_borrowed(x_3, x_4);
x_12 = lean_uint64_of_nat(x_9);
x_13 = lean_uint64_of_nat(x_10);
x_14 = lean_uint64_mix_hash(x_12, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = 5;
x_17 = lean_unsigned_to_nat(1u);
x_18 = 1;
x_19 = lean_usize_sub(x_1, x_18);
x_20 = lean_usize_mul(x_16, x_19);
x_21 = lean_usize_shift_right(x_15, x_20);
x_22 = lean_nat_add(x_4, x_17);
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_8);
x_23 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___redArg(x_5, x_21, x_1, x_8, x_11);
x_4 = x_22;
x_5 = x_23;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__2___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_uint64_of_nat(x_4);
x_7 = lean_uint64_of_nat(x_5);
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = lean_uint64_to_usize(x_8);
x_10 = 1;
x_11 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___redArg(x_1, x_9, x_10, x_2, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_47; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 3);
x_10 = lean_ctor_get(x_5, 4);
x_11 = lean_ctor_get(x_5, 5);
x_12 = lean_ctor_get(x_5, 6);
x_13 = lean_ctor_get(x_5, 7);
x_14 = lean_ctor_get(x_5, 8);
x_15 = lean_ctor_get(x_5, 9);
x_16 = lean_ctor_get_uint8(x_5, sizeof(void*)*22);
x_17 = lean_ctor_get(x_5, 10);
x_18 = lean_ctor_get(x_5, 11);
x_19 = lean_ctor_get(x_5, 12);
x_20 = lean_ctor_get(x_5, 13);
x_21 = lean_ctor_get(x_5, 14);
x_22 = lean_ctor_get(x_5, 15);
x_23 = lean_ctor_get(x_5, 16);
x_24 = lean_ctor_get(x_5, 17);
x_25 = lean_ctor_get(x_5, 18);
x_26 = lean_ctor_get(x_5, 19);
x_27 = lean_ctor_get(x_5, 20);
x_28 = lean_ctor_get(x_5, 21);
x_47 = !lean_is_exclusive(x_5);
if (x_47 == 0)
{
x_29 = x_5;
x_30 = x_47;
goto block_46;
}
else
{
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_29 = lean_box(0);
x_30 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_39; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_31 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0___redArg(x_23, x_1, x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_4);
lean_inc_ref(x_24);
x_39 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1___redArg(x_24, x_32);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_1);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_33 = x_42;
goto block_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_33 = x_45;
goto block_38;
}
block_38:
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0___redArg(x_24, x_32, x_33);
if (x_30 == 0)
{
lean_ctor_set(x_29, 17, x_34);
lean_ctor_set(x_29, 16, x_31);
x_35 = x_29;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(x_37, 0, x_6);
lean_ctor_set(x_37, 1, x_7);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_10);
lean_ctor_set(x_37, 5, x_11);
lean_ctor_set(x_37, 6, x_12);
lean_ctor_set(x_37, 7, x_13);
lean_ctor_set(x_37, 8, x_14);
lean_ctor_set(x_37, 9, x_15);
lean_ctor_set(x_37, 10, x_17);
lean_ctor_set(x_37, 11, x_18);
lean_ctor_set(x_37, 12, x_19);
lean_ctor_set(x_37, 13, x_20);
lean_ctor_set(x_37, 14, x_21);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_31);
lean_ctor_set(x_37, 17, x_34);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_27);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*22, x_16);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_69; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_1);
x_69 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_206; 
x_70 = lean_ctor_get(x_69, 0);
x_206 = !lean_is_exclusive(x_69);
if (x_206 == 0)
{
x_71 = x_69;
x_72 = x_206;
goto block_205;
}
else
{
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_box(0);
x_72 = x_206;
goto block_205;
}
block_205:
{
if (lean_obj_tag(x_70) == 1)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_200; 
lean_del_object(x_71);
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
lean_dec_ref(x_70);
x_165 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__0));
x_166 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__0___redArg(x_165, x_14);
x_167 = lean_ctor_get(x_166, 0);
x_200 = !lean_is_exclusive(x_166);
if (x_200 == 0)
{
x_168 = x_166;
x_169 = x_200;
goto block_199;
}
else
{
lean_inc(x_167);
lean_dec(x_166);
x_168 = lean_box(0);
x_169 = x_200;
goto block_199;
}
block_147:
{
uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_146; 
x_86 = lean_ctor_get_uint8(x_73, sizeof(void*)*5);
x_87 = lean_ctor_get(x_73, 0);
x_88 = lean_ctor_get(x_73, 1);
x_89 = lean_ctor_get(x_73, 2);
x_90 = lean_ctor_get(x_73, 3);
x_91 = lean_ctor_get(x_73, 4);
x_146 = !lean_is_exclusive(x_73);
if (x_146 == 0)
{
x_92 = x_73;
x_93 = x_146;
goto block_145;
}
else
{
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_73);
x_92 = lean_box(0);
x_93 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_94; 
lean_inc(x_84);
lean_inc_ref(x_83);
lean_inc(x_82);
lean_inc_ref(x_81);
lean_inc(x_80);
lean_inc_ref(x_79);
lean_inc(x_78);
lean_inc_ref(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
x_94 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode(x_87, x_74, x_75, x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
lean_inc(x_84);
lean_inc_ref(x_83);
lean_inc(x_82);
lean_inc_ref(x_81);
lean_inc(x_80);
lean_inc_ref(x_79);
lean_inc(x_78);
lean_inc_ref(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
x_96 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode(x_88, x_74, x_75, x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
lean_inc(x_97);
lean_inc(x_95);
if (x_93 == 0)
{
lean_ctor_set(x_92, 1, x_97);
lean_ctor_set(x_92, 0, x_95);
x_98 = x_92;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_128, 0, x_95);
lean_ctor_set(x_128, 1, x_97);
lean_ctor_set(x_128, 2, x_89);
lean_ctor_set(x_128, 3, x_90);
lean_ctor_set(x_128, 4, x_91);
lean_ctor_set_uint8(x_128, sizeof(void*)*5, x_86);
x_98 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_99; uint8_t x_100; 
x_99 = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(x_98);
x_100 = lean_nat_dec_eq(x_95, x_97);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = l_Lean_Meta_Grind_Order_getDist_x3f(x_95, x_97, x_74, x_75, x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
lean_inc(x_97);
lean_inc(x_95);
lean_inc_ref(x_98);
lean_inc_ref(x_1);
x_103 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___lam__0), 5, 4);
lean_closure_set(x_103, 0, x_1);
lean_closure_set(x_103, 1, x_98);
lean_closure_set(x_103, 2, x_95);
lean_closure_set(x_103, 3, x_97);
if (lean_obj_tag(x_102) == 1)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
lean_dec_ref(x_102);
x_105 = l_Lean_Meta_Grind_Order_instDecidableLEWeight(x_104, x_99);
if (x_105 == 0)
{
lean_dec(x_104);
x_28 = x_98;
x_29 = x_103;
x_30 = x_97;
x_31 = x_95;
x_32 = x_99;
x_33 = x_74;
x_34 = x_75;
x_35 = x_76;
x_36 = x_77;
x_37 = x_78;
x_38 = x_79;
x_39 = x_80;
x_40 = x_81;
x_41 = x_82;
x_42 = x_83;
x_43 = x_84;
x_44 = lean_box(0);
goto block_68;
}
else
{
lean_object* x_106; 
lean_dec_ref(x_103);
x_106 = l_Lean_Meta_Grind_Order_propagateEqTrue(x_98, x_1, x_95, x_97, x_104, x_99, x_74, x_75, x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84);
lean_dec_ref(x_99);
lean_dec(x_104);
lean_dec(x_97);
lean_dec(x_95);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; uint8_t x_108; uint8_t x_114; 
x_114 = !lean_is_exclusive(x_106);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_106, 0);
lean_dec(x_115);
x_107 = x_106;
x_108 = x_114;
goto block_113;
}
else
{
lean_dec(x_106);
x_107 = lean_box(0);
x_108 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_box(0);
if (x_108 == 0)
{
lean_ctor_set(x_107, 0, x_109);
x_110 = x_107;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_109);
x_110 = x_112;
goto block_111;
}
block_111:
{
return x_110;
}
}
}
else
{
return x_106;
}
}
}
else
{
lean_dec(x_102);
x_28 = x_98;
x_29 = x_103;
x_30 = x_97;
x_31 = x_95;
x_32 = x_99;
x_33 = x_74;
x_34 = x_75;
x_35 = x_76;
x_36 = x_77;
x_37 = x_78;
x_38 = x_79;
x_39 = x_80;
x_40 = x_81;
x_41 = x_82;
x_42 = x_83;
x_43 = x_84;
x_44 = lean_box(0);
goto block_68;
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_123; 
lean_dec_ref(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_1);
x_116 = lean_ctor_get(x_101, 0);
x_123 = !lean_is_exclusive(x_101);
if (x_123 == 0)
{
x_117 = x_101;
x_118 = x_123;
goto block_122;
}
else
{
lean_inc(x_116);
lean_dec(x_101);
x_117 = lean_box(0);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_119; 
if (x_118 == 0)
{
x_119 = x_117;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_116);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_97);
lean_dec(x_95);
x_124 = l_Lean_Meta_Grind_Order_Weight_isNeg(x_99);
lean_dec_ref(x_99);
if (x_124 == 0)
{
lean_object* x_125; 
x_125 = l_Lean_Meta_Grind_Order_propagateSelfEqTrue(x_98, x_1, x_74, x_75, x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84);
if (lean_obj_tag(x_125) == 0)
{
lean_dec_ref(x_125);
x_17 = lean_box(0);
goto block_20;
}
else
{
return x_125;
}
}
else
{
lean_object* x_126; 
x_126 = l_Lean_Meta_Grind_Order_propagateSelfEqFalse(x_98, x_1, x_74, x_75, x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84);
if (lean_obj_tag(x_126) == 0)
{
lean_dec_ref(x_126);
x_17 = lean_box(0);
goto block_20;
}
else
{
return x_126;
}
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_136; 
lean_dec(x_95);
lean_del_object(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_1);
x_129 = lean_ctor_get(x_96, 0);
x_136 = !lean_is_exclusive(x_96);
if (x_136 == 0)
{
x_130 = x_96;
x_131 = x_136;
goto block_135;
}
else
{
lean_inc(x_129);
lean_dec(x_96);
x_130 = lean_box(0);
x_131 = x_136;
goto block_135;
}
block_135:
{
lean_object* x_132; 
if (x_131 == 0)
{
x_132 = x_130;
goto block_133;
}
else
{
lean_object* x_134; 
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_129);
x_132 = x_134;
goto block_133;
}
block_133:
{
return x_132;
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_144; 
lean_del_object(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_1);
x_137 = lean_ctor_get(x_94, 0);
x_144 = !lean_is_exclusive(x_94);
if (x_144 == 0)
{
x_138 = x_94;
x_139 = x_144;
goto block_143;
}
else
{
lean_inc(x_137);
lean_dec(x_94);
x_138 = lean_box(0);
x_139 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_140; 
if (x_139 == 0)
{
x_140 = x_138;
goto block_141;
}
else
{
lean_object* x_142; 
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_137);
x_140 = x_142;
goto block_141;
}
block_141:
{
return x_140;
}
}
}
}
}
block_164:
{
uint8_t x_160; 
x_160 = lean_ctor_get_uint8(x_151, sizeof(void*)*7 + 2);
if (x_160 == 0)
{
x_74 = x_148;
x_75 = x_149;
x_76 = x_150;
x_77 = x_151;
x_78 = x_152;
x_79 = x_153;
x_80 = x_154;
x_81 = x_155;
x_82 = x_156;
x_83 = x_157;
x_84 = x_158;
x_85 = lean_box(0);
goto block_147;
}
else
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_73, 4);
if (lean_obj_tag(x_161) == 1)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_162);
x_163 = l_Lean_Meta_check(x_162, x_155, x_156, x_157, x_158);
if (lean_obj_tag(x_163) == 0)
{
lean_dec_ref(x_163);
x_74 = x_148;
x_75 = x_149;
x_76 = x_150;
x_77 = x_151;
x_78 = x_152;
x_79 = x_153;
x_80 = x_154;
x_81 = x_155;
x_82 = x_156;
x_83 = x_157;
x_84 = x_158;
x_85 = lean_box(0);
goto block_147;
}
else
{
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_73);
lean_dec_ref(x_1);
return x_163;
}
}
else
{
x_74 = x_148;
x_75 = x_149;
x_76 = x_150;
x_77 = x_151;
x_78 = x_152;
x_79 = x_153;
x_80 = x_154;
x_81 = x_155;
x_82 = x_156;
x_83 = x_157;
x_84 = x_158;
x_85 = lean_box(0);
goto block_147;
}
}
}
block_199:
{
uint8_t x_170; 
x_170 = lean_unbox(x_167);
lean_dec(x_167);
if (x_170 == 0)
{
lean_del_object(x_168);
x_148 = x_5;
x_149 = x_6;
x_150 = x_7;
x_151 = x_8;
x_152 = x_9;
x_153 = x_10;
x_154 = x_11;
x_155 = x_12;
x_156 = x_13;
x_157 = x_14;
x_158 = x_15;
x_159 = lean_box(0);
goto block_164;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_188; uint8_t x_189; 
x_171 = lean_ctor_get(x_73, 0);
x_172 = lean_ctor_get(x_73, 1);
x_173 = lean_ctor_get(x_73, 2);
lean_inc(x_171);
x_174 = l_Lean_MessageData_ofExpr(x_171);
x_175 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__2);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
lean_inc(x_172);
x_177 = l_Lean_MessageData_ofExpr(x_172);
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_175);
x_188 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0);
x_189 = lean_int_dec_lt(x_173, x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_nat_abs(x_173);
x_191 = l_Nat_reprFast(x_190);
x_180 = x_191;
goto block_187;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_192 = lean_nat_abs(x_173);
x_193 = lean_unsigned_to_nat(1u);
x_194 = lean_nat_sub(x_192, x_193);
lean_dec(x_192);
x_195 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___closed__3));
x_196 = lean_nat_add(x_194, x_193);
lean_dec(x_194);
x_197 = l_Nat_reprFast(x_196);
x_198 = lean_string_append(x_195, x_197);
lean_dec_ref(x_197);
x_180 = x_198;
goto block_187;
}
block_187:
{
lean_object* x_181; 
if (x_169 == 0)
{
lean_ctor_set_tag(x_168, 3);
lean_ctor_set(x_168, 0, x_180);
x_181 = x_168;
goto block_185;
}
else
{
lean_object* x_186; 
x_186 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_186, 0, x_180);
x_181 = x_186;
goto block_185;
}
block_185:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = l_Lean_MessageData_ofFormat(x_181);
x_183 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_183, 0, x_179);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_spec__1___redArg(x_165, x_183, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_184) == 0)
{
lean_dec_ref(x_184);
x_148 = x_5;
x_149 = x_6;
x_150 = x_7;
x_151 = x_8;
x_152 = x_9;
x_153 = x_10;
x_154 = x_11;
x_155 = x_12;
x_156 = x_13;
x_157 = x_14;
x_158 = x_15;
x_159 = lean_box(0);
goto block_164;
}
else
{
lean_dec(x_73);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_184;
}
}
}
}
}
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_70);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_201 = lean_box(0);
if (x_72 == 0)
{
lean_ctor_set(x_71, 0, x_201);
x_202 = x_71;
goto block_203;
}
else
{
lean_object* x_204; 
x_204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_204, 0, x_201);
x_202 = x_204;
goto block_203;
}
block_203:
{
return x_202;
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; uint8_t x_214; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_207 = lean_ctor_get(x_69, 0);
x_214 = !lean_is_exclusive(x_69);
if (x_214 == 0)
{
x_208 = x_69;
x_209 = x_214;
goto block_213;
}
else
{
lean_inc(x_207);
lean_dec(x_69);
x_208 = lean_box(0);
x_209 = x_214;
goto block_213;
}
block_213:
{
lean_object* x_210; 
if (x_209 == 0)
{
x_210 = x_208;
goto block_211;
}
else
{
lean_object* x_212; 
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_207);
x_210 = x_212;
goto block_211;
}
block_211:
{
return x_210;
}
}
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
block_27:
{
lean_object* x_25; 
lean_inc(x_22);
x_25 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId___redArg(x_1, x_22, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec_ref(x_25);
x_26 = l_Lean_Meta_Grind_Order_modifyStruct___redArg(x_21, x_22, x_23);
lean_dec(x_23);
return x_26;
}
else
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
return x_25;
}
}
block_68:
{
lean_object* x_45; 
x_45 = l_Lean_Meta_Grind_Order_getDist_x3f(x_30, x_31, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_41, x_42, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
lean_inc_ref(x_32);
x_48 = l_Lean_Meta_Grind_Order_Weight_add(x_47, x_32);
x_49 = l_Lean_Meta_Grind_Order_Weight_isNeg(x_48);
lean_dec_ref(x_48);
if (x_49 == 0)
{
lean_dec(x_47);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_28);
x_21 = x_29;
x_22 = x_33;
x_23 = x_34;
x_24 = lean_box(0);
goto block_27;
}
else
{
lean_object* x_50; 
lean_dec_ref(x_29);
x_50 = l_Lean_Meta_Grind_Order_propagateEqFalse(x_28, x_1, x_30, x_31, x_47, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_41, x_42, x_43);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_47);
lean_dec(x_31);
lean_dec(x_30);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; uint8_t x_58; 
x_58 = !lean_is_exclusive(x_50);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_50, 0);
lean_dec(x_59);
x_51 = x_50;
x_52 = x_58;
goto block_57;
}
else
{
lean_dec(x_50);
x_51 = lean_box(0);
x_52 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_box(0);
if (x_52 == 0)
{
lean_ctor_set(x_51, 0, x_53);
x_54 = x_51;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_53);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
else
{
return x_50;
}
}
}
else
{
lean_dec(x_46);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_28);
x_21 = x_29;
x_22 = x_33;
x_23 = x_34;
x_24 = lean_box(0);
goto block_27;
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_67; 
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_1);
x_60 = lean_ctor_get(x_45, 0);
x_67 = !lean_is_exclusive(x_45);
if (x_67 == 0)
{
x_61 = x_45;
x_62 = x_67;
goto block_66;
}
else
{
lean_inc(x_60);
lean_dec(x_45);
x_61 = lean_box(0);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_62 == 0)
{
x_63 = x_61;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_60);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_2);
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2_spec__5___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__1_spec__2_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr_spec__0_spec__0_spec__1_spec__3___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_46; 
x_15 = lean_ctor_get(x_14, 0);
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
x_16 = x_14;
x_17 = x_46;
goto block_45;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_18, 14);
lean_inc_ref(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec_ref(x_1);
x_40 = lean_ctor_get(x_19, 2);
x_41 = l_Lean_instInhabitedExpr;
x_42 = lean_nat_dec_lt(x_20, x_40);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_20);
lean_dec_ref(x_19);
x_43 = l_outOfBounds___redArg(x_41);
x_22 = x_43;
goto block_39;
}
else
{
lean_object* x_44; 
x_44 = l_Lean_PersistentArray_get_x21___redArg(x_41, x_19, x_20);
lean_dec(x_20);
x_22 = x_44;
goto block_39;
}
block_39:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_dec_eq(x_21, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_del_object(x_16);
x_25 = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_35; 
x_26 = lean_ctor_get(x_25, 0);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
x_27 = x_25;
x_28 = x_35;
goto block_34;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_mkNatLit(x_21);
x_30 = l_Lean_mkAppB(x_26, x_22, x_29);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_30);
x_31 = x_27;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
else
{
lean_dec_ref(x_22);
lean_dec(x_21);
return x_25;
}
}
else
{
lean_object* x_36; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_22);
x_36 = x_16;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_22);
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
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_47 = lean_ctor_get(x_14, 0);
x_54 = !lean_is_exclusive(x_14);
if (x_54 == 0)
{
x_48 = x_14;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_14);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec_ref(x_1);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_18 = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_20 = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1_spec__2(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_mkAppB(x_19, x_2, x_21);
x_1 = x_17;
x_2 = x_22;
goto _start;
}
else
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_20;
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_obj_once(&l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___closed__0, &l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___closed__0);
x_15 = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec_ref(x_1);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_18 = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1_spec__2(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1_spec__3(x_17, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_20;
}
else
{
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_obj_once(&l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___closed__0, &l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___closed__0);
x_16 = lean_int_dec_eq(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_17 = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__5(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_19 = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
x_22 = lean_ctor_get(x_21, 0);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
x_23 = x_21;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_mkAppB(x_18, x_20, x_22);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_25);
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_18);
return x_21;
}
}
else
{
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_19;
}
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_17;
}
}
else
{
lean_object* x_31; 
x_31 = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_36; 
x_15 = lean_ctor_get(x_1, 0);
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
x_16 = x_1;
x_17 = x_36;
goto block_35;
}
else
{
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0);
x_19 = lean_int_dec_eq(x_15, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_del_object(x_16);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_20 = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_31; 
x_23 = lean_ctor_get(x_22, 0);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
x_24 = x_22;
x_25 = x_31;
goto block_30;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_mkAppB(x_21, x_2, x_23);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_26);
x_27 = x_24;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_dec(x_21);
lean_dec_ref(x_2);
return x_22;
}
}
else
{
lean_dec(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_20;
}
}
else
{
lean_object* x_32; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_2);
x_32 = x_16;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_2);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_39);
lean_dec_ref(x_1);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_40 = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__1_spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_42 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0(x_37, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_37);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = l_Lean_mkAppB(x_41, x_2, x_43);
x_1 = x_39;
x_2 = x_44;
goto _start;
}
else
{
lean_dec(x_41);
lean_dec_ref(x_39);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_42;
}
}
else
{
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__1(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_18);
lean_dec_ref(x_1);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0(x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__1(x_18, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
else
{
lean_dec_ref(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_16 = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(x_1, x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_102; 
x_17 = lean_ctor_get(x_16, 0);
x_102 = !lean_is_exclusive(x_16);
if (x_102 == 0)
{
x_18 = x_16;
x_19 = x_102;
goto block_101;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_102;
goto block_101;
}
block_101:
{
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_96; 
lean_del_object(x_18);
x_20 = lean_ctor_get(x_17, 0);
x_96 = !lean_is_exclusive(x_17);
if (x_96 == 0)
{
x_21 = x_17;
x_22 = x_96;
goto block_95;
}
else
{
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_23; 
lean_inc_ref(x_11);
lean_inc(x_20);
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_86; 
x_24 = lean_ctor_get(x_23, 0);
x_86 = !lean_is_exclusive(x_23);
if (x_86 == 0)
{
x_25 = x_23;
x_26 = x_86;
goto block_85;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_86;
goto block_85;
}
block_85:
{
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_80; 
lean_del_object(x_25);
x_27 = lean_ctor_get(x_24, 0);
x_80 = !lean_is_exclusive(x_24);
if (x_80 == 0)
{
x_28 = x_24;
x_29 = x_80;
goto block_79;
}
else
{
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = l_Lean_Grind_CommRing_Poly_getConst(x_27);
x_31 = lean_int_neg(x_30);
x_32 = l_Lean_Grind_CommRing_Poly_addConst(x_27, x_31);
lean_dec(x_31);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_32);
x_33 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l_Lean_Meta_Sym_shareCommon___redArg(x_34, x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_Grind_CommRing_Poly_toExpr(x_32);
lean_inc(x_30);
if (x_22 == 0)
{
lean_ctor_set_tag(x_21, 2);
lean_ctor_set(x_21, 0, x_30);
x_38 = x_21;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_30);
x_38 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_Grind_Arith_CommRing_mkTermEqProof(x_20, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_52; 
x_41 = lean_ctor_get(x_40, 0);
x_52 = !lean_is_exclusive(x_40);
if (x_52 == 0)
{
x_42 = x_40;
x_43 = x_52;
goto block_51;
}
else
{
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_30);
lean_ctor_set(x_44, 2, x_41);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_44);
x_45 = x_28;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_44);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_45);
x_46 = x_42;
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
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec(x_36);
lean_dec(x_30);
lean_del_object(x_28);
x_53 = lean_ctor_get(x_40, 0);
x_60 = !lean_is_exclusive(x_40);
if (x_60 == 0)
{
x_54 = x_40;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_40);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
lean_dec_ref(x_32);
lean_dec(x_30);
lean_del_object(x_28);
lean_del_object(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_63 = lean_ctor_get(x_35, 0);
x_70 = !lean_is_exclusive(x_35);
if (x_70 == 0)
{
x_64 = x_35;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_35);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
lean_dec_ref(x_32);
lean_dec(x_30);
lean_del_object(x_28);
lean_del_object(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_71 = lean_ctor_get(x_33, 0);
x_78 = !lean_is_exclusive(x_33);
if (x_78 == 0)
{
x_72 = x_33;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_33);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_24);
lean_del_object(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_81 = lean_box(0);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_81);
x_82 = x_25;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_81);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_94; 
lean_del_object(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_87 = lean_ctor_get(x_23, 0);
x_94 = !lean_is_exclusive(x_23);
if (x_94 == 0)
{
x_88 = x_23;
x_89 = x_94;
goto block_93;
}
else
{
lean_inc(x_87);
lean_dec(x_23);
x_88 = lean_box(0);
x_89 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_90; 
if (x_89 == 0)
{
x_90 = x_88;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_87);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_97 = lean_box(0);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_97);
x_98 = x_18;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_97);
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
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_110; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_103 = lean_ctor_get(x_16, 0);
x_110 = !lean_is_exclusive(x_16);
if (x_110 == 0)
{
x_104 = x_16;
x_105 = x_110;
goto block_109;
}
else
{
lean_inc(x_103);
lean_dec(x_16);
x_104 = lean_box(0);
x_105 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_106; 
if (x_105 == 0)
{
x_106 = x_104;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_103);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_45; 
x_15 = lean_ctor_get(x_14, 0);
x_45 = !lean_is_exclusive(x_14);
if (x_45 == 0)
{
x_16 = x_14;
x_17 = x_45;
goto block_44;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_18 = lean_ctor_get(x_15, 14);
lean_inc_ref(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec_ref(x_1);
x_39 = lean_ctor_get(x_18, 2);
x_40 = l_Lean_instInhabitedExpr;
x_41 = lean_nat_dec_lt(x_19, x_39);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_19);
lean_dec_ref(x_18);
x_42 = l_outOfBounds___redArg(x_40);
x_21 = x_42;
goto block_38;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_PersistentArray_get_x21___redArg(x_40, x_18, x_19);
lean_dec(x_19);
x_21 = x_43;
goto block_38;
}
block_38:
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_dec_eq(x_20, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_del_object(x_16);
x_24 = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__6(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_34; 
x_25 = lean_ctor_get(x_24, 0);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
x_26 = x_24;
x_27 = x_34;
goto block_33;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l_Lean_mkNatLit(x_20);
x_29 = l_Lean_mkAppB(x_25, x_21, x_28);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_29);
x_30 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
lean_dec_ref(x_21);
lean_dec(x_20);
return x_24;
}
}
else
{
lean_object* x_35; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_21);
x_35 = x_16;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_21);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_46 = lean_ctor_get(x_14, 0);
x_53 = !lean_is_exclusive(x_14);
if (x_53 == 0)
{
x_47 = x_14;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_14);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec_ref(x_1);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__5(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1_spec__2(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_mkAppB(x_19, x_2, x_21);
x_1 = x_17;
x_2 = x_22;
goto _start;
}
else
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_20;
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_obj_once(&l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___closed__0, &l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___closed__0);
x_15 = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__1(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec_ref(x_1);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1_spec__2(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1_spec__3(x_17, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_20;
}
else
{
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_obj_once(&l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___closed__0, &l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f_spec__0_spec__0_spec__1___closed__0);
x_16 = lean_int_dec_eq(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__5(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
x_22 = lean_ctor_get(x_21, 0);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
x_23 = x_21;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_mkAppB(x_18, x_20, x_22);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_25);
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_18);
return x_21;
}
}
else
{
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
else
{
lean_object* x_31; 
x_31 = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0_spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_36; 
x_15 = lean_ctor_get(x_1, 0);
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
x_16 = x_1;
x_17 = x_36;
goto block_35;
}
else
{
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0);
x_19 = lean_int_dec_eq(x_15, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_del_object(x_16);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__1(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_31; 
x_23 = lean_ctor_get(x_22, 0);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
x_24 = x_22;
x_25 = x_31;
goto block_30;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_mkAppB(x_21, x_2, x_23);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_26);
x_27 = x_24;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_dec(x_21);
lean_dec_ref(x_2);
return x_22;
}
}
else
{
lean_dec(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_20;
}
}
else
{
lean_object* x_32; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_2);
x_32 = x_16;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_2);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_39);
lean_dec_ref(x_1);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_40 = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkDenote0___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__1_spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0(x_37, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_37);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = l_Lean_mkAppB(x_41, x_2, x_43);
x_1 = x_39;
x_2 = x_44;
goto _start;
}
else
{
lean_dec(x_41);
lean_dec_ref(x_39);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_42;
}
}
else
{
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNonCommRingCnstr_x3f_spec__0_spec__0_spec__1(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_18);
lean_dec_ref(x_1);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__0(x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0_spec__1(x_18, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
else
{
lean_dec_ref(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(x_1, x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_78; 
x_17 = lean_ctor_get(x_16, 0);
x_78 = !lean_is_exclusive(x_16);
if (x_78 == 0)
{
x_18 = x_16;
x_19 = x_78;
goto block_77;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_78;
goto block_77;
}
block_77:
{
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_72; 
lean_del_object(x_18);
x_20 = lean_ctor_get(x_17, 0);
x_72 = !lean_is_exclusive(x_17);
if (x_72 == 0)
{
x_21 = x_17;
x_22 = x_72;
goto block_71;
}
else
{
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc(x_20);
x_23 = l_Lean_Grind_CommRing_Expr_toPoly__nc(x_20);
x_24 = l_Lean_Grind_CommRing_Poly_getConst(x_23);
x_25 = lean_int_neg(x_24);
x_26 = l_Lean_Grind_CommRing_Poly_addConst(x_23, x_25);
lean_dec(x_25);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_26);
x_27 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f_spec__0(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_Meta_Sym_shareCommon___redArg(x_28, x_8);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_Grind_CommRing_Poly_toExpr(x_26);
lean_inc(x_24);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_24);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Meta_Grind_Arith_CommRing_mkNonCommTermEqProof(x_20, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_46; 
x_35 = lean_ctor_get(x_34, 0);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
x_36 = x_34;
x_37 = x_46;
goto block_45;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_24);
lean_ctor_set(x_38, 2, x_35);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_38);
x_39 = x_21;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_38);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_39);
x_40 = x_36;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_30);
lean_dec(x_24);
lean_del_object(x_21);
x_47 = lean_ctor_get(x_34, 0);
x_54 = !lean_is_exclusive(x_34);
if (x_54 == 0)
{
x_48 = x_34;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_34);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec_ref(x_26);
lean_dec(x_24);
lean_del_object(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_ctor_get(x_29, 0);
x_62 = !lean_is_exclusive(x_29);
if (x_62 == 0)
{
x_56 = x_29;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_29);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
lean_dec_ref(x_26);
lean_dec(x_24);
lean_del_object(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_ctor_get(x_27, 0);
x_70 = !lean_is_exclusive(x_27);
if (x_70 == 0)
{
x_64 = x_27;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_27);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_box(0);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_73);
x_74 = x_18;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_73);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_ctor_get(x_16, 0);
x_86 = !lean_is_exclusive(x_16);
if (x_86 == 0)
{
x_80 = x_16;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_16);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTerm_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_36; 
x_15 = lean_ctor_get(x_14, 0);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
x_16 = x_14;
x_17 = x_36;
goto block_35;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_15, 6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_19 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_19);
x_20 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_15, 9);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 1)
{
uint8_t x_24; 
lean_del_object(x_16);
x_24 = lean_ctor_get_uint8(x_15, sizeof(void*)*22);
lean_dec(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermNonCommRing_x3f(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec_ref(x_23);
x_28 = 0;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTermCommRing_x3f(x_1, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_31 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_31);
x_32 = x_16;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_37 = lean_ctor_get(x_14, 0);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
x_38 = x_14;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_14);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTerm_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTerm_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__6_spec__11___closed__2);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__4);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_denoteExprCore_go___at___00Lean_Grind_CommRing_Expr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkCommRingCnstr_x3f_spec__0_spec__0_spec__3___closed__5));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__6));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__9));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_46; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_46 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_toOffsetTerm_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_113; 
x_47 = lean_ctor_get(x_46, 0);
x_113 = !lean_is_exclusive(x_46);
if (x_113 == 0)
{
x_48 = x_46;
x_49 = x_113;
goto block_112;
}
else
{
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_box(0);
x_49 = x_113;
goto block_112;
}
block_112:
{
if (lean_obj_tag(x_47) == 1)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_105; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec_ref(x_47);
x_51 = lean_ctor_get(x_50, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 2);
lean_inc_ref(x_53);
lean_dec(x_50);
x_105 = lean_expr_eqv(x_1, x_51);
if (x_105 == 0)
{
x_54 = x_105;
goto block_104;
}
else
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0);
x_107 = lean_int_dec_eq(x_52, x_106);
x_54 = x_107;
goto block_104;
}
block_104:
{
if (x_54 == 0)
{
lean_object* x_55; 
lean_del_object(x_48);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_55 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_51);
x_57 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__0));
x_60 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent___closed__1));
x_61 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__1));
x_62 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__3));
x_63 = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_split___closed__0);
x_66 = lean_int_dec_le(x_65, x_52);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__5);
x_68 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__7, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__7);
x_69 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__10);
x_70 = lean_int_neg(x_52);
x_71 = l_Int_toNat(x_70);
lean_dec(x_70);
x_72 = l_Lean_instToExprInt_mkNat(x_71);
x_73 = l_Lean_mkApp3(x_67, x_68, x_69, x_72);
x_14 = x_58;
x_15 = x_64;
x_16 = x_59;
x_17 = x_60;
x_18 = x_52;
x_19 = x_51;
x_20 = x_56;
x_21 = x_54;
x_22 = x_53;
x_23 = x_61;
x_24 = lean_box(0);
x_25 = x_73;
goto block_45;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Int_toNat(x_52);
x_75 = l_Lean_instToExprInt_mkNat(x_74);
x_14 = x_58;
x_15 = x_64;
x_16 = x_59;
x_17 = x_60;
x_18 = x_52;
x_19 = x_51;
x_20 = x_56;
x_21 = x_54;
x_22 = x_53;
x_23 = x_61;
x_24 = lean_box(0);
x_25 = x_75;
goto block_45;
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_76 = lean_ctor_get(x_63, 0);
x_83 = !lean_is_exclusive(x_63);
if (x_83 == 0)
{
x_77 = x_63;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_63);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
lean_dec(x_56);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_84 = lean_ctor_get(x_57, 0);
x_91 = !lean_is_exclusive(x_57);
if (x_91 == 0)
{
x_85 = x_57;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_57);
x_85 = lean_box(0);
x_86 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_87; 
if (x_86 == 0)
{
x_87 = x_85;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_84);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_99; 
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_92 = lean_ctor_get(x_55, 0);
x_99 = !lean_is_exclusive(x_55);
if (x_99 == 0)
{
x_93 = x_55;
x_94 = x_99;
goto block_98;
}
else
{
lean_inc(x_92);
lean_dec(x_55);
x_93 = lean_box(0);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_94 == 0)
{
x_95 = x_93;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_92);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_100 = lean_box(0);
if (x_49 == 0)
{
lean_ctor_set(x_48, 0, x_100);
x_101 = x_48;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_100);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_47);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_108 = lean_box(0);
if (x_49 == 0)
{
lean_ctor_set(x_48, 0, x_108);
x_109 = x_48;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_108);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_121; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_114 = lean_ctor_get(x_46, 0);
x_121 = !lean_is_exclusive(x_46);
if (x_121 == 0)
{
x_115 = x_46;
x_116 = x_121;
goto block_120;
}
else
{
lean_inc(x_114);
lean_dec(x_46);
x_115 = lean_box(0);
x_116 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_117; 
if (x_116 == 0)
{
x_117 = x_115;
goto block_118;
}
else
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_114);
x_117 = x_119;
goto block_118;
}
block_118:
{
return x_117;
}
}
}
block_45:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_inc_ref(x_22);
lean_inc_ref(x_25);
lean_inc_ref(x_19);
lean_inc_ref(x_1);
x_26 = l_Lean_mkApp4(x_15, x_1, x_19, x_25, x_22);
lean_inc(x_18);
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_21);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_14);
lean_inc(x_20);
x_28 = l_Lean_Meta_Grind_Order_addEdge(x_20, x_14, x_27, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_28);
x_29 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___closed__0));
x_30 = l_Lean_Name_mkStr4(x_16, x_17, x_23, x_29);
x_31 = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_mkApp4(x_32, x_1, x_19, x_25, x_22);
x_34 = lean_int_neg(x_18);
lean_dec(x_18);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_21);
x_36 = l_Lean_Meta_Grind_Order_addEdge(x_14, x_20, x_35, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_37 = lean_ctor_get(x_31, 0);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
x_38 = x_31;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_dec_ref(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_5);
lean_inc_ref(x_3);
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_47; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
if (x_4 == 0)
{
lean_object* x_51; 
lean_inc(x_22);
lean_inc(x_18);
x_51 = l_Lean_mkIntLE(x_18, x_22);
x_47 = x_51;
goto block_50;
}
else
{
lean_object* x_52; 
lean_inc(x_22);
lean_inc(x_18);
x_52 = l_Lean_mkIntLT(x_18, x_22);
x_47 = x_52;
goto block_50;
}
block_46:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_box(0);
x_27 = l_Lean_mkConst(x_25, x_26);
x_28 = l_Lean_mkApp6(x_27, x_2, x_3, x_18, x_22, x_19, x_23);
lean_inc_ref(x_24);
x_29 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap___redArg(x_1, x_24, x_28, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; uint8_t x_36; 
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_29, 0);
lean_dec(x_37);
x_30 = x_29;
x_31 = x_36;
goto block_35;
}
else
{
lean_dec(x_29);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_24);
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_24);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec_ref(x_24);
x_38 = lean_ctor_get(x_29, 0);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
x_39 = x_29;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
block_50:
{
if (x_4 == 0)
{
lean_object* x_48; 
x_48 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__2));
x_24 = x_47;
x_25 = x_48;
goto block_46;
}
else
{
lean_object* x_49; 
x_49 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___closed__4));
x_24 = x_47;
x_25 = x_49;
goto block_46;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = lean_ctor_get(x_20, 0);
x_60 = !lean_is_exclusive(x_20);
if (x_60 == 0)
{
x_54 = x_20;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_20);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_61 = lean_ctor_get(x_16, 0);
x_68 = !lean_is_exclusive(x_16);
if (x_68 == 0)
{
x_62 = x_16;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_16);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
x_17 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_15);
x_17 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_updateTermMap___redArg(x_1, x_15, x_16, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_18 = x_17;
x_19 = x_24;
goto block_23;
}
else
{
lean_dec(x_17);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_15);
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_15);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_15);
x_26 = lean_ctor_get(x_17, 0);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
x_27 = x_17;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_34 = lean_ctor_get(x_13, 0);
x_41 = !lean_is_exclusive(x_13);
if (x_41 == 0)
{
x_35 = x_13;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_13);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_82; 
x_14 = lean_ctor_get(x_13, 0);
x_82 = !lean_is_exclusive(x_13);
if (x_82 == 0)
{
x_15 = x_13;
x_16 = x_82;
goto block_81;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 3);
lean_inc_ref(x_17);
lean_dec(x_14);
x_18 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_mkNode_getOriginal_x3f_spec__0___redArg(x_17, x_1);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_20);
x_21 = x_15;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; 
lean_dec(x_18);
lean_del_object(x_15);
lean_inc_ref(x_1);
x_24 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_9);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_80; 
x_25 = lean_ctor_get(x_24, 0);
x_80 = !lean_is_exclusive(x_24);
if (x_80 == 0)
{
x_26 = x_24;
x_27 = x_80;
goto block_79;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Expr_cleanupAnnotations(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec_ref(x_28);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_1);
x_30 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_1);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_33);
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_35 = l_Lean_Expr_isApp(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_1);
x_36 = x_26;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_1);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_39);
x_40 = l_Lean_Expr_appFnCleanup___redArg(x_34);
x_41 = l_Lean_Expr_isApp(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_33);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_1);
x_42 = x_26;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_1);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = l_Lean_Expr_appFnCleanup___redArg(x_40);
x_46 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__2));
x_47 = l_Lean_Expr_isConstOf(x_45, x_46);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Expr_isApp(x_45);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec_ref(x_45);
lean_dec_ref(x_39);
lean_dec_ref(x_33);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_1);
x_49 = x_26;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_1);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = l_Lean_Expr_appFnCleanup___redArg(x_45);
x_53 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__7));
x_54 = l_Lean_Expr_isConstOf(x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__10));
x_56 = l_Lean_Expr_isConstOf(x_52, x_55);
if (x_56 == 0)
{
uint8_t x_57; 
lean_dec_ref(x_39);
lean_dec_ref(x_33);
x_57 = l_Lean_Expr_isApp(x_52);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec_ref(x_52);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_1);
x_58 = x_26;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_1);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = l_Lean_Expr_appFnCleanup___redArg(x_52);
x_62 = l_Lean_Expr_isApp(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec_ref(x_61);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_1);
x_63 = x_26;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_1);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = l_Lean_Expr_appFnCleanup___redArg(x_61);
x_67 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__13));
x_68 = l_Lean_Expr_isConstOf(x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__16));
x_70 = l_Lean_Expr_isConstOf(x_66, x_69);
lean_dec_ref(x_66);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_1);
x_71 = x_26;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_1);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
else
{
lean_object* x_74; 
lean_del_object(x_26);
x_74 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_74;
}
}
else
{
lean_object* x_75; 
lean_dec_ref(x_66);
lean_del_object(x_26);
x_75 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_75;
}
}
}
}
else
{
lean_object* x_76; 
lean_dec_ref(x_52);
lean_del_object(x_26);
x_76 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr(x_1, x_39, x_33, x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_76;
}
}
else
{
lean_object* x_77; 
lean_dec_ref(x_52);
lean_del_object(x_26);
x_77 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptCnstr(x_1, x_39, x_33, x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_77;
}
}
}
else
{
lean_object* x_78; 
lean_dec_ref(x_45);
lean_dec_ref(x_39);
lean_dec_ref(x_33);
lean_del_object(x_26);
x_78 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat_adaptTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_78;
}
}
}
}
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_24;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_90; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_83 = lean_ctor_get(x_13, 0);
x_90 = !lean_is_exclusive(x_13);
if (x_90 == 0)
{
x_84 = x_13;
x_85 = x_90;
goto block_89;
}
else
{
lean_inc(x_83);
lean_dec(x_13);
x_84 = lean_box(0);
x_85 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_86; 
if (x_85 == 0)
{
x_86 = x_84;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_83);
x_86 = x_88;
goto block_87;
}
block_87:
{
return x_86;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adapt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Nat_mkType;
x_15 = lean_expr_eqv(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec_ref(x_1);
lean_inc_ref(x_7);
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adaptNat(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Meta_Sym_getIntExpr___redArg(x_7);
lean_dec_ref(x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_29; 
x_21 = lean_ctor_get(x_20, 0);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
x_22 = x_20;
x_23 = x_29;
goto block_28;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_19);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_24);
x_25 = x_22;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_19);
x_30 = lean_ctor_get(x_20, 0);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
x_31 = x_20;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
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
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec_ref(x_7);
x_38 = lean_ctor_get(x_18, 0);
x_45 = !lean_is_exclusive(x_18);
if (x_45 == 0)
{
x_39 = x_18;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_18);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adapt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adapt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_setStructId_spec__0_spec__0___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0_spec__1___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_31; 
x_15 = lean_ctor_get(x_14, 0);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
x_16 = x_14;
x_17 = x_31;
goto block_30;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_15, 15);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_15, 16);
lean_inc_ref(x_19);
lean_dec(x_15);
x_20 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0___redArg(x_19, x_1);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0___redArg(x_18, x_1);
x_22 = lean_box(x_21);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_22);
x_23 = x_16;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_18);
x_26 = lean_box(x_20);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_26);
x_27 = x_16;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
x_32 = lean_ctor_get(x_14, 0);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
x_33 = x_14;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_14);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0_spec__1___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_internalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_getConfig___redArg(x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_159; 
x_15 = lean_ctor_get(x_14, 0);
x_159 = !lean_is_exclusive(x_14);
if (x_159 == 0)
{
x_16 = x_14;
x_17 = x_159;
goto block_158;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_159;
goto block_158;
}
block_158:
{
uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 26);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_19);
x_20 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; 
lean_inc_ref(x_1);
x_23 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f(x_1);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; lean_object* x_25; 
lean_del_object(x_16);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_adapt(x_24, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_145; 
x_26 = lean_ctor_get(x_25, 0);
x_145 = !lean_is_exclusive(x_25);
if (x_145 == 0)
{
x_27 = x_25;
x_28 = x_145;
goto block_144;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_isForbiddenParent(x_2);
if (x_31 == 0)
{
lean_object* x_32; 
lean_del_object(x_27);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_32 = l_Lean_Meta_Grind_Order_getStructId_x3f(x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_131; 
x_33 = lean_ctor_get(x_32, 0);
x_131 = !lean_is_exclusive(x_32);
if (x_131 == 0)
{
x_34 = x_32;
x_35 = x_131;
goto block_130;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_131;
goto block_130;
}
block_130:
{
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_36; lean_object* x_37; 
lean_del_object(x_34);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec_ref(x_33);
x_37 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_alreadyInternalizedHere(x_30, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_117; 
x_38 = lean_ctor_get(x_37, 0);
x_117 = !lean_is_exclusive(x_37);
if (x_117 == 0)
{
x_39 = x_37;
x_40 = x_117;
goto block_116;
}
else
{
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = x_117;
goto block_116;
}
block_116:
{
uint8_t x_41; 
x_41 = lean_unbox(x_38);
lean_dec(x_38);
if (x_41 == 0)
{
lean_object* x_42; 
lean_del_object(x_39);
lean_inc(x_30);
x_42 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_30, x_10);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_103; 
x_43 = lean_ctor_get(x_42, 0);
x_103 = !lean_is_exclusive(x_42);
if (x_103 == 0)
{
x_44 = x_42;
x_45 = x_103;
goto block_102;
}
else
{
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_Lean_Expr_cleanupAnnotations(x_43);
x_52 = l_Lean_Expr_isApp(x_51);
if (x_52 == 0)
{
lean_dec_ref(x_51);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_50;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc_ref(x_53);
x_54 = l_Lean_Expr_appFnCleanup___redArg(x_51);
x_55 = l_Lean_Expr_isApp(x_54);
if (x_55 == 0)
{
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_50;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_54, 1);
lean_inc_ref(x_56);
x_57 = l_Lean_Expr_appFnCleanup___redArg(x_54);
x_58 = l_Lean_Expr_isApp(x_57);
if (x_58 == 0)
{
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec_ref(x_53);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_50;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = l_Lean_Expr_appFnCleanup___redArg(x_57);
x_60 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__2));
x_61 = l_Lean_Expr_isConstOf(x_59, x_60);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = l_Lean_Expr_isApp(x_59);
if (x_62 == 0)
{
lean_dec_ref(x_59);
lean_dec_ref(x_56);
lean_dec_ref(x_53);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_50;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = l_Lean_Expr_appFnCleanup___redArg(x_59);
x_64 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__7));
x_65 = l_Lean_Expr_isConstOf(x_63, x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__10));
x_67 = l_Lean_Expr_isConstOf(x_63, x_66);
if (x_67 == 0)
{
uint8_t x_68; 
lean_dec_ref(x_56);
lean_dec_ref(x_53);
x_68 = l_Lean_Expr_isApp(x_63);
if (x_68 == 0)
{
lean_dec_ref(x_63);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_50;
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = l_Lean_Expr_appFnCleanup___redArg(x_63);
x_70 = l_Lean_Expr_isApp(x_69);
if (x_70 == 0)
{
lean_dec_ref(x_69);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_50;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = l_Lean_Expr_appFnCleanup___redArg(x_69);
x_72 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__13));
x_73 = l_Lean_Expr_isConstOf(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_getType_x3f___closed__16));
x_75 = l_Lean_Expr_isConstOf(x_71, x_74);
lean_dec_ref(x_71);
if (x_75 == 0)
{
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_50;
}
else
{
lean_object* x_76; 
lean_del_object(x_44);
x_76 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm(x_30, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_76;
}
}
else
{
lean_object* x_77; 
lean_dec_ref(x_71);
lean_del_object(x_44);
x_77 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm(x_30, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_77;
}
}
}
}
else
{
uint8_t x_78; lean_object* x_79; 
lean_dec_ref(x_63);
lean_del_object(x_44);
x_78 = 0;
x_79 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr(x_30, x_78, x_56, x_53, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_79;
}
}
else
{
lean_object* x_80; 
lean_dec_ref(x_63);
lean_del_object(x_44);
x_80 = l_Lean_Meta_Grind_Order_hasLt(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_92; 
x_81 = lean_ctor_get(x_80, 0);
x_92 = !lean_is_exclusive(x_80);
if (x_92 == 0)
{
x_82 = x_80;
x_83 = x_92;
goto block_91;
}
else
{
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_box(0);
x_83 = x_92;
goto block_91;
}
block_91:
{
uint8_t x_84; 
x_84 = lean_unbox(x_81);
lean_dec(x_81);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_56);
lean_dec_ref(x_53);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = lean_box(0);
if (x_83 == 0)
{
lean_ctor_set(x_82, 0, x_85);
x_86 = x_82;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_85);
x_86 = x_88;
goto block_87;
}
block_87:
{
return x_86;
}
}
else
{
uint8_t x_89; lean_object* x_90; 
lean_del_object(x_82);
x_89 = 1;
x_90 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeCnstr(x_30, x_89, x_56, x_53, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_90;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_100; 
lean_dec_ref(x_56);
lean_dec_ref(x_53);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_93 = lean_ctor_get(x_80, 0);
x_100 = !lean_is_exclusive(x_80);
if (x_100 == 0)
{
x_94 = x_80;
x_95 = x_100;
goto block_99;
}
else
{
lean_inc(x_93);
lean_dec(x_80);
x_94 = lean_box(0);
x_95 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_96; 
if (x_95 == 0)
{
x_96 = x_94;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_93);
x_96 = x_98;
goto block_97;
}
block_97:
{
return x_96;
}
}
}
}
}
}
else
{
lean_object* x_101; 
lean_dec_ref(x_59);
lean_dec_ref(x_56);
lean_dec_ref(x_53);
lean_del_object(x_44);
x_101 = l___private_Lean_Meta_Tactic_Grind_Order_Internalize_0__Lean_Meta_Grind_Order_internalizeTerm(x_30, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_101;
}
}
}
}
block_50:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_46);
x_47 = x_44;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_46);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_111; 
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_104 = lean_ctor_get(x_42, 0);
x_111 = !lean_is_exclusive(x_42);
if (x_111 == 0)
{
x_105 = x_42;
x_106 = x_111;
goto block_110;
}
else
{
lean_inc(x_104);
lean_dec(x_42);
x_105 = lean_box(0);
x_106 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_107; 
if (x_106 == 0)
{
x_107 = x_105;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_104);
x_107 = x_109;
goto block_108;
}
block_108:
{
return x_107;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = lean_box(0);
if (x_40 == 0)
{
lean_ctor_set(x_39, 0, x_112);
x_113 = x_39;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_112);
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
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_125; 
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_118 = lean_ctor_get(x_37, 0);
x_125 = !lean_is_exclusive(x_37);
if (x_125 == 0)
{
x_119 = x_37;
x_120 = x_125;
goto block_124;
}
else
{
lean_inc(x_118);
lean_dec(x_37);
x_119 = lean_box(0);
x_120 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_121; 
if (x_120 == 0)
{
x_121 = x_119;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_118);
x_121 = x_123;
goto block_122;
}
block_122:
{
return x_121;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_126 = lean_box(0);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_126);
x_127 = x_34;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_126);
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
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; uint8_t x_139; 
lean_dec(x_30);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_132 = lean_ctor_get(x_32, 0);
x_139 = !lean_is_exclusive(x_32);
if (x_139 == 0)
{
x_133 = x_32;
x_134 = x_139;
goto block_138;
}
else
{
lean_inc(x_132);
lean_dec(x_32);
x_133 = lean_box(0);
x_134 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_135; 
if (x_134 == 0)
{
x_135 = x_133;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_132);
x_135 = x_137;
goto block_136;
}
block_136:
{
return x_135;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_140 = lean_box(0);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_140);
x_141 = x_27;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_140);
x_141 = x_143;
goto block_142;
}
block_142:
{
return x_141;
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_153; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_146 = lean_ctor_get(x_25, 0);
x_153 = !lean_is_exclusive(x_25);
if (x_153 == 0)
{
x_147 = x_25;
x_148 = x_153;
goto block_152;
}
else
{
lean_inc(x_146);
lean_dec(x_25);
x_147 = lean_box(0);
x_148 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_149; 
if (x_148 == 0)
{
x_149 = x_147;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_146);
x_149 = x_151;
goto block_150;
}
block_150:
{
return x_149;
}
}
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_154 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_154);
x_155 = x_16;
goto block_156;
}
else
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_157, 0, x_154);
x_155 = x_157;
goto block_156;
}
block_156:
{
return x_155;
}
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_167; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_160 = lean_ctor_get(x_14, 0);
x_167 = !lean_is_exclusive(x_14);
if (x_167 == 0)
{
x_161 = x_14;
x_162 = x_167;
goto block_166;
}
else
{
lean_inc(x_160);
lean_dec(x_14);
x_161 = lean_box(0);
x_162 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_163; 
if (x_162 == 0)
{
x_163 = x_161;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_160);
x_163 = x_165;
goto block_164;
}
block_164:
{
return x_163;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_internalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_internalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_Envelope(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Order(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_StructId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Assert(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Proof(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Module_Envelope(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Order(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_StructId(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Assert(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Proof(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Order_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Grind_Module_Envelope(uint8_t builtin);
lean_object* initialize_Init_Grind_Order(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_StructId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Assert(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Proof(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Module_Envelope(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Order(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Order_StructId(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Order_Assert(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Order_Proof(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Internalize(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Order_Internalize(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Order_Internalize(builtin);
}
#ifdef __cplusplus
}
#endif
