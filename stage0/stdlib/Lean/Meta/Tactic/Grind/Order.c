// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order
// Imports: public import Lean.Meta.Tactic.Grind.Order.Types public import Lean.Meta.Tactic.Grind.Order.Internalize public import Lean.Meta.Tactic.Grind.Order.StructId public import Lean.Meta.Tactic.Grind.Order.OrderM public import Lean.Meta.Tactic.Grind.Order.Assert public import Lean.Meta.Tactic.Grind.Order.Util
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "order"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 139, 28, 5, 248, 187, 127, 111)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 178, 115, 128, 126, 251, 25, 30)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(121, 133, 4, 98, 42, 126, 81, 51)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(220, 115, 45, 111, 172, 228, 163, 35)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 74, 77, 255, 124, 163, 215, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(234, 208, 235, 225, 68, 35, 225, 255)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(11, 56, 170, 224, 103, 184, 65, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 115, 33, 16, 142, 83, 222, 71)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 34, 100, 110, 63, 36, 99, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 246, 231, 251, 255, 239, 70, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(10, 247, 170, 136, 139, 232, 156, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 96, 151, 74, 84, 214, 213, 130)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 196, 54, 246, 26, 254, 28, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(196, 47, 227, 22, 241, 240, 140, 193)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 139, 28, 5, 248, 187, 127, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(118, 196, 12, 238, 101, 107, 106, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)(((size_t)(344686027) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(144, 155, 147, 196, 144, 125, 240, 184)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 213, 184, 163, 227, 141, 183, 243)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 159, 64, 157, 43, 3, 53, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(10, 150, 80, 17, 205, 251, 163, 126)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "internalize"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 139, 28, 5, 248, 187, 127, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 111, 26, 150, 112, 124, 18, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)(((size_t)(563761110) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(132, 29, 160, 0, 0, 2, 106, 120)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(171, 106, 210, 194, 250, 182, 78, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 114, 114, 178, 22, 238, 66, 104)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(190, 152, 204, 247, 41, 173, 249, 63)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 139, 28, 5, 248, 187, 127, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 111, 26, 150, 112, 124, 18, 136)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(193, 231, 27, 63, 201, 183, 177, 76)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)(((size_t)(413082279) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(23, 38, 69, 61, 96, 164, 95, 89)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(28, 216, 23, 189, 203, 41, 156, 213)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 126, 44, 43, 220, 199, 78, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(169, 117, 152, 61, 178, 120, 38, 73)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 118, 119, 155, 86, 132, 17, 202)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)(((size_t)(907713757) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(192, 53, 153, 94, 168, 174, 198, 181)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 49, 252, 236, 188, 155, 62, 215)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 92, 156, 239, 17, 234, 240, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(186, 253, 123, 231, 214, 9, 189, 200)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "add_edge"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 118, 119, 155, 86, 132, 17, 202)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 172, 169, 19, 106, 199, 68, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "propagate"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 118, 119, 155, 86, 132, 17, 202)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(142, 44, 102, 149, 148, 89, 41, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "check_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 118, 119, 155, 86, 132, 17, 202)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(234, 223, 60, 213, 11, 195, 227, 109)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)(((size_t)(185970682) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(80, 191, 244, 4, 166, 92, 62, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(199, 16, 92, 193, 11, 44, 158, 242)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 133, 23, 169, 186, 247, 30, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(74, 217, 150, 205, 29, 50, 136, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "check_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 118, 119, 155, 86, 132, 17, 202)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 206, 15, 111, 12, 66, 29, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),((lean_object*)(((size_t)(673264261) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(42, 122, 183, 75, 145, 204, 145, 255)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 241, 27, 121, 49, 133, 141, 172)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 229, 160, 217, 252, 131, 41, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(200, 242, 79, 41, 57, 100, 10, 204)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value;
lean_object* l_Lean_Meta_Grind_Order_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Order_internalize___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value;
lean_object* l_Lean_Meta_Grind_Order_processNewEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Order_processNewEq___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value;
extern lean_object* l_Lean_Meta_Grind_Order_orderExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3007973156u);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_);
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
x_3 = 0;
x_4 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_);
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3999496204u);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_);
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_));
x_3 = 1;
x_4 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_);
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3855794043u);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_);
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_));
x_3 = 1;
x_4 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_);
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_));
x_3 = 1;
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_));
x_3 = 1;
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = lean_apply_11(x_2, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed), 12, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_));
x_4 = l_Lean_Meta_Grind_Order_orderExt;
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_));
x_6 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_));
x_7 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_);
x_8 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_));
x_9 = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(x_4, x_5, x_6, x_2, x_7, x_3, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Internalize(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_StructId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Assert(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Order(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Order_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Order_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Order_Assert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
