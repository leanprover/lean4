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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Order_orderExt;
lean_object* l_Lean_Meta_Grind_Order_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_processNewEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "order"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 139, 28, 5, 248, 187, 127, 111)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__value;
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
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Order_internalize___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Order_processNewEq___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_unsigned_to_nat(3007973156u);
v___x_69_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
v___x_70_ = l_Lean_Name_num___override(v___x_69_, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
v___x_73_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_);
v___x_74_ = l_Lean_Name_str___override(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
v___x_77_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_);
v___x_78_ = l_Lean_Name_str___override(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(2u);
v___x_80_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_);
v___x_81_ = l_Lean_Name_num___override(v___x_80_, v___x_79_);
return v___x_81_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_83_; uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
v___x_84_ = 0;
v___x_85_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_);
v___x_86_ = l_Lean_registerTraceClass(v___x_83_, v___x_84_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_87_;
v_res_87_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_();
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2____boxed(lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_();
return v_res_89_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_));
v___x_109_ = 0;
v___x_110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_));
v___x_111_ = l_Lean_registerTraceClass(v___x_108_, v___x_109_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_112_;
v_res_112_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_();
stack->m_obj
 = v_res_112_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2____boxed(lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_();
return v_res_114_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_));
v___x_134_ = 0;
v___x_135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_));
v___x_136_ = l_Lean_registerTraceClass(v___x_133_, v___x_134_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_137_;
v_res_137_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_();
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2____boxed(lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_();
return v_res_139_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_159_; uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_));
v___x_160_ = 0;
v___x_161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_));
v___x_162_ = l_Lean_registerTraceClass(v___x_159_, v___x_160_, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_163_;
v_res_163_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_();
stack->m_obj
 = v_res_163_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2____boxed(lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_();
return v_res_165_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_));
v___x_185_ = 0;
v___x_186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_));
v___x_187_ = l_Lean_registerTraceClass(v___x_184_, v___x_185_, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_188_;
v_res_188_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_();
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2____boxed(lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_();
return v_res_190_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_unsigned_to_nat(3999496204u);
v___x_198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
v___x_199_ = l_Lean_Name_num___override(v___x_198_, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
v___x_201_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_);
v___x_202_ = l_Lean_Name_str___override(v___x_201_, v___x_200_);
return v___x_202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
v___x_204_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_);
v___x_205_ = l_Lean_Name_str___override(v___x_204_, v___x_203_);
return v___x_205_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_unsigned_to_nat(2u);
v___x_207_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_);
v___x_208_ = l_Lean_Name_num___override(v___x_207_, v___x_206_);
return v___x_208_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_));
v___x_211_ = 1;
v___x_212_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_);
v___x_213_ = l_Lean_registerTraceClass(v___x_210_, v___x_211_, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_214_;
v_res_214_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_();
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2____boxed(lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_();
return v_res_216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_223_ = lean_unsigned_to_nat(3855794043u);
v___x_224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
v___x_225_ = l_Lean_Name_num___override(v___x_224_, v___x_223_);
return v___x_225_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
v___x_227_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_);
v___x_228_ = l_Lean_Name_str___override(v___x_227_, v___x_226_);
return v___x_228_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_));
v___x_230_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_);
v___x_231_ = l_Lean_Name_str___override(v___x_230_, v___x_229_);
return v___x_231_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_unsigned_to_nat(2u);
v___x_233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_);
v___x_234_ = l_Lean_Name_num___override(v___x_233_, v___x_232_);
return v___x_234_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_236_; uint8_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_236_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_));
v___x_237_ = 1;
v___x_238_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_);
v___x_239_ = l_Lean_registerTraceClass(v___x_236_, v___x_237_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_240_;
v_res_240_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_();
stack->m_obj
 = v_res_240_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2____boxed(lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_();
return v_res_242_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_));
v___x_263_ = 1;
v___x_264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_));
v___x_265_ = l_Lean_registerTraceClass(v___x_262_, v___x_263_, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_266_;
v_res_266_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_();
stack->m_obj
 = v_res_266_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2____boxed(lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_();
return v_res_268_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_));
v___x_289_ = 1;
v___x_290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_));
v___x_291_ = l_Lean_registerTraceClass(v___x_288_, v___x_289_, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_292_;
v_res_292_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_();
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2____boxed(lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_();
return v_res_294_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_box(0);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_295_ = stack[0].m_obj;
lean_object* v_x_296_ = stack[1].m_obj;
lean_object* v___y_297_ = stack[2].m_obj;
lean_object* v___y_298_ = stack[3].m_obj;
lean_object* v___y_299_ = stack[4].m_obj;
lean_object* v___y_300_ = stack[5].m_obj;
lean_object* v___y_301_ = stack[6].m_obj;
lean_object* v___y_302_ = stack[7].m_obj;
lean_object* v___y_303_ = stack[8].m_obj;
lean_object* v___y_304_ = stack[9].m_obj;
lean_object* v___y_305_ = stack[10].m_obj;
lean_object* v___y_306_ = stack[11].m_obj;
lean_object* v_res_310_;
v_res_310_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(v_x_295_, v_x_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
stack->m_obj
 = v_res_310_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(v_x_311_, v_x_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v_x_312_);
lean_dec_ref(v_x_311_);
return v_res_324_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = lean_apply_11(v___y_326_, v___y_325_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, lean_box(0));
return v___x_338_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___y_325_ = stack[0].m_obj;
lean_object* v___y_326_ = stack[1].m_obj;
lean_object* v___y_327_ = stack[2].m_obj;
lean_object* v___y_328_ = stack[3].m_obj;
lean_object* v___y_329_ = stack[4].m_obj;
lean_object* v___y_330_ = stack[5].m_obj;
lean_object* v___y_331_ = stack[6].m_obj;
lean_object* v___y_332_ = stack[7].m_obj;
lean_object* v___y_333_ = stack[8].m_obj;
lean_object* v___y_334_ = stack[9].m_obj;
lean_object* v___y_335_ = stack[10].m_obj;
lean_object* v___y_336_ = stack[11].m_obj;
lean_object* v_res_339_;
v_res_339_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
lean_dec_ref(v___y_342_);
return v_res_353_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(uint8_t v___x_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_box(v___x_354_);
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
uint8_t v___x_354_ = stack[0].m_num;
lean_object* v___y_355_ = stack[1].m_obj;
lean_object* v___y_356_ = stack[2].m_obj;
lean_object* v___y_357_ = stack[3].m_obj;
lean_object* v___y_358_ = stack[4].m_obj;
lean_object* v___y_359_ = stack[5].m_obj;
lean_object* v___y_360_ = stack[6].m_obj;
lean_object* v___y_361_ = stack[7].m_obj;
lean_object* v___y_362_ = stack[8].m_obj;
lean_object* v___y_363_ = stack[9].m_obj;
lean_object* v___y_364_ = stack[10].m_obj;
lean_object* v_res_368_;
v_res_368_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(v___x_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
stack->m_obj
 = v_res_368_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object* v___x_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
uint8_t v___x_1449__boxed_381_; lean_object* v_res_382_; 
v___x_1449__boxed_381_ = lean_unbox(v___x_369_);
v_res_382_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(v___x_1449__boxed_381_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec(v___y_370_);
return v_res_382_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(lean_object* v___x_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_383_);
return v___x_395_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_383_ = stack[0].m_obj;
lean_object* v___y_384_ = stack[1].m_obj;
lean_object* v___y_385_ = stack[2].m_obj;
lean_object* v___y_386_ = stack[3].m_obj;
lean_object* v___y_387_ = stack[4].m_obj;
lean_object* v___y_388_ = stack[5].m_obj;
lean_object* v___y_389_ = stack[6].m_obj;
lean_object* v___y_390_ = stack[7].m_obj;
lean_object* v___y_391_ = stack[8].m_obj;
lean_object* v___y_392_ = stack[9].m_obj;
lean_object* v___y_393_ = stack[10].m_obj;
lean_object* v_res_396_;
v_res_396_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(v___x_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
stack->m_obj
 = v_res_396_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object* v___x_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(v___x_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec(v___y_398_);
return v_res_409_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_420_; lean_object* v___f_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___f_425_; lean_object* v___f_426_; lean_object* v___x_427_; 
v___f_420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_));
v___f_421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_));
v___x_422_ = l_Lean_Meta_Grind_Order_orderExt;
v___x_423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_));
v___x_424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_));
v___f_425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_));
v___f_426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_));
v___x_427_ = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(v___x_422_, v___x_423_, v___x_424_, v___f_420_, v___f_425_, v___f_421_, v___f_425_, v___f_426_);
return v___x_427_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_428_;
v_res_428_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_();
stack->m_obj
 = v_res_428_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2____boxed(lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_();
return v_res_430_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_StructId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Assert(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Assert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3007973156____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_344686027____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_563761110____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_413082279____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_907713757____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3999496204____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_3855794043____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_185970682____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_673264261____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Order_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_2371102220____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Order(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Order(builtin);
}
#ifdef __cplusplus
}
#endif
