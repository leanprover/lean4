// Lean compiler output
// Module: Lean.Meta.Tactic.Try
// Imports: public import Lean.Meta.Tactic.Try.Collect
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
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 242, 127, 137, 194, 226, 122, 11)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Try"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 100, 206, 3, 147, 112, 116, 183)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(66, 199, 53, 213, 89, 84, 146, 207)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(163, 180, 232, 49, 165, 56, 38, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(130, 233, 219, 242, 15, 97, 248, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 51, 40, 31, 163, 58, 239, 49)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 88, 140, 191, 57, 135, 7, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 196, 135, 151, 141, 54, 26, 99)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 133, 95, 138, 32, 225, 204, 93)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 156, 0, 35, 163, 204, 182, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "collect"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 242, 127, 137, 194, 226, 122, 11)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(193, 94, 218, 79, 189, 16, 234, 24)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),((lean_object*)(((size_t)(381124472) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(136, 176, 149, 153, 236, 237, 92, 156)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(175, 190, 205, 253, 120, 254, 219, 87)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(23, 176, 39, 200, 174, 167, 240, 132)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(194, 187, 214, 121, 121, 30, 238, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "funInd"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 242, 127, 137, 194, 226, 122, 11)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(193, 94, 218, 79, 189, 16, 234, 24)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 176, 89, 100, 228, 1, 218, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 242, 127, 137, 194, 226, 122, 11)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 156, 131, 6, 193, 145, 84, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),((lean_object*)(((size_t)(103928808) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(81, 178, 139, 246, 248, 238, 77, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(50, 142, 142, 69, 75, 28, 102, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(94, 204, 173, 202, 228, 200, 216, 70)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(239, 73, 215, 111, 177, 112, 84, 111)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 242, 127, 137, 194, 226, 122, 11)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 156, 131, 6, 193, 145, 84, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 65, 87, 213, 10, 251, 20, 129)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "chain"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 242, 127, 137, 194, 226, 122, 11)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 156, 131, 6, 193, 145, 84, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 201, 202, 212, 31, 221, 47, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2909380237u);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_);
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
x_3 = 0;
x_4 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_);
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3813147919u);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_);
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_));
x_3 = 0;
x_4 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_);
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2260799134u);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_);
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_));
x_3 = 0;
x_4 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_);
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2306426978u);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_);
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_));
x_3 = 0;
x_4 = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_);
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_Try_Collect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Try(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Try_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
