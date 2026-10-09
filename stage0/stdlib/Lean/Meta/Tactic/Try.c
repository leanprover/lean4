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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 242, 127, 137, 194, 226, 122, 11)}};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "collect"};
static const lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__value;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_unsigned_to_nat(2909380237u);
v___x_51_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
v___x_52_ = l_Lean_Name_num___override(v___x_51_, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
v___x_55_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_);
v___x_56_ = l_Lean_Name_str___override(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
v___x_59_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_);
v___x_60_ = l_Lean_Name_str___override(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_unsigned_to_nat(2u);
v___x_62_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_);
v___x_63_ = l_Lean_Name_num___override(v___x_62_, v___x_61_);
return v___x_63_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_65_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
v___x_66_ = 0;
v___x_67_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_);
v___x_68_ = l_Lean_registerTraceClass(v___x_65_, v___x_66_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_69_;
v_res_69_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_();
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2____boxed(lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_();
return v_res_71_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_89_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_));
v___x_90_ = 0;
v___x_91_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_));
v___x_92_ = l_Lean_registerTraceClass(v___x_89_, v___x_90_, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_93_;
v_res_93_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_();
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2____boxed(lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_();
return v_res_95_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_unsigned_to_nat(3813147919u);
v___x_102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
v___x_103_ = l_Lean_Name_num___override(v___x_102_, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
v___x_105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_);
v___x_106_ = l_Lean_Name_str___override(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
v___x_108_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_);
v___x_109_ = l_Lean_Name_str___override(v___x_108_, v___x_107_);
return v___x_109_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_unsigned_to_nat(2u);
v___x_111_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_);
v___x_112_ = l_Lean_Name_num___override(v___x_111_, v___x_110_);
return v___x_112_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_114_; uint8_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_));
v___x_115_ = 0;
v___x_116_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_);
v___x_117_ = l_Lean_registerTraceClass(v___x_114_, v___x_115_, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_118_;
v_res_118_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_();
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2____boxed(lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_();
return v_res_120_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_));
v___x_139_ = 0;
v___x_140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_));
v___x_141_ = l_Lean_registerTraceClass(v___x_138_, v___x_139_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_142_;
v_res_142_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_();
stack->m_obj
 = v_res_142_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2____boxed(lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_();
return v_res_144_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_unsigned_to_nat(2260799134u);
v___x_150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
v___x_151_ = l_Lean_Name_num___override(v___x_150_, v___x_149_);
return v___x_151_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
v___x_153_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_);
v___x_154_ = l_Lean_Name_str___override(v___x_153_, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
v___x_156_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_);
v___x_157_ = l_Lean_Name_str___override(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_unsigned_to_nat(2u);
v___x_159_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_);
v___x_160_ = l_Lean_Name_num___override(v___x_159_, v___x_158_);
return v___x_160_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_162_; uint8_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_));
v___x_163_ = 0;
v___x_164_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_);
v___x_165_ = l_Lean_registerTraceClass(v___x_162_, v___x_163_, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_166_;
v_res_166_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_();
stack->m_obj
 = v_res_166_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2____boxed(lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_();
return v_res_168_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_unsigned_to_nat(2306426978u);
v___x_175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
v___x_176_ = l_Lean_Name_num___override(v___x_175_, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
v___x_178_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_);
v___x_179_ = l_Lean_Name_str___override(v___x_178_, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_));
v___x_181_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_);
v___x_182_ = l_Lean_Name_str___override(v___x_181_, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_unsigned_to_nat(2u);
v___x_184_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_);
v___x_185_ = l_Lean_Name_num___override(v___x_184_, v___x_183_);
return v___x_185_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_187_; uint8_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_));
v___x_188_ = 0;
v___x_189_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Try_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_);
v___x_190_ = l_Lean_registerTraceClass(v___x_187_, v___x_188_, v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_191_;
v_res_191_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_();
stack->m_obj
 = v_res_191_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2____boxed(lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_();
return v_res_193_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Try_Collect(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Try(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Try_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2909380237____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_381124472____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_3813147919____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_103928808____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2260799134____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Try_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Try_2306426978____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Try(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Meta_Tactic_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Try(builtin);
}
#ifdef __cplusplus
}
#endif
