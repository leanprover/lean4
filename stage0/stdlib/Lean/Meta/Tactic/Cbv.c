// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv
// Imports: public import Lean.Meta.Tactic.Cbv.Main public import Lean.Meta.Tactic.Cbv.Util public import Lean.Meta.Tactic.Cbv.CbvEvalExt
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Cbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(93, 144, 236, 69, 149, 78, 215, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(104, 233, 230, 17, 104, 34, 42, 35)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(193, 42, 146, 39, 4, 165, 228, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 216, 194, 136, 102, 253, 179, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 140, 92, 135, 129, 64, 68, 20)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 184, 254, 39, 104, 43, 50, 206)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(48, 171, 45, 36, 194, 31, 106, 202)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(77, 180, 219, 125, 73, 143, 148, 126)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(179, 98, 217, 98, 62, 12, 69, 239)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 248, 27, 31, 3, 126, 142, 13)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 140, 6, 58, 231, 192, 8, 160)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 39, 251, 153, 6, 255, 160, 132)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(16, 195, 245, 152, 44, 204, 206, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simprocs"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 248, 27, 31, 3, 126, 142, 13)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 140, 6, 58, 231, 192, 8, 160)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 39, 251, 153, 6, 255, 160, 132)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(16, 195, 245, 152, 44, 204, 206, 86)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(177, 11, 95, 174, 175, 24, 243, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_unsigned_to_nat(4268171306u);
v___x_53_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_54_ = l_Lean_Name_num___override(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_57_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_);
v___x_58_ = l_Lean_Name_str___override(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_61_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_);
v___x_62_ = l_Lean_Name_str___override(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_unsigned_to_nat(2u);
v___x_64_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_);
v___x_65_ = l_Lean_Name_num___override(v___x_64_, v___x_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_67_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_68_ = 0;
v___x_69_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_);
v___x_70_ = l_Lean_registerTraceClass(v___x_67_, v___x_68_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2____boxed(lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_();
return v_res_72_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(2526460641u);
v___x_80_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_81_ = l_Lean_Name_num___override(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_83_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_);
v___x_84_ = l_Lean_Name_str___override(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_86_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_);
v___x_87_ = l_Lean_Name_str___override(v___x_86_, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_unsigned_to_nat(2u);
v___x_89_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_);
v___x_90_ = l_Lean_Name_num___override(v___x_89_, v___x_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_));
v___x_93_ = 0;
v___x_94_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_);
v___x_95_ = l_Lean_registerTraceClass(v___x_92_, v___x_93_, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2____boxed(lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_();
return v_res_97_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_unsigned_to_nat(2416529480u);
v___x_106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_107_ = l_Lean_Name_num___override(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_109_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_);
v___x_110_ = l_Lean_Name_str___override(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_112_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_);
v___x_113_ = l_Lean_Name_str___override(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_unsigned_to_nat(2u);
v___x_115_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_);
v___x_116_ = l_Lean_Name_num___override(v___x_115_, v___x_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_));
v___x_119_ = 1;
v___x_120_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_);
v___x_121_ = l_Lean_registerTraceClass(v___x_118_, v___x_119_, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2____boxed(lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_();
return v_res_123_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Cbv_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2416529480____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Cbv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Cbv_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Cbv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Cbv_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Cbv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Cbv(builtin);
}
#ifdef __cplusplus
}
#endif
