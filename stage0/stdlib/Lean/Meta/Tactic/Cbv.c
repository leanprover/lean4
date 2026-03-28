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
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rewrite"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 58, 109, 183, 100, 138, 243, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1674345266) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(103, 233, 114, 5, 164, 58, 78, 73)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 79, 136, 139, 210, 108, 14, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 49, 251, 2, 78, 173, 11, 39)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(57, 14, 227, 21, 243, 164, 235, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unfold"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(162, 17, 43, 156, 90, 102, 144, 138)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1090948466) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(66, 234, 164, 170, 114, 188, 9, 110)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 5, 133, 209, 197, 44, 229, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 160, 22, 242, 0, 209, 45, 9)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(128, 74, 136, 123, 32, 158, 47, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "controlFlow"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 7, 140, 41, 97, 241, 74, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1675791195) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(50, 235, 19, 179, 194, 128, 232, 81)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(189, 105, 27, 254, 22, 240, 164, 217)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(157, 160, 254, 124, 109, 123, 138, 140)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(112, 22, 44, 140, 241, 45, 253, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simprocs"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(61, 69, 90, 123, 228, 205, 71, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "reduce"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 248, 27, 31, 3, 126, 142, 13)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 140, 6, 58, 231, 192, 8, 160)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 39, 251, 153, 6, 255, 160, 132)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(16, 195, 245, 152, 44, 204, 206, 86)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 16, 126, 88, 211, 46, 70, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_));
v___x_93_ = 1;
v___x_94_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_));
v___x_95_ = l_Lean_registerTraceClass(v___x_92_, v___x_93_, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2____boxed(lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_();
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_));
v___x_118_ = 1;
v___x_119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_));
v___x_120_ = l_Lean_registerTraceClass(v___x_117_, v___x_118_, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2____boxed(lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_();
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_142_; uint8_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_));
v___x_143_ = 1;
v___x_144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_));
v___x_145_ = l_Lean_registerTraceClass(v___x_142_, v___x_143_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2____boxed(lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_();
return v_res_147_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_unsigned_to_nat(3053287543u);
v___x_155_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_156_ = l_Lean_Name_num___override(v___x_155_, v___x_154_);
return v___x_156_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_158_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_);
v___x_159_ = l_Lean_Name_str___override(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_161_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_);
v___x_162_ = l_Lean_Name_str___override(v___x_161_, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_unsigned_to_nat(2u);
v___x_164_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_);
v___x_165_ = l_Lean_Name_num___override(v___x_164_, v___x_163_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_));
v___x_168_ = 1;
v___x_169_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_);
v___x_170_ = l_Lean_registerTraceClass(v___x_167_, v___x_168_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2____boxed(lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_();
return v_res_172_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_unsigned_to_nat(2526460641u);
v___x_180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_181_ = l_Lean_Name_num___override(v___x_180_, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_183_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_);
v___x_184_ = l_Lean_Name_str___override(v___x_183_, v___x_182_);
return v___x_184_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_186_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_);
v___x_187_ = l_Lean_Name_str___override(v___x_186_, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lean_unsigned_to_nat(2u);
v___x_189_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_);
v___x_190_ = l_Lean_Name_num___override(v___x_189_, v___x_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_));
v___x_193_ = 0;
v___x_194_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_);
v___x_195_ = l_Lean_registerTraceClass(v___x_192_, v___x_193_, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2____boxed(lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_();
return v_res_197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_unsigned_to_nat(4273416105u);
v___x_206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_207_ = l_Lean_Name_num___override(v___x_206_, v___x_205_);
return v___x_207_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_209_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_);
v___x_210_ = l_Lean_Name_str___override(v___x_209_, v___x_208_);
return v___x_210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_4268171306____hygCtx___hyg_2_));
v___x_212_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_);
v___x_213_ = l_Lean_Name_str___override(v___x_212_, v___x_211_);
return v___x_213_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_unsigned_to_nat(2u);
v___x_215_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_);
v___x_216_ = l_Lean_Name_num___override(v___x_215_, v___x_214_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_218_; uint8_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_));
v___x_219_ = 1;
v___x_220_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_);
v___x_221_ = l_Lean_registerTraceClass(v___x_218_, v___x_219_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2____boxed(lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_();
return v_res_223_;
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
res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1674345266____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1090948466____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_1675791195____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_3053287543____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_2526460641____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Cbv_4273416105____hygCtx___hyg_2_();
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
