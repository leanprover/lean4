// Lean compiler output
// Module: Lean.Meta.Tactic.Simp
// Imports: public import Lean.Meta.Tactic.Simp.SimpTheorems public import Lean.Meta.Tactic.Simp.SimpCongrTheorems public import Lean.Meta.Tactic.Simp.Types public import Lean.Meta.Tactic.Simp.Main public import Lean.Meta.Tactic.Simp.Rewrite public import Lean.Meta.Tactic.Simp.SimpAll public import Lean.Meta.Tactic.Simp.Simproc public import Lean.Meta.Tactic.Simp.BuiltinSimprocs public import Lean.Meta.Tactic.Simp.RegisterCommand public import Lean.Meta.Tactic.Simp.Attr public import Lean.Meta.Tactic.Simp.Diagnostics public import Lean.Meta.Tactic.Simp.Arith
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 18, 104, 2, 176, 25, 65, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(203, 9, 234, 253, 232, 127, 99, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(182, 36, 205, 214, 225, 177, 90, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 45, 45, 88, 52, 85, 28, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 126, 124, 2, 142, 30, 205, 125)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 34, 41, 191, 87, 50, 104, 129)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 105, 25, 240, 86, 99, 201, 211)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 66, 17, 204, 245, 109, 134, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(219, 148, 234, 222, 135, 136, 75, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 51, 244, 254, 124, 142, 109, 156)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1719608285) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(204, 27, 222, 134, 76, 63, 44, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(67, 173, 110, 197, 236, 254, 131, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 152, 124, 185, 215, 178, 134, 159)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(102, 67, 147, 2, 202, 217, 124, 149)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 18, 104, 2, 176, 25, 65, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(41, 160, 244, 6, 151, 149, 13, 175)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "discharge"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 18, 104, 2, 176, 25, 65, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(137, 214, 139, 105, 48, 33, 191, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1097110872) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(151, 4, 101, 239, 154, 193, 148, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(156, 215, 136, 72, 228, 23, 178, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(104, 138, 83, 72, 129, 104, 176, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(41, 231, 80, 203, 213, 235, 117, 195)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rewrite"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 18, 104, 2, 176, 25, 65, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 22, 186, 64, 96, 9, 151, 73)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1156789139) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(177, 136, 108, 197, 166, 34, 167, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 253, 142, 255, 16, 72, 0, 181)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 111, 95, 3, 167, 218, 133, 103)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(207, 128, 180, 181, 106, 223, 98, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "backwardDefEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 18, 104, 2, 176, 25, 65, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 110, 171, 41, 36, 30, 226, 140)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unify"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 18, 104, 2, 176, 25, 65, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(190, 130, 190, 16, 161, 70, 238, 162)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1418113237) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(144, 82, 74, 217, 252, 37, 142, 192)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 40, 159, 24, 148, 92, 27, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 24, 88, 153, 169, 49, 205, 120)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(10, 3, 123, 102, 206, 151, 252, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ground"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 18, 104, 2, 176, 25, 65, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(177, 141, 3, 232, 9, 172, 52, 6)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)(((size_t)(793727544) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(207, 57, 155, 181, 116, 107, 58, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(132, 122, 194, 124, 111, 149, 159, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(16, 224, 49, 98, 41, 235, 198, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(129, 104, 158, 46, 117, 164, 132, 70)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "loopProtection"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 18, 104, 2, 176, 25, 65, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(240, 184, 129, 165, 74, 170, 27, 160)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)(((size_t)(768544759) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(197, 226, 212, 52, 244, 154, 56, 5)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(86, 115, 166, 247, 235, 93, 190, 26)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(42, 173, 133, 149, 113, 255, 183, 64)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(19, 116, 146, 2, 204, 106, 226, 122)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "numSteps"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 18, 104, 2, 176, 25, 65, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(163, 202, 121, 219, 52, 103, 253, 190)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)(((size_t)(581839081) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(80, 215, 245, 242, 89, 248, 223, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(199, 24, 11, 23, 119, 159, 199, 172)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 45, 21, 55, 211, 108, 92, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(74, 97, 16, 76, 189, 148, 16, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "heads"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 18, 104, 2, 176, 25, 65, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 243, 74, 195, 146, 136, 98, 64)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)(((size_t)(888696210) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(241, 134, 7, 73, 198, 131, 204, 113)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(18, 141, 35, 101, 32, 73, 118, 242)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(190, 218, 2, 246, 94, 153, 6, 110)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(143, 162, 105, 244, 112, 43, 36, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 248, 27, 31, 3, 126, 142, 13)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 140, 6, 58, 231, 192, 8, 160)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 39, 251, 153, 6, 255, 160, 132)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(66, 96, 215, 110, 82, 218, 253, 207)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),((lean_object*)(((size_t)(337957312) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(138, 99, 181, 156, 7, 191, 239, 104)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 70, 215, 202, 241, 99, 120, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 133, 160, 194, 66, 77, 100, 32)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(40, 32, 224, 94, 54, 206, 65, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 248, 27, 31, 3, 126, 142, 13)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 140, 6, 58, 231, 192, 8, 160)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 39, 251, 153, 6, 255, 160, 132)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(66, 96, 215, 110, 82, 218, 253, 207)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 183, 139, 101, 67, 3, 30, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2____boxed(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_67_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_));
v___x_68_ = 0;
v___x_69_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_));
v___x_70_ = l_Lean_registerTraceClass(v___x_67_, v___x_68_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_71_;
v_res_71_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_();
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2____boxed(lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_();
return v_res_73_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(3870689133u);
v___x_81_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_));
v___x_82_ = l_Lean_Name_num___override(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_));
v___x_84_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_);
v___x_85_ = l_Lean_Name_str___override(v___x_84_, v___x_83_);
return v___x_85_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_));
v___x_87_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_);
v___x_88_ = l_Lean_Name_str___override(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_unsigned_to_nat(2u);
v___x_90_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_);
v___x_91_ = l_Lean_Name_num___override(v___x_90_, v___x_89_);
return v___x_91_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_));
v___x_94_ = 1;
v___x_95_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_);
v___x_96_ = l_Lean_registerTraceClass(v___x_93_, v___x_94_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_97_;
v_res_97_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_();
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2____boxed(lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_();
return v_res_99_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_));
v___x_120_ = 1;
v___x_121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_));
v___x_122_ = l_Lean_registerTraceClass(v___x_119_, v___x_120_, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_123_;
v_res_123_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_();
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2____boxed(lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_();
return v_res_125_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_145_; uint8_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_));
v___x_146_ = 1;
v___x_147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_));
v___x_148_ = l_Lean_registerTraceClass(v___x_145_, v___x_146_, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_149_;
v_res_149_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_();
stack->m_obj
 = v_res_149_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2____boxed(lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_();
return v_res_151_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_unsigned_to_nat(4009644764u);
v___x_159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_));
v___x_160_ = l_Lean_Name_num___override(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_));
v___x_162_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_);
v___x_163_ = l_Lean_Name_str___override(v___x_162_, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_));
v___x_165_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_);
v___x_166_ = l_Lean_Name_str___override(v___x_165_, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_unsigned_to_nat(2u);
v___x_168_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_);
v___x_169_ = l_Lean_Name_num___override(v___x_168_, v___x_167_);
return v___x_169_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_));
v___x_172_ = 1;
v___x_173_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_);
v___x_174_ = l_Lean_registerTraceClass(v___x_171_, v___x_172_, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_175_;
v_res_175_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_();
stack->m_obj
 = v_res_175_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2____boxed(lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_();
return v_res_177_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_197_; uint8_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_));
v___x_198_ = 1;
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_));
v___x_200_ = l_Lean_registerTraceClass(v___x_197_, v___x_198_, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_201_;
v_res_201_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_();
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2____boxed(lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_();
return v_res_203_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_));
v___x_224_ = 1;
v___x_225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_));
v___x_226_ = l_Lean_registerTraceClass(v___x_223_, v___x_224_, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_227_;
v_res_227_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_();
stack->m_obj
 = v_res_227_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2____boxed(lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_();
return v_res_229_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_249_; uint8_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_249_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_));
v___x_250_ = 1;
v___x_251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_));
v___x_252_ = l_Lean_registerTraceClass(v___x_249_, v___x_250_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_253_;
v_res_253_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_();
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2____boxed(lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_();
return v_res_255_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_));
v___x_276_ = 0;
v___x_277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_));
v___x_278_ = l_Lean_registerTraceClass(v___x_275_, v___x_276_, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_279_;
v_res_279_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_();
stack->m_obj
 = v_res_279_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2____boxed(lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_();
return v_res_281_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_301_; uint8_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_));
v___x_302_ = 0;
v___x_303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_));
v___x_304_ = l_Lean_registerTraceClass(v___x_301_, v___x_302_, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_305_;
v_res_305_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_();
stack->m_obj
 = v_res_305_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2____boxed(lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_();
return v_res_307_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_));
v___x_328_ = 0;
v___x_329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_));
v___x_330_ = l_Lean_registerTraceClass(v___x_327_, v___x_328_, v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_331_;
v_res_331_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_();
stack->m_obj
 = v_res_331_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2____boxed(lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_();
return v_res_333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_unsigned_to_nat(2225316046u);
v___x_341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_));
v___x_342_ = l_Lean_Name_num___override(v___x_341_, v___x_340_);
return v___x_342_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_));
v___x_344_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_);
v___x_345_ = l_Lean_Name_str___override(v___x_344_, v___x_343_);
return v___x_345_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_));
v___x_347_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_);
v___x_348_ = l_Lean_Name_str___override(v___x_347_, v___x_346_);
return v___x_348_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = lean_unsigned_to_nat(2u);
v___x_350_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_);
v___x_351_ = l_Lean_Name_num___override(v___x_350_, v___x_349_);
return v___x_351_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_353_; uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_353_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_));
v___x_354_ = 1;
v___x_355_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_);
v___x_356_ = l_Lean_registerTraceClass(v___x_353_, v___x_354_, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_357_;
v_res_357_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_();
stack->m_obj
 = v_res_357_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2____boxed(lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_();
return v_res_359_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_SimpAll(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Diagnostics(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpAll(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1719608285____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_3870689133____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1097110872____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1156789139____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_4009644764____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_1418113237____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_793727544____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_768544759____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_581839081____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_888696210____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_337957312____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Simp_2225316046____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpAll(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Diagnostics(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpAll(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp(builtin);
}
#ifdef __cplusplus
}
#endif
