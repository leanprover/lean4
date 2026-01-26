// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC
// Imports: public import Lean.Meta.Tactic.Grind.AC.Types public import Lean.Meta.Tactic.Grind.AC.Util public import Lean.Meta.Tactic.Grind.AC.Var public import Lean.Meta.Tactic.Grind.AC.Internalize public import Lean.Meta.Tactic.Grind.AC.Eq public import Lean.Meta.Tactic.Grind.AC.Seq public import Lean.Meta.Tactic.Grind.AC.Proof public import Lean.Meta.Tactic.Grind.AC.DenoteExpr public import Lean.Meta.Tactic.Grind.AC.ToExpr public import Lean.Meta.Tactic.Grind.AC.VarRename public import Lean.Meta.Tactic.Grind.AC.PP public import Lean.Meta.Tactic.Grind.AC.Inv public import Lean.Meta.Tactic.Grind.AC.Action
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ac"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(9, 156, 240, 157, 146, 53, 54, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "AC"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(98, 173, 184, 202, 154, 63, 120, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(195, 242, 176, 140, 52, 16, 241, 150)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(142, 156, 176, 168, 3, 176, 159, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(218, 60, 57, 47, 250, 182, 202, 157)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 248, 228, 69, 166, 7, 253, 184)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 73, 62, 186, 82, 218, 177, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(162, 74, 239, 165, 223, 23, 35, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 5, 33, 41, 151, 35, 178, 50)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(22, 251, 158, 124, 177, 96, 37, 149)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 220, 221, 90, 156, 163, 113, 6)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(247, 149, 214, 127, 194, 172, 56, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(57, 38, 247, 72, 49, 163, 249, 159)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 45, 37, 206, 122, 101, 36, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(9, 156, 240, 157, 146, 53, 54, 12)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(171, 121, 118, 166, 1, 171, 169, 237)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)(((size_t)(728928005) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(253, 252, 151, 108, 150, 169, 231, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(190, 216, 51, 183, 113, 185, 40, 110)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(50, 79, 14, 235, 178, 243, 0, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(11, 228, 115, 67, 157, 220, 96, 23)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "internalize"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(9, 156, 240, 157, 146, 53, 54, 12)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(148, 182, 35, 4, 116, 197, 166, 64)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2063561435) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(222, 249, 113, 81, 114, 249, 59, 193)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 10, 249, 117, 82, 20, 158, 16)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(97, 39, 200, 74, 207, 225, 122, 69)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(60, 107, 139, 61, 16, 133, 199, 127)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "basis"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(9, 156, 240, 157, 146, 53, 54, 12)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 50, 12, 85, 24, 137, 101, 42)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "op"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 146, 207, 37, 132, 85, 33, 194)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 114, 160, 105, 78, 163, 71, 213)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1142390893) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(222, 196, 148, 167, 166, 134, 229, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 25, 198, 153, 189, 126, 97, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(97, 184, 95, 135, 53, 74, 179, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(60, 208, 157, 81, 121, 215, 144, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 146, 207, 37, 132, 85, 33, 194)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 212, 29, 201, 249, 64, 34, 231)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "check"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 146, 207, 37, 132, 85, 33, 194)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(191, 43, 33, 40, 253, 241, 64, 63)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "queue"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 146, 207, 37, 132, 85, 33, 194)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 176, 25, 61, 76, 87, 21, 89)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1839863265) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 159, 142, 71, 246, 168, 227, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(66, 251, 114, 27, 64, 93, 175, 195)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(206, 20, 42, 99, 93, 95, 216, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(31, 99, 97, 126, 205, 229, 157, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "superpose"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 146, 207, 37, 132, 85, 33, 194)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 3, 205, 175, 108, 182, 147, 66)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 146, 207, 37, 132, 85, 33, 194)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 145, 208, 88, 181, 5, 239, 4)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1601100932) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(249, 2, 172, 183, 109, 172, 47, 195)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 20, 233, 108, 48, 5, 195, 114)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(22, 75, 178, 110, 165, 0, 163, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(87, 28, 87, 169, 133, 169, 233, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_internalize___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value;
lean_object* l_Lean_Meta_Grind_AC_processNewEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_processNewEq___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value;
lean_object* l_Lean_Meta_Grind_AC_processNewDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_processNewDiseq___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_;
lean_object* l_Lean_Meta_Grind_Action_ac___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_ac___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value;
lean_object* l_Lean_Meta_Grind_AC_check_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_check_x27___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value;
lean_object* l_Lean_Meta_Grind_AC_checkInvariants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_checkInvariants___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value;
extern lean_object* l_Lean_Meta_Grind_AC_acExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3214356224u);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_3 = 0;
x_4 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3749149120u);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_));
x_3 = 0;
x_4 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4001898889u);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_));
x_3 = 0;
x_4 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3362372890u);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_));
x_3 = 0;
x_4 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3823406372u);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_));
x_3 = 0;
x_4 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
x_14 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2____boxed), 12, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = l_Lean_Meta_Grind_AC_acExt;
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_));
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_));
x_6 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_;
x_7 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_));
x_8 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_));
x_9 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_));
x_10 = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Var(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Internalize(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Eq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Seq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Proof(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_VarRename(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_PP(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Inv(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Action(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_AC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_Eq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
