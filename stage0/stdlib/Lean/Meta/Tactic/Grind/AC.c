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
lean_object* l_Lean_Meta_Grind_Action_ac___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_processNewEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_AC_acExt;
lean_object* l_Lean_Meta_Grind_AC_processNewDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_check_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_checkInvariants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ac"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(9, 156, 240, 157, 146, 53, 54, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__value;
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "op"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__value;
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
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
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_internalize___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_processNewEq___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_processNewDiseq___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2____boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_ac___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_check_x27___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_checkInvariants___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_unsigned_to_nat(3214356224u);
v___x_69_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_70_ = l_Lean_Name_num___override(v___x_69_, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_73_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_);
v___x_74_ = l_Lean_Name_str___override(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_77_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_);
v___x_78_ = l_Lean_Name_str___override(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(2u);
v___x_80_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_);
v___x_81_ = l_Lean_Name_num___override(v___x_80_, v___x_79_);
return v___x_81_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_83_; uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_84_ = 0;
v___x_85_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_);
v___x_86_ = l_Lean_registerTraceClass(v___x_83_, v___x_84_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_87_;
v_res_87_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_();
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2____boxed(lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_();
return v_res_89_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_));
v___x_109_ = 0;
v___x_110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_));
v___x_111_ = l_Lean_registerTraceClass(v___x_108_, v___x_109_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_112_;
v_res_112_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_();
stack->m_obj
 = v_res_112_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2____boxed(lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_();
return v_res_114_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_));
v___x_134_ = 0;
v___x_135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_));
v___x_136_ = l_Lean_registerTraceClass(v___x_133_, v___x_134_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_137_;
v_res_137_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_();
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2____boxed(lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_();
return v_res_139_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_unsigned_to_nat(3749149120u);
v___x_146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_147_ = l_Lean_Name_num___override(v___x_146_, v___x_145_);
return v___x_147_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_149_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_);
v___x_150_ = l_Lean_Name_str___override(v___x_149_, v___x_148_);
return v___x_150_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_152_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_);
v___x_153_ = l_Lean_Name_str___override(v___x_152_, v___x_151_);
return v___x_153_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_unsigned_to_nat(2u);
v___x_155_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_);
v___x_156_ = l_Lean_Name_num___override(v___x_155_, v___x_154_);
return v___x_156_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_158_; uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_));
v___x_159_ = 0;
v___x_160_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_);
v___x_161_ = l_Lean_registerTraceClass(v___x_158_, v___x_159_, v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_162_;
v_res_162_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_();
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2____boxed(lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_();
return v_res_164_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_185_; uint8_t v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_));
v___x_186_ = 0;
v___x_187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_));
v___x_188_ = l_Lean_registerTraceClass(v___x_185_, v___x_186_, v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_189_;
v_res_189_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_();
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2____boxed(lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_();
return v_res_191_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_unsigned_to_nat(4001898889u);
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_200_ = l_Lean_Name_num___override(v___x_199_, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_202_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_);
v___x_203_ = l_Lean_Name_str___override(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_205_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_);
v___x_206_ = l_Lean_Name_str___override(v___x_205_, v___x_204_);
return v___x_206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_unsigned_to_nat(2u);
v___x_208_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_);
v___x_209_ = l_Lean_Name_num___override(v___x_208_, v___x_207_);
return v___x_209_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_211_; uint8_t v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_));
v___x_212_ = 0;
v___x_213_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_);
v___x_214_ = l_Lean_registerTraceClass(v___x_211_, v___x_212_, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_215_;
v_res_215_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_();
stack->m_obj
 = v_res_215_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2____boxed(lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_();
return v_res_217_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_unsigned_to_nat(3362372890u);
v___x_225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_226_ = l_Lean_Name_num___override(v___x_225_, v___x_224_);
return v___x_226_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_228_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_);
v___x_229_ = l_Lean_Name_str___override(v___x_228_, v___x_227_);
return v___x_229_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_231_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_);
v___x_232_ = l_Lean_Name_str___override(v___x_231_, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_unsigned_to_nat(2u);
v___x_234_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_);
v___x_235_ = l_Lean_Name_num___override(v___x_234_, v___x_233_);
return v___x_235_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_237_; uint8_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_237_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_));
v___x_238_ = 0;
v___x_239_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_);
v___x_240_ = l_Lean_registerTraceClass(v___x_237_, v___x_238_, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_241_;
v_res_241_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_();
stack->m_obj
 = v_res_241_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2____boxed(lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_();
return v_res_243_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_));
v___x_264_ = 0;
v___x_265_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_));
v___x_266_ = l_Lean_registerTraceClass(v___x_263_, v___x_264_, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_267_;
v_res_267_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_();
stack->m_obj
 = v_res_267_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2____boxed(lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_();
return v_res_269_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_unsigned_to_nat(3823406372u);
v___x_277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_278_ = l_Lean_Name_num___override(v___x_277_, v___x_276_);
return v___x_278_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_280_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_);
v___x_281_ = l_Lean_Name_str___override(v___x_280_, v___x_279_);
return v___x_281_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_));
v___x_283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_);
v___x_284_ = l_Lean_Name_str___override(v___x_283_, v___x_282_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_unsigned_to_nat(2u);
v___x_286_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_);
v___x_287_ = l_Lean_Name_num___override(v___x_286_, v___x_285_);
return v___x_287_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_));
v___x_290_ = 0;
v___x_291_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_);
v___x_292_ = l_Lean_registerTraceClass(v___x_289_, v___x_290_, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_293_;
v_res_293_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_();
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2____boxed(lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_();
return v_res_295_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_));
v___x_316_ = 0;
v___x_317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_));
v___x_318_ = l_Lean_registerTraceClass(v___x_315_, v___x_316_, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_319_;
v_res_319_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_();
stack->m_obj
 = v_res_319_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2____boxed(lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_();
return v_res_321_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_(uint8_t v___x_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_box(v___x_322_);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
uint8_t v___x_322_ = stack[0].m_num;
lean_object* v___y_323_ = stack[1].m_obj;
lean_object* v___y_324_ = stack[2].m_obj;
lean_object* v___y_325_ = stack[3].m_obj;
lean_object* v___y_326_ = stack[4].m_obj;
lean_object* v___y_327_ = stack[5].m_obj;
lean_object* v___y_328_ = stack[6].m_obj;
lean_object* v___y_329_ = stack[7].m_obj;
lean_object* v___y_330_ = stack[8].m_obj;
lean_object* v___y_331_ = stack[9].m_obj;
lean_object* v___y_332_ = stack[10].m_obj;
lean_object* v_res_336_;
v_res_336_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_(v___x_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
stack->m_obj
 = v_res_336_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2____boxed(lean_object* v___x_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
uint8_t v___x_511__boxed_349_; lean_object* v_res_350_; 
v___x_511__boxed_349_ = lean_unbox(v___x_337_);
v_res_350_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_(v___x_511__boxed_349_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec(v___y_338_);
return v_res_350_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_361_ = l_Lean_Meta_Grind_AC_acExt;
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_));
v___x_363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_));
v___x_364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_));
v___f_365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_));
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_));
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_));
v___x_368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_));
v___x_369_ = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(v___x_361_, v___x_362_, v___x_363_, v___x_364_, v___f_365_, v___x_366_, v___x_367_, v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_370_;
v_res_370_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_();
stack->m_obj
 = v_res_370_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2____boxed(lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_();
return v_res_372_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Eq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Proof(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Inv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Action(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Eq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3214356224____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_728928005____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_2063561435____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3749149120____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1142390893____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_4001898889____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3362372890____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1839863265____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3823406372____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_1601100932____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_AC_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_3475356978____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_AC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_AC(builtin);
}
#ifdef __cplusplus
}
#endif
