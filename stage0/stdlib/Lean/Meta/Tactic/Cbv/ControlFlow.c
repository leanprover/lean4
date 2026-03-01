// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.ControlFlow
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.Simp.Result import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.Simp.ControlFlow import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.InferType import Lean.Meta.Sym.Simp.App import Lean.Meta.SynthInstance import Lean.Meta.WHNF import Lean.Meta.AppBuilder import Init.Sym.Lemmas import Lean.Meta.Tactic.Cbv.TheoremsLookup import Lean.Meta.Tactic.Cbv.Opaque
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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__3_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_false_of_decide"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(171, 157, 112, 124, 91, 52, 64, 56)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instDecidableFalse"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(49, 216, 212, 175, 154, 176, 165, 174)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__12_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ite_cond_congr"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__14_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(149, 115, 5, 135, 85, 70, 205, 95)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ite_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__16 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(217, 231, 214, 152, 207, 100, 121, 38)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "eq_true_of_decide"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__18 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(10, 132, 193, 70, 136, 209, 66, 149)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "instDecidableTrue"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__21 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__21_value),LEAN_SCALAR_PTR_LITERAL(45, 239, 189, 64, 160, 216, 116, 23)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ite_true"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__24 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__24_value),LEAN_SCALAR_PTR_LITERAL(28, 219, 17, 217, 43, 100, 109, 98)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "decidable_of_decidable_of_eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__26 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(124, 56, 184, 219, 10, 120, 143, 114)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ite_cond_eq_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__29 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__29_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__29_value),LEAN_SCALAR_PTR_LITERAL(4, 35, 104, 204, 105, 138, 171, 217)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ite_cond_eq_true"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__31 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__31_value),LEAN_SCALAR_PTR_LITERAL(217, 214, 153, 207, 191, 74, 245, 103)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__32 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__32_value;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFn(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mpr_prop"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(169, 177, 76, 157, 211, 15, 217, 219)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
lean_object* l_Lean_mkBVar(lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mpr_not"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(121, 56, 250, 51, 9, 123, 141, 181)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(155, 21, 178, 198, 97, 164, 246, 137)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dite_cond_congr"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(72, 238, 116, 219, 106, 19, 52, 46)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dite_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(78, 119, 178, 178, 249, 126, 188, 7)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__19 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__19_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__21 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__21_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__22 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dite_true"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25_value),LEAN_SCALAR_PTR_LITERAL(65, 218, 189, 96, 14, 237, 238, 210)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__26 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__26_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "dite_cond_eq_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27_value),LEAN_SCALAR_PTR_LITERAL(153, 159, 146, 90, 178, 85, 98, 212)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__28 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__28_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "dite_cond_eq_true"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29_value),LEAN_SCALAR_PTR_LITERAL(13, 104, 142, 126, 111, 138, 152, 2)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__30 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__30_value;
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(lean_object*, lean_object*);
uint8_t l_Lean_instBEqReducibilityStatus_beq(uint8_t, uint8_t);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0_value;
lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0_value;
lean_object* l_Lean_Meta_reduceRecMatcher_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__2_value),LEAN_SCALAR_PTR_LITERAL(158, 146, 92, 125, 27, 135, 153, 152)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__3_value;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_15 = lean_st_ref_get(x_4);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_10 = x_4;
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_17; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
lean_inc(x_4);
lean_inc_ref(x_2);
x_18 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_dec_ref(x_18);
x_10 = x_4;
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_18, 0);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
x_20 = x_18;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
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
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_17, 0);
x_34 = !lean_is_exclusive(x_17);
if (x_34 == 0)
{
x_28 = x_17;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_17);
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
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_app___override(x_1, x_2);
x_13 = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(x_12, x_10);
lean_dec(x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_14 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(x_1, x_2, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(x_15, x_3, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_15 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(x_16, x_4, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_16 = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1_spec__2(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(x_17, x_5, x_9, x_10, x_11, x_12, x_13, x_14);
return x_18;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
return x_16;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_16; uint8_t x_17; 
lean_inc_ref(x_2);
x_16 = l_Lean_Expr_cleanupAnnotations(x_2);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__1));
x_33 = l_Lean_Expr_isConstOf(x_31, x_32);
if (x_33 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_34; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_27);
x_34 = lean_sym_simp(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; uint8_t x_257; 
x_257 = !lean_is_exclusive(x_35);
if (x_257 == 0)
{
x_36 = x_35;
x_37 = x_257;
goto block_256;
}
else
{
lean_dec(x_35);
x_36 = lean_box(0);
x_37 = x_257;
goto block_256;
}
block_256:
{
lean_object* x_38; 
x_38 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_247; 
x_39 = lean_ctor_get(x_38, 0);
x_247 = !lean_is_exclusive(x_38);
if (x_247 == 0)
{
x_40 = x_38;
x_41 = x_247;
goto block_246;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_247;
goto block_246;
}
block_246:
{
uint8_t x_42; 
x_42 = lean_unbox(x_39);
if (x_42 == 0)
{
lean_object* x_43; 
lean_del_object(x_40);
x_43 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_229; 
x_44 = lean_ctor_get(x_43, 0);
x_229 = !lean_is_exclusive(x_43);
if (x_229 == 0)
{
x_45 = x_43;
x_46 = x_229;
goto block_228;
}
else
{
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_box(0);
x_46 = x_229;
goto block_228;
}
block_228:
{
uint8_t x_47; 
x_47 = lean_unbox(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_del_object(x_45);
lean_dec(x_39);
x_48 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_24);
lean_inc_ref(x_27);
x_49 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_48, x_27, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_51 = lean_sym_simp(x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_210; 
x_52 = lean_ctor_get(x_51, 0);
x_210 = !lean_is_exclusive(x_51);
if (x_210 == 0)
{
x_53 = x_51;
x_54 = x_210;
goto block_209;
}
else
{
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_box(0);
x_54 = x_210;
goto block_209;
}
block_209:
{
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_55; uint8_t x_56; uint8_t x_64; 
lean_dec(x_44);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_64 = !lean_is_exclusive(x_52);
if (x_64 == 0)
{
x_55 = x_52;
x_56 = x_64;
goto block_63;
}
else
{
lean_dec(x_52);
x_55 = lean_box(0);
x_56 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 0, 1);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
lean_ctor_set_uint8(x_57, 0, x_33);
if (x_54 == 0)
{
lean_ctor_set(x_53, 0, x_57);
x_58 = x_53;
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
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_208; 
lean_del_object(x_53);
x_65 = lean_ctor_get(x_52, 0);
x_66 = lean_ctor_get(x_52, 1);
x_208 = !lean_is_exclusive(x_52);
if (x_208 == 0)
{
x_67 = x_52;
x_68 = x_208;
goto block_207;
}
else
{
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_52);
x_67 = lean_box(0);
x_68 = x_208;
goto block_207;
}
block_207:
{
lean_object* x_69; 
x_69 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_65, x_6);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = lean_unbox(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_44);
x_72 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_65, x_6);
lean_dec_ref(x_65);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_137; 
x_73 = lean_ctor_get(x_72, 0);
x_137 = !lean_is_exclusive(x_72);
if (x_137 == 0)
{
x_74 = x_72;
x_75 = x_137;
goto block_136;
}
else
{
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_box(0);
x_75 = x_137;
goto block_136;
}
block_136:
{
uint8_t x_76; 
x_76 = lean_unbox(x_73);
lean_dec(x_73);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_70);
lean_del_object(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
if (x_37 == 0)
{
x_77 = x_36;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 0, 1);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
lean_ctor_set_uint8(x_77, 0, x_33);
if (x_75 == 0)
{
lean_ctor_set(x_74, 0, x_77);
x_78 = x_74;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_77);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
else
{
lean_object* x_83; 
lean_del_object(x_74);
lean_del_object(x_36);
x_83 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
x_86 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_87 = lean_unsigned_to_nat(4u);
x_88 = l_Lean_Expr_getBoundedAppFn(x_87, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_84);
x_89 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_88, x_84, x_86, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = l_Lean_mkApp3(x_85, x_27, x_24, x_66);
x_92 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_93 = l_Lean_Expr_replaceFn(x_2, x_92);
x_94 = l_Lean_mkApp3(x_93, x_84, x_86, x_91);
x_95 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_96 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_97 = l_Lean_mkConst(x_95, x_96);
lean_inc_ref(x_18);
x_98 = l_Lean_mkApp3(x_97, x_30, x_21, x_18);
lean_inc_ref(x_18);
x_99 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_90, x_94, x_18, x_98, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_111; 
x_100 = lean_ctor_get(x_99, 0);
x_111 = !lean_is_exclusive(x_99);
if (x_111 == 0)
{
x_101 = x_99;
x_102 = x_111;
goto block_110;
}
else
{
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_box(0);
x_102 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_103; 
if (x_68 == 0)
{
lean_ctor_set(x_67, 1, x_100);
lean_ctor_set(x_67, 0, x_18);
x_103 = x_67;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_109, 0, x_18);
lean_ctor_set(x_109, 1, x_100);
x_103 = x_109;
goto block_108;
}
block_108:
{
uint8_t x_104; lean_object* x_105; 
x_104 = lean_unbox(x_70);
lean_dec(x_70);
lean_ctor_set_uint8(x_103, sizeof(void*)*2, x_104);
if (x_102 == 0)
{
lean_ctor_set(x_101, 0, x_103);
x_105 = x_101;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_103);
x_105 = x_107;
goto block_106;
}
block_106:
{
return x_105;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_119; 
lean_dec(x_70);
lean_del_object(x_67);
lean_dec_ref(x_18);
x_112 = lean_ctor_get(x_99, 0);
x_119 = !lean_is_exclusive(x_99);
if (x_119 == 0)
{
x_113 = x_99;
x_114 = x_119;
goto block_118;
}
else
{
lean_inc(x_112);
lean_dec(x_99);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
return x_115;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_127; 
lean_dec(x_84);
lean_dec(x_70);
lean_del_object(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_120 = lean_ctor_get(x_89, 0);
x_127 = !lean_is_exclusive(x_89);
if (x_127 == 0)
{
x_121 = x_89;
x_122 = x_127;
goto block_126;
}
else
{
lean_inc(x_120);
lean_dec(x_89);
x_121 = lean_box(0);
x_122 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_123; 
if (x_122 == 0)
{
x_123 = x_121;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_120);
x_123 = x_125;
goto block_124;
}
block_124:
{
return x_123;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_135; 
lean_dec(x_70);
lean_del_object(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_128 = lean_ctor_get(x_83, 0);
x_135 = !lean_is_exclusive(x_83);
if (x_135 == 0)
{
x_129 = x_83;
x_130 = x_135;
goto block_134;
}
else
{
lean_inc(x_128);
lean_dec(x_83);
x_129 = lean_box(0);
x_130 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_131; 
if (x_130 == 0)
{
x_131 = x_129;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_128);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
}
}
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_145; 
lean_dec(x_70);
lean_del_object(x_67);
lean_dec_ref(x_66);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_138 = lean_ctor_get(x_72, 0);
x_145 = !lean_is_exclusive(x_72);
if (x_145 == 0)
{
x_139 = x_72;
x_140 = x_145;
goto block_144;
}
else
{
lean_inc(x_138);
lean_dec(x_72);
x_139 = lean_box(0);
x_140 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_141; 
if (x_140 == 0)
{
x_141 = x_139;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_138);
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
lean_object* x_146; 
lean_dec(x_70);
lean_dec_ref(x_65);
lean_del_object(x_36);
x_146 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
x_148 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20);
x_149 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23);
x_150 = lean_unsigned_to_nat(4u);
x_151 = l_Lean_Expr_getBoundedAppFn(x_150, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_147);
x_152 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_151, x_147, x_149, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec_ref(x_152);
x_154 = l_Lean_mkApp3(x_148, x_27, x_24, x_66);
x_155 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_156 = l_Lean_Expr_replaceFn(x_2, x_155);
x_157 = l_Lean_mkApp3(x_156, x_147, x_149, x_154);
x_158 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25));
x_159 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_160 = l_Lean_mkConst(x_158, x_159);
lean_inc_ref(x_21);
x_161 = l_Lean_mkApp3(x_160, x_30, x_21, x_18);
lean_inc_ref(x_21);
x_162 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_153, x_157, x_21, x_161, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_174; 
x_163 = lean_ctor_get(x_162, 0);
x_174 = !lean_is_exclusive(x_162);
if (x_174 == 0)
{
x_164 = x_162;
x_165 = x_174;
goto block_173;
}
else
{
lean_inc(x_163);
lean_dec(x_162);
x_164 = lean_box(0);
x_165 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_166; 
if (x_68 == 0)
{
lean_ctor_set(x_67, 1, x_163);
lean_ctor_set(x_67, 0, x_21);
x_166 = x_67;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_172, 0, x_21);
lean_ctor_set(x_172, 1, x_163);
x_166 = x_172;
goto block_171;
}
block_171:
{
uint8_t x_167; lean_object* x_168; 
x_167 = lean_unbox(x_44);
lean_dec(x_44);
lean_ctor_set_uint8(x_166, sizeof(void*)*2, x_167);
if (x_165 == 0)
{
lean_ctor_set(x_164, 0, x_166);
x_168 = x_164;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_170, 0, x_166);
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
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_182; 
lean_del_object(x_67);
lean_dec(x_44);
lean_dec_ref(x_21);
x_175 = lean_ctor_get(x_162, 0);
x_182 = !lean_is_exclusive(x_162);
if (x_182 == 0)
{
x_176 = x_162;
x_177 = x_182;
goto block_181;
}
else
{
lean_inc(x_175);
lean_dec(x_162);
x_176 = lean_box(0);
x_177 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_178; 
if (x_177 == 0)
{
x_178 = x_176;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_175);
x_178 = x_180;
goto block_179;
}
block_179:
{
return x_178;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; uint8_t x_190; 
lean_dec(x_147);
lean_del_object(x_67);
lean_dec_ref(x_66);
lean_dec(x_44);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_183 = lean_ctor_get(x_152, 0);
x_190 = !lean_is_exclusive(x_152);
if (x_190 == 0)
{
x_184 = x_152;
x_185 = x_190;
goto block_189;
}
else
{
lean_inc(x_183);
lean_dec(x_152);
x_184 = lean_box(0);
x_185 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_186; 
if (x_185 == 0)
{
x_186 = x_184;
goto block_187;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_183);
x_186 = x_188;
goto block_187;
}
block_187:
{
return x_186;
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_198; 
lean_del_object(x_67);
lean_dec_ref(x_66);
lean_dec(x_44);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_191 = lean_ctor_get(x_146, 0);
x_198 = !lean_is_exclusive(x_146);
if (x_198 == 0)
{
x_192 = x_146;
x_193 = x_198;
goto block_197;
}
else
{
lean_inc(x_191);
lean_dec(x_146);
x_192 = lean_box(0);
x_193 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_194; 
if (x_193 == 0)
{
x_194 = x_192;
goto block_195;
}
else
{
lean_object* x_196; 
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_191);
x_194 = x_196;
goto block_195;
}
block_195:
{
return x_194;
}
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; uint8_t x_206; 
lean_del_object(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec(x_44);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_199 = lean_ctor_get(x_69, 0);
x_206 = !lean_is_exclusive(x_69);
if (x_206 == 0)
{
x_200 = x_69;
x_201 = x_206;
goto block_205;
}
else
{
lean_inc(x_199);
lean_dec(x_69);
x_200 = lean_box(0);
x_201 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_202; 
if (x_201 == 0)
{
x_202 = x_200;
goto block_203;
}
else
{
lean_object* x_204; 
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_199);
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
}
}
}
else
{
lean_dec(x_44);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_51;
}
}
else
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; uint8_t x_218; 
lean_dec(x_44);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_211 = lean_ctor_get(x_49, 0);
x_218 = !lean_is_exclusive(x_49);
if (x_218 == 0)
{
x_212 = x_49;
x_213 = x_218;
goto block_217;
}
else
{
lean_inc(x_211);
lean_dec(x_49);
x_212 = lean_box(0);
x_213 = x_218;
goto block_217;
}
block_217:
{
lean_object* x_214; 
if (x_213 == 0)
{
x_214 = x_212;
goto block_215;
}
else
{
lean_object* x_216; 
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_211);
x_214 = x_216;
goto block_215;
}
block_215:
{
return x_214;
}
}
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; 
lean_dec(x_44);
lean_del_object(x_36);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_219 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_220 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_221 = l_Lean_mkConst(x_219, x_220);
lean_inc_ref(x_18);
x_222 = l_Lean_mkApp3(x_221, x_30, x_21, x_18);
x_223 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_223, 0, x_18);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_unbox(x_39);
lean_dec(x_39);
lean_ctor_set_uint8(x_223, sizeof(void*)*2, x_224);
if (x_46 == 0)
{
lean_ctor_set(x_45, 0, x_223);
x_225 = x_45;
goto block_226;
}
else
{
lean_object* x_227; 
x_227 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_227, 0, x_223);
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
lean_dec(x_39);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_230 = lean_ctor_get(x_43, 0);
x_237 = !lean_is_exclusive(x_43);
if (x_237 == 0)
{
x_231 = x_43;
x_232 = x_237;
goto block_236;
}
else
{
lean_inc(x_230);
lean_dec(x_43);
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
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_39);
lean_del_object(x_36);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_238 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25));
x_239 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_240 = l_Lean_mkConst(x_238, x_239);
lean_inc_ref(x_21);
x_241 = l_Lean_mkApp3(x_240, x_30, x_21, x_18);
x_242 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_242, 0, x_21);
lean_ctor_set(x_242, 1, x_241);
lean_ctor_set_uint8(x_242, sizeof(void*)*2, x_1);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_242);
x_243 = x_40;
goto block_244;
}
else
{
lean_object* x_245; 
x_245 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_245, 0, x_242);
x_243 = x_245;
goto block_244;
}
block_244:
{
return x_243;
}
}
}
}
else
{
lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_255; 
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_248 = lean_ctor_get(x_38, 0);
x_255 = !lean_is_exclusive(x_38);
if (x_255 == 0)
{
x_249 = x_38;
x_250 = x_255;
goto block_254;
}
else
{
lean_inc(x_248);
lean_dec(x_38);
x_249 = lean_box(0);
x_250 = x_255;
goto block_254;
}
block_254:
{
lean_object* x_251; 
if (x_250 == 0)
{
x_251 = x_249;
goto block_252;
}
else
{
lean_object* x_253; 
x_253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_253, 0, x_248);
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
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; uint8_t x_340; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
x_258 = lean_ctor_get(x_35, 0);
x_259 = lean_ctor_get(x_35, 1);
x_340 = !lean_is_exclusive(x_35);
if (x_340 == 0)
{
x_260 = x_35;
x_261 = x_340;
goto block_339;
}
else
{
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_35);
x_260 = lean_box(0);
x_261 = x_340;
goto block_339;
}
block_339:
{
lean_object* x_262; 
x_262 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_258, x_6);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; uint8_t x_330; 
x_263 = lean_ctor_get(x_262, 0);
x_330 = !lean_is_exclusive(x_262);
if (x_330 == 0)
{
x_264 = x_262;
x_265 = x_330;
goto block_329;
}
else
{
lean_inc(x_263);
lean_dec(x_262);
x_264 = lean_box(0);
x_265 = x_330;
goto block_329;
}
block_329:
{
uint8_t x_266; 
x_266 = lean_unbox(x_263);
if (x_266 == 0)
{
lean_object* x_267; 
lean_del_object(x_264);
x_267 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_258, x_6);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; uint8_t x_311; 
x_268 = lean_ctor_get(x_267, 0);
x_311 = !lean_is_exclusive(x_267);
if (x_311 == 0)
{
x_269 = x_267;
x_270 = x_311;
goto block_310;
}
else
{
lean_inc(x_268);
lean_dec(x_267);
x_269 = lean_box(0);
x_270 = x_311;
goto block_310;
}
block_310:
{
uint8_t x_271; 
x_271 = lean_unbox(x_268);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_del_object(x_269);
lean_dec(x_263);
x_272 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28);
lean_inc_ref(x_259);
lean_inc_ref(x_258);
x_273 = l_Lean_mkApp4(x_272, x_27, x_258, x_24, x_259);
x_274 = lean_unsigned_to_nat(4u);
x_275 = l_Lean_Expr_getBoundedAppFn(x_274, x_2);
lean_inc_ref(x_273);
lean_inc_ref(x_258);
x_276 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_275, x_258, x_273, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; uint8_t x_279; uint8_t x_291; 
x_277 = lean_ctor_get(x_276, 0);
x_291 = !lean_is_exclusive(x_276);
if (x_291 == 0)
{
x_278 = x_276;
x_279 = x_291;
goto block_290;
}
else
{
lean_inc(x_277);
lean_dec(x_276);
x_278 = lean_box(0);
x_279 = x_291;
goto block_290;
}
block_290:
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_280 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
x_281 = l_Lean_Expr_replaceFn(x_2, x_280);
x_282 = l_Lean_mkApp3(x_281, x_258, x_273, x_259);
if (x_261 == 0)
{
lean_ctor_set(x_260, 1, x_282);
lean_ctor_set(x_260, 0, x_277);
x_283 = x_260;
goto block_288;
}
else
{
lean_object* x_289; 
x_289 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_289, 0, x_277);
lean_ctor_set(x_289, 1, x_282);
x_283 = x_289;
goto block_288;
}
block_288:
{
uint8_t x_284; lean_object* x_285; 
x_284 = lean_unbox(x_268);
lean_dec(x_268);
lean_ctor_set_uint8(x_283, sizeof(void*)*2, x_284);
if (x_279 == 0)
{
lean_ctor_set(x_278, 0, x_283);
x_285 = x_278;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_287, 0, x_283);
x_285 = x_287;
goto block_286;
}
block_286:
{
return x_285;
}
}
}
}
else
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; uint8_t x_299; 
lean_dec_ref(x_273);
lean_dec(x_268);
lean_del_object(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_2);
x_292 = lean_ctor_get(x_276, 0);
x_299 = !lean_is_exclusive(x_276);
if (x_299 == 0)
{
x_293 = x_276;
x_294 = x_299;
goto block_298;
}
else
{
lean_inc(x_292);
lean_dec(x_276);
x_293 = lean_box(0);
x_294 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_295; 
if (x_294 == 0)
{
x_295 = x_293;
goto block_296;
}
else
{
lean_object* x_297; 
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_292);
x_295 = x_297;
goto block_296;
}
block_296:
{
return x_295;
}
}
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_268);
lean_dec_ref(x_258);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_300 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30));
x_301 = l_Lean_Expr_replaceFn(x_2, x_300);
x_302 = l_Lean_Expr_app___override(x_301, x_259);
if (x_261 == 0)
{
lean_ctor_set(x_260, 1, x_302);
lean_ctor_set(x_260, 0, x_18);
x_303 = x_260;
goto block_308;
}
else
{
lean_object* x_309; 
x_309 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_309, 0, x_18);
lean_ctor_set(x_309, 1, x_302);
x_303 = x_309;
goto block_308;
}
block_308:
{
uint8_t x_304; lean_object* x_305; 
x_304 = lean_unbox(x_263);
lean_dec(x_263);
lean_ctor_set_uint8(x_303, sizeof(void*)*2, x_304);
if (x_270 == 0)
{
lean_ctor_set(x_269, 0, x_303);
x_305 = x_269;
goto block_306;
}
else
{
lean_object* x_307; 
x_307 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_307, 0, x_303);
x_305 = x_307;
goto block_306;
}
block_306:
{
return x_305;
}
}
}
}
}
else
{
lean_object* x_312; lean_object* x_313; uint8_t x_314; uint8_t x_319; 
lean_dec(x_263);
lean_del_object(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_312 = lean_ctor_get(x_267, 0);
x_319 = !lean_is_exclusive(x_267);
if (x_319 == 0)
{
x_313 = x_267;
x_314 = x_319;
goto block_318;
}
else
{
lean_inc(x_312);
lean_dec(x_267);
x_313 = lean_box(0);
x_314 = x_319;
goto block_318;
}
block_318:
{
lean_object* x_315; 
if (x_314 == 0)
{
x_315 = x_313;
goto block_316;
}
else
{
lean_object* x_317; 
x_317 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_317, 0, x_312);
x_315 = x_317;
goto block_316;
}
block_316:
{
return x_315;
}
}
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_263);
lean_dec_ref(x_258);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_320 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__32));
x_321 = l_Lean_Expr_replaceFn(x_2, x_320);
x_322 = l_Lean_Expr_app___override(x_321, x_259);
if (x_261 == 0)
{
lean_ctor_set(x_260, 1, x_322);
lean_ctor_set(x_260, 0, x_21);
x_323 = x_260;
goto block_327;
}
else
{
lean_object* x_328; 
x_328 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_328, 0, x_21);
lean_ctor_set(x_328, 1, x_322);
x_323 = x_328;
goto block_327;
}
block_327:
{
lean_object* x_324; 
lean_ctor_set_uint8(x_323, sizeof(void*)*2, x_1);
if (x_265 == 0)
{
lean_ctor_set(x_264, 0, x_323);
x_324 = x_264;
goto block_325;
}
else
{
lean_object* x_326; 
x_326 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_326, 0, x_323);
x_324 = x_326;
goto block_325;
}
block_325:
{
return x_324;
}
}
}
}
}
else
{
lean_object* x_331; lean_object* x_332; uint8_t x_333; uint8_t x_338; 
lean_del_object(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_331 = lean_ctor_get(x_262, 0);
x_338 = !lean_is_exclusive(x_262);
if (x_338 == 0)
{
x_332 = x_262;
x_333 = x_338;
goto block_337;
}
else
{
lean_inc(x_331);
lean_dec(x_262);
x_332 = lean_box(0);
x_333 = x_338;
goto block_337;
}
block_337:
{
lean_object* x_334; 
if (x_333 == 0)
{
x_334 = x_332;
goto block_335;
}
else
{
lean_object* x_336; 
x_336 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_336, 0, x_331);
x_334 = x_336;
goto block_335;
}
block_335:
{
return x_334;
}
}
}
}
}
}
else
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_34;
}
}
}
}
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_13, 0, x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
x_14 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Expr_getAppNumArgs(x_1);
x_13 = lean_unsigned_to_nat(5u);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_box(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 12, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_18 = l_Lean_Meta_Sym_Simp_propagateOverApplied(x_1, x_17, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_19, 0, x_14);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Simp_simpIteCbv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkBVar(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_array_push(x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__22));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_array_push(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_16; uint8_t x_17; 
lean_inc_ref(x_2);
x_16 = l_Lean_Expr_cleanupAnnotations(x_2);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1));
x_33 = l_Lean_Expr_isConstOf(x_31, x_32);
if (x_33 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_34; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_27);
x_34 = lean_sym_simp(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; uint8_t x_411; 
x_411 = !lean_is_exclusive(x_35);
if (x_411 == 0)
{
x_36 = x_35;
x_37 = x_411;
goto block_410;
}
else
{
lean_dec(x_35);
x_36 = lean_box(0);
x_37 = x_411;
goto block_410;
}
block_410:
{
lean_object* x_38; 
x_38 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_unbox(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_39);
x_44 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_24);
lean_inc_ref(x_27);
x_45 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_44, x_27, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_47 = lean_sym_simp(x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_334; 
x_48 = lean_ctor_get(x_47, 0);
x_334 = !lean_is_exclusive(x_47);
if (x_334 == 0)
{
x_49 = x_47;
x_50 = x_334;
goto block_333;
}
else
{
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = x_334;
goto block_333;
}
block_333:
{
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_51; uint8_t x_52; uint8_t x_60; 
lean_dec(x_42);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_60 = !lean_is_exclusive(x_48);
if (x_60 == 0)
{
x_51 = x_48;
x_52 = x_60;
goto block_59;
}
else
{
lean_dec(x_48);
x_51 = lean_box(0);
x_52 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 0, 1);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
lean_ctor_set_uint8(x_53, 0, x_33);
if (x_50 == 0)
{
lean_ctor_set(x_49, 0, x_53);
x_54 = x_49;
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
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_332; 
lean_del_object(x_49);
x_61 = lean_ctor_get(x_48, 0);
x_62 = lean_ctor_get(x_48, 1);
x_332 = !lean_is_exclusive(x_48);
if (x_332 == 0)
{
x_63 = x_48;
x_64 = x_332;
goto block_331;
}
else
{
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_48);
x_63 = lean_box(0);
x_64 = x_332;
goto block_331;
}
block_331:
{
lean_object* x_65; 
x_65 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_61, x_6);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = lean_unbox(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_42);
x_68 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_61, x_6);
lean_dec_ref(x_61);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_197; 
x_69 = lean_ctor_get(x_68, 0);
x_197 = !lean_is_exclusive(x_68);
if (x_197 == 0)
{
x_70 = x_68;
x_71 = x_197;
goto block_196;
}
else
{
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
x_71 = x_197;
goto block_196;
}
block_196:
{
uint8_t x_72; 
x_72 = lean_unbox(x_69);
lean_dec(x_69);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
if (x_37 == 0)
{
x_73 = x_36;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 0, 1);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
lean_ctor_set_uint8(x_73, 0, x_33);
if (x_71 == 0)
{
lean_ctor_set(x_70, 0, x_73);
x_74 = x_70;
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
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_del_object(x_70);
lean_del_object(x_36);
x_79 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
lean_inc_ref(x_27);
x_80 = l_Lean_mkApp3(x_79, x_27, x_24, x_62);
x_81 = l_Lean_Meta_Sym_shareCommon___redArg(x_80, x_7);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_86 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_87 = 0;
x_88 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_89 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_82);
lean_inc(x_84);
lean_inc_ref(x_27);
x_90 = l_Lean_mkApp4(x_88, x_27, x_84, x_82, x_89);
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_mk_empty_array_with_capacity(x_91);
lean_inc_ref(x_92);
x_93 = lean_array_push(x_92, x_90);
x_94 = lean_unbox(x_66);
x_95 = lean_unbox(x_66);
x_96 = l_Lean_Expr_betaRev(x_21, x_93, x_94, x_95);
lean_dec_ref(x_93);
lean_inc(x_84);
x_97 = l_Lean_mkLambda(x_86, x_87, x_84, x_96);
x_98 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_97, x_7);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
lean_inc(x_84);
x_100 = l_Lean_mkNot(x_84);
x_101 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11);
lean_inc(x_82);
lean_inc(x_84);
x_102 = l_Lean_mkApp4(x_101, x_27, x_84, x_82, x_89);
x_103 = lean_array_push(x_92, x_102);
x_104 = lean_unbox(x_66);
x_105 = lean_unbox(x_66);
x_106 = l_Lean_Expr_betaRev(x_18, x_103, x_104, x_105);
lean_dec_ref(x_103);
x_107 = l_Lean_mkLambda(x_86, x_87, x_100, x_106);
x_108 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_107, x_7);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = lean_unsigned_to_nat(4u);
x_111 = l_Lean_Expr_getBoundedAppFn(x_110, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_109);
lean_inc(x_99);
lean_inc(x_84);
x_112 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_111, x_84, x_85, x_99, x_109, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15);
x_115 = lean_unbox(x_66);
x_116 = lean_unbox(x_66);
lean_inc(x_109);
x_117 = l_Lean_Expr_betaRev(x_109, x_114, x_115, x_116);
x_118 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_117, x_7);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_120 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_121 = l_Lean_Expr_replaceFn(x_2, x_120);
x_122 = l_Lean_mkApp3(x_121, x_84, x_85, x_82);
x_123 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__19));
x_124 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_125 = l_Lean_mkConst(x_123, x_124);
x_126 = l_Lean_mkApp3(x_125, x_30, x_99, x_109);
lean_inc(x_119);
x_127 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_113, x_122, x_119, x_126, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_139; 
x_128 = lean_ctor_get(x_127, 0);
x_139 = !lean_is_exclusive(x_127);
if (x_139 == 0)
{
x_129 = x_127;
x_130 = x_139;
goto block_138;
}
else
{
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_box(0);
x_130 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_131; 
if (x_64 == 0)
{
lean_ctor_set(x_63, 1, x_128);
lean_ctor_set(x_63, 0, x_119);
x_131 = x_63;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_137, 0, x_119);
lean_ctor_set(x_137, 1, x_128);
x_131 = x_137;
goto block_136;
}
block_136:
{
uint8_t x_132; lean_object* x_133; 
x_132 = lean_unbox(x_66);
lean_dec(x_66);
lean_ctor_set_uint8(x_131, sizeof(void*)*2, x_132);
if (x_130 == 0)
{
lean_ctor_set(x_129, 0, x_131);
x_133 = x_129;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_131);
x_133 = x_135;
goto block_134;
}
block_134:
{
return x_133;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_147; 
lean_dec(x_119);
lean_dec(x_66);
lean_del_object(x_63);
x_140 = lean_ctor_get(x_127, 0);
x_147 = !lean_is_exclusive(x_127);
if (x_147 == 0)
{
x_141 = x_127;
x_142 = x_147;
goto block_146;
}
else
{
lean_inc(x_140);
lean_dec(x_127);
x_141 = lean_box(0);
x_142 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_143; 
if (x_142 == 0)
{
x_143 = x_141;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_140);
x_143 = x_145;
goto block_144;
}
block_144:
{
return x_143;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_155; 
lean_dec(x_113);
lean_dec(x_109);
lean_dec(x_99);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_148 = lean_ctor_get(x_118, 0);
x_155 = !lean_is_exclusive(x_118);
if (x_155 == 0)
{
x_149 = x_118;
x_150 = x_155;
goto block_154;
}
else
{
lean_inc(x_148);
lean_dec(x_118);
x_149 = lean_box(0);
x_150 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_151; 
if (x_150 == 0)
{
x_151 = x_149;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_148);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_163; 
lean_dec(x_109);
lean_dec(x_99);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_156 = lean_ctor_get(x_112, 0);
x_163 = !lean_is_exclusive(x_112);
if (x_163 == 0)
{
x_157 = x_112;
x_158 = x_163;
goto block_162;
}
else
{
lean_inc(x_156);
lean_dec(x_112);
x_157 = lean_box(0);
x_158 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_159; 
if (x_158 == 0)
{
x_159 = x_157;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_156);
x_159 = x_161;
goto block_160;
}
block_160:
{
return x_159;
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; uint8_t x_171; 
lean_dec(x_99);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_164 = lean_ctor_get(x_108, 0);
x_171 = !lean_is_exclusive(x_108);
if (x_171 == 0)
{
x_165 = x_108;
x_166 = x_171;
goto block_170;
}
else
{
lean_inc(x_164);
lean_dec(x_108);
x_165 = lean_box(0);
x_166 = x_171;
goto block_170;
}
block_170:
{
lean_object* x_167; 
if (x_166 == 0)
{
x_167 = x_165;
goto block_168;
}
else
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_164);
x_167 = x_169;
goto block_168;
}
block_168:
{
return x_167;
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_179; 
lean_dec_ref(x_92);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_172 = lean_ctor_get(x_98, 0);
x_179 = !lean_is_exclusive(x_98);
if (x_179 == 0)
{
x_173 = x_98;
x_174 = x_179;
goto block_178;
}
else
{
lean_inc(x_172);
lean_dec(x_98);
x_173 = lean_box(0);
x_174 = x_179;
goto block_178;
}
block_178:
{
lean_object* x_175; 
if (x_174 == 0)
{
x_175 = x_173;
goto block_176;
}
else
{
lean_object* x_177; 
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_172);
x_175 = x_177;
goto block_176;
}
block_176:
{
return x_175;
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; uint8_t x_187; 
lean_dec(x_82);
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_180 = lean_ctor_get(x_83, 0);
x_187 = !lean_is_exclusive(x_83);
if (x_187 == 0)
{
x_181 = x_83;
x_182 = x_187;
goto block_186;
}
else
{
lean_inc(x_180);
lean_dec(x_83);
x_181 = lean_box(0);
x_182 = x_187;
goto block_186;
}
block_186:
{
lean_object* x_183; 
if (x_182 == 0)
{
x_183 = x_181;
goto block_184;
}
else
{
lean_object* x_185; 
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_180);
x_183 = x_185;
goto block_184;
}
block_184:
{
return x_183;
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_195; 
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_188 = lean_ctor_get(x_81, 0);
x_195 = !lean_is_exclusive(x_81);
if (x_195 == 0)
{
x_189 = x_81;
x_190 = x_195;
goto block_194;
}
else
{
lean_inc(x_188);
lean_dec(x_81);
x_189 = lean_box(0);
x_190 = x_195;
goto block_194;
}
block_194:
{
lean_object* x_191; 
if (x_190 == 0)
{
x_191 = x_189;
goto block_192;
}
else
{
lean_object* x_193; 
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_188);
x_191 = x_193;
goto block_192;
}
block_192:
{
return x_191;
}
}
}
}
}
}
else
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_205; 
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_62);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_198 = lean_ctor_get(x_68, 0);
x_205 = !lean_is_exclusive(x_68);
if (x_205 == 0)
{
x_199 = x_68;
x_200 = x_205;
goto block_204;
}
else
{
lean_inc(x_198);
lean_dec(x_68);
x_199 = lean_box(0);
x_200 = x_205;
goto block_204;
}
block_204:
{
lean_object* x_201; 
if (x_200 == 0)
{
x_201 = x_199;
goto block_202;
}
else
{
lean_object* x_203; 
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_198);
x_201 = x_203;
goto block_202;
}
block_202:
{
return x_201;
}
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_66);
lean_dec_ref(x_61);
lean_del_object(x_36);
x_206 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20);
lean_inc_ref(x_27);
x_207 = l_Lean_mkApp3(x_206, x_27, x_24, x_62);
x_208 = l_Lean_Meta_Sym_shareCommon___redArg(x_207, x_7);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec_ref(x_208);
x_210 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec_ref(x_210);
x_212 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23);
x_213 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_214 = 0;
x_215 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_216 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_209);
lean_inc(x_211);
lean_inc_ref(x_27);
x_217 = l_Lean_mkApp4(x_215, x_27, x_211, x_209, x_216);
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_mk_empty_array_with_capacity(x_218);
lean_inc_ref(x_219);
x_220 = lean_array_push(x_219, x_217);
x_221 = lean_unbox(x_42);
x_222 = lean_unbox(x_42);
x_223 = l_Lean_Expr_betaRev(x_21, x_220, x_221, x_222);
lean_dec_ref(x_220);
lean_inc(x_211);
x_224 = l_Lean_mkLambda(x_213, x_214, x_211, x_223);
x_225 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_224, x_7);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec_ref(x_225);
lean_inc(x_211);
x_227 = l_Lean_mkNot(x_211);
x_228 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11);
lean_inc(x_209);
lean_inc(x_211);
x_229 = l_Lean_mkApp4(x_228, x_27, x_211, x_209, x_216);
x_230 = lean_array_push(x_219, x_229);
x_231 = lean_unbox(x_42);
x_232 = lean_unbox(x_42);
x_233 = l_Lean_Expr_betaRev(x_18, x_230, x_231, x_232);
lean_dec_ref(x_230);
x_234 = l_Lean_mkLambda(x_213, x_214, x_227, x_233);
x_235 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_234, x_7);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
lean_dec_ref(x_235);
x_237 = lean_unsigned_to_nat(4u);
x_238 = l_Lean_Expr_getBoundedAppFn(x_237, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_236);
lean_inc(x_226);
lean_inc(x_211);
x_239 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_238, x_211, x_212, x_226, x_236, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
lean_dec_ref(x_239);
x_241 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24);
x_242 = lean_unbox(x_42);
x_243 = lean_unbox(x_42);
lean_inc(x_226);
x_244 = l_Lean_Expr_betaRev(x_226, x_241, x_242, x_243);
x_245 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_244, x_7);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
x_247 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_248 = l_Lean_Expr_replaceFn(x_2, x_247);
x_249 = l_Lean_mkApp3(x_248, x_211, x_212, x_209);
x_250 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__26));
x_251 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_252 = l_Lean_mkConst(x_250, x_251);
x_253 = l_Lean_mkApp3(x_252, x_30, x_226, x_236);
lean_inc(x_246);
x_254 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_240, x_249, x_246, x_253, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; uint8_t x_266; 
x_255 = lean_ctor_get(x_254, 0);
x_266 = !lean_is_exclusive(x_254);
if (x_266 == 0)
{
x_256 = x_254;
x_257 = x_266;
goto block_265;
}
else
{
lean_inc(x_255);
lean_dec(x_254);
x_256 = lean_box(0);
x_257 = x_266;
goto block_265;
}
block_265:
{
lean_object* x_258; 
if (x_64 == 0)
{
lean_ctor_set(x_63, 1, x_255);
lean_ctor_set(x_63, 0, x_246);
x_258 = x_63;
goto block_263;
}
else
{
lean_object* x_264; 
x_264 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_264, 0, x_246);
lean_ctor_set(x_264, 1, x_255);
x_258 = x_264;
goto block_263;
}
block_263:
{
uint8_t x_259; lean_object* x_260; 
x_259 = lean_unbox(x_42);
lean_dec(x_42);
lean_ctor_set_uint8(x_258, sizeof(void*)*2, x_259);
if (x_257 == 0)
{
lean_ctor_set(x_256, 0, x_258);
x_260 = x_256;
goto block_261;
}
else
{
lean_object* x_262; 
x_262 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_262, 0, x_258);
x_260 = x_262;
goto block_261;
}
block_261:
{
return x_260;
}
}
}
}
else
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; uint8_t x_274; 
lean_dec(x_246);
lean_del_object(x_63);
lean_dec(x_42);
x_267 = lean_ctor_get(x_254, 0);
x_274 = !lean_is_exclusive(x_254);
if (x_274 == 0)
{
x_268 = x_254;
x_269 = x_274;
goto block_273;
}
else
{
lean_inc(x_267);
lean_dec(x_254);
x_268 = lean_box(0);
x_269 = x_274;
goto block_273;
}
block_273:
{
lean_object* x_270; 
if (x_269 == 0)
{
x_270 = x_268;
goto block_271;
}
else
{
lean_object* x_272; 
x_272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_272, 0, x_267);
x_270 = x_272;
goto block_271;
}
block_271:
{
return x_270;
}
}
}
}
else
{
lean_object* x_275; lean_object* x_276; uint8_t x_277; uint8_t x_282; 
lean_dec(x_240);
lean_dec(x_236);
lean_dec(x_226);
lean_dec(x_211);
lean_dec(x_209);
lean_del_object(x_63);
lean_dec(x_42);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_275 = lean_ctor_get(x_245, 0);
x_282 = !lean_is_exclusive(x_245);
if (x_282 == 0)
{
x_276 = x_245;
x_277 = x_282;
goto block_281;
}
else
{
lean_inc(x_275);
lean_dec(x_245);
x_276 = lean_box(0);
x_277 = x_282;
goto block_281;
}
block_281:
{
lean_object* x_278; 
if (x_277 == 0)
{
x_278 = x_276;
goto block_279;
}
else
{
lean_object* x_280; 
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_275);
x_278 = x_280;
goto block_279;
}
block_279:
{
return x_278;
}
}
}
}
else
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; uint8_t x_290; 
lean_dec(x_236);
lean_dec(x_226);
lean_dec(x_211);
lean_dec(x_209);
lean_del_object(x_63);
lean_dec(x_42);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_283 = lean_ctor_get(x_239, 0);
x_290 = !lean_is_exclusive(x_239);
if (x_290 == 0)
{
x_284 = x_239;
x_285 = x_290;
goto block_289;
}
else
{
lean_inc(x_283);
lean_dec(x_239);
x_284 = lean_box(0);
x_285 = x_290;
goto block_289;
}
block_289:
{
lean_object* x_286; 
if (x_285 == 0)
{
x_286 = x_284;
goto block_287;
}
else
{
lean_object* x_288; 
x_288 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_288, 0, x_283);
x_286 = x_288;
goto block_287;
}
block_287:
{
return x_286;
}
}
}
}
else
{
lean_object* x_291; lean_object* x_292; uint8_t x_293; uint8_t x_298; 
lean_dec(x_226);
lean_dec(x_211);
lean_dec(x_209);
lean_del_object(x_63);
lean_dec(x_42);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_291 = lean_ctor_get(x_235, 0);
x_298 = !lean_is_exclusive(x_235);
if (x_298 == 0)
{
x_292 = x_235;
x_293 = x_298;
goto block_297;
}
else
{
lean_inc(x_291);
lean_dec(x_235);
x_292 = lean_box(0);
x_293 = x_298;
goto block_297;
}
block_297:
{
lean_object* x_294; 
if (x_293 == 0)
{
x_294 = x_292;
goto block_295;
}
else
{
lean_object* x_296; 
x_296 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_296, 0, x_291);
x_294 = x_296;
goto block_295;
}
block_295:
{
return x_294;
}
}
}
}
else
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; uint8_t x_306; 
lean_dec_ref(x_219);
lean_dec(x_211);
lean_dec(x_209);
lean_del_object(x_63);
lean_dec(x_42);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_299 = lean_ctor_get(x_225, 0);
x_306 = !lean_is_exclusive(x_225);
if (x_306 == 0)
{
x_300 = x_225;
x_301 = x_306;
goto block_305;
}
else
{
lean_inc(x_299);
lean_dec(x_225);
x_300 = lean_box(0);
x_301 = x_306;
goto block_305;
}
block_305:
{
lean_object* x_302; 
if (x_301 == 0)
{
x_302 = x_300;
goto block_303;
}
else
{
lean_object* x_304; 
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_299);
x_302 = x_304;
goto block_303;
}
block_303:
{
return x_302;
}
}
}
}
else
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; uint8_t x_314; 
lean_dec(x_209);
lean_del_object(x_63);
lean_dec(x_42);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_307 = lean_ctor_get(x_210, 0);
x_314 = !lean_is_exclusive(x_210);
if (x_314 == 0)
{
x_308 = x_210;
x_309 = x_314;
goto block_313;
}
else
{
lean_inc(x_307);
lean_dec(x_210);
x_308 = lean_box(0);
x_309 = x_314;
goto block_313;
}
block_313:
{
lean_object* x_310; 
if (x_309 == 0)
{
x_310 = x_308;
goto block_311;
}
else
{
lean_object* x_312; 
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_307);
x_310 = x_312;
goto block_311;
}
block_311:
{
return x_310;
}
}
}
}
else
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; uint8_t x_322; 
lean_del_object(x_63);
lean_dec(x_42);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_315 = lean_ctor_get(x_208, 0);
x_322 = !lean_is_exclusive(x_208);
if (x_322 == 0)
{
x_316 = x_208;
x_317 = x_322;
goto block_321;
}
else
{
lean_inc(x_315);
lean_dec(x_208);
x_316 = lean_box(0);
x_317 = x_322;
goto block_321;
}
block_321:
{
lean_object* x_318; 
if (x_317 == 0)
{
x_318 = x_316;
goto block_319;
}
else
{
lean_object* x_320; 
x_320 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_320, 0, x_315);
x_318 = x_320;
goto block_319;
}
block_319:
{
return x_318;
}
}
}
}
}
else
{
lean_object* x_323; lean_object* x_324; uint8_t x_325; uint8_t x_330; 
lean_del_object(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_dec(x_42);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_323 = lean_ctor_get(x_65, 0);
x_330 = !lean_is_exclusive(x_65);
if (x_330 == 0)
{
x_324 = x_65;
x_325 = x_330;
goto block_329;
}
else
{
lean_inc(x_323);
lean_dec(x_65);
x_324 = lean_box(0);
x_325 = x_330;
goto block_329;
}
block_329:
{
lean_object* x_326; 
if (x_325 == 0)
{
x_326 = x_324;
goto block_327;
}
else
{
lean_object* x_328; 
x_328 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_328, 0, x_323);
x_326 = x_328;
goto block_327;
}
block_327:
{
return x_326;
}
}
}
}
}
}
}
else
{
lean_dec(x_42);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_47;
}
}
else
{
lean_object* x_335; lean_object* x_336; uint8_t x_337; uint8_t x_342; 
lean_dec(x_42);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_335 = lean_ctor_get(x_45, 0);
x_342 = !lean_is_exclusive(x_45);
if (x_342 == 0)
{
x_336 = x_45;
x_337 = x_342;
goto block_341;
}
else
{
lean_inc(x_335);
lean_dec(x_45);
x_336 = lean_box(0);
x_337 = x_342;
goto block_341;
}
block_341:
{
lean_object* x_338; 
if (x_337 == 0)
{
x_338 = x_336;
goto block_339;
}
else
{
lean_object* x_340; 
x_340 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_340, 0, x_335);
x_338 = x_340;
goto block_339;
}
block_339:
{
return x_338;
}
}
}
}
else
{
lean_object* x_343; uint8_t x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_42);
lean_del_object(x_36);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_343 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15);
x_344 = lean_unbox(x_39);
x_345 = lean_unbox(x_39);
lean_inc_ref(x_18);
x_346 = l_Lean_Expr_betaRev(x_18, x_343, x_344, x_345);
x_347 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_346, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; uint8_t x_350; uint8_t x_361; 
x_348 = lean_ctor_get(x_347, 0);
x_361 = !lean_is_exclusive(x_347);
if (x_361 == 0)
{
x_349 = x_347;
x_350 = x_361;
goto block_360;
}
else
{
lean_inc(x_348);
lean_dec(x_347);
x_349 = lean_box(0);
x_350 = x_361;
goto block_360;
}
block_360:
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; lean_object* x_357; 
x_351 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__19));
x_352 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_353 = l_Lean_mkConst(x_351, x_352);
x_354 = l_Lean_mkApp3(x_353, x_30, x_21, x_18);
x_355 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_355, 0, x_348);
lean_ctor_set(x_355, 1, x_354);
x_356 = lean_unbox(x_39);
lean_dec(x_39);
lean_ctor_set_uint8(x_355, sizeof(void*)*2, x_356);
if (x_350 == 0)
{
lean_ctor_set(x_349, 0, x_355);
x_357 = x_349;
goto block_358;
}
else
{
lean_object* x_359; 
x_359 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_359, 0, x_355);
x_357 = x_359;
goto block_358;
}
block_358:
{
return x_357;
}
}
}
else
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; uint8_t x_369; 
lean_dec(x_39);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_362 = lean_ctor_get(x_347, 0);
x_369 = !lean_is_exclusive(x_347);
if (x_369 == 0)
{
x_363 = x_347;
x_364 = x_369;
goto block_368;
}
else
{
lean_inc(x_362);
lean_dec(x_347);
x_363 = lean_box(0);
x_364 = x_369;
goto block_368;
}
block_368:
{
lean_object* x_365; 
if (x_364 == 0)
{
x_365 = x_363;
goto block_366;
}
else
{
lean_object* x_367; 
x_367 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_367, 0, x_362);
x_365 = x_367;
goto block_366;
}
block_366:
{
return x_365;
}
}
}
}
}
else
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; uint8_t x_377; 
lean_dec(x_39);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_370 = lean_ctor_get(x_41, 0);
x_377 = !lean_is_exclusive(x_41);
if (x_377 == 0)
{
x_371 = x_41;
x_372 = x_377;
goto block_376;
}
else
{
lean_inc(x_370);
lean_dec(x_41);
x_371 = lean_box(0);
x_372 = x_377;
goto block_376;
}
block_376:
{
lean_object* x_373; 
if (x_372 == 0)
{
x_373 = x_371;
goto block_374;
}
else
{
lean_object* x_375; 
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_370);
x_373 = x_375;
goto block_374;
}
block_374:
{
return x_373;
}
}
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_39);
lean_del_object(x_36);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_378 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24);
lean_inc_ref(x_21);
x_379 = l_Lean_Expr_betaRev(x_21, x_378, x_1, x_1);
x_380 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_379, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; uint8_t x_383; uint8_t x_393; 
x_381 = lean_ctor_get(x_380, 0);
x_393 = !lean_is_exclusive(x_380);
if (x_393 == 0)
{
x_382 = x_380;
x_383 = x_393;
goto block_392;
}
else
{
lean_inc(x_381);
lean_dec(x_380);
x_382 = lean_box(0);
x_383 = x_393;
goto block_392;
}
block_392:
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_384 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__26));
x_385 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_386 = l_Lean_mkConst(x_384, x_385);
x_387 = l_Lean_mkApp3(x_386, x_30, x_21, x_18);
x_388 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_388, 0, x_381);
lean_ctor_set(x_388, 1, x_387);
lean_ctor_set_uint8(x_388, sizeof(void*)*2, x_1);
if (x_383 == 0)
{
lean_ctor_set(x_382, 0, x_388);
x_389 = x_382;
goto block_390;
}
else
{
lean_object* x_391; 
x_391 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_391, 0, x_388);
x_389 = x_391;
goto block_390;
}
block_390:
{
return x_389;
}
}
}
else
{
lean_object* x_394; lean_object* x_395; uint8_t x_396; uint8_t x_401; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_394 = lean_ctor_get(x_380, 0);
x_401 = !lean_is_exclusive(x_380);
if (x_401 == 0)
{
x_395 = x_380;
x_396 = x_401;
goto block_400;
}
else
{
lean_inc(x_394);
lean_dec(x_380);
x_395 = lean_box(0);
x_396 = x_401;
goto block_400;
}
block_400:
{
lean_object* x_397; 
if (x_396 == 0)
{
x_397 = x_395;
goto block_398;
}
else
{
lean_object* x_399; 
x_399 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_399, 0, x_394);
x_397 = x_399;
goto block_398;
}
block_398:
{
return x_397;
}
}
}
}
}
else
{
lean_object* x_402; lean_object* x_403; uint8_t x_404; uint8_t x_409; 
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_402 = lean_ctor_get(x_38, 0);
x_409 = !lean_is_exclusive(x_38);
if (x_409 == 0)
{
x_403 = x_38;
x_404 = x_409;
goto block_408;
}
else
{
lean_inc(x_402);
lean_dec(x_38);
x_403 = lean_box(0);
x_404 = x_409;
goto block_408;
}
block_408:
{
lean_object* x_405; 
if (x_404 == 0)
{
x_405 = x_403;
goto block_406;
}
else
{
lean_object* x_407; 
x_407 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_407, 0, x_402);
x_405 = x_407;
goto block_406;
}
block_406:
{
return x_405;
}
}
}
}
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; uint8_t x_596; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
x_412 = lean_ctor_get(x_35, 0);
x_413 = lean_ctor_get(x_35, 1);
x_596 = !lean_is_exclusive(x_35);
if (x_596 == 0)
{
x_414 = x_35;
x_415 = x_596;
goto block_595;
}
else
{
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_35);
x_414 = lean_box(0);
x_415 = x_596;
goto block_595;
}
block_595:
{
lean_object* x_416; 
x_416 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_412, x_6);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; uint8_t x_418; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
lean_dec_ref(x_416);
x_418 = lean_unbox(x_417);
if (x_418 == 0)
{
lean_object* x_419; 
x_419 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_412, x_6);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; uint8_t x_421; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
lean_dec_ref(x_419);
x_421 = lean_unbox(x_420);
if (x_421 == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_417);
x_422 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28);
lean_inc_ref(x_413);
lean_inc_ref(x_412);
lean_inc_ref(x_27);
x_423 = l_Lean_mkApp4(x_422, x_27, x_412, x_24, x_413);
x_424 = l_Lean_Meta_Sym_shareCommon___redArg(x_413, x_7);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; uint8_t x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
lean_dec_ref(x_424);
x_426 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_427 = 0;
x_428 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_429 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_425);
lean_inc_ref(x_412);
lean_inc_ref(x_27);
x_430 = l_Lean_mkApp4(x_428, x_27, x_412, x_425, x_429);
x_431 = lean_unsigned_to_nat(1u);
x_432 = lean_mk_empty_array_with_capacity(x_431);
lean_inc_ref(x_432);
x_433 = lean_array_push(x_432, x_430);
x_434 = lean_unbox(x_420);
x_435 = lean_unbox(x_420);
x_436 = l_Lean_Expr_betaRev(x_21, x_433, x_434, x_435);
lean_dec_ref(x_433);
lean_inc_ref(x_412);
x_437 = l_Lean_mkLambda(x_426, x_427, x_412, x_436);
x_438 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_437, x_7);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; uint8_t x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
lean_dec_ref(x_438);
lean_inc_ref(x_412);
x_440 = l_Lean_mkNot(x_412);
x_441 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11);
lean_inc(x_425);
lean_inc_ref(x_412);
x_442 = l_Lean_mkApp4(x_441, x_27, x_412, x_425, x_429);
x_443 = lean_array_push(x_432, x_442);
x_444 = lean_unbox(x_420);
x_445 = lean_unbox(x_420);
x_446 = l_Lean_Expr_betaRev(x_18, x_443, x_444, x_445);
lean_dec_ref(x_443);
x_447 = l_Lean_mkLambda(x_426, x_427, x_440, x_446);
x_448 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_447, x_7);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
lean_dec_ref(x_448);
x_450 = lean_unsigned_to_nat(4u);
x_451 = l_Lean_Expr_getBoundedAppFn(x_450, x_2);
lean_inc_ref(x_423);
lean_inc_ref(x_412);
x_452 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_451, x_412, x_423, x_439, x_449, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; uint8_t x_455; uint8_t x_467; 
x_453 = lean_ctor_get(x_452, 0);
x_467 = !lean_is_exclusive(x_452);
if (x_467 == 0)
{
x_454 = x_452;
x_455 = x_467;
goto block_466;
}
else
{
lean_inc(x_453);
lean_dec(x_452);
x_454 = lean_box(0);
x_455 = x_467;
goto block_466;
}
block_466:
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_456 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17));
x_457 = l_Lean_Expr_replaceFn(x_2, x_456);
x_458 = l_Lean_mkApp3(x_457, x_412, x_423, x_425);
if (x_415 == 0)
{
lean_ctor_set(x_414, 1, x_458);
lean_ctor_set(x_414, 0, x_453);
x_459 = x_414;
goto block_464;
}
else
{
lean_object* x_465; 
x_465 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_465, 0, x_453);
lean_ctor_set(x_465, 1, x_458);
x_459 = x_465;
goto block_464;
}
block_464:
{
uint8_t x_460; lean_object* x_461; 
x_460 = lean_unbox(x_420);
lean_dec(x_420);
lean_ctor_set_uint8(x_459, sizeof(void*)*2, x_460);
if (x_455 == 0)
{
lean_ctor_set(x_454, 0, x_459);
x_461 = x_454;
goto block_462;
}
else
{
lean_object* x_463; 
x_463 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_463, 0, x_459);
x_461 = x_463;
goto block_462;
}
block_462:
{
return x_461;
}
}
}
}
else
{
lean_object* x_468; lean_object* x_469; uint8_t x_470; uint8_t x_475; 
lean_dec(x_425);
lean_dec_ref(x_423);
lean_dec(x_420);
lean_del_object(x_414);
lean_dec_ref(x_412);
lean_dec_ref(x_2);
x_468 = lean_ctor_get(x_452, 0);
x_475 = !lean_is_exclusive(x_452);
if (x_475 == 0)
{
x_469 = x_452;
x_470 = x_475;
goto block_474;
}
else
{
lean_inc(x_468);
lean_dec(x_452);
x_469 = lean_box(0);
x_470 = x_475;
goto block_474;
}
block_474:
{
lean_object* x_471; 
if (x_470 == 0)
{
x_471 = x_469;
goto block_472;
}
else
{
lean_object* x_473; 
x_473 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_473, 0, x_468);
x_471 = x_473;
goto block_472;
}
block_472:
{
return x_471;
}
}
}
}
else
{
lean_object* x_476; lean_object* x_477; uint8_t x_478; uint8_t x_483; 
lean_dec(x_439);
lean_dec(x_425);
lean_dec_ref(x_423);
lean_dec(x_420);
lean_del_object(x_414);
lean_dec_ref(x_412);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_476 = lean_ctor_get(x_448, 0);
x_483 = !lean_is_exclusive(x_448);
if (x_483 == 0)
{
x_477 = x_448;
x_478 = x_483;
goto block_482;
}
else
{
lean_inc(x_476);
lean_dec(x_448);
x_477 = lean_box(0);
x_478 = x_483;
goto block_482;
}
block_482:
{
lean_object* x_479; 
if (x_478 == 0)
{
x_479 = x_477;
goto block_480;
}
else
{
lean_object* x_481; 
x_481 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_481, 0, x_476);
x_479 = x_481;
goto block_480;
}
block_480:
{
return x_479;
}
}
}
}
else
{
lean_object* x_484; lean_object* x_485; uint8_t x_486; uint8_t x_491; 
lean_dec_ref(x_432);
lean_dec(x_425);
lean_dec_ref(x_423);
lean_dec(x_420);
lean_del_object(x_414);
lean_dec_ref(x_412);
lean_dec_ref(x_27);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_484 = lean_ctor_get(x_438, 0);
x_491 = !lean_is_exclusive(x_438);
if (x_491 == 0)
{
x_485 = x_438;
x_486 = x_491;
goto block_490;
}
else
{
lean_inc(x_484);
lean_dec(x_438);
x_485 = lean_box(0);
x_486 = x_491;
goto block_490;
}
block_490:
{
lean_object* x_487; 
if (x_486 == 0)
{
x_487 = x_485;
goto block_488;
}
else
{
lean_object* x_489; 
x_489 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_489, 0, x_484);
x_487 = x_489;
goto block_488;
}
block_488:
{
return x_487;
}
}
}
}
else
{
lean_object* x_492; lean_object* x_493; uint8_t x_494; uint8_t x_499; 
lean_dec_ref(x_423);
lean_dec(x_420);
lean_del_object(x_414);
lean_dec_ref(x_412);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_492 = lean_ctor_get(x_424, 0);
x_499 = !lean_is_exclusive(x_424);
if (x_499 == 0)
{
x_493 = x_424;
x_494 = x_499;
goto block_498;
}
else
{
lean_inc(x_492);
lean_dec(x_424);
x_493 = lean_box(0);
x_494 = x_499;
goto block_498;
}
block_498:
{
lean_object* x_495; 
if (x_494 == 0)
{
x_495 = x_493;
goto block_496;
}
else
{
lean_object* x_497; 
x_497 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_497, 0, x_492);
x_495 = x_497;
goto block_496;
}
block_496:
{
return x_495;
}
}
}
}
else
{
lean_object* x_500; lean_object* x_501; 
lean_dec(x_420);
lean_dec_ref(x_412);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_413);
x_500 = l_Lean_Meta_mkOfEqFalseCore(x_27, x_413);
x_501 = l_Lean_Meta_Sym_shareCommon___redArg(x_500, x_7);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; uint8_t x_507; lean_object* x_508; lean_object* x_509; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
lean_dec_ref(x_501);
x_503 = lean_unsigned_to_nat(1u);
x_504 = lean_mk_empty_array_with_capacity(x_503);
x_505 = lean_array_push(x_504, x_502);
x_506 = lean_unbox(x_417);
x_507 = lean_unbox(x_417);
x_508 = l_Lean_Expr_betaRev(x_18, x_505, x_506, x_507);
lean_dec_ref(x_505);
x_509 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_508, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; uint8_t x_512; uint8_t x_524; 
x_510 = lean_ctor_get(x_509, 0);
x_524 = !lean_is_exclusive(x_509);
if (x_524 == 0)
{
x_511 = x_509;
x_512 = x_524;
goto block_523;
}
else
{
lean_inc(x_510);
lean_dec(x_509);
x_511 = lean_box(0);
x_512 = x_524;
goto block_523;
}
block_523:
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_513 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__28));
x_514 = l_Lean_Expr_replaceFn(x_2, x_513);
x_515 = l_Lean_Expr_app___override(x_514, x_413);
if (x_415 == 0)
{
lean_ctor_set(x_414, 1, x_515);
lean_ctor_set(x_414, 0, x_510);
x_516 = x_414;
goto block_521;
}
else
{
lean_object* x_522; 
x_522 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_522, 0, x_510);
lean_ctor_set(x_522, 1, x_515);
x_516 = x_522;
goto block_521;
}
block_521:
{
uint8_t x_517; lean_object* x_518; 
x_517 = lean_unbox(x_417);
lean_dec(x_417);
lean_ctor_set_uint8(x_516, sizeof(void*)*2, x_517);
if (x_512 == 0)
{
lean_ctor_set(x_511, 0, x_516);
x_518 = x_511;
goto block_519;
}
else
{
lean_object* x_520; 
x_520 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_520, 0, x_516);
x_518 = x_520;
goto block_519;
}
block_519:
{
return x_518;
}
}
}
}
else
{
lean_object* x_525; lean_object* x_526; uint8_t x_527; uint8_t x_532; 
lean_dec(x_417);
lean_del_object(x_414);
lean_dec_ref(x_413);
lean_dec_ref(x_2);
x_525 = lean_ctor_get(x_509, 0);
x_532 = !lean_is_exclusive(x_509);
if (x_532 == 0)
{
x_526 = x_509;
x_527 = x_532;
goto block_531;
}
else
{
lean_inc(x_525);
lean_dec(x_509);
x_526 = lean_box(0);
x_527 = x_532;
goto block_531;
}
block_531:
{
lean_object* x_528; 
if (x_527 == 0)
{
x_528 = x_526;
goto block_529;
}
else
{
lean_object* x_530; 
x_530 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_530, 0, x_525);
x_528 = x_530;
goto block_529;
}
block_529:
{
return x_528;
}
}
}
}
else
{
lean_object* x_533; lean_object* x_534; uint8_t x_535; uint8_t x_540; 
lean_dec(x_417);
lean_del_object(x_414);
lean_dec_ref(x_413);
lean_dec_ref(x_18);
lean_dec(x_7);
lean_dec_ref(x_2);
x_533 = lean_ctor_get(x_501, 0);
x_540 = !lean_is_exclusive(x_501);
if (x_540 == 0)
{
x_534 = x_501;
x_535 = x_540;
goto block_539;
}
else
{
lean_inc(x_533);
lean_dec(x_501);
x_534 = lean_box(0);
x_535 = x_540;
goto block_539;
}
block_539:
{
lean_object* x_536; 
if (x_535 == 0)
{
x_536 = x_534;
goto block_537;
}
else
{
lean_object* x_538; 
x_538 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_538, 0, x_533);
x_536 = x_538;
goto block_537;
}
block_537:
{
return x_536;
}
}
}
}
}
else
{
lean_object* x_541; lean_object* x_542; uint8_t x_543; uint8_t x_548; 
lean_dec(x_417);
lean_del_object(x_414);
lean_dec_ref(x_413);
lean_dec_ref(x_412);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_541 = lean_ctor_get(x_419, 0);
x_548 = !lean_is_exclusive(x_419);
if (x_548 == 0)
{
x_542 = x_419;
x_543 = x_548;
goto block_547;
}
else
{
lean_inc(x_541);
lean_dec(x_419);
x_542 = lean_box(0);
x_543 = x_548;
goto block_547;
}
block_547:
{
lean_object* x_544; 
if (x_543 == 0)
{
x_544 = x_542;
goto block_545;
}
else
{
lean_object* x_546; 
x_546 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_546, 0, x_541);
x_544 = x_546;
goto block_545;
}
block_545:
{
return x_544;
}
}
}
}
else
{
lean_object* x_549; lean_object* x_550; 
lean_dec(x_417);
lean_dec_ref(x_412);
lean_dec_ref(x_24);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_413);
x_549 = l_Lean_Meta_mkOfEqTrueCore(x_27, x_413);
x_550 = l_Lean_Meta_Sym_shareCommon___redArg(x_549, x_7);
if (lean_obj_tag(x_550) == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
lean_dec_ref(x_550);
x_552 = lean_unsigned_to_nat(1u);
x_553 = lean_mk_empty_array_with_capacity(x_552);
x_554 = lean_array_push(x_553, x_551);
x_555 = l_Lean_Expr_betaRev(x_21, x_554, x_1, x_1);
lean_dec_ref(x_554);
x_556 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_555, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; uint8_t x_559; uint8_t x_570; 
x_557 = lean_ctor_get(x_556, 0);
x_570 = !lean_is_exclusive(x_556);
if (x_570 == 0)
{
x_558 = x_556;
x_559 = x_570;
goto block_569;
}
else
{
lean_inc(x_557);
lean_dec(x_556);
x_558 = lean_box(0);
x_559 = x_570;
goto block_569;
}
block_569:
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_560 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__30));
x_561 = l_Lean_Expr_replaceFn(x_2, x_560);
x_562 = l_Lean_Expr_app___override(x_561, x_413);
if (x_415 == 0)
{
lean_ctor_set(x_414, 1, x_562);
lean_ctor_set(x_414, 0, x_557);
x_563 = x_414;
goto block_567;
}
else
{
lean_object* x_568; 
x_568 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_568, 0, x_557);
lean_ctor_set(x_568, 1, x_562);
x_563 = x_568;
goto block_567;
}
block_567:
{
lean_object* x_564; 
lean_ctor_set_uint8(x_563, sizeof(void*)*2, x_1);
if (x_559 == 0)
{
lean_ctor_set(x_558, 0, x_563);
x_564 = x_558;
goto block_565;
}
else
{
lean_object* x_566; 
x_566 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_566, 0, x_563);
x_564 = x_566;
goto block_565;
}
block_565:
{
return x_564;
}
}
}
}
else
{
lean_object* x_571; lean_object* x_572; uint8_t x_573; uint8_t x_578; 
lean_del_object(x_414);
lean_dec_ref(x_413);
lean_dec_ref(x_2);
x_571 = lean_ctor_get(x_556, 0);
x_578 = !lean_is_exclusive(x_556);
if (x_578 == 0)
{
x_572 = x_556;
x_573 = x_578;
goto block_577;
}
else
{
lean_inc(x_571);
lean_dec(x_556);
x_572 = lean_box(0);
x_573 = x_578;
goto block_577;
}
block_577:
{
lean_object* x_574; 
if (x_573 == 0)
{
x_574 = x_572;
goto block_575;
}
else
{
lean_object* x_576; 
x_576 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_576, 0, x_571);
x_574 = x_576;
goto block_575;
}
block_575:
{
return x_574;
}
}
}
}
else
{
lean_object* x_579; lean_object* x_580; uint8_t x_581; uint8_t x_586; 
lean_del_object(x_414);
lean_dec_ref(x_413);
lean_dec_ref(x_21);
lean_dec(x_7);
lean_dec_ref(x_2);
x_579 = lean_ctor_get(x_550, 0);
x_586 = !lean_is_exclusive(x_550);
if (x_586 == 0)
{
x_580 = x_550;
x_581 = x_586;
goto block_585;
}
else
{
lean_inc(x_579);
lean_dec(x_550);
x_580 = lean_box(0);
x_581 = x_586;
goto block_585;
}
block_585:
{
lean_object* x_582; 
if (x_581 == 0)
{
x_582 = x_580;
goto block_583;
}
else
{
lean_object* x_584; 
x_584 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_584, 0, x_579);
x_582 = x_584;
goto block_583;
}
block_583:
{
return x_582;
}
}
}
}
}
else
{
lean_object* x_587; lean_object* x_588; uint8_t x_589; uint8_t x_594; 
lean_del_object(x_414);
lean_dec_ref(x_413);
lean_dec_ref(x_412);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_587 = lean_ctor_get(x_416, 0);
x_594 = !lean_is_exclusive(x_416);
if (x_594 == 0)
{
x_588 = x_416;
x_589 = x_594;
goto block_593;
}
else
{
lean_inc(x_587);
lean_dec(x_416);
x_588 = lean_box(0);
x_589 = x_594;
goto block_593;
}
block_593:
{
lean_object* x_590; 
if (x_589 == 0)
{
x_590 = x_588;
goto block_591;
}
else
{
lean_object* x_592; 
x_592 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_592, 0, x_587);
x_590 = x_592;
goto block_591;
}
block_591:
{
return x_590;
}
}
}
}
}
}
else
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_34;
}
}
}
}
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_13, 0, x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
x_14 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Expr_getAppNumArgs(x_1);
x_13 = lean_unsigned_to_nat(5u);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_box(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed), 12, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_18 = l_Lean_Meta_Sym_Simp_propagateOverApplied(x_1, x_17, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_19, 0, x_14);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Simp_simpDIteCbv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_get_reducibility_status(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_21; 
x_5 = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(x_1, x_3);
x_6 = lean_ctor_get(x_5, 0);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
x_7 = x_5;
x_8 = x_21;
goto block_20;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_21;
goto block_20;
}
block_20:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
if (x_9 == 2)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_11);
x_12 = x_7;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
else
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_box(x_15);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_16);
x_17 = x_7;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
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
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ConstantInfo_name(x_3);
x_8 = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_11; 
lean_dec_ref(x_3);
x_11 = lean_ctor_get_uint8(x_2, 9);
lean_dec_ref(x_2);
switch (x_11) {
case 4:
{
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_8;
}
case 0:
{
lean_object* x_12; uint8_t x_13; uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_8, 0);
lean_dec(x_21);
x_12 = x_8;
x_13 = x_20;
goto block_19;
}
else
{
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = x_20;
goto block_19;
}
block_19:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_box(x_14);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_15);
x_16 = x_12;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
case 1:
{
lean_object* x_22; 
lean_dec_ref(x_8);
x_22 = l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(x_7, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_36; 
x_23 = lean_ctor_get(x_22, 0);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
x_24 = x_22;
x_25 = x_36;
goto block_35;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_26; 
x_26 = lean_unbox(x_23);
lean_dec(x_23);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
x_27 = 1;
x_28 = lean_box(x_27);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_28);
x_29 = x_24;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
else
{
lean_object* x_32; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_9);
x_32 = x_24;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_9);
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
lean_dec(x_9);
return x_22;
}
}
default: 
{
lean_object* x_37; uint8_t x_38; uint8_t x_69; 
lean_dec(x_9);
lean_dec_ref(x_4);
x_69 = !lean_is_exclusive(x_8);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_8, 0);
lean_dec(x_70);
x_37 = x_8;
x_38 = x_69;
goto block_68;
}
else
{
lean_dec(x_8);
x_37 = lean_box(0);
x_38 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_67; 
x_39 = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(x_7, x_5);
lean_dec(x_5);
x_40 = lean_ctor_get(x_39, 0);
x_67 = !lean_is_exclusive(x_39);
if (x_67 == 0)
{
x_41 = x_39;
x_42 = x_67;
goto block_66;
}
else
{
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_box(0);
x_42 = x_67;
goto block_66;
}
block_66:
{
uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; 
x_43 = 0;
x_44 = lean_unbox(x_40);
x_45 = l_Lean_instBEqReducibilityStatus_beq(x_44, x_43);
x_46 = 1;
if (x_45 == 0)
{
uint8_t x_57; uint8_t x_58; 
lean_del_object(x_37);
x_57 = 3;
x_58 = l_Lean_Meta_instBEqTransparencyMode_beq(x_11, x_57);
if (x_58 == 0)
{
lean_dec(x_40);
x_47 = x_58;
goto block_56;
}
else
{
uint8_t x_59; uint8_t x_60; uint8_t x_61; 
x_59 = 3;
x_60 = lean_unbox(x_40);
lean_dec(x_40);
x_61 = l_Lean_instBEqReducibilityStatus_beq(x_60, x_59);
x_47 = x_61;
goto block_56;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_del_object(x_41);
lean_dec(x_40);
x_62 = lean_box(x_46);
if (x_38 == 0)
{
lean_ctor_set(x_37, 0, x_62);
x_63 = x_37;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
block_56:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(x_47);
if (x_42 == 0)
{
lean_ctor_set(x_41, 0, x_48);
x_49 = x_41;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_48);
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
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(x_46);
if (x_42 == 0)
{
lean_ctor_set(x_41, 0, x_52);
x_53 = x_41;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_52);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
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
lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
lean_dec_ref(x_1);
x_72 = lean_apply_5(x_71, x_2, x_3, x_4, x_5, lean_box(0));
return x_72;
}
}
else
{
lean_object* x_73; uint8_t x_74; uint8_t x_81; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_8);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_8, 0);
lean_dec(x_82);
x_73 = x_8;
x_74 = x_81;
goto block_80;
}
else
{
lean_dec(x_8);
x_73 = lean_box(0);
x_74 = x_81;
goto block_80;
}
block_80:
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_75 = 0;
x_76 = lean_box(x_75);
if (x_74 == 0)
{
lean_ctor_set(x_73, 0, x_76);
x_77 = x_73;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_76);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_27; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 3);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
x_18 = x_2;
x_19 = x_27;
goto block_26;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_dec(x_2);
x_18 = lean_box(0);
x_19 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_20, 0, x_14);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (x_19 == 0)
{
lean_ctor_set(x_18, 6, x_21);
x_22 = x_18;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_9);
lean_ctor_set(x_25, 2, x_10);
lean_ctor_set(x_25, 3, x_11);
lean_ctor_set(x_25, 4, x_12);
lean_ctor_set(x_25, 5, x_13);
lean_ctor_set(x_25, 6, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*7, x_8);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 1, x_15);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 2, x_16);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 3, x_17);
x_22 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_23; 
x_23 = lean_apply_5(x_1, x_22, x_3, x_4, x_5, lean_box(0));
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_13 = l_Lean_Meta_Tactic_Cbv_getMatchTheorems(x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0));
x_16 = l_Lean_Meta_Sym_Simp_Theorems_rewrite(x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_17 = lean_ctor_get(x_13, 0);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
x_18 = x_13;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___boxed), 6, 1);
lean_closure_set(x_8, 0, x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_9 = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(x_8, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_38; 
x_10 = lean_ctor_get(x_9, 0);
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
x_11 = x_9;
x_12 = x_38;
goto block_37;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_38;
goto block_37;
}
block_37:
{
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_del_object(x_11);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
lean_inc(x_13);
x_14 = l_Lean_Meta_Sym_mkEqRefl___redArg(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_15 = lean_ctor_get(x_14, 0);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
x_16 = x_14;
x_17 = x_24;
goto block_23;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
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
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec(x_13);
x_25 = lean_ctor_get(x_14, 0);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
x_26 = x_14;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_33 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_33);
x_34 = x_11;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_39 = lean_ctor_get(x_9, 0);
x_46 = !lean_is_exclusive(x_9);
if (x_46 == 0)
{
x_40 = x_9;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_9);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(x_1, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(x_1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_17; 
x_17 = l_Lean_Expr_isApp(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_Expr_getAppFn(x_1);
x_21 = l_Lean_Expr_constName_x3f(x_20);
lean_dec_ref(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_89; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_22);
x_23 = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(x_22, x_10);
x_24 = lean_ctor_get(x_23, 0);
x_89 = !lean_is_exclusive(x_23);
if (x_89 == 0)
{
x_25 = x_23;
x_26 = x_89;
goto block_88;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_89;
goto block_88;
}
block_88:
{
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_del_object(x_25);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec_ref(x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_28, x_30);
lean_dec(x_28);
x_32 = lean_nat_add(x_31, x_29);
lean_dec(x_29);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_33 = l_Lean_Meta_Sym_Simp_simpAppArgRange(x_1, x_31, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = lean_ctor_get_uint8(x_34, 0);
lean_dec_ref(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec_ref(x_33);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_1);
x_36 = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(x_22, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = x_36;
goto block_16;
}
else
{
lean_dec(x_22);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_12 = x_33;
goto block_16;
}
}
else
{
uint8_t x_37; 
x_37 = lean_ctor_get_uint8(x_34, sizeof(void*)*2);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_83; 
lean_dec_ref(x_33);
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
x_83 = !lean_is_exclusive(x_34);
if (x_83 == 0)
{
x_40 = x_34;
x_41 = x_83;
goto block_82;
}
else
{
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_box(0);
x_41 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_42; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_38);
x_42 = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(x_22, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_81; 
x_43 = lean_ctor_get(x_42, 0);
x_81 = !lean_is_exclusive(x_42);
if (x_81 == 0)
{
x_44 = x_42;
x_45 = x_81;
goto block_80;
}
else
{
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = x_81;
goto block_80;
}
block_80:
{
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_46; lean_object* x_47; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_46 = lean_ctor_get_uint8(x_43, 0);
lean_dec_ref(x_43);
if (x_41 == 0)
{
x_47 = x_40;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_52, 0, x_38);
lean_ctor_set(x_52, 1, x_39);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_46);
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_47);
x_48 = x_44;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_47);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; uint8_t x_79; 
lean_del_object(x_44);
lean_del_object(x_40);
x_53 = lean_ctor_get(x_43, 0);
x_54 = lean_ctor_get(x_43, 1);
x_55 = lean_ctor_get_uint8(x_43, sizeof(void*)*2);
x_79 = !lean_is_exclusive(x_43);
if (x_79 == 0)
{
x_56 = x_43;
x_57 = x_79;
goto block_78;
}
else
{
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_43);
x_56 = lean_box(0);
x_57 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_58; 
lean_inc_ref(x_53);
x_58 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_1, x_38, x_39, x_53, x_54, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_69; 
x_59 = lean_ctor_get(x_58, 0);
x_69 = !lean_is_exclusive(x_58);
if (x_69 == 0)
{
x_60 = x_58;
x_61 = x_69;
goto block_68;
}
else
{
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_62; 
if (x_57 == 0)
{
lean_ctor_set(x_56, 1, x_59);
x_62 = x_56;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_55);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_61 == 0)
{
lean_ctor_set(x_60, 0, x_62);
x_63 = x_60;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_62);
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
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_77; 
lean_del_object(x_56);
lean_dec_ref(x_53);
x_70 = lean_ctor_get(x_58, 0);
x_77 = !lean_is_exclusive(x_58);
if (x_77 == 0)
{
x_71 = x_58;
x_72 = x_77;
goto block_76;
}
else
{
lean_inc(x_70);
lean_dec(x_58);
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
}
}
}
else
{
lean_del_object(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
x_12 = x_42;
goto block_16;
}
}
}
else
{
lean_dec_ref(x_34);
lean_dec(x_22);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_12 = x_33;
goto block_16;
}
}
}
else
{
lean_dec(x_22);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_12 = x_33;
goto block_16;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_84 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_84);
x_85 = x_25;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_84);
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
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_90 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
block_16:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_13, 0);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_12);
x_15 = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(x_1, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_15;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_12;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_12;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__1));
x_15 = lean_name_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__1));
x_17 = lean_name_eq(x_13, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1));
x_19 = lean_name_eq(x_13, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__3));
x_21 = lean_name_eq(x_13, x_20);
lean_dec(x_13);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_unsigned_to_nat(5u);
x_24 = lean_mk_empty_array_with_capacity(x_23);
x_25 = lean_box(x_19);
x_26 = lean_array_push(x_24, x_25);
x_27 = lean_box(x_19);
x_28 = lean_array_push(x_26, x_27);
x_29 = lean_box(x_21);
x_30 = lean_array_push(x_28, x_29);
x_31 = lean_box(x_21);
x_32 = lean_array_push(x_30, x_31);
x_33 = lean_box(x_21);
x_34 = lean_array_push(x_32, x_33);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_1);
x_35 = l_Lean_Meta_Sym_Simp_simpInterlaced(x_1, x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = lean_ctor_get_uint8(x_36, 0);
lean_dec_ref(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec_ref(x_35);
x_38 = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(x_1, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_38;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_35;
}
}
else
{
uint8_t x_39; 
x_39 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_85; 
lean_dec_ref(x_35);
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
x_85 = !lean_is_exclusive(x_36);
if (x_85 == 0)
{
x_42 = x_36;
x_43 = x_85;
goto block_84;
}
else
{
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_box(0);
x_43 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_44; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_40);
x_44 = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(x_40, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_83; 
x_45 = lean_ctor_get(x_44, 0);
x_83 = !lean_is_exclusive(x_44);
if (x_83 == 0)
{
x_46 = x_44;
x_47 = x_83;
goto block_82;
}
else
{
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = x_83;
goto block_82;
}
block_82:
{
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_48; lean_object* x_49; 
lean_dec_ref(x_45);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_48 = 0;
if (x_43 == 0)
{
x_49 = x_42;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_54, 0, x_40);
lean_ctor_set(x_54, 1, x_41);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_48);
if (x_47 == 0)
{
lean_ctor_set(x_46, 0, x_49);
x_50 = x_46;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_49);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_81; 
lean_del_object(x_46);
lean_del_object(x_42);
x_55 = lean_ctor_get(x_45, 0);
x_56 = lean_ctor_get(x_45, 1);
x_81 = !lean_is_exclusive(x_45);
if (x_81 == 0)
{
x_57 = x_45;
x_58 = x_81;
goto block_80;
}
else
{
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_45);
x_57 = lean_box(0);
x_58 = x_81;
goto block_80;
}
block_80:
{
uint8_t x_59; lean_object* x_60; 
x_59 = 0;
lean_inc_ref(x_55);
x_60 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_1, x_40, x_41, x_55, x_56, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_71; 
x_61 = lean_ctor_get(x_60, 0);
x_71 = !lean_is_exclusive(x_60);
if (x_71 == 0)
{
x_62 = x_60;
x_63 = x_71;
goto block_70;
}
else
{
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_box(0);
x_63 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_64; 
if (x_58 == 0)
{
lean_ctor_set(x_57, 1, x_61);
x_64 = x_57;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_69, 0, x_55);
lean_ctor_set(x_69, 1, x_61);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_59);
if (x_63 == 0)
{
lean_ctor_set(x_62, 0, x_64);
x_65 = x_62;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_64);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_del_object(x_57);
lean_dec_ref(x_55);
x_72 = lean_ctor_get(x_60, 0);
x_79 = !lean_is_exclusive(x_60);
if (x_79 == 0)
{
x_73 = x_60;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_60);
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
}
}
}
else
{
lean_del_object(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_44;
}
}
}
else
{
lean_dec_ref(x_36);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_35;
}
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_35;
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_13);
x_86 = l_Lean_Meta_Sym_Simp_simpDIteCbv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_86;
}
}
else
{
lean_object* x_87; 
lean_dec(x_13);
x_87 = l_Lean_Meta_Sym_Simp_simpCond(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_87;
}
}
else
{
lean_object* x_88; 
lean_dec(x_13);
x_88 = l_Lean_Meta_Sym_Simp_simpIteCbv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_89 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Tactic_Cbv_simpControlCbv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Sym_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_Opaque(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SynthInstance(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Sym_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Init_Sym_Lemmas(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_Opaque(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Cbv_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Result(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_App(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Sym_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin);
}
#ifdef __cplusplus
}
#endif
