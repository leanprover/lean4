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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mpr_not"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(121, 56, 250, 51, 9, 123, 141, 181)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(155, 21, 178, 198, 97, 164, 246, 137)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dite_cond_congr"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(72, 238, 116, 219, 106, 19, 52, 46)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dite_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__19 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(78, 119, 178, 178, 249, 126, 188, 7)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__21 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__21_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__22 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__21_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__22_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dite_true"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__26 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(65, 218, 189, 96, 14, 237, 238, 210)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "dite_cond_eq_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__28 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__28_value),LEAN_SCALAR_PTR_LITERAL(153, 159, 146, 90, 178, 85, 98, 212)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "dite_cond_eq_true"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__30 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__30_value),LEAN_SCALAR_PTR_LITERAL(13, 104, 142, 126, 111, 138, 152, 2)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__31 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__31_value;
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
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4;
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
uint8_t x_19; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
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
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_unbox(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_free_object(x_37);
x_41 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_unbox(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_free_object(x_41);
lean_dec(x_39);
x_45 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_24);
lean_inc_ref(x_27);
x_46 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_45, x_27, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_48 = lean_sym_simp(x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
lean_dec(x_43);
lean_free_object(x_35);
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
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_ctor_set_uint8(x_50, 0, x_33);
return x_48;
}
else
{
lean_object* x_52; 
lean_dec(x_50);
x_52 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_52, 0, x_33);
lean_ctor_set(x_48, 0, x_52);
return x_48;
}
}
else
{
uint8_t x_53; 
lean_free_object(x_48);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
x_56 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_54, x_6);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_unbox(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_43);
x_59 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_54, x_6);
lean_dec_ref(x_54);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_dec(x_57);
lean_free_object(x_50);
lean_dec_ref(x_55);
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
lean_ctor_set_uint8(x_35, 0, x_33);
lean_ctor_set(x_59, 0, x_35);
return x_59;
}
else
{
lean_object* x_63; 
lean_free_object(x_59);
lean_free_object(x_35);
x_63 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
x_66 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_67 = lean_unsigned_to_nat(4u);
x_68 = l_Lean_Expr_getBoundedAppFn(x_67, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_64);
x_69 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_68, x_64, x_66, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = l_Lean_mkApp3(x_65, x_27, x_24, x_55);
x_72 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_73 = l_Lean_Expr_replaceFn(x_2, x_72);
x_74 = l_Lean_mkApp3(x_73, x_64, x_66, x_71);
x_75 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_76 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_77 = l_Lean_mkConst(x_75, x_76);
lean_inc_ref(x_18);
x_78 = l_Lean_mkApp3(x_77, x_30, x_21, x_18);
lean_inc_ref(x_18);
x_79 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_70, x_74, x_18, x_78, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_79, 0);
lean_ctor_set(x_50, 1, x_81);
lean_ctor_set(x_50, 0, x_18);
x_82 = lean_unbox(x_57);
lean_dec(x_57);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_82);
lean_ctor_set(x_79, 0, x_50);
return x_79;
}
else
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_79, 0);
lean_inc(x_83);
lean_dec(x_79);
lean_ctor_set(x_50, 1, x_83);
lean_ctor_set(x_50, 0, x_18);
x_84 = lean_unbox(x_57);
lean_dec(x_57);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_84);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_50);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_57);
lean_free_object(x_50);
lean_dec_ref(x_18);
x_86 = !lean_is_exclusive(x_79);
if (x_86 == 0)
{
return x_79;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_79, 0);
lean_inc(x_87);
lean_dec(x_79);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_64);
lean_dec(x_57);
lean_free_object(x_50);
lean_dec_ref(x_55);
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
x_89 = !lean_is_exclusive(x_69);
if (x_89 == 0)
{
return x_69;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_69, 0);
lean_inc(x_90);
lean_dec(x_69);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_57);
lean_free_object(x_50);
lean_dec_ref(x_55);
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
x_92 = !lean_is_exclusive(x_63);
if (x_92 == 0)
{
return x_63;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_63, 0);
lean_inc(x_93);
lean_dec(x_63);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
else
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_59, 0);
lean_inc(x_95);
lean_dec(x_59);
x_96 = lean_unbox(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_57);
lean_free_object(x_50);
lean_dec_ref(x_55);
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
lean_ctor_set_uint8(x_35, 0, x_33);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_35);
return x_97;
}
else
{
lean_object* x_98; 
lean_free_object(x_35);
x_98 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
x_101 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_102 = lean_unsigned_to_nat(4u);
x_103 = l_Lean_Expr_getBoundedAppFn(x_102, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_99);
x_104 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_103, x_99, x_101, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = l_Lean_mkApp3(x_100, x_27, x_24, x_55);
x_107 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_108 = l_Lean_Expr_replaceFn(x_2, x_107);
x_109 = l_Lean_mkApp3(x_108, x_99, x_101, x_106);
x_110 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_111 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_112 = l_Lean_mkConst(x_110, x_111);
lean_inc_ref(x_18);
x_113 = l_Lean_mkApp3(x_112, x_30, x_21, x_18);
lean_inc_ref(x_18);
x_114 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_105, x_109, x_18, x_113, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
lean_ctor_set(x_50, 1, x_115);
lean_ctor_set(x_50, 0, x_18);
x_117 = lean_unbox(x_57);
lean_dec(x_57);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_117);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 1, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_50);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_57);
lean_free_object(x_50);
lean_dec_ref(x_18);
x_119 = lean_ctor_get(x_114, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_120 = x_114;
} else {
 lean_dec_ref(x_114);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 1, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_99);
lean_dec(x_57);
lean_free_object(x_50);
lean_dec_ref(x_55);
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
x_122 = lean_ctor_get(x_104, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_123 = x_104;
} else {
 lean_dec_ref(x_104);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 1, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_122);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_57);
lean_free_object(x_50);
lean_dec_ref(x_55);
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
x_125 = lean_ctor_get(x_98, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_126 = x_98;
} else {
 lean_dec_ref(x_98);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
return x_127;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_57);
lean_free_object(x_50);
lean_dec_ref(x_55);
lean_free_object(x_35);
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
x_128 = !lean_is_exclusive(x_59);
if (x_128 == 0)
{
return x_59;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_59, 0);
lean_inc(x_129);
lean_dec(x_59);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
else
{
lean_object* x_131; 
lean_dec(x_57);
lean_dec_ref(x_54);
lean_free_object(x_35);
x_131 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20);
x_134 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23);
x_135 = lean_unsigned_to_nat(4u);
x_136 = l_Lean_Expr_getBoundedAppFn(x_135, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_132);
x_137 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_136, x_132, x_134, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = l_Lean_mkApp3(x_133, x_27, x_24, x_55);
x_140 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_141 = l_Lean_Expr_replaceFn(x_2, x_140);
x_142 = l_Lean_mkApp3(x_141, x_132, x_134, x_139);
x_143 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25));
x_144 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_145 = l_Lean_mkConst(x_143, x_144);
lean_inc_ref(x_21);
x_146 = l_Lean_mkApp3(x_145, x_30, x_21, x_18);
lean_inc_ref(x_21);
x_147 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_138, x_142, x_21, x_146, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_ctor_get(x_147, 0);
lean_ctor_set(x_50, 1, x_149);
lean_ctor_set(x_50, 0, x_21);
x_150 = lean_unbox(x_43);
lean_dec(x_43);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_150);
lean_ctor_set(x_147, 0, x_50);
return x_147;
}
else
{
lean_object* x_151; uint8_t x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_147, 0);
lean_inc(x_151);
lean_dec(x_147);
lean_ctor_set(x_50, 1, x_151);
lean_ctor_set(x_50, 0, x_21);
x_152 = lean_unbox(x_43);
lean_dec(x_43);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_152);
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_50);
return x_153;
}
}
else
{
uint8_t x_154; 
lean_free_object(x_50);
lean_dec(x_43);
lean_dec_ref(x_21);
x_154 = !lean_is_exclusive(x_147);
if (x_154 == 0)
{
return x_147;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_147, 0);
lean_inc(x_155);
lean_dec(x_147);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_132);
lean_free_object(x_50);
lean_dec_ref(x_55);
lean_dec(x_43);
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
x_157 = !lean_is_exclusive(x_137);
if (x_157 == 0)
{
return x_137;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_137, 0);
lean_inc(x_158);
lean_dec(x_137);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_free_object(x_50);
lean_dec_ref(x_55);
lean_dec(x_43);
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
x_160 = !lean_is_exclusive(x_131);
if (x_160 == 0)
{
return x_131;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_131, 0);
lean_inc(x_161);
lean_dec(x_131);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
return x_162;
}
}
}
}
else
{
uint8_t x_163; 
lean_free_object(x_50);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_43);
lean_free_object(x_35);
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
x_163 = !lean_is_exclusive(x_56);
if (x_163 == 0)
{
return x_56;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_56, 0);
lean_inc(x_164);
lean_dec(x_56);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_50, 0);
x_167 = lean_ctor_get(x_50, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_50);
x_168 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_166, x_6);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; uint8_t x_170; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec_ref(x_168);
x_170 = lean_unbox(x_169);
if (x_170 == 0)
{
lean_object* x_171; 
lean_dec(x_43);
x_171 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_166, x_6);
lean_dec_ref(x_166);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_173 = x_171;
} else {
 lean_dec_ref(x_171);
 x_173 = lean_box(0);
}
x_174 = lean_unbox(x_172);
lean_dec(x_172);
if (x_174 == 0)
{
lean_object* x_175; 
lean_dec(x_169);
lean_dec_ref(x_167);
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
lean_ctor_set_uint8(x_35, 0, x_33);
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(0, 1, 0);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_35);
return x_175;
}
else
{
lean_object* x_176; 
lean_dec(x_173);
lean_free_object(x_35);
x_176 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec_ref(x_176);
x_178 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
x_179 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_180 = lean_unsigned_to_nat(4u);
x_181 = l_Lean_Expr_getBoundedAppFn(x_180, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_177);
x_182 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_181, x_177, x_179, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec_ref(x_182);
x_184 = l_Lean_mkApp3(x_178, x_27, x_24, x_167);
x_185 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_186 = l_Lean_Expr_replaceFn(x_2, x_185);
x_187 = l_Lean_mkApp3(x_186, x_177, x_179, x_184);
x_188 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_189 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_190 = l_Lean_mkConst(x_188, x_189);
lean_inc_ref(x_18);
x_191 = l_Lean_mkApp3(x_190, x_30, x_21, x_18);
lean_inc_ref(x_18);
x_192 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_183, x_187, x_18, x_191, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
x_195 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_195, 0, x_18);
lean_ctor_set(x_195, 1, x_193);
x_196 = lean_unbox(x_169);
lean_dec(x_169);
lean_ctor_set_uint8(x_195, sizeof(void*)*2, x_196);
if (lean_is_scalar(x_194)) {
 x_197 = lean_alloc_ctor(0, 1, 0);
} else {
 x_197 = x_194;
}
lean_ctor_set(x_197, 0, x_195);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_169);
lean_dec_ref(x_18);
x_198 = lean_ctor_get(x_192, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_199 = x_192;
} else {
 lean_dec_ref(x_192);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_198);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_177);
lean_dec(x_169);
lean_dec_ref(x_167);
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
x_201 = lean_ctor_get(x_182, 0);
lean_inc(x_201);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 x_202 = x_182;
} else {
 lean_dec_ref(x_182);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 1, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_201);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_169);
lean_dec_ref(x_167);
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
x_204 = lean_ctor_get(x_176, 0);
lean_inc(x_204);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_205 = x_176;
} else {
 lean_dec_ref(x_176);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 1, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_204);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_169);
lean_dec_ref(x_167);
lean_free_object(x_35);
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
x_207 = lean_ctor_get(x_171, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_208 = x_171;
} else {
 lean_dec_ref(x_171);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 1, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_207);
return x_209;
}
}
else
{
lean_object* x_210; 
lean_dec(x_169);
lean_dec_ref(x_166);
lean_free_object(x_35);
x_210 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec_ref(x_210);
x_212 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20);
x_213 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23);
x_214 = lean_unsigned_to_nat(4u);
x_215 = l_Lean_Expr_getBoundedAppFn(x_214, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_211);
x_216 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_215, x_211, x_213, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
lean_dec_ref(x_216);
x_218 = l_Lean_mkApp3(x_212, x_27, x_24, x_167);
x_219 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_220 = l_Lean_Expr_replaceFn(x_2, x_219);
x_221 = l_Lean_mkApp3(x_220, x_211, x_213, x_218);
x_222 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25));
x_223 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_224 = l_Lean_mkConst(x_222, x_223);
lean_inc_ref(x_21);
x_225 = l_Lean_mkApp3(x_224, x_30, x_21, x_18);
lean_inc_ref(x_21);
x_226 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_217, x_221, x_21, x_225, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 x_228 = x_226;
} else {
 lean_dec_ref(x_226);
 x_228 = lean_box(0);
}
x_229 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_229, 0, x_21);
lean_ctor_set(x_229, 1, x_227);
x_230 = lean_unbox(x_43);
lean_dec(x_43);
lean_ctor_set_uint8(x_229, sizeof(void*)*2, x_230);
if (lean_is_scalar(x_228)) {
 x_231 = lean_alloc_ctor(0, 1, 0);
} else {
 x_231 = x_228;
}
lean_ctor_set(x_231, 0, x_229);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_43);
lean_dec_ref(x_21);
x_232 = lean_ctor_get(x_226, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 x_233 = x_226;
} else {
 lean_dec_ref(x_226);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 1, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_232);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_211);
lean_dec_ref(x_167);
lean_dec(x_43);
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
x_235 = lean_ctor_get(x_216, 0);
lean_inc(x_235);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 x_236 = x_216;
} else {
 lean_dec_ref(x_216);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 1, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_235);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec_ref(x_167);
lean_dec(x_43);
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
x_238 = lean_ctor_get(x_210, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 x_239 = x_210;
} else {
 lean_dec_ref(x_210);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 1, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_238);
return x_240;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec_ref(x_167);
lean_dec_ref(x_166);
lean_dec(x_43);
lean_free_object(x_35);
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
x_241 = lean_ctor_get(x_168, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_242 = x_168;
} else {
 lean_dec_ref(x_168);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 1, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_241);
return x_243;
}
}
}
}
else
{
lean_object* x_244; 
x_244 = lean_ctor_get(x_48, 0);
lean_inc(x_244);
lean_dec(x_48);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_43);
lean_free_object(x_35);
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
if (lean_is_exclusive(x_244)) {
 x_245 = x_244;
} else {
 lean_dec_ref(x_244);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(0, 0, 1);
} else {
 x_246 = x_245;
}
lean_ctor_set_uint8(x_246, 0, x_33);
x_247 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_247, 0, x_246);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_ctor_get(x_244, 0);
lean_inc_ref(x_248);
x_249 = lean_ctor_get(x_244, 1);
lean_inc_ref(x_249);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_250 = x_244;
} else {
 lean_dec_ref(x_244);
 x_250 = lean_box(0);
}
x_251 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_248, x_6);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; uint8_t x_253; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
lean_dec_ref(x_251);
x_253 = lean_unbox(x_252);
if (x_253 == 0)
{
lean_object* x_254; 
lean_dec(x_43);
x_254 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_248, x_6);
lean_dec_ref(x_248);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 x_256 = x_254;
} else {
 lean_dec_ref(x_254);
 x_256 = lean_box(0);
}
x_257 = lean_unbox(x_255);
lean_dec(x_255);
if (x_257 == 0)
{
lean_object* x_258; 
lean_dec(x_252);
lean_dec(x_250);
lean_dec_ref(x_249);
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
lean_ctor_set_uint8(x_35, 0, x_33);
if (lean_is_scalar(x_256)) {
 x_258 = lean_alloc_ctor(0, 1, 0);
} else {
 x_258 = x_256;
}
lean_ctor_set(x_258, 0, x_35);
return x_258;
}
else
{
lean_object* x_259; 
lean_dec(x_256);
lean_free_object(x_35);
x_259 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
lean_dec_ref(x_259);
x_261 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
x_262 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_263 = lean_unsigned_to_nat(4u);
x_264 = l_Lean_Expr_getBoundedAppFn(x_263, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_260);
x_265 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_264, x_260, x_262, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec_ref(x_265);
x_267 = l_Lean_mkApp3(x_261, x_27, x_24, x_249);
x_268 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_269 = l_Lean_Expr_replaceFn(x_2, x_268);
x_270 = l_Lean_mkApp3(x_269, x_260, x_262, x_267);
x_271 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_272 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_273 = l_Lean_mkConst(x_271, x_272);
lean_inc_ref(x_18);
x_274 = l_Lean_mkApp3(x_273, x_30, x_21, x_18);
lean_inc_ref(x_18);
x_275 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_266, x_270, x_18, x_274, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 x_277 = x_275;
} else {
 lean_dec_ref(x_275);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_278 = lean_alloc_ctor(1, 2, 1);
} else {
 x_278 = x_250;
}
lean_ctor_set(x_278, 0, x_18);
lean_ctor_set(x_278, 1, x_276);
x_279 = lean_unbox(x_252);
lean_dec(x_252);
lean_ctor_set_uint8(x_278, sizeof(void*)*2, x_279);
if (lean_is_scalar(x_277)) {
 x_280 = lean_alloc_ctor(0, 1, 0);
} else {
 x_280 = x_277;
}
lean_ctor_set(x_280, 0, x_278);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_252);
lean_dec(x_250);
lean_dec_ref(x_18);
x_281 = lean_ctor_get(x_275, 0);
lean_inc(x_281);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 x_282 = x_275;
} else {
 lean_dec_ref(x_275);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 1, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_281);
return x_283;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_260);
lean_dec(x_252);
lean_dec(x_250);
lean_dec_ref(x_249);
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
x_284 = lean_ctor_get(x_265, 0);
lean_inc(x_284);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_285 = x_265;
} else {
 lean_dec_ref(x_265);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 1, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_284);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_252);
lean_dec(x_250);
lean_dec_ref(x_249);
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
x_287 = lean_ctor_get(x_259, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_288 = x_259;
} else {
 lean_dec_ref(x_259);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 1, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_287);
return x_289;
}
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_252);
lean_dec(x_250);
lean_dec_ref(x_249);
lean_free_object(x_35);
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
x_290 = lean_ctor_get(x_254, 0);
lean_inc(x_290);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 x_291 = x_254;
} else {
 lean_dec_ref(x_254);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 1, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_290);
return x_292;
}
}
else
{
lean_object* x_293; 
lean_dec(x_252);
lean_dec_ref(x_248);
lean_free_object(x_35);
x_293 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
lean_dec_ref(x_293);
x_295 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20);
x_296 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23);
x_297 = lean_unsigned_to_nat(4u);
x_298 = l_Lean_Expr_getBoundedAppFn(x_297, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_294);
x_299 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_298, x_294, x_296, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
lean_dec_ref(x_299);
x_301 = l_Lean_mkApp3(x_295, x_27, x_24, x_249);
x_302 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_303 = l_Lean_Expr_replaceFn(x_2, x_302);
x_304 = l_Lean_mkApp3(x_303, x_294, x_296, x_301);
x_305 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25));
x_306 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_307 = l_Lean_mkConst(x_305, x_306);
lean_inc_ref(x_21);
x_308 = l_Lean_mkApp3(x_307, x_30, x_21, x_18);
lean_inc_ref(x_21);
x_309 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_300, x_304, x_21, x_308, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_311 = x_309;
} else {
 lean_dec_ref(x_309);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_312 = lean_alloc_ctor(1, 2, 1);
} else {
 x_312 = x_250;
}
lean_ctor_set(x_312, 0, x_21);
lean_ctor_set(x_312, 1, x_310);
x_313 = lean_unbox(x_43);
lean_dec(x_43);
lean_ctor_set_uint8(x_312, sizeof(void*)*2, x_313);
if (lean_is_scalar(x_311)) {
 x_314 = lean_alloc_ctor(0, 1, 0);
} else {
 x_314 = x_311;
}
lean_ctor_set(x_314, 0, x_312);
return x_314;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_250);
lean_dec(x_43);
lean_dec_ref(x_21);
x_315 = lean_ctor_get(x_309, 0);
lean_inc(x_315);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_316 = x_309;
} else {
 lean_dec_ref(x_309);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 1, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_315);
return x_317;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_294);
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec(x_43);
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
x_318 = lean_ctor_get(x_299, 0);
lean_inc(x_318);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 x_319 = x_299;
} else {
 lean_dec_ref(x_299);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 1, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_318);
return x_320;
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec(x_43);
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
x_321 = lean_ctor_get(x_293, 0);
lean_inc(x_321);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 x_322 = x_293;
} else {
 lean_dec_ref(x_293);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 1, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_321);
return x_323;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec_ref(x_248);
lean_dec(x_43);
lean_free_object(x_35);
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
x_324 = lean_ctor_get(x_251, 0);
lean_inc(x_324);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 x_325 = x_251;
} else {
 lean_dec_ref(x_251);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 1, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_324);
return x_326;
}
}
}
}
else
{
lean_dec(x_43);
lean_free_object(x_35);
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
return x_48;
}
}
else
{
uint8_t x_327; 
lean_dec(x_43);
lean_free_object(x_35);
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
x_327 = !lean_is_exclusive(x_46);
if (x_327 == 0)
{
return x_46;
}
else
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_46, 0);
lean_inc(x_328);
lean_dec(x_46);
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_328);
return x_329;
}
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
lean_dec(x_43);
lean_free_object(x_35);
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
x_330 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_331 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_332 = l_Lean_mkConst(x_330, x_331);
lean_inc_ref(x_18);
x_333 = l_Lean_mkApp3(x_332, x_30, x_21, x_18);
x_334 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_334, 0, x_18);
lean_ctor_set(x_334, 1, x_333);
x_335 = lean_unbox(x_39);
lean_dec(x_39);
lean_ctor_set_uint8(x_334, sizeof(void*)*2, x_335);
lean_ctor_set(x_41, 0, x_334);
return x_41;
}
}
else
{
lean_object* x_336; uint8_t x_337; 
x_336 = lean_ctor_get(x_41, 0);
lean_inc(x_336);
lean_dec(x_41);
x_337 = lean_unbox(x_336);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; 
lean_dec(x_39);
x_338 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_24);
lean_inc_ref(x_27);
x_339 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_338, x_27, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
lean_dec_ref(x_339);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_341 = lean_sym_simp(x_340, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 x_343 = x_341;
} else {
 lean_dec_ref(x_341);
 x_343 = lean_box(0);
}
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_336);
lean_free_object(x_35);
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
if (lean_is_exclusive(x_342)) {
 x_344 = x_342;
} else {
 lean_dec_ref(x_342);
 x_344 = lean_box(0);
}
if (lean_is_scalar(x_344)) {
 x_345 = lean_alloc_ctor(0, 0, 1);
} else {
 x_345 = x_344;
}
lean_ctor_set_uint8(x_345, 0, x_33);
if (lean_is_scalar(x_343)) {
 x_346 = lean_alloc_ctor(0, 1, 0);
} else {
 x_346 = x_343;
}
lean_ctor_set(x_346, 0, x_345);
return x_346;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_343);
x_347 = lean_ctor_get(x_342, 0);
lean_inc_ref(x_347);
x_348 = lean_ctor_get(x_342, 1);
lean_inc_ref(x_348);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_349 = x_342;
} else {
 lean_dec_ref(x_342);
 x_349 = lean_box(0);
}
x_350 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_347, x_6);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; uint8_t x_352; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
lean_dec_ref(x_350);
x_352 = lean_unbox(x_351);
if (x_352 == 0)
{
lean_object* x_353; 
lean_dec(x_336);
x_353 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_347, x_6);
lean_dec_ref(x_347);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; uint8_t x_356; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 x_355 = x_353;
} else {
 lean_dec_ref(x_353);
 x_355 = lean_box(0);
}
x_356 = lean_unbox(x_354);
lean_dec(x_354);
if (x_356 == 0)
{
lean_object* x_357; 
lean_dec(x_351);
lean_dec(x_349);
lean_dec_ref(x_348);
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
lean_ctor_set_uint8(x_35, 0, x_33);
if (lean_is_scalar(x_355)) {
 x_357 = lean_alloc_ctor(0, 1, 0);
} else {
 x_357 = x_355;
}
lean_ctor_set(x_357, 0, x_35);
return x_357;
}
else
{
lean_object* x_358; 
lean_dec(x_355);
lean_free_object(x_35);
x_358 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
lean_dec_ref(x_358);
x_360 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
x_361 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_362 = lean_unsigned_to_nat(4u);
x_363 = l_Lean_Expr_getBoundedAppFn(x_362, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_359);
x_364 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_363, x_359, x_361, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
lean_dec_ref(x_364);
x_366 = l_Lean_mkApp3(x_360, x_27, x_24, x_348);
x_367 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_368 = l_Lean_Expr_replaceFn(x_2, x_367);
x_369 = l_Lean_mkApp3(x_368, x_359, x_361, x_366);
x_370 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_371 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_372 = l_Lean_mkConst(x_370, x_371);
lean_inc_ref(x_18);
x_373 = l_Lean_mkApp3(x_372, x_30, x_21, x_18);
lean_inc_ref(x_18);
x_374 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_365, x_369, x_18, x_373, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; lean_object* x_379; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 x_376 = x_374;
} else {
 lean_dec_ref(x_374);
 x_376 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_377 = lean_alloc_ctor(1, 2, 1);
} else {
 x_377 = x_349;
}
lean_ctor_set(x_377, 0, x_18);
lean_ctor_set(x_377, 1, x_375);
x_378 = lean_unbox(x_351);
lean_dec(x_351);
lean_ctor_set_uint8(x_377, sizeof(void*)*2, x_378);
if (lean_is_scalar(x_376)) {
 x_379 = lean_alloc_ctor(0, 1, 0);
} else {
 x_379 = x_376;
}
lean_ctor_set(x_379, 0, x_377);
return x_379;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_351);
lean_dec(x_349);
lean_dec_ref(x_18);
x_380 = lean_ctor_get(x_374, 0);
lean_inc(x_380);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 x_381 = x_374;
} else {
 lean_dec_ref(x_374);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(1, 1, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_380);
return x_382;
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_359);
lean_dec(x_351);
lean_dec(x_349);
lean_dec_ref(x_348);
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
x_383 = lean_ctor_get(x_364, 0);
lean_inc(x_383);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 x_384 = x_364;
} else {
 lean_dec_ref(x_364);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(1, 1, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_383);
return x_385;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_351);
lean_dec(x_349);
lean_dec_ref(x_348);
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
x_386 = lean_ctor_get(x_358, 0);
lean_inc(x_386);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 x_387 = x_358;
} else {
 lean_dec_ref(x_358);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 1, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_386);
return x_388;
}
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_351);
lean_dec(x_349);
lean_dec_ref(x_348);
lean_free_object(x_35);
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
x_389 = lean_ctor_get(x_353, 0);
lean_inc(x_389);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 x_390 = x_353;
} else {
 lean_dec_ref(x_353);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(1, 1, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_389);
return x_391;
}
}
else
{
lean_object* x_392; 
lean_dec(x_351);
lean_dec_ref(x_347);
lean_free_object(x_35);
x_392 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
lean_dec_ref(x_392);
x_394 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20);
x_395 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23);
x_396 = lean_unsigned_to_nat(4u);
x_397 = l_Lean_Expr_getBoundedAppFn(x_396, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_393);
x_398 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_397, x_393, x_395, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
lean_dec_ref(x_398);
x_400 = l_Lean_mkApp3(x_394, x_27, x_24, x_348);
x_401 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_402 = l_Lean_Expr_replaceFn(x_2, x_401);
x_403 = l_Lean_mkApp3(x_402, x_393, x_395, x_400);
x_404 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25));
x_405 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_406 = l_Lean_mkConst(x_404, x_405);
lean_inc_ref(x_21);
x_407 = l_Lean_mkApp3(x_406, x_30, x_21, x_18);
lean_inc_ref(x_21);
x_408 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_399, x_403, x_21, x_407, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_410 = x_408;
} else {
 lean_dec_ref(x_408);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_411 = lean_alloc_ctor(1, 2, 1);
} else {
 x_411 = x_349;
}
lean_ctor_set(x_411, 0, x_21);
lean_ctor_set(x_411, 1, x_409);
x_412 = lean_unbox(x_336);
lean_dec(x_336);
lean_ctor_set_uint8(x_411, sizeof(void*)*2, x_412);
if (lean_is_scalar(x_410)) {
 x_413 = lean_alloc_ctor(0, 1, 0);
} else {
 x_413 = x_410;
}
lean_ctor_set(x_413, 0, x_411);
return x_413;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_dec(x_349);
lean_dec(x_336);
lean_dec_ref(x_21);
x_414 = lean_ctor_get(x_408, 0);
lean_inc(x_414);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_415 = x_408;
} else {
 lean_dec_ref(x_408);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 1, 0);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_414);
return x_416;
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_393);
lean_dec(x_349);
lean_dec_ref(x_348);
lean_dec(x_336);
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
x_417 = lean_ctor_get(x_398, 0);
lean_inc(x_417);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 x_418 = x_398;
} else {
 lean_dec_ref(x_398);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(1, 1, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_417);
return x_419;
}
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_349);
lean_dec_ref(x_348);
lean_dec(x_336);
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
x_420 = lean_ctor_get(x_392, 0);
lean_inc(x_420);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 x_421 = x_392;
} else {
 lean_dec_ref(x_392);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(1, 1, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_420);
return x_422;
}
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_349);
lean_dec_ref(x_348);
lean_dec_ref(x_347);
lean_dec(x_336);
lean_free_object(x_35);
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
x_423 = lean_ctor_get(x_350, 0);
lean_inc(x_423);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 x_424 = x_350;
} else {
 lean_dec_ref(x_350);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 1, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_423);
return x_425;
}
}
}
else
{
lean_dec(x_336);
lean_free_object(x_35);
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
return x_341;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_336);
lean_free_object(x_35);
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
x_426 = lean_ctor_get(x_339, 0);
lean_inc(x_426);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 x_427 = x_339;
} else {
 lean_dec_ref(x_339);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(1, 1, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_426);
return x_428;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; 
lean_dec(x_336);
lean_free_object(x_35);
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
x_429 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_430 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_431 = l_Lean_mkConst(x_429, x_430);
lean_inc_ref(x_18);
x_432 = l_Lean_mkApp3(x_431, x_30, x_21, x_18);
x_433 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_433, 0, x_18);
lean_ctor_set(x_433, 1, x_432);
x_434 = lean_unbox(x_39);
lean_dec(x_39);
lean_ctor_set_uint8(x_433, sizeof(void*)*2, x_434);
x_435 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_435, 0, x_433);
return x_435;
}
}
}
else
{
uint8_t x_436; 
lean_dec(x_39);
lean_free_object(x_35);
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
x_436 = !lean_is_exclusive(x_41);
if (x_436 == 0)
{
return x_41;
}
else
{
lean_object* x_437; lean_object* x_438; 
x_437 = lean_ctor_get(x_41, 0);
lean_inc(x_437);
lean_dec(x_41);
x_438 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_438, 0, x_437);
return x_438;
}
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_39);
lean_free_object(x_35);
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
x_439 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25));
x_440 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_441 = l_Lean_mkConst(x_439, x_440);
lean_inc_ref(x_21);
x_442 = l_Lean_mkApp3(x_441, x_30, x_21, x_18);
x_443 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_443, 0, x_21);
lean_ctor_set(x_443, 1, x_442);
lean_ctor_set_uint8(x_443, sizeof(void*)*2, x_1);
lean_ctor_set(x_37, 0, x_443);
return x_37;
}
}
else
{
lean_object* x_444; uint8_t x_445; 
x_444 = lean_ctor_get(x_37, 0);
lean_inc(x_444);
lean_dec(x_37);
x_445 = lean_unbox(x_444);
if (x_445 == 0)
{
lean_object* x_446; 
x_446 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; uint8_t x_449; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 x_448 = x_446;
} else {
 lean_dec_ref(x_446);
 x_448 = lean_box(0);
}
x_449 = lean_unbox(x_447);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; 
lean_dec(x_448);
lean_dec(x_444);
x_450 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_24);
lean_inc_ref(x_27);
x_451 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_450, x_27, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
lean_dec_ref(x_451);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_453 = lean_sym_simp(x_452, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; lean_object* x_455; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 x_455 = x_453;
} else {
 lean_dec_ref(x_453);
 x_455 = lean_box(0);
}
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_447);
lean_free_object(x_35);
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
if (lean_is_exclusive(x_454)) {
 x_456 = x_454;
} else {
 lean_dec_ref(x_454);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(0, 0, 1);
} else {
 x_457 = x_456;
}
lean_ctor_set_uint8(x_457, 0, x_33);
if (lean_is_scalar(x_455)) {
 x_458 = lean_alloc_ctor(0, 1, 0);
} else {
 x_458 = x_455;
}
lean_ctor_set(x_458, 0, x_457);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_455);
x_459 = lean_ctor_get(x_454, 0);
lean_inc_ref(x_459);
x_460 = lean_ctor_get(x_454, 1);
lean_inc_ref(x_460);
if (lean_is_exclusive(x_454)) {
 lean_ctor_release(x_454, 0);
 lean_ctor_release(x_454, 1);
 x_461 = x_454;
} else {
 lean_dec_ref(x_454);
 x_461 = lean_box(0);
}
x_462 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_459, x_6);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; uint8_t x_464; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
lean_dec_ref(x_462);
x_464 = lean_unbox(x_463);
if (x_464 == 0)
{
lean_object* x_465; 
lean_dec(x_447);
x_465 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_459, x_6);
lean_dec_ref(x_459);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; uint8_t x_468; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 x_467 = x_465;
} else {
 lean_dec_ref(x_465);
 x_467 = lean_box(0);
}
x_468 = lean_unbox(x_466);
lean_dec(x_466);
if (x_468 == 0)
{
lean_object* x_469; 
lean_dec(x_463);
lean_dec(x_461);
lean_dec_ref(x_460);
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
lean_ctor_set_uint8(x_35, 0, x_33);
if (lean_is_scalar(x_467)) {
 x_469 = lean_alloc_ctor(0, 1, 0);
} else {
 x_469 = x_467;
}
lean_ctor_set(x_469, 0, x_35);
return x_469;
}
else
{
lean_object* x_470; 
lean_dec(x_467);
lean_free_object(x_35);
x_470 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
lean_dec_ref(x_470);
x_472 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
x_473 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_474 = lean_unsigned_to_nat(4u);
x_475 = l_Lean_Expr_getBoundedAppFn(x_474, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_471);
x_476 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_475, x_471, x_473, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
lean_dec_ref(x_476);
x_478 = l_Lean_mkApp3(x_472, x_27, x_24, x_460);
x_479 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_480 = l_Lean_Expr_replaceFn(x_2, x_479);
x_481 = l_Lean_mkApp3(x_480, x_471, x_473, x_478);
x_482 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_483 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_484 = l_Lean_mkConst(x_482, x_483);
lean_inc_ref(x_18);
x_485 = l_Lean_mkApp3(x_484, x_30, x_21, x_18);
lean_inc_ref(x_18);
x_486 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_477, x_481, x_18, x_485, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 x_488 = x_486;
} else {
 lean_dec_ref(x_486);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_489 = lean_alloc_ctor(1, 2, 1);
} else {
 x_489 = x_461;
}
lean_ctor_set(x_489, 0, x_18);
lean_ctor_set(x_489, 1, x_487);
x_490 = lean_unbox(x_463);
lean_dec(x_463);
lean_ctor_set_uint8(x_489, sizeof(void*)*2, x_490);
if (lean_is_scalar(x_488)) {
 x_491 = lean_alloc_ctor(0, 1, 0);
} else {
 x_491 = x_488;
}
lean_ctor_set(x_491, 0, x_489);
return x_491;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_463);
lean_dec(x_461);
lean_dec_ref(x_18);
x_492 = lean_ctor_get(x_486, 0);
lean_inc(x_492);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 x_493 = x_486;
} else {
 lean_dec_ref(x_486);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(1, 1, 0);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_492);
return x_494;
}
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
lean_dec(x_471);
lean_dec(x_463);
lean_dec(x_461);
lean_dec_ref(x_460);
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
x_495 = lean_ctor_get(x_476, 0);
lean_inc(x_495);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 x_496 = x_476;
} else {
 lean_dec_ref(x_476);
 x_496 = lean_box(0);
}
if (lean_is_scalar(x_496)) {
 x_497 = lean_alloc_ctor(1, 1, 0);
} else {
 x_497 = x_496;
}
lean_ctor_set(x_497, 0, x_495);
return x_497;
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_463);
lean_dec(x_461);
lean_dec_ref(x_460);
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
x_498 = lean_ctor_get(x_470, 0);
lean_inc(x_498);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 x_499 = x_470;
} else {
 lean_dec_ref(x_470);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 1, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_498);
return x_500;
}
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_463);
lean_dec(x_461);
lean_dec_ref(x_460);
lean_free_object(x_35);
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
x_501 = lean_ctor_get(x_465, 0);
lean_inc(x_501);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 x_502 = x_465;
} else {
 lean_dec_ref(x_465);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 1, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_501);
return x_503;
}
}
else
{
lean_object* x_504; 
lean_dec(x_463);
lean_dec_ref(x_459);
lean_free_object(x_35);
x_504 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
lean_dec_ref(x_504);
x_506 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20);
x_507 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23);
x_508 = lean_unsigned_to_nat(4u);
x_509 = l_Lean_Expr_getBoundedAppFn(x_508, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_505);
x_510 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_509, x_505, x_507, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
lean_dec_ref(x_510);
x_512 = l_Lean_mkApp3(x_506, x_27, x_24, x_460);
x_513 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_514 = l_Lean_Expr_replaceFn(x_2, x_513);
x_515 = l_Lean_mkApp3(x_514, x_505, x_507, x_512);
x_516 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25));
x_517 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_518 = l_Lean_mkConst(x_516, x_517);
lean_inc_ref(x_21);
x_519 = l_Lean_mkApp3(x_518, x_30, x_21, x_18);
lean_inc_ref(x_21);
x_520 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_511, x_515, x_21, x_519, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; uint8_t x_524; lean_object* x_525; 
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 x_522 = x_520;
} else {
 lean_dec_ref(x_520);
 x_522 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_523 = lean_alloc_ctor(1, 2, 1);
} else {
 x_523 = x_461;
}
lean_ctor_set(x_523, 0, x_21);
lean_ctor_set(x_523, 1, x_521);
x_524 = lean_unbox(x_447);
lean_dec(x_447);
lean_ctor_set_uint8(x_523, sizeof(void*)*2, x_524);
if (lean_is_scalar(x_522)) {
 x_525 = lean_alloc_ctor(0, 1, 0);
} else {
 x_525 = x_522;
}
lean_ctor_set(x_525, 0, x_523);
return x_525;
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_461);
lean_dec(x_447);
lean_dec_ref(x_21);
x_526 = lean_ctor_get(x_520, 0);
lean_inc(x_526);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 x_527 = x_520;
} else {
 lean_dec_ref(x_520);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_528 = lean_alloc_ctor(1, 1, 0);
} else {
 x_528 = x_527;
}
lean_ctor_set(x_528, 0, x_526);
return x_528;
}
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_505);
lean_dec(x_461);
lean_dec_ref(x_460);
lean_dec(x_447);
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
x_529 = lean_ctor_get(x_510, 0);
lean_inc(x_529);
if (lean_is_exclusive(x_510)) {
 lean_ctor_release(x_510, 0);
 x_530 = x_510;
} else {
 lean_dec_ref(x_510);
 x_530 = lean_box(0);
}
if (lean_is_scalar(x_530)) {
 x_531 = lean_alloc_ctor(1, 1, 0);
} else {
 x_531 = x_530;
}
lean_ctor_set(x_531, 0, x_529);
return x_531;
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_dec(x_461);
lean_dec_ref(x_460);
lean_dec(x_447);
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
x_532 = lean_ctor_get(x_504, 0);
lean_inc(x_532);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 x_533 = x_504;
} else {
 lean_dec_ref(x_504);
 x_533 = lean_box(0);
}
if (lean_is_scalar(x_533)) {
 x_534 = lean_alloc_ctor(1, 1, 0);
} else {
 x_534 = x_533;
}
lean_ctor_set(x_534, 0, x_532);
return x_534;
}
}
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_461);
lean_dec_ref(x_460);
lean_dec_ref(x_459);
lean_dec(x_447);
lean_free_object(x_35);
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
x_535 = lean_ctor_get(x_462, 0);
lean_inc(x_535);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 x_536 = x_462;
} else {
 lean_dec_ref(x_462);
 x_536 = lean_box(0);
}
if (lean_is_scalar(x_536)) {
 x_537 = lean_alloc_ctor(1, 1, 0);
} else {
 x_537 = x_536;
}
lean_ctor_set(x_537, 0, x_535);
return x_537;
}
}
}
else
{
lean_dec(x_447);
lean_free_object(x_35);
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
return x_453;
}
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_447);
lean_free_object(x_35);
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
x_538 = lean_ctor_get(x_451, 0);
lean_inc(x_538);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 x_539 = x_451;
} else {
 lean_dec_ref(x_451);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 1, 0);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_538);
return x_540;
}
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_546; lean_object* x_547; 
lean_dec(x_447);
lean_free_object(x_35);
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
x_541 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_542 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_543 = l_Lean_mkConst(x_541, x_542);
lean_inc_ref(x_18);
x_544 = l_Lean_mkApp3(x_543, x_30, x_21, x_18);
x_545 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_545, 0, x_18);
lean_ctor_set(x_545, 1, x_544);
x_546 = lean_unbox(x_444);
lean_dec(x_444);
lean_ctor_set_uint8(x_545, sizeof(void*)*2, x_546);
if (lean_is_scalar(x_448)) {
 x_547 = lean_alloc_ctor(0, 1, 0);
} else {
 x_547 = x_448;
}
lean_ctor_set(x_547, 0, x_545);
return x_547;
}
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_444);
lean_free_object(x_35);
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
x_548 = lean_ctor_get(x_446, 0);
lean_inc(x_548);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 x_549 = x_446;
} else {
 lean_dec_ref(x_446);
 x_549 = lean_box(0);
}
if (lean_is_scalar(x_549)) {
 x_550 = lean_alloc_ctor(1, 1, 0);
} else {
 x_550 = x_549;
}
lean_ctor_set(x_550, 0, x_548);
return x_550;
}
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
lean_dec(x_444);
lean_free_object(x_35);
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
x_551 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25));
x_552 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_553 = l_Lean_mkConst(x_551, x_552);
lean_inc_ref(x_21);
x_554 = l_Lean_mkApp3(x_553, x_30, x_21, x_18);
x_555 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_555, 0, x_21);
lean_ctor_set(x_555, 1, x_554);
lean_ctor_set_uint8(x_555, sizeof(void*)*2, x_1);
x_556 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_556, 0, x_555);
return x_556;
}
}
}
else
{
uint8_t x_557; 
lean_free_object(x_35);
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
x_557 = !lean_is_exclusive(x_37);
if (x_557 == 0)
{
return x_37;
}
else
{
lean_object* x_558; lean_object* x_559; 
x_558 = lean_ctor_get(x_37, 0);
lean_inc(x_558);
lean_dec(x_37);
x_559 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_559, 0, x_558);
return x_559;
}
}
}
else
{
lean_object* x_560; 
lean_dec(x_35);
x_560 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; uint8_t x_563; 
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 x_562 = x_560;
} else {
 lean_dec_ref(x_560);
 x_562 = lean_box(0);
}
x_563 = lean_unbox(x_561);
if (x_563 == 0)
{
lean_object* x_564; 
lean_dec(x_562);
x_564 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; uint8_t x_567; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 x_566 = x_564;
} else {
 lean_dec_ref(x_564);
 x_566 = lean_box(0);
}
x_567 = lean_unbox(x_565);
if (x_567 == 0)
{
lean_object* x_568; lean_object* x_569; 
lean_dec(x_566);
lean_dec(x_561);
x_568 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_24);
lean_inc_ref(x_27);
x_569 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_568, x_27, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; 
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
lean_dec_ref(x_569);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_571 = lean_sym_simp(x_570, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; lean_object* x_573; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 x_573 = x_571;
} else {
 lean_dec_ref(x_571);
 x_573 = lean_box(0);
}
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_565);
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
if (lean_is_exclusive(x_572)) {
 x_574 = x_572;
} else {
 lean_dec_ref(x_572);
 x_574 = lean_box(0);
}
if (lean_is_scalar(x_574)) {
 x_575 = lean_alloc_ctor(0, 0, 1);
} else {
 x_575 = x_574;
}
lean_ctor_set_uint8(x_575, 0, x_33);
if (lean_is_scalar(x_573)) {
 x_576 = lean_alloc_ctor(0, 1, 0);
} else {
 x_576 = x_573;
}
lean_ctor_set(x_576, 0, x_575);
return x_576;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_dec(x_573);
x_577 = lean_ctor_get(x_572, 0);
lean_inc_ref(x_577);
x_578 = lean_ctor_get(x_572, 1);
lean_inc_ref(x_578);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_579 = x_572;
} else {
 lean_dec_ref(x_572);
 x_579 = lean_box(0);
}
x_580 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_577, x_6);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; uint8_t x_582; 
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
lean_dec_ref(x_580);
x_582 = lean_unbox(x_581);
if (x_582 == 0)
{
lean_object* x_583; 
lean_dec(x_565);
x_583 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_577, x_6);
lean_dec_ref(x_577);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; uint8_t x_586; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 x_585 = x_583;
} else {
 lean_dec_ref(x_583);
 x_585 = lean_box(0);
}
x_586 = lean_unbox(x_584);
lean_dec(x_584);
if (x_586 == 0)
{
lean_object* x_587; lean_object* x_588; 
lean_dec(x_581);
lean_dec(x_579);
lean_dec_ref(x_578);
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
x_587 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_587, 0, x_33);
if (lean_is_scalar(x_585)) {
 x_588 = lean_alloc_ctor(0, 1, 0);
} else {
 x_588 = x_585;
}
lean_ctor_set(x_588, 0, x_587);
return x_588;
}
else
{
lean_object* x_589; 
lean_dec(x_585);
x_589 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
lean_dec_ref(x_589);
x_591 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
x_592 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_593 = lean_unsigned_to_nat(4u);
x_594 = l_Lean_Expr_getBoundedAppFn(x_593, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_590);
x_595 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_594, x_590, x_592, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_595) == 0)
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
lean_dec_ref(x_595);
x_597 = l_Lean_mkApp3(x_591, x_27, x_24, x_578);
x_598 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_599 = l_Lean_Expr_replaceFn(x_2, x_598);
x_600 = l_Lean_mkApp3(x_599, x_590, x_592, x_597);
x_601 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_602 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_603 = l_Lean_mkConst(x_601, x_602);
lean_inc_ref(x_18);
x_604 = l_Lean_mkApp3(x_603, x_30, x_21, x_18);
lean_inc_ref(x_18);
x_605 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_596, x_600, x_18, x_604, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; uint8_t x_609; lean_object* x_610; 
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 x_607 = x_605;
} else {
 lean_dec_ref(x_605);
 x_607 = lean_box(0);
}
if (lean_is_scalar(x_579)) {
 x_608 = lean_alloc_ctor(1, 2, 1);
} else {
 x_608 = x_579;
}
lean_ctor_set(x_608, 0, x_18);
lean_ctor_set(x_608, 1, x_606);
x_609 = lean_unbox(x_581);
lean_dec(x_581);
lean_ctor_set_uint8(x_608, sizeof(void*)*2, x_609);
if (lean_is_scalar(x_607)) {
 x_610 = lean_alloc_ctor(0, 1, 0);
} else {
 x_610 = x_607;
}
lean_ctor_set(x_610, 0, x_608);
return x_610;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_581);
lean_dec(x_579);
lean_dec_ref(x_18);
x_611 = lean_ctor_get(x_605, 0);
lean_inc(x_611);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 x_612 = x_605;
} else {
 lean_dec_ref(x_605);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(1, 1, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_611);
return x_613;
}
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
lean_dec(x_590);
lean_dec(x_581);
lean_dec(x_579);
lean_dec_ref(x_578);
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
x_614 = lean_ctor_get(x_595, 0);
lean_inc(x_614);
if (lean_is_exclusive(x_595)) {
 lean_ctor_release(x_595, 0);
 x_615 = x_595;
} else {
 lean_dec_ref(x_595);
 x_615 = lean_box(0);
}
if (lean_is_scalar(x_615)) {
 x_616 = lean_alloc_ctor(1, 1, 0);
} else {
 x_616 = x_615;
}
lean_ctor_set(x_616, 0, x_614);
return x_616;
}
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; 
lean_dec(x_581);
lean_dec(x_579);
lean_dec_ref(x_578);
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
x_617 = lean_ctor_get(x_589, 0);
lean_inc(x_617);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 x_618 = x_589;
} else {
 lean_dec_ref(x_589);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(1, 1, 0);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_617);
return x_619;
}
}
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
lean_dec(x_581);
lean_dec(x_579);
lean_dec_ref(x_578);
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
x_620 = lean_ctor_get(x_583, 0);
lean_inc(x_620);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 x_621 = x_583;
} else {
 lean_dec_ref(x_583);
 x_621 = lean_box(0);
}
if (lean_is_scalar(x_621)) {
 x_622 = lean_alloc_ctor(1, 1, 0);
} else {
 x_622 = x_621;
}
lean_ctor_set(x_622, 0, x_620);
return x_622;
}
}
else
{
lean_object* x_623; 
lean_dec(x_581);
lean_dec_ref(x_577);
x_623 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
lean_dec_ref(x_623);
x_625 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20);
x_626 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23);
x_627 = lean_unsigned_to_nat(4u);
x_628 = l_Lean_Expr_getBoundedAppFn(x_627, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_624);
x_629 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_628, x_624, x_626, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
lean_dec_ref(x_629);
x_631 = l_Lean_mkApp3(x_625, x_27, x_24, x_578);
x_632 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_633 = l_Lean_Expr_replaceFn(x_2, x_632);
x_634 = l_Lean_mkApp3(x_633, x_624, x_626, x_631);
x_635 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25));
x_636 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_637 = l_Lean_mkConst(x_635, x_636);
lean_inc_ref(x_21);
x_638 = l_Lean_mkApp3(x_637, x_30, x_21, x_18);
lean_inc_ref(x_21);
x_639 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_630, x_634, x_21, x_638, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_639) == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; uint8_t x_643; lean_object* x_644; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 x_641 = x_639;
} else {
 lean_dec_ref(x_639);
 x_641 = lean_box(0);
}
if (lean_is_scalar(x_579)) {
 x_642 = lean_alloc_ctor(1, 2, 1);
} else {
 x_642 = x_579;
}
lean_ctor_set(x_642, 0, x_21);
lean_ctor_set(x_642, 1, x_640);
x_643 = lean_unbox(x_565);
lean_dec(x_565);
lean_ctor_set_uint8(x_642, sizeof(void*)*2, x_643);
if (lean_is_scalar(x_641)) {
 x_644 = lean_alloc_ctor(0, 1, 0);
} else {
 x_644 = x_641;
}
lean_ctor_set(x_644, 0, x_642);
return x_644;
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; 
lean_dec(x_579);
lean_dec(x_565);
lean_dec_ref(x_21);
x_645 = lean_ctor_get(x_639, 0);
lean_inc(x_645);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 x_646 = x_639;
} else {
 lean_dec_ref(x_639);
 x_646 = lean_box(0);
}
if (lean_is_scalar(x_646)) {
 x_647 = lean_alloc_ctor(1, 1, 0);
} else {
 x_647 = x_646;
}
lean_ctor_set(x_647, 0, x_645);
return x_647;
}
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
lean_dec(x_624);
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec(x_565);
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
x_648 = lean_ctor_get(x_629, 0);
lean_inc(x_648);
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 x_649 = x_629;
} else {
 lean_dec_ref(x_629);
 x_649 = lean_box(0);
}
if (lean_is_scalar(x_649)) {
 x_650 = lean_alloc_ctor(1, 1, 0);
} else {
 x_650 = x_649;
}
lean_ctor_set(x_650, 0, x_648);
return x_650;
}
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec(x_565);
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
x_651 = lean_ctor_get(x_623, 0);
lean_inc(x_651);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 x_652 = x_623;
} else {
 lean_dec_ref(x_623);
 x_652 = lean_box(0);
}
if (lean_is_scalar(x_652)) {
 x_653 = lean_alloc_ctor(1, 1, 0);
} else {
 x_653 = x_652;
}
lean_ctor_set(x_653, 0, x_651);
return x_653;
}
}
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec_ref(x_577);
lean_dec(x_565);
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
x_654 = lean_ctor_get(x_580, 0);
lean_inc(x_654);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 x_655 = x_580;
} else {
 lean_dec_ref(x_580);
 x_655 = lean_box(0);
}
if (lean_is_scalar(x_655)) {
 x_656 = lean_alloc_ctor(1, 1, 0);
} else {
 x_656 = x_655;
}
lean_ctor_set(x_656, 0, x_654);
return x_656;
}
}
}
else
{
lean_dec(x_565);
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
return x_571;
}
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
lean_dec(x_565);
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
x_657 = lean_ctor_get(x_569, 0);
lean_inc(x_657);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 x_658 = x_569;
} else {
 lean_dec_ref(x_569);
 x_658 = lean_box(0);
}
if (lean_is_scalar(x_658)) {
 x_659 = lean_alloc_ctor(1, 1, 0);
} else {
 x_659 = x_658;
}
lean_ctor_set(x_659, 0, x_657);
return x_659;
}
}
else
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; lean_object* x_666; 
lean_dec(x_565);
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
x_660 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_661 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_662 = l_Lean_mkConst(x_660, x_661);
lean_inc_ref(x_18);
x_663 = l_Lean_mkApp3(x_662, x_30, x_21, x_18);
x_664 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_664, 0, x_18);
lean_ctor_set(x_664, 1, x_663);
x_665 = lean_unbox(x_561);
lean_dec(x_561);
lean_ctor_set_uint8(x_664, sizeof(void*)*2, x_665);
if (lean_is_scalar(x_566)) {
 x_666 = lean_alloc_ctor(0, 1, 0);
} else {
 x_666 = x_566;
}
lean_ctor_set(x_666, 0, x_664);
return x_666;
}
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_561);
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
x_667 = lean_ctor_get(x_564, 0);
lean_inc(x_667);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 x_668 = x_564;
} else {
 lean_dec_ref(x_564);
 x_668 = lean_box(0);
}
if (lean_is_scalar(x_668)) {
 x_669 = lean_alloc_ctor(1, 1, 0);
} else {
 x_669 = x_668;
}
lean_ctor_set(x_669, 0, x_667);
return x_669;
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
lean_dec(x_561);
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
x_670 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25));
x_671 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_672 = l_Lean_mkConst(x_670, x_671);
lean_inc_ref(x_21);
x_673 = l_Lean_mkApp3(x_672, x_30, x_21, x_18);
x_674 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_674, 0, x_21);
lean_ctor_set(x_674, 1, x_673);
lean_ctor_set_uint8(x_674, sizeof(void*)*2, x_1);
if (lean_is_scalar(x_562)) {
 x_675 = lean_alloc_ctor(0, 1, 0);
} else {
 x_675 = x_562;
}
lean_ctor_set(x_675, 0, x_674);
return x_675;
}
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; 
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
x_676 = lean_ctor_get(x_560, 0);
lean_inc(x_676);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 x_677 = x_560;
} else {
 lean_dec_ref(x_560);
 x_677 = lean_box(0);
}
if (lean_is_scalar(x_677)) {
 x_678 = lean_alloc_ctor(1, 1, 0);
} else {
 x_678 = x_677;
}
lean_ctor_set(x_678, 0, x_676);
return x_678;
}
}
}
else
{
uint8_t x_679; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
x_679 = !lean_is_exclusive(x_35);
if (x_679 == 0)
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_680 = lean_ctor_get(x_35, 0);
x_681 = lean_ctor_get(x_35, 1);
x_682 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_680, x_6);
if (lean_obj_tag(x_682) == 0)
{
uint8_t x_683; 
x_683 = !lean_is_exclusive(x_682);
if (x_683 == 0)
{
lean_object* x_684; uint8_t x_685; 
x_684 = lean_ctor_get(x_682, 0);
x_685 = lean_unbox(x_684);
if (x_685 == 0)
{
lean_object* x_686; 
lean_free_object(x_682);
x_686 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_680, x_6);
if (lean_obj_tag(x_686) == 0)
{
uint8_t x_687; 
x_687 = !lean_is_exclusive(x_686);
if (x_687 == 0)
{
lean_object* x_688; uint8_t x_689; 
x_688 = lean_ctor_get(x_686, 0);
x_689 = lean_unbox(x_688);
if (x_689 == 0)
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
lean_free_object(x_686);
lean_dec(x_684);
x_690 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28);
lean_inc_ref(x_681);
lean_inc_ref(x_680);
x_691 = l_Lean_mkApp4(x_690, x_27, x_680, x_24, x_681);
x_692 = lean_unsigned_to_nat(4u);
x_693 = l_Lean_Expr_getBoundedAppFn(x_692, x_2);
lean_inc_ref(x_691);
lean_inc_ref(x_680);
x_694 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_693, x_680, x_691, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_694) == 0)
{
uint8_t x_695; 
x_695 = !lean_is_exclusive(x_694);
if (x_695 == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; uint8_t x_700; 
x_696 = lean_ctor_get(x_694, 0);
x_697 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
x_698 = l_Lean_Expr_replaceFn(x_2, x_697);
x_699 = l_Lean_mkApp3(x_698, x_680, x_691, x_681);
lean_ctor_set(x_35, 1, x_699);
lean_ctor_set(x_35, 0, x_696);
x_700 = lean_unbox(x_688);
lean_dec(x_688);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_700);
lean_ctor_set(x_694, 0, x_35);
return x_694;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; uint8_t x_705; lean_object* x_706; 
x_701 = lean_ctor_get(x_694, 0);
lean_inc(x_701);
lean_dec(x_694);
x_702 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
x_703 = l_Lean_Expr_replaceFn(x_2, x_702);
x_704 = l_Lean_mkApp3(x_703, x_680, x_691, x_681);
lean_ctor_set(x_35, 1, x_704);
lean_ctor_set(x_35, 0, x_701);
x_705 = lean_unbox(x_688);
lean_dec(x_688);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_705);
x_706 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_706, 0, x_35);
return x_706;
}
}
else
{
uint8_t x_707; 
lean_dec_ref(x_691);
lean_dec(x_688);
lean_free_object(x_35);
lean_dec_ref(x_681);
lean_dec_ref(x_680);
lean_dec_ref(x_2);
x_707 = !lean_is_exclusive(x_694);
if (x_707 == 0)
{
return x_694;
}
else
{
lean_object* x_708; lean_object* x_709; 
x_708 = lean_ctor_get(x_694, 0);
lean_inc(x_708);
lean_dec(x_694);
x_709 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_709, 0, x_708);
return x_709;
}
}
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; uint8_t x_713; 
lean_dec(x_688);
lean_dec_ref(x_680);
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
x_710 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30));
x_711 = l_Lean_Expr_replaceFn(x_2, x_710);
x_712 = l_Lean_Expr_app___override(x_711, x_681);
lean_ctor_set(x_35, 1, x_712);
lean_ctor_set(x_35, 0, x_18);
x_713 = lean_unbox(x_684);
lean_dec(x_684);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_713);
lean_ctor_set(x_686, 0, x_35);
return x_686;
}
}
else
{
lean_object* x_714; uint8_t x_715; 
x_714 = lean_ctor_get(x_686, 0);
lean_inc(x_714);
lean_dec(x_686);
x_715 = lean_unbox(x_714);
if (x_715 == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_684);
x_716 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28);
lean_inc_ref(x_681);
lean_inc_ref(x_680);
x_717 = l_Lean_mkApp4(x_716, x_27, x_680, x_24, x_681);
x_718 = lean_unsigned_to_nat(4u);
x_719 = l_Lean_Expr_getBoundedAppFn(x_718, x_2);
lean_inc_ref(x_717);
lean_inc_ref(x_680);
x_720 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_719, x_680, x_717, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_720) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; uint8_t x_726; lean_object* x_727; 
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 x_722 = x_720;
} else {
 lean_dec_ref(x_720);
 x_722 = lean_box(0);
}
x_723 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
x_724 = l_Lean_Expr_replaceFn(x_2, x_723);
x_725 = l_Lean_mkApp3(x_724, x_680, x_717, x_681);
lean_ctor_set(x_35, 1, x_725);
lean_ctor_set(x_35, 0, x_721);
x_726 = lean_unbox(x_714);
lean_dec(x_714);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_726);
if (lean_is_scalar(x_722)) {
 x_727 = lean_alloc_ctor(0, 1, 0);
} else {
 x_727 = x_722;
}
lean_ctor_set(x_727, 0, x_35);
return x_727;
}
else
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
lean_dec_ref(x_717);
lean_dec(x_714);
lean_free_object(x_35);
lean_dec_ref(x_681);
lean_dec_ref(x_680);
lean_dec_ref(x_2);
x_728 = lean_ctor_get(x_720, 0);
lean_inc(x_728);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 x_729 = x_720;
} else {
 lean_dec_ref(x_720);
 x_729 = lean_box(0);
}
if (lean_is_scalar(x_729)) {
 x_730 = lean_alloc_ctor(1, 1, 0);
} else {
 x_730 = x_729;
}
lean_ctor_set(x_730, 0, x_728);
return x_730;
}
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; uint8_t x_734; lean_object* x_735; 
lean_dec(x_714);
lean_dec_ref(x_680);
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
x_731 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30));
x_732 = l_Lean_Expr_replaceFn(x_2, x_731);
x_733 = l_Lean_Expr_app___override(x_732, x_681);
lean_ctor_set(x_35, 1, x_733);
lean_ctor_set(x_35, 0, x_18);
x_734 = lean_unbox(x_684);
lean_dec(x_684);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_734);
x_735 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_735, 0, x_35);
return x_735;
}
}
}
else
{
uint8_t x_736; 
lean_dec(x_684);
lean_free_object(x_35);
lean_dec_ref(x_681);
lean_dec_ref(x_680);
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
x_736 = !lean_is_exclusive(x_686);
if (x_736 == 0)
{
return x_686;
}
else
{
lean_object* x_737; lean_object* x_738; 
x_737 = lean_ctor_get(x_686, 0);
lean_inc(x_737);
lean_dec(x_686);
x_738 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_738, 0, x_737);
return x_738;
}
}
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; 
lean_dec(x_684);
lean_dec_ref(x_680);
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
x_739 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__32));
x_740 = l_Lean_Expr_replaceFn(x_2, x_739);
x_741 = l_Lean_Expr_app___override(x_740, x_681);
lean_ctor_set(x_35, 1, x_741);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_1);
lean_ctor_set(x_682, 0, x_35);
return x_682;
}
}
else
{
lean_object* x_742; uint8_t x_743; 
x_742 = lean_ctor_get(x_682, 0);
lean_inc(x_742);
lean_dec(x_682);
x_743 = lean_unbox(x_742);
if (x_743 == 0)
{
lean_object* x_744; 
x_744 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_680, x_6);
if (lean_obj_tag(x_744) == 0)
{
lean_object* x_745; lean_object* x_746; uint8_t x_747; 
x_745 = lean_ctor_get(x_744, 0);
lean_inc(x_745);
if (lean_is_exclusive(x_744)) {
 lean_ctor_release(x_744, 0);
 x_746 = x_744;
} else {
 lean_dec_ref(x_744);
 x_746 = lean_box(0);
}
x_747 = lean_unbox(x_745);
if (x_747 == 0)
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
lean_dec(x_746);
lean_dec(x_742);
x_748 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28);
lean_inc_ref(x_681);
lean_inc_ref(x_680);
x_749 = l_Lean_mkApp4(x_748, x_27, x_680, x_24, x_681);
x_750 = lean_unsigned_to_nat(4u);
x_751 = l_Lean_Expr_getBoundedAppFn(x_750, x_2);
lean_inc_ref(x_749);
lean_inc_ref(x_680);
x_752 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_751, x_680, x_749, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_752) == 0)
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; uint8_t x_758; lean_object* x_759; 
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
if (lean_is_exclusive(x_752)) {
 lean_ctor_release(x_752, 0);
 x_754 = x_752;
} else {
 lean_dec_ref(x_752);
 x_754 = lean_box(0);
}
x_755 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
x_756 = l_Lean_Expr_replaceFn(x_2, x_755);
x_757 = l_Lean_mkApp3(x_756, x_680, x_749, x_681);
lean_ctor_set(x_35, 1, x_757);
lean_ctor_set(x_35, 0, x_753);
x_758 = lean_unbox(x_745);
lean_dec(x_745);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_758);
if (lean_is_scalar(x_754)) {
 x_759 = lean_alloc_ctor(0, 1, 0);
} else {
 x_759 = x_754;
}
lean_ctor_set(x_759, 0, x_35);
return x_759;
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; 
lean_dec_ref(x_749);
lean_dec(x_745);
lean_free_object(x_35);
lean_dec_ref(x_681);
lean_dec_ref(x_680);
lean_dec_ref(x_2);
x_760 = lean_ctor_get(x_752, 0);
lean_inc(x_760);
if (lean_is_exclusive(x_752)) {
 lean_ctor_release(x_752, 0);
 x_761 = x_752;
} else {
 lean_dec_ref(x_752);
 x_761 = lean_box(0);
}
if (lean_is_scalar(x_761)) {
 x_762 = lean_alloc_ctor(1, 1, 0);
} else {
 x_762 = x_761;
}
lean_ctor_set(x_762, 0, x_760);
return x_762;
}
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; uint8_t x_766; lean_object* x_767; 
lean_dec(x_745);
lean_dec_ref(x_680);
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
x_763 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30));
x_764 = l_Lean_Expr_replaceFn(x_2, x_763);
x_765 = l_Lean_Expr_app___override(x_764, x_681);
lean_ctor_set(x_35, 1, x_765);
lean_ctor_set(x_35, 0, x_18);
x_766 = lean_unbox(x_742);
lean_dec(x_742);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_766);
if (lean_is_scalar(x_746)) {
 x_767 = lean_alloc_ctor(0, 1, 0);
} else {
 x_767 = x_746;
}
lean_ctor_set(x_767, 0, x_35);
return x_767;
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
lean_dec(x_742);
lean_free_object(x_35);
lean_dec_ref(x_681);
lean_dec_ref(x_680);
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
x_768 = lean_ctor_get(x_744, 0);
lean_inc(x_768);
if (lean_is_exclusive(x_744)) {
 lean_ctor_release(x_744, 0);
 x_769 = x_744;
} else {
 lean_dec_ref(x_744);
 x_769 = lean_box(0);
}
if (lean_is_scalar(x_769)) {
 x_770 = lean_alloc_ctor(1, 1, 0);
} else {
 x_770 = x_769;
}
lean_ctor_set(x_770, 0, x_768);
return x_770;
}
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
lean_dec(x_742);
lean_dec_ref(x_680);
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
x_771 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__32));
x_772 = l_Lean_Expr_replaceFn(x_2, x_771);
x_773 = l_Lean_Expr_app___override(x_772, x_681);
lean_ctor_set(x_35, 1, x_773);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_1);
x_774 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_774, 0, x_35);
return x_774;
}
}
}
else
{
uint8_t x_775; 
lean_free_object(x_35);
lean_dec_ref(x_681);
lean_dec_ref(x_680);
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
x_775 = !lean_is_exclusive(x_682);
if (x_775 == 0)
{
return x_682;
}
else
{
lean_object* x_776; lean_object* x_777; 
x_776 = lean_ctor_get(x_682, 0);
lean_inc(x_776);
lean_dec(x_682);
x_777 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_777, 0, x_776);
return x_777;
}
}
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_778 = lean_ctor_get(x_35, 0);
x_779 = lean_ctor_get(x_35, 1);
lean_inc(x_779);
lean_inc(x_778);
lean_dec(x_35);
x_780 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_778, x_6);
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_781; lean_object* x_782; uint8_t x_783; 
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 x_782 = x_780;
} else {
 lean_dec_ref(x_780);
 x_782 = lean_box(0);
}
x_783 = lean_unbox(x_781);
if (x_783 == 0)
{
lean_object* x_784; 
lean_dec(x_782);
x_784 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_778, x_6);
if (lean_obj_tag(x_784) == 0)
{
lean_object* x_785; lean_object* x_786; uint8_t x_787; 
x_785 = lean_ctor_get(x_784, 0);
lean_inc(x_785);
if (lean_is_exclusive(x_784)) {
 lean_ctor_release(x_784, 0);
 x_786 = x_784;
} else {
 lean_dec_ref(x_784);
 x_786 = lean_box(0);
}
x_787 = lean_unbox(x_785);
if (x_787 == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; 
lean_dec(x_786);
lean_dec(x_781);
x_788 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28);
lean_inc_ref(x_779);
lean_inc_ref(x_778);
x_789 = l_Lean_mkApp4(x_788, x_27, x_778, x_24, x_779);
x_790 = lean_unsigned_to_nat(4u);
x_791 = l_Lean_Expr_getBoundedAppFn(x_790, x_2);
lean_inc_ref(x_789);
lean_inc_ref(x_778);
x_792 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_791, x_778, x_789, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_792) == 0)
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; uint8_t x_799; lean_object* x_800; 
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
if (lean_is_exclusive(x_792)) {
 lean_ctor_release(x_792, 0);
 x_794 = x_792;
} else {
 lean_dec_ref(x_792);
 x_794 = lean_box(0);
}
x_795 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
x_796 = l_Lean_Expr_replaceFn(x_2, x_795);
x_797 = l_Lean_mkApp3(x_796, x_778, x_789, x_779);
x_798 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_798, 0, x_793);
lean_ctor_set(x_798, 1, x_797);
x_799 = lean_unbox(x_785);
lean_dec(x_785);
lean_ctor_set_uint8(x_798, sizeof(void*)*2, x_799);
if (lean_is_scalar(x_794)) {
 x_800 = lean_alloc_ctor(0, 1, 0);
} else {
 x_800 = x_794;
}
lean_ctor_set(x_800, 0, x_798);
return x_800;
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; 
lean_dec_ref(x_789);
lean_dec(x_785);
lean_dec_ref(x_779);
lean_dec_ref(x_778);
lean_dec_ref(x_2);
x_801 = lean_ctor_get(x_792, 0);
lean_inc(x_801);
if (lean_is_exclusive(x_792)) {
 lean_ctor_release(x_792, 0);
 x_802 = x_792;
} else {
 lean_dec_ref(x_792);
 x_802 = lean_box(0);
}
if (lean_is_scalar(x_802)) {
 x_803 = lean_alloc_ctor(1, 1, 0);
} else {
 x_803 = x_802;
}
lean_ctor_set(x_803, 0, x_801);
return x_803;
}
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; uint8_t x_808; lean_object* x_809; 
lean_dec(x_785);
lean_dec_ref(x_778);
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
x_804 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30));
x_805 = l_Lean_Expr_replaceFn(x_2, x_804);
x_806 = l_Lean_Expr_app___override(x_805, x_779);
x_807 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_807, 0, x_18);
lean_ctor_set(x_807, 1, x_806);
x_808 = lean_unbox(x_781);
lean_dec(x_781);
lean_ctor_set_uint8(x_807, sizeof(void*)*2, x_808);
if (lean_is_scalar(x_786)) {
 x_809 = lean_alloc_ctor(0, 1, 0);
} else {
 x_809 = x_786;
}
lean_ctor_set(x_809, 0, x_807);
return x_809;
}
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; 
lean_dec(x_781);
lean_dec_ref(x_779);
lean_dec_ref(x_778);
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
x_810 = lean_ctor_get(x_784, 0);
lean_inc(x_810);
if (lean_is_exclusive(x_784)) {
 lean_ctor_release(x_784, 0);
 x_811 = x_784;
} else {
 lean_dec_ref(x_784);
 x_811 = lean_box(0);
}
if (lean_is_scalar(x_811)) {
 x_812 = lean_alloc_ctor(1, 1, 0);
} else {
 x_812 = x_811;
}
lean_ctor_set(x_812, 0, x_810);
return x_812;
}
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
lean_dec(x_781);
lean_dec_ref(x_778);
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
x_813 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__32));
x_814 = l_Lean_Expr_replaceFn(x_2, x_813);
x_815 = l_Lean_Expr_app___override(x_814, x_779);
x_816 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_816, 0, x_21);
lean_ctor_set(x_816, 1, x_815);
lean_ctor_set_uint8(x_816, sizeof(void*)*2, x_1);
if (lean_is_scalar(x_782)) {
 x_817 = lean_alloc_ctor(0, 1, 0);
} else {
 x_817 = x_782;
}
lean_ctor_set(x_817, 0, x_816);
return x_817;
}
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; 
lean_dec_ref(x_779);
lean_dec_ref(x_778);
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
x_818 = lean_ctor_get(x_780, 0);
lean_inc(x_818);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 x_819 = x_780;
} else {
 lean_dec_ref(x_780);
 x_819 = lean_box(0);
}
if (lean_is_scalar(x_819)) {
 x_820 = lean_alloc_ctor(1, 1, 0);
} else {
 x_820 = x_819;
}
lean_ctor_set(x_820, 0, x_818);
return x_820;
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
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15);
x_2 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24);
x_2 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_3 = lean_array_push(x_2, x_1);
return x_3;
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
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_unbox(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_unbox(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_38);
x_43 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_24);
lean_inc_ref(x_27);
x_44 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_43, x_27, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_46 = lean_sym_simp(x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_dec(x_41);
lean_free_object(x_35);
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
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_ctor_set_uint8(x_48, 0, x_33);
return x_46;
}
else
{
lean_object* x_50; 
lean_dec(x_48);
x_50 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_50, 0, x_33);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
}
else
{
uint8_t x_51; 
lean_free_object(x_46);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
x_54 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_52, x_6);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_unbox(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_41);
x_57 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_52, x_6);
lean_dec_ref(x_52);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_dec(x_55);
lean_free_object(x_48);
lean_dec_ref(x_53);
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
lean_ctor_set_uint8(x_35, 0, x_33);
lean_ctor_set(x_57, 0, x_35);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_free_object(x_57);
lean_free_object(x_35);
x_61 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
lean_inc_ref(x_27);
x_62 = l_Lean_mkApp3(x_61, x_27, x_24, x_53);
x_63 = l_Lean_Meta_Sym_shareCommon___redArg(x_62, x_7);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_68 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_69 = 0;
x_70 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_71 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_64);
lean_inc(x_66);
lean_inc_ref(x_27);
x_72 = l_Lean_mkApp4(x_70, x_27, x_66, x_64, x_71);
x_73 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_74 = lean_array_push(x_73, x_72);
x_75 = lean_unbox(x_55);
x_76 = lean_unbox(x_55);
x_77 = l_Lean_Expr_betaRev(x_21, x_74, x_75, x_76);
lean_dec_ref(x_74);
lean_inc(x_66);
x_78 = l_Lean_mkLambda(x_68, x_69, x_66, x_77);
x_79 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_78, x_7);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
lean_inc(x_66);
x_81 = l_Lean_mkNot(x_66);
x_82 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12);
lean_inc(x_64);
lean_inc(x_66);
x_83 = l_Lean_mkApp4(x_82, x_27, x_66, x_64, x_71);
x_84 = lean_array_push(x_73, x_83);
x_85 = lean_unbox(x_55);
x_86 = lean_unbox(x_55);
x_87 = l_Lean_Expr_betaRev(x_18, x_84, x_85, x_86);
lean_dec_ref(x_84);
x_88 = l_Lean_mkLambda(x_68, x_69, x_81, x_87);
x_89 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_88, x_7);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = lean_unsigned_to_nat(4u);
x_92 = l_Lean_Expr_getBoundedAppFn(x_91, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_90);
lean_inc(x_80);
lean_inc(x_66);
x_93 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_92, x_66, x_67, x_80, x_90, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_95 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16);
x_96 = lean_unbox(x_55);
x_97 = lean_unbox(x_55);
lean_inc(x_90);
x_98 = l_Lean_Expr_betaRev(x_90, x_95, x_96, x_97);
x_99 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_98, x_7);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_102 = l_Lean_Expr_replaceFn(x_2, x_101);
x_103 = l_Lean_mkApp3(x_102, x_66, x_67, x_64);
x_104 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_105 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_106 = l_Lean_mkConst(x_104, x_105);
x_107 = l_Lean_mkApp3(x_106, x_30, x_80, x_90);
lean_inc(x_100);
x_108 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_94, x_103, x_100, x_107, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_108, 0);
lean_ctor_set(x_48, 1, x_110);
lean_ctor_set(x_48, 0, x_100);
x_111 = lean_unbox(x_55);
lean_dec(x_55);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_111);
lean_ctor_set(x_108, 0, x_48);
return x_108;
}
else
{
lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_108, 0);
lean_inc(x_112);
lean_dec(x_108);
lean_ctor_set(x_48, 1, x_112);
lean_ctor_set(x_48, 0, x_100);
x_113 = lean_unbox(x_55);
lean_dec(x_55);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_113);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_48);
return x_114;
}
}
else
{
uint8_t x_115; 
lean_dec(x_100);
lean_dec(x_55);
lean_free_object(x_48);
x_115 = !lean_is_exclusive(x_108);
if (x_115 == 0)
{
return x_108;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_108, 0);
lean_inc(x_116);
lean_dec(x_108);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_94);
lean_dec(x_90);
lean_dec(x_80);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_55);
lean_free_object(x_48);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_118 = !lean_is_exclusive(x_99);
if (x_118 == 0)
{
return x_99;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_99, 0);
lean_inc(x_119);
lean_dec(x_99);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_90);
lean_dec(x_80);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_55);
lean_free_object(x_48);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_121 = !lean_is_exclusive(x_93);
if (x_121 == 0)
{
return x_93;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_93, 0);
lean_inc(x_122);
lean_dec(x_93);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_80);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_55);
lean_free_object(x_48);
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
x_124 = !lean_is_exclusive(x_89);
if (x_124 == 0)
{
return x_89;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_89, 0);
lean_inc(x_125);
lean_dec(x_89);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_55);
lean_free_object(x_48);
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
x_127 = !lean_is_exclusive(x_79);
if (x_127 == 0)
{
return x_79;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_79, 0);
lean_inc(x_128);
lean_dec(x_79);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_64);
lean_dec(x_55);
lean_free_object(x_48);
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
x_130 = !lean_is_exclusive(x_65);
if (x_130 == 0)
{
return x_65;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_65, 0);
lean_inc(x_131);
lean_dec(x_65);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_55);
lean_free_object(x_48);
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
x_133 = !lean_is_exclusive(x_63);
if (x_133 == 0)
{
return x_63;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_63, 0);
lean_inc(x_134);
lean_dec(x_63);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
}
else
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_57, 0);
lean_inc(x_136);
lean_dec(x_57);
x_137 = lean_unbox(x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_55);
lean_free_object(x_48);
lean_dec_ref(x_53);
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
lean_ctor_set_uint8(x_35, 0, x_33);
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_35);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_free_object(x_35);
x_139 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
lean_inc_ref(x_27);
x_140 = l_Lean_mkApp3(x_139, x_27, x_24, x_53);
x_141 = l_Lean_Meta_Sym_shareCommon___redArg(x_140, x_7);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec_ref(x_141);
x_143 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
x_145 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_146 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_147 = 0;
x_148 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_149 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_142);
lean_inc(x_144);
lean_inc_ref(x_27);
x_150 = l_Lean_mkApp4(x_148, x_27, x_144, x_142, x_149);
x_151 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_152 = lean_array_push(x_151, x_150);
x_153 = lean_unbox(x_55);
x_154 = lean_unbox(x_55);
x_155 = l_Lean_Expr_betaRev(x_21, x_152, x_153, x_154);
lean_dec_ref(x_152);
lean_inc(x_144);
x_156 = l_Lean_mkLambda(x_146, x_147, x_144, x_155);
x_157 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_156, x_7);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec_ref(x_157);
lean_inc(x_144);
x_159 = l_Lean_mkNot(x_144);
x_160 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12);
lean_inc(x_142);
lean_inc(x_144);
x_161 = l_Lean_mkApp4(x_160, x_27, x_144, x_142, x_149);
x_162 = lean_array_push(x_151, x_161);
x_163 = lean_unbox(x_55);
x_164 = lean_unbox(x_55);
x_165 = l_Lean_Expr_betaRev(x_18, x_162, x_163, x_164);
lean_dec_ref(x_162);
x_166 = l_Lean_mkLambda(x_146, x_147, x_159, x_165);
x_167 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_166, x_7);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec_ref(x_167);
x_169 = lean_unsigned_to_nat(4u);
x_170 = l_Lean_Expr_getBoundedAppFn(x_169, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_168);
lean_inc(x_158);
lean_inc(x_144);
x_171 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_170, x_144, x_145, x_158, x_168, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec_ref(x_171);
x_173 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16);
x_174 = lean_unbox(x_55);
x_175 = lean_unbox(x_55);
lean_inc(x_168);
x_176 = l_Lean_Expr_betaRev(x_168, x_173, x_174, x_175);
x_177 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_176, x_7);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_180 = l_Lean_Expr_replaceFn(x_2, x_179);
x_181 = l_Lean_mkApp3(x_180, x_144, x_145, x_142);
x_182 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_183 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_184 = l_Lean_mkConst(x_182, x_183);
x_185 = l_Lean_mkApp3(x_184, x_30, x_158, x_168);
lean_inc(x_178);
x_186 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_172, x_181, x_178, x_185, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 x_188 = x_186;
} else {
 lean_dec_ref(x_186);
 x_188 = lean_box(0);
}
lean_ctor_set(x_48, 1, x_187);
lean_ctor_set(x_48, 0, x_178);
x_189 = lean_unbox(x_55);
lean_dec(x_55);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_189);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(0, 1, 0);
} else {
 x_190 = x_188;
}
lean_ctor_set(x_190, 0, x_48);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_178);
lean_dec(x_55);
lean_free_object(x_48);
x_191 = lean_ctor_get(x_186, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 x_192 = x_186;
} else {
 lean_dec_ref(x_186);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_191);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_172);
lean_dec(x_168);
lean_dec(x_158);
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_55);
lean_free_object(x_48);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_194 = lean_ctor_get(x_177, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 x_195 = x_177;
} else {
 lean_dec_ref(x_177);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 1, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_194);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_168);
lean_dec(x_158);
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_55);
lean_free_object(x_48);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_197 = lean_ctor_get(x_171, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_198 = x_171;
} else {
 lean_dec_ref(x_171);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 1, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_197);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_158);
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_55);
lean_free_object(x_48);
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
x_200 = lean_ctor_get(x_167, 0);
lean_inc(x_200);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_201 = x_167;
} else {
 lean_dec_ref(x_167);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 1, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_200);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_55);
lean_free_object(x_48);
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
x_203 = lean_ctor_get(x_157, 0);
lean_inc(x_203);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 x_204 = x_157;
} else {
 lean_dec_ref(x_157);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 1, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_203);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_142);
lean_dec(x_55);
lean_free_object(x_48);
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
x_206 = lean_ctor_get(x_143, 0);
lean_inc(x_206);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 x_207 = x_143;
} else {
 lean_dec_ref(x_143);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 1, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_55);
lean_free_object(x_48);
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
x_209 = lean_ctor_get(x_141, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_210 = x_141;
} else {
 lean_dec_ref(x_141);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 1, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_209);
return x_211;
}
}
}
}
else
{
uint8_t x_212; 
lean_dec(x_55);
lean_free_object(x_48);
lean_dec_ref(x_53);
lean_free_object(x_35);
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
x_212 = !lean_is_exclusive(x_57);
if (x_212 == 0)
{
return x_57;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_57, 0);
lean_inc(x_213);
lean_dec(x_57);
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_213);
return x_214;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_55);
lean_dec_ref(x_52);
lean_free_object(x_35);
x_215 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20);
lean_inc_ref(x_27);
x_216 = l_Lean_mkApp3(x_215, x_27, x_24, x_53);
x_217 = l_Lean_Meta_Sym_shareCommon___redArg(x_216, x_7);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
lean_dec_ref(x_217);
x_219 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec_ref(x_219);
x_221 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23);
x_222 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_223 = 0;
x_224 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_225 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_218);
lean_inc(x_220);
lean_inc_ref(x_27);
x_226 = l_Lean_mkApp4(x_224, x_27, x_220, x_218, x_225);
x_227 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_228 = lean_array_push(x_227, x_226);
x_229 = lean_unbox(x_41);
x_230 = lean_unbox(x_41);
x_231 = l_Lean_Expr_betaRev(x_21, x_228, x_229, x_230);
lean_dec_ref(x_228);
lean_inc(x_220);
x_232 = l_Lean_mkLambda(x_222, x_223, x_220, x_231);
x_233 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_232, x_7);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
lean_dec_ref(x_233);
lean_inc(x_220);
x_235 = l_Lean_mkNot(x_220);
x_236 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12);
lean_inc(x_218);
lean_inc(x_220);
x_237 = l_Lean_mkApp4(x_236, x_27, x_220, x_218, x_225);
x_238 = lean_array_push(x_227, x_237);
x_239 = lean_unbox(x_41);
x_240 = lean_unbox(x_41);
x_241 = l_Lean_Expr_betaRev(x_18, x_238, x_239, x_240);
lean_dec_ref(x_238);
x_242 = l_Lean_mkLambda(x_222, x_223, x_235, x_241);
x_243 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_242, x_7);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec_ref(x_243);
x_245 = lean_unsigned_to_nat(4u);
x_246 = l_Lean_Expr_getBoundedAppFn(x_245, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_244);
lean_inc(x_234);
lean_inc(x_220);
x_247 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_246, x_220, x_221, x_234, x_244, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
lean_dec_ref(x_247);
x_249 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25);
x_250 = lean_unbox(x_41);
x_251 = lean_unbox(x_41);
lean_inc(x_234);
x_252 = l_Lean_Expr_betaRev(x_234, x_249, x_250, x_251);
x_253 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_252, x_7);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
x_255 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_256 = l_Lean_Expr_replaceFn(x_2, x_255);
x_257 = l_Lean_mkApp3(x_256, x_220, x_221, x_218);
x_258 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_259 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_260 = l_Lean_mkConst(x_258, x_259);
x_261 = l_Lean_mkApp3(x_260, x_30, x_234, x_244);
lean_inc(x_254);
x_262 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_248, x_257, x_254, x_261, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_262) == 0)
{
uint8_t x_263; 
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
lean_object* x_264; uint8_t x_265; 
x_264 = lean_ctor_get(x_262, 0);
lean_ctor_set(x_48, 1, x_264);
lean_ctor_set(x_48, 0, x_254);
x_265 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_265);
lean_ctor_set(x_262, 0, x_48);
return x_262;
}
else
{
lean_object* x_266; uint8_t x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_262, 0);
lean_inc(x_266);
lean_dec(x_262);
lean_ctor_set(x_48, 1, x_266);
lean_ctor_set(x_48, 0, x_254);
x_267 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_267);
x_268 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_268, 0, x_48);
return x_268;
}
}
else
{
uint8_t x_269; 
lean_dec(x_254);
lean_free_object(x_48);
lean_dec(x_41);
x_269 = !lean_is_exclusive(x_262);
if (x_269 == 0)
{
return x_262;
}
else
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_262, 0);
lean_inc(x_270);
lean_dec(x_262);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_270);
return x_271;
}
}
}
else
{
uint8_t x_272; 
lean_dec(x_248);
lean_dec(x_244);
lean_dec(x_234);
lean_dec(x_220);
lean_dec(x_218);
lean_free_object(x_48);
lean_dec(x_41);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_272 = !lean_is_exclusive(x_253);
if (x_272 == 0)
{
return x_253;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_253, 0);
lean_inc(x_273);
lean_dec(x_253);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_273);
return x_274;
}
}
}
else
{
uint8_t x_275; 
lean_dec(x_244);
lean_dec(x_234);
lean_dec(x_220);
lean_dec(x_218);
lean_free_object(x_48);
lean_dec(x_41);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_275 = !lean_is_exclusive(x_247);
if (x_275 == 0)
{
return x_247;
}
else
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_ctor_get(x_247, 0);
lean_inc(x_276);
lean_dec(x_247);
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_276);
return x_277;
}
}
}
else
{
uint8_t x_278; 
lean_dec(x_234);
lean_dec(x_220);
lean_dec(x_218);
lean_free_object(x_48);
lean_dec(x_41);
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
x_278 = !lean_is_exclusive(x_243);
if (x_278 == 0)
{
return x_243;
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_243, 0);
lean_inc(x_279);
lean_dec(x_243);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_279);
return x_280;
}
}
}
else
{
uint8_t x_281; 
lean_dec(x_220);
lean_dec(x_218);
lean_free_object(x_48);
lean_dec(x_41);
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
x_281 = !lean_is_exclusive(x_233);
if (x_281 == 0)
{
return x_233;
}
else
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_233, 0);
lean_inc(x_282);
lean_dec(x_233);
x_283 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_283, 0, x_282);
return x_283;
}
}
}
else
{
uint8_t x_284; 
lean_dec(x_218);
lean_free_object(x_48);
lean_dec(x_41);
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
x_284 = !lean_is_exclusive(x_219);
if (x_284 == 0)
{
return x_219;
}
else
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_219, 0);
lean_inc(x_285);
lean_dec(x_219);
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_285);
return x_286;
}
}
}
else
{
uint8_t x_287; 
lean_free_object(x_48);
lean_dec(x_41);
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
x_287 = !lean_is_exclusive(x_217);
if (x_287 == 0)
{
return x_217;
}
else
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_217, 0);
lean_inc(x_288);
lean_dec(x_217);
x_289 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_289, 0, x_288);
return x_289;
}
}
}
}
else
{
uint8_t x_290; 
lean_free_object(x_48);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_41);
lean_free_object(x_35);
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
x_290 = !lean_is_exclusive(x_54);
if (x_290 == 0)
{
return x_54;
}
else
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_54, 0);
lean_inc(x_291);
lean_dec(x_54);
x_292 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_292, 0, x_291);
return x_292;
}
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_48, 0);
x_294 = lean_ctor_get(x_48, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_48);
x_295 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_293, x_6);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; uint8_t x_297; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
lean_dec_ref(x_295);
x_297 = lean_unbox(x_296);
if (x_297 == 0)
{
lean_object* x_298; 
lean_dec(x_41);
x_298 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_293, x_6);
lean_dec_ref(x_293);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 x_300 = x_298;
} else {
 lean_dec_ref(x_298);
 x_300 = lean_box(0);
}
x_301 = lean_unbox(x_299);
lean_dec(x_299);
if (x_301 == 0)
{
lean_object* x_302; 
lean_dec(x_296);
lean_dec_ref(x_294);
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
lean_ctor_set_uint8(x_35, 0, x_33);
if (lean_is_scalar(x_300)) {
 x_302 = lean_alloc_ctor(0, 1, 0);
} else {
 x_302 = x_300;
}
lean_ctor_set(x_302, 0, x_35);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_300);
lean_free_object(x_35);
x_303 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
lean_inc_ref(x_27);
x_304 = l_Lean_mkApp3(x_303, x_27, x_24, x_294);
x_305 = l_Lean_Meta_Sym_shareCommon___redArg(x_304, x_7);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
lean_dec_ref(x_305);
x_307 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; uint8_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
lean_dec_ref(x_307);
x_309 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_310 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_311 = 0;
x_312 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_313 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_306);
lean_inc(x_308);
lean_inc_ref(x_27);
x_314 = l_Lean_mkApp4(x_312, x_27, x_308, x_306, x_313);
x_315 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_316 = lean_array_push(x_315, x_314);
x_317 = lean_unbox(x_296);
x_318 = lean_unbox(x_296);
x_319 = l_Lean_Expr_betaRev(x_21, x_316, x_317, x_318);
lean_dec_ref(x_316);
lean_inc(x_308);
x_320 = l_Lean_mkLambda(x_310, x_311, x_308, x_319);
x_321 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_320, x_7);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
lean_dec_ref(x_321);
lean_inc(x_308);
x_323 = l_Lean_mkNot(x_308);
x_324 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12);
lean_inc(x_306);
lean_inc(x_308);
x_325 = l_Lean_mkApp4(x_324, x_27, x_308, x_306, x_313);
x_326 = lean_array_push(x_315, x_325);
x_327 = lean_unbox(x_296);
x_328 = lean_unbox(x_296);
x_329 = l_Lean_Expr_betaRev(x_18, x_326, x_327, x_328);
lean_dec_ref(x_326);
x_330 = l_Lean_mkLambda(x_310, x_311, x_323, x_329);
x_331 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_330, x_7);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
lean_dec_ref(x_331);
x_333 = lean_unsigned_to_nat(4u);
x_334 = l_Lean_Expr_getBoundedAppFn(x_333, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_332);
lean_inc(x_322);
lean_inc(x_308);
x_335 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_334, x_308, x_309, x_322, x_332, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; uint8_t x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
lean_dec_ref(x_335);
x_337 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16);
x_338 = lean_unbox(x_296);
x_339 = lean_unbox(x_296);
lean_inc(x_332);
x_340 = l_Lean_Expr_betaRev(x_332, x_337, x_338, x_339);
x_341 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_340, x_7);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
lean_dec_ref(x_341);
x_343 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_344 = l_Lean_Expr_replaceFn(x_2, x_343);
x_345 = l_Lean_mkApp3(x_344, x_308, x_309, x_306);
x_346 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_347 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_348 = l_Lean_mkConst(x_346, x_347);
x_349 = l_Lean_mkApp3(x_348, x_30, x_322, x_332);
lean_inc(x_342);
x_350 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_336, x_345, x_342, x_349, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; lean_object* x_355; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 x_352 = x_350;
} else {
 lean_dec_ref(x_350);
 x_352 = lean_box(0);
}
x_353 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_353, 0, x_342);
lean_ctor_set(x_353, 1, x_351);
x_354 = lean_unbox(x_296);
lean_dec(x_296);
lean_ctor_set_uint8(x_353, sizeof(void*)*2, x_354);
if (lean_is_scalar(x_352)) {
 x_355 = lean_alloc_ctor(0, 1, 0);
} else {
 x_355 = x_352;
}
lean_ctor_set(x_355, 0, x_353);
return x_355;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_342);
lean_dec(x_296);
x_356 = lean_ctor_get(x_350, 0);
lean_inc(x_356);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 x_357 = x_350;
} else {
 lean_dec_ref(x_350);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 1, 0);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_356);
return x_358;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_336);
lean_dec(x_332);
lean_dec(x_322);
lean_dec(x_308);
lean_dec(x_306);
lean_dec(x_296);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_359 = lean_ctor_get(x_341, 0);
lean_inc(x_359);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 x_360 = x_341;
} else {
 lean_dec_ref(x_341);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 1, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_359);
return x_361;
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_332);
lean_dec(x_322);
lean_dec(x_308);
lean_dec(x_306);
lean_dec(x_296);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_362 = lean_ctor_get(x_335, 0);
lean_inc(x_362);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 x_363 = x_335;
} else {
 lean_dec_ref(x_335);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(1, 1, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_362);
return x_364;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_322);
lean_dec(x_308);
lean_dec(x_306);
lean_dec(x_296);
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
x_365 = lean_ctor_get(x_331, 0);
lean_inc(x_365);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 x_366 = x_331;
} else {
 lean_dec_ref(x_331);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(1, 1, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_365);
return x_367;
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_308);
lean_dec(x_306);
lean_dec(x_296);
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
x_368 = lean_ctor_get(x_321, 0);
lean_inc(x_368);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 x_369 = x_321;
} else {
 lean_dec_ref(x_321);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(1, 1, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_368);
return x_370;
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_306);
lean_dec(x_296);
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
x_371 = lean_ctor_get(x_307, 0);
lean_inc(x_371);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 x_372 = x_307;
} else {
 lean_dec_ref(x_307);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(1, 1, 0);
} else {
 x_373 = x_372;
}
lean_ctor_set(x_373, 0, x_371);
return x_373;
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_296);
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
x_374 = lean_ctor_get(x_305, 0);
lean_inc(x_374);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 x_375 = x_305;
} else {
 lean_dec_ref(x_305);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(1, 1, 0);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_374);
return x_376;
}
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_296);
lean_dec_ref(x_294);
lean_free_object(x_35);
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
x_377 = lean_ctor_get(x_298, 0);
lean_inc(x_377);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 x_378 = x_298;
} else {
 lean_dec_ref(x_298);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(1, 1, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_377);
return x_379;
}
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_296);
lean_dec_ref(x_293);
lean_free_object(x_35);
x_380 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20);
lean_inc_ref(x_27);
x_381 = l_Lean_mkApp3(x_380, x_27, x_24, x_294);
x_382 = l_Lean_Meta_Sym_shareCommon___redArg(x_381, x_7);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
lean_dec_ref(x_382);
x_384 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; uint8_t x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
lean_dec_ref(x_384);
x_386 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23);
x_387 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_388 = 0;
x_389 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_390 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_383);
lean_inc(x_385);
lean_inc_ref(x_27);
x_391 = l_Lean_mkApp4(x_389, x_27, x_385, x_383, x_390);
x_392 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_393 = lean_array_push(x_392, x_391);
x_394 = lean_unbox(x_41);
x_395 = lean_unbox(x_41);
x_396 = l_Lean_Expr_betaRev(x_21, x_393, x_394, x_395);
lean_dec_ref(x_393);
lean_inc(x_385);
x_397 = l_Lean_mkLambda(x_387, x_388, x_385, x_396);
x_398 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_397, x_7);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
lean_dec_ref(x_398);
lean_inc(x_385);
x_400 = l_Lean_mkNot(x_385);
x_401 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12);
lean_inc(x_383);
lean_inc(x_385);
x_402 = l_Lean_mkApp4(x_401, x_27, x_385, x_383, x_390);
x_403 = lean_array_push(x_392, x_402);
x_404 = lean_unbox(x_41);
x_405 = lean_unbox(x_41);
x_406 = l_Lean_Expr_betaRev(x_18, x_403, x_404, x_405);
lean_dec_ref(x_403);
x_407 = l_Lean_mkLambda(x_387, x_388, x_400, x_406);
x_408 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_407, x_7);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
lean_dec_ref(x_408);
x_410 = lean_unsigned_to_nat(4u);
x_411 = l_Lean_Expr_getBoundedAppFn(x_410, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_409);
lean_inc(x_399);
lean_inc(x_385);
x_412 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_411, x_385, x_386, x_399, x_409, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; uint8_t x_415; uint8_t x_416; lean_object* x_417; lean_object* x_418; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
lean_dec_ref(x_412);
x_414 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25);
x_415 = lean_unbox(x_41);
x_416 = lean_unbox(x_41);
lean_inc(x_399);
x_417 = l_Lean_Expr_betaRev(x_399, x_414, x_415, x_416);
x_418 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_417, x_7);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
lean_dec_ref(x_418);
x_420 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_421 = l_Lean_Expr_replaceFn(x_2, x_420);
x_422 = l_Lean_mkApp3(x_421, x_385, x_386, x_383);
x_423 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_424 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_425 = l_Lean_mkConst(x_423, x_424);
x_426 = l_Lean_mkApp3(x_425, x_30, x_399, x_409);
lean_inc(x_419);
x_427 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_413, x_422, x_419, x_426, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; lean_object* x_432; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 x_429 = x_427;
} else {
 lean_dec_ref(x_427);
 x_429 = lean_box(0);
}
x_430 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_430, 0, x_419);
lean_ctor_set(x_430, 1, x_428);
x_431 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_430, sizeof(void*)*2, x_431);
if (lean_is_scalar(x_429)) {
 x_432 = lean_alloc_ctor(0, 1, 0);
} else {
 x_432 = x_429;
}
lean_ctor_set(x_432, 0, x_430);
return x_432;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_419);
lean_dec(x_41);
x_433 = lean_ctor_get(x_427, 0);
lean_inc(x_433);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 x_434 = x_427;
} else {
 lean_dec_ref(x_427);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(1, 1, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_433);
return x_435;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec(x_413);
lean_dec(x_409);
lean_dec(x_399);
lean_dec(x_385);
lean_dec(x_383);
lean_dec(x_41);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_436 = lean_ctor_get(x_418, 0);
lean_inc(x_436);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 x_437 = x_418;
} else {
 lean_dec_ref(x_418);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(1, 1, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_436);
return x_438;
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_409);
lean_dec(x_399);
lean_dec(x_385);
lean_dec(x_383);
lean_dec(x_41);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_439 = lean_ctor_get(x_412, 0);
lean_inc(x_439);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 x_440 = x_412;
} else {
 lean_dec_ref(x_412);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 1, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_439);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_399);
lean_dec(x_385);
lean_dec(x_383);
lean_dec(x_41);
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
x_442 = lean_ctor_get(x_408, 0);
lean_inc(x_442);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_443 = x_408;
} else {
 lean_dec_ref(x_408);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(1, 1, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_442);
return x_444;
}
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_385);
lean_dec(x_383);
lean_dec(x_41);
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
x_445 = lean_ctor_get(x_398, 0);
lean_inc(x_445);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 x_446 = x_398;
} else {
 lean_dec_ref(x_398);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(1, 1, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_445);
return x_447;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_383);
lean_dec(x_41);
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
x_448 = lean_ctor_get(x_384, 0);
lean_inc(x_448);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 x_449 = x_384;
} else {
 lean_dec_ref(x_384);
 x_449 = lean_box(0);
}
if (lean_is_scalar(x_449)) {
 x_450 = lean_alloc_ctor(1, 1, 0);
} else {
 x_450 = x_449;
}
lean_ctor_set(x_450, 0, x_448);
return x_450;
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_41);
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
x_451 = lean_ctor_get(x_382, 0);
lean_inc(x_451);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 x_452 = x_382;
} else {
 lean_dec_ref(x_382);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 1, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_451);
return x_453;
}
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec_ref(x_294);
lean_dec_ref(x_293);
lean_dec(x_41);
lean_free_object(x_35);
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
x_454 = lean_ctor_get(x_295, 0);
lean_inc(x_454);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_455 = x_295;
} else {
 lean_dec_ref(x_295);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(1, 1, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_454);
return x_456;
}
}
}
}
else
{
lean_object* x_457; 
x_457 = lean_ctor_get(x_46, 0);
lean_inc(x_457);
lean_dec(x_46);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_41);
lean_free_object(x_35);
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
if (lean_is_exclusive(x_457)) {
 x_458 = x_457;
} else {
 lean_dec_ref(x_457);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(0, 0, 1);
} else {
 x_459 = x_458;
}
lean_ctor_set_uint8(x_459, 0, x_33);
x_460 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_460, 0, x_459);
return x_460;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_461 = lean_ctor_get(x_457, 0);
lean_inc_ref(x_461);
x_462 = lean_ctor_get(x_457, 1);
lean_inc_ref(x_462);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 x_463 = x_457;
} else {
 lean_dec_ref(x_457);
 x_463 = lean_box(0);
}
x_464 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_461, x_6);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; uint8_t x_466; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
lean_dec_ref(x_464);
x_466 = lean_unbox(x_465);
if (x_466 == 0)
{
lean_object* x_467; 
lean_dec(x_41);
x_467 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_461, x_6);
lean_dec_ref(x_461);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; uint8_t x_470; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 x_469 = x_467;
} else {
 lean_dec_ref(x_467);
 x_469 = lean_box(0);
}
x_470 = lean_unbox(x_468);
lean_dec(x_468);
if (x_470 == 0)
{
lean_object* x_471; 
lean_dec(x_465);
lean_dec(x_463);
lean_dec_ref(x_462);
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
lean_ctor_set_uint8(x_35, 0, x_33);
if (lean_is_scalar(x_469)) {
 x_471 = lean_alloc_ctor(0, 1, 0);
} else {
 x_471 = x_469;
}
lean_ctor_set(x_471, 0, x_35);
return x_471;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_469);
lean_free_object(x_35);
x_472 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
lean_inc_ref(x_27);
x_473 = l_Lean_mkApp3(x_472, x_27, x_24, x_462);
x_474 = l_Lean_Meta_Sym_shareCommon___redArg(x_473, x_7);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
lean_dec_ref(x_474);
x_476 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; uint8_t x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
lean_dec_ref(x_476);
x_478 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_479 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_480 = 0;
x_481 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_482 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_475);
lean_inc(x_477);
lean_inc_ref(x_27);
x_483 = l_Lean_mkApp4(x_481, x_27, x_477, x_475, x_482);
x_484 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_485 = lean_array_push(x_484, x_483);
x_486 = lean_unbox(x_465);
x_487 = lean_unbox(x_465);
x_488 = l_Lean_Expr_betaRev(x_21, x_485, x_486, x_487);
lean_dec_ref(x_485);
lean_inc(x_477);
x_489 = l_Lean_mkLambda(x_479, x_480, x_477, x_488);
x_490 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_489, x_7);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; uint8_t x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
lean_dec_ref(x_490);
lean_inc(x_477);
x_492 = l_Lean_mkNot(x_477);
x_493 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12);
lean_inc(x_475);
lean_inc(x_477);
x_494 = l_Lean_mkApp4(x_493, x_27, x_477, x_475, x_482);
x_495 = lean_array_push(x_484, x_494);
x_496 = lean_unbox(x_465);
x_497 = lean_unbox(x_465);
x_498 = l_Lean_Expr_betaRev(x_18, x_495, x_496, x_497);
lean_dec_ref(x_495);
x_499 = l_Lean_mkLambda(x_479, x_480, x_492, x_498);
x_500 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_499, x_7);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
lean_dec_ref(x_500);
x_502 = lean_unsigned_to_nat(4u);
x_503 = l_Lean_Expr_getBoundedAppFn(x_502, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_501);
lean_inc(x_491);
lean_inc(x_477);
x_504 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_503, x_477, x_478, x_491, x_501, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; lean_object* x_506; uint8_t x_507; uint8_t x_508; lean_object* x_509; lean_object* x_510; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
lean_dec_ref(x_504);
x_506 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16);
x_507 = lean_unbox(x_465);
x_508 = lean_unbox(x_465);
lean_inc(x_501);
x_509 = l_Lean_Expr_betaRev(x_501, x_506, x_507, x_508);
x_510 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_509, x_7);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
lean_dec_ref(x_510);
x_512 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_513 = l_Lean_Expr_replaceFn(x_2, x_512);
x_514 = l_Lean_mkApp3(x_513, x_477, x_478, x_475);
x_515 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_516 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_517 = l_Lean_mkConst(x_515, x_516);
x_518 = l_Lean_mkApp3(x_517, x_30, x_491, x_501);
lean_inc(x_511);
x_519 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_505, x_514, x_511, x_518, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; uint8_t x_523; lean_object* x_524; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 x_521 = x_519;
} else {
 lean_dec_ref(x_519);
 x_521 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_522 = lean_alloc_ctor(1, 2, 1);
} else {
 x_522 = x_463;
}
lean_ctor_set(x_522, 0, x_511);
lean_ctor_set(x_522, 1, x_520);
x_523 = lean_unbox(x_465);
lean_dec(x_465);
lean_ctor_set_uint8(x_522, sizeof(void*)*2, x_523);
if (lean_is_scalar(x_521)) {
 x_524 = lean_alloc_ctor(0, 1, 0);
} else {
 x_524 = x_521;
}
lean_ctor_set(x_524, 0, x_522);
return x_524;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_511);
lean_dec(x_465);
lean_dec(x_463);
x_525 = lean_ctor_get(x_519, 0);
lean_inc(x_525);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 x_526 = x_519;
} else {
 lean_dec_ref(x_519);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_526)) {
 x_527 = lean_alloc_ctor(1, 1, 0);
} else {
 x_527 = x_526;
}
lean_ctor_set(x_527, 0, x_525);
return x_527;
}
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_505);
lean_dec(x_501);
lean_dec(x_491);
lean_dec(x_477);
lean_dec(x_475);
lean_dec(x_465);
lean_dec(x_463);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_528 = lean_ctor_get(x_510, 0);
lean_inc(x_528);
if (lean_is_exclusive(x_510)) {
 lean_ctor_release(x_510, 0);
 x_529 = x_510;
} else {
 lean_dec_ref(x_510);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(1, 1, 0);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_528);
return x_530;
}
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_501);
lean_dec(x_491);
lean_dec(x_477);
lean_dec(x_475);
lean_dec(x_465);
lean_dec(x_463);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_531 = lean_ctor_get(x_504, 0);
lean_inc(x_531);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 x_532 = x_504;
} else {
 lean_dec_ref(x_504);
 x_532 = lean_box(0);
}
if (lean_is_scalar(x_532)) {
 x_533 = lean_alloc_ctor(1, 1, 0);
} else {
 x_533 = x_532;
}
lean_ctor_set(x_533, 0, x_531);
return x_533;
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
lean_dec(x_491);
lean_dec(x_477);
lean_dec(x_475);
lean_dec(x_465);
lean_dec(x_463);
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
x_534 = lean_ctor_get(x_500, 0);
lean_inc(x_534);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 x_535 = x_500;
} else {
 lean_dec_ref(x_500);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 1, 0);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_534);
return x_536;
}
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_477);
lean_dec(x_475);
lean_dec(x_465);
lean_dec(x_463);
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
x_537 = lean_ctor_get(x_490, 0);
lean_inc(x_537);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 x_538 = x_490;
} else {
 lean_dec_ref(x_490);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(1, 1, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_537);
return x_539;
}
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_475);
lean_dec(x_465);
lean_dec(x_463);
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
x_540 = lean_ctor_get(x_476, 0);
lean_inc(x_540);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 x_541 = x_476;
} else {
 lean_dec_ref(x_476);
 x_541 = lean_box(0);
}
if (lean_is_scalar(x_541)) {
 x_542 = lean_alloc_ctor(1, 1, 0);
} else {
 x_542 = x_541;
}
lean_ctor_set(x_542, 0, x_540);
return x_542;
}
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_465);
lean_dec(x_463);
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
x_543 = lean_ctor_get(x_474, 0);
lean_inc(x_543);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 x_544 = x_474;
} else {
 lean_dec_ref(x_474);
 x_544 = lean_box(0);
}
if (lean_is_scalar(x_544)) {
 x_545 = lean_alloc_ctor(1, 1, 0);
} else {
 x_545 = x_544;
}
lean_ctor_set(x_545, 0, x_543);
return x_545;
}
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_465);
lean_dec(x_463);
lean_dec_ref(x_462);
lean_free_object(x_35);
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
x_546 = lean_ctor_get(x_467, 0);
lean_inc(x_546);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 x_547 = x_467;
} else {
 lean_dec_ref(x_467);
 x_547 = lean_box(0);
}
if (lean_is_scalar(x_547)) {
 x_548 = lean_alloc_ctor(1, 1, 0);
} else {
 x_548 = x_547;
}
lean_ctor_set(x_548, 0, x_546);
return x_548;
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
lean_dec(x_465);
lean_dec_ref(x_461);
lean_free_object(x_35);
x_549 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20);
lean_inc_ref(x_27);
x_550 = l_Lean_mkApp3(x_549, x_27, x_24, x_462);
x_551 = l_Lean_Meta_Sym_shareCommon___redArg(x_550, x_7);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; 
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
lean_dec_ref(x_551);
x_553 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_553) == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; uint8_t x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; uint8_t x_563; uint8_t x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
lean_dec_ref(x_553);
x_555 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23);
x_556 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_557 = 0;
x_558 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_559 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_552);
lean_inc(x_554);
lean_inc_ref(x_27);
x_560 = l_Lean_mkApp4(x_558, x_27, x_554, x_552, x_559);
x_561 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_562 = lean_array_push(x_561, x_560);
x_563 = lean_unbox(x_41);
x_564 = lean_unbox(x_41);
x_565 = l_Lean_Expr_betaRev(x_21, x_562, x_563, x_564);
lean_dec_ref(x_562);
lean_inc(x_554);
x_566 = l_Lean_mkLambda(x_556, x_557, x_554, x_565);
x_567 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_566, x_7);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; uint8_t x_573; uint8_t x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
lean_dec_ref(x_567);
lean_inc(x_554);
x_569 = l_Lean_mkNot(x_554);
x_570 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12);
lean_inc(x_552);
lean_inc(x_554);
x_571 = l_Lean_mkApp4(x_570, x_27, x_554, x_552, x_559);
x_572 = lean_array_push(x_561, x_571);
x_573 = lean_unbox(x_41);
x_574 = lean_unbox(x_41);
x_575 = l_Lean_Expr_betaRev(x_18, x_572, x_573, x_574);
lean_dec_ref(x_572);
x_576 = l_Lean_mkLambda(x_556, x_557, x_569, x_575);
x_577 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_576, x_7);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
lean_dec_ref(x_577);
x_579 = lean_unsigned_to_nat(4u);
x_580 = l_Lean_Expr_getBoundedAppFn(x_579, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_578);
lean_inc(x_568);
lean_inc(x_554);
x_581 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_580, x_554, x_555, x_568, x_578, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; lean_object* x_583; uint8_t x_584; uint8_t x_585; lean_object* x_586; lean_object* x_587; 
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
lean_dec_ref(x_581);
x_583 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25);
x_584 = lean_unbox(x_41);
x_585 = lean_unbox(x_41);
lean_inc(x_568);
x_586 = l_Lean_Expr_betaRev(x_568, x_583, x_584, x_585);
x_587 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_586, x_7);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
lean_dec_ref(x_587);
x_589 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_590 = l_Lean_Expr_replaceFn(x_2, x_589);
x_591 = l_Lean_mkApp3(x_590, x_554, x_555, x_552);
x_592 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_593 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_594 = l_Lean_mkConst(x_592, x_593);
x_595 = l_Lean_mkApp3(x_594, x_30, x_568, x_578);
lean_inc(x_588);
x_596 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_582, x_591, x_588, x_595, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; uint8_t x_600; lean_object* x_601; 
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 x_598 = x_596;
} else {
 lean_dec_ref(x_596);
 x_598 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_599 = lean_alloc_ctor(1, 2, 1);
} else {
 x_599 = x_463;
}
lean_ctor_set(x_599, 0, x_588);
lean_ctor_set(x_599, 1, x_597);
x_600 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_599, sizeof(void*)*2, x_600);
if (lean_is_scalar(x_598)) {
 x_601 = lean_alloc_ctor(0, 1, 0);
} else {
 x_601 = x_598;
}
lean_ctor_set(x_601, 0, x_599);
return x_601;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec(x_588);
lean_dec(x_463);
lean_dec(x_41);
x_602 = lean_ctor_get(x_596, 0);
lean_inc(x_602);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 x_603 = x_596;
} else {
 lean_dec_ref(x_596);
 x_603 = lean_box(0);
}
if (lean_is_scalar(x_603)) {
 x_604 = lean_alloc_ctor(1, 1, 0);
} else {
 x_604 = x_603;
}
lean_ctor_set(x_604, 0, x_602);
return x_604;
}
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_dec(x_582);
lean_dec(x_578);
lean_dec(x_568);
lean_dec(x_554);
lean_dec(x_552);
lean_dec(x_463);
lean_dec(x_41);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_605 = lean_ctor_get(x_587, 0);
lean_inc(x_605);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 x_606 = x_587;
} else {
 lean_dec_ref(x_587);
 x_606 = lean_box(0);
}
if (lean_is_scalar(x_606)) {
 x_607 = lean_alloc_ctor(1, 1, 0);
} else {
 x_607 = x_606;
}
lean_ctor_set(x_607, 0, x_605);
return x_607;
}
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_578);
lean_dec(x_568);
lean_dec(x_554);
lean_dec(x_552);
lean_dec(x_463);
lean_dec(x_41);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_608 = lean_ctor_get(x_581, 0);
lean_inc(x_608);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 x_609 = x_581;
} else {
 lean_dec_ref(x_581);
 x_609 = lean_box(0);
}
if (lean_is_scalar(x_609)) {
 x_610 = lean_alloc_ctor(1, 1, 0);
} else {
 x_610 = x_609;
}
lean_ctor_set(x_610, 0, x_608);
return x_610;
}
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_568);
lean_dec(x_554);
lean_dec(x_552);
lean_dec(x_463);
lean_dec(x_41);
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
x_611 = lean_ctor_get(x_577, 0);
lean_inc(x_611);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 x_612 = x_577;
} else {
 lean_dec_ref(x_577);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(1, 1, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_611);
return x_613;
}
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
lean_dec(x_554);
lean_dec(x_552);
lean_dec(x_463);
lean_dec(x_41);
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
x_614 = lean_ctor_get(x_567, 0);
lean_inc(x_614);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 x_615 = x_567;
} else {
 lean_dec_ref(x_567);
 x_615 = lean_box(0);
}
if (lean_is_scalar(x_615)) {
 x_616 = lean_alloc_ctor(1, 1, 0);
} else {
 x_616 = x_615;
}
lean_ctor_set(x_616, 0, x_614);
return x_616;
}
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; 
lean_dec(x_552);
lean_dec(x_463);
lean_dec(x_41);
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
x_617 = lean_ctor_get(x_553, 0);
lean_inc(x_617);
if (lean_is_exclusive(x_553)) {
 lean_ctor_release(x_553, 0);
 x_618 = x_553;
} else {
 lean_dec_ref(x_553);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(1, 1, 0);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_617);
return x_619;
}
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
lean_dec(x_463);
lean_dec(x_41);
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
x_620 = lean_ctor_get(x_551, 0);
lean_inc(x_620);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 x_621 = x_551;
} else {
 lean_dec_ref(x_551);
 x_621 = lean_box(0);
}
if (lean_is_scalar(x_621)) {
 x_622 = lean_alloc_ctor(1, 1, 0);
} else {
 x_622 = x_621;
}
lean_ctor_set(x_622, 0, x_620);
return x_622;
}
}
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_463);
lean_dec_ref(x_462);
lean_dec_ref(x_461);
lean_dec(x_41);
lean_free_object(x_35);
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
x_623 = lean_ctor_get(x_464, 0);
lean_inc(x_623);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 x_624 = x_464;
} else {
 lean_dec_ref(x_464);
 x_624 = lean_box(0);
}
if (lean_is_scalar(x_624)) {
 x_625 = lean_alloc_ctor(1, 1, 0);
} else {
 x_625 = x_624;
}
lean_ctor_set(x_625, 0, x_623);
return x_625;
}
}
}
}
else
{
lean_dec(x_41);
lean_free_object(x_35);
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
return x_46;
}
}
else
{
uint8_t x_626; 
lean_dec(x_41);
lean_free_object(x_35);
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
x_626 = !lean_is_exclusive(x_44);
if (x_626 == 0)
{
return x_44;
}
else
{
lean_object* x_627; lean_object* x_628; 
x_627 = lean_ctor_get(x_44, 0);
lean_inc(x_627);
lean_dec(x_44);
x_628 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_628, 0, x_627);
return x_628;
}
}
}
else
{
lean_object* x_629; uint8_t x_630; uint8_t x_631; lean_object* x_632; lean_object* x_633; 
lean_dec(x_41);
lean_free_object(x_35);
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
x_629 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16);
x_630 = lean_unbox(x_38);
x_631 = lean_unbox(x_38);
lean_inc_ref(x_18);
x_632 = l_Lean_Expr_betaRev(x_18, x_629, x_630, x_631);
x_633 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_632, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_633) == 0)
{
uint8_t x_634; 
x_634 = !lean_is_exclusive(x_633);
if (x_634 == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; uint8_t x_641; 
x_635 = lean_ctor_get(x_633, 0);
x_636 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_637 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_638 = l_Lean_mkConst(x_636, x_637);
x_639 = l_Lean_mkApp3(x_638, x_30, x_21, x_18);
x_640 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_640, 0, x_635);
lean_ctor_set(x_640, 1, x_639);
x_641 = lean_unbox(x_38);
lean_dec(x_38);
lean_ctor_set_uint8(x_640, sizeof(void*)*2, x_641);
lean_ctor_set(x_633, 0, x_640);
return x_633;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; uint8_t x_648; lean_object* x_649; 
x_642 = lean_ctor_get(x_633, 0);
lean_inc(x_642);
lean_dec(x_633);
x_643 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_644 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_645 = l_Lean_mkConst(x_643, x_644);
x_646 = l_Lean_mkApp3(x_645, x_30, x_21, x_18);
x_647 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_647, 0, x_642);
lean_ctor_set(x_647, 1, x_646);
x_648 = lean_unbox(x_38);
lean_dec(x_38);
lean_ctor_set_uint8(x_647, sizeof(void*)*2, x_648);
x_649 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_649, 0, x_647);
return x_649;
}
}
else
{
uint8_t x_650; 
lean_dec(x_38);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_650 = !lean_is_exclusive(x_633);
if (x_650 == 0)
{
return x_633;
}
else
{
lean_object* x_651; lean_object* x_652; 
x_651 = lean_ctor_get(x_633, 0);
lean_inc(x_651);
lean_dec(x_633);
x_652 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_652, 0, x_651);
return x_652;
}
}
}
}
else
{
uint8_t x_653; 
lean_dec(x_38);
lean_free_object(x_35);
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
x_653 = !lean_is_exclusive(x_40);
if (x_653 == 0)
{
return x_40;
}
else
{
lean_object* x_654; lean_object* x_655; 
x_654 = lean_ctor_get(x_40, 0);
lean_inc(x_654);
lean_dec(x_40);
x_655 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_655, 0, x_654);
return x_655;
}
}
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
lean_dec(x_38);
lean_free_object(x_35);
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
x_656 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25);
lean_inc_ref(x_21);
x_657 = l_Lean_Expr_betaRev(x_21, x_656, x_1, x_1);
x_658 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_657, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_658) == 0)
{
uint8_t x_659; 
x_659 = !lean_is_exclusive(x_658);
if (x_659 == 0)
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_660 = lean_ctor_get(x_658, 0);
x_661 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_662 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_663 = l_Lean_mkConst(x_661, x_662);
x_664 = l_Lean_mkApp3(x_663, x_30, x_21, x_18);
x_665 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_665, 0, x_660);
lean_ctor_set(x_665, 1, x_664);
lean_ctor_set_uint8(x_665, sizeof(void*)*2, x_1);
lean_ctor_set(x_658, 0, x_665);
return x_658;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_666 = lean_ctor_get(x_658, 0);
lean_inc(x_666);
lean_dec(x_658);
x_667 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_668 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_669 = l_Lean_mkConst(x_667, x_668);
x_670 = l_Lean_mkApp3(x_669, x_30, x_21, x_18);
x_671 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_671, 0, x_666);
lean_ctor_set(x_671, 1, x_670);
lean_ctor_set_uint8(x_671, sizeof(void*)*2, x_1);
x_672 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_672, 0, x_671);
return x_672;
}
}
else
{
uint8_t x_673; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_673 = !lean_is_exclusive(x_658);
if (x_673 == 0)
{
return x_658;
}
else
{
lean_object* x_674; lean_object* x_675; 
x_674 = lean_ctor_get(x_658, 0);
lean_inc(x_674);
lean_dec(x_658);
x_675 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_675, 0, x_674);
return x_675;
}
}
}
}
else
{
uint8_t x_676; 
lean_free_object(x_35);
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
x_676 = !lean_is_exclusive(x_37);
if (x_676 == 0)
{
return x_37;
}
else
{
lean_object* x_677; lean_object* x_678; 
x_677 = lean_ctor_get(x_37, 0);
lean_inc(x_677);
lean_dec(x_37);
x_678 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_678, 0, x_677);
return x_678;
}
}
}
else
{
lean_object* x_679; 
lean_dec(x_35);
x_679 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_679) == 0)
{
lean_object* x_680; uint8_t x_681; 
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
lean_dec_ref(x_679);
x_681 = lean_unbox(x_680);
if (x_681 == 0)
{
lean_object* x_682; 
x_682 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; uint8_t x_684; 
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
lean_dec_ref(x_682);
x_684 = lean_unbox(x_683);
if (x_684 == 0)
{
lean_object* x_685; lean_object* x_686; 
lean_dec(x_680);
x_685 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_24);
lean_inc_ref(x_27);
x_686 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_685, x_27, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; 
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
lean_dec_ref(x_686);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_688 = lean_sym_simp(x_687, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; lean_object* x_690; 
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 x_690 = x_688;
} else {
 lean_dec_ref(x_688);
 x_690 = lean_box(0);
}
if (lean_obj_tag(x_689) == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; 
lean_dec(x_683);
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
if (lean_is_exclusive(x_689)) {
 x_691 = x_689;
} else {
 lean_dec_ref(x_689);
 x_691 = lean_box(0);
}
if (lean_is_scalar(x_691)) {
 x_692 = lean_alloc_ctor(0, 0, 1);
} else {
 x_692 = x_691;
}
lean_ctor_set_uint8(x_692, 0, x_33);
if (lean_is_scalar(x_690)) {
 x_693 = lean_alloc_ctor(0, 1, 0);
} else {
 x_693 = x_690;
}
lean_ctor_set(x_693, 0, x_692);
return x_693;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
lean_dec(x_690);
x_694 = lean_ctor_get(x_689, 0);
lean_inc_ref(x_694);
x_695 = lean_ctor_get(x_689, 1);
lean_inc_ref(x_695);
if (lean_is_exclusive(x_689)) {
 lean_ctor_release(x_689, 0);
 lean_ctor_release(x_689, 1);
 x_696 = x_689;
} else {
 lean_dec_ref(x_689);
 x_696 = lean_box(0);
}
x_697 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_694, x_6);
if (lean_obj_tag(x_697) == 0)
{
lean_object* x_698; uint8_t x_699; 
x_698 = lean_ctor_get(x_697, 0);
lean_inc(x_698);
lean_dec_ref(x_697);
x_699 = lean_unbox(x_698);
if (x_699 == 0)
{
lean_object* x_700; 
lean_dec(x_683);
x_700 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_694, x_6);
lean_dec_ref(x_694);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; lean_object* x_702; uint8_t x_703; 
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
if (lean_is_exclusive(x_700)) {
 lean_ctor_release(x_700, 0);
 x_702 = x_700;
} else {
 lean_dec_ref(x_700);
 x_702 = lean_box(0);
}
x_703 = lean_unbox(x_701);
lean_dec(x_701);
if (x_703 == 0)
{
lean_object* x_704; lean_object* x_705; 
lean_dec(x_698);
lean_dec(x_696);
lean_dec_ref(x_695);
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
x_704 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_704, 0, x_33);
if (lean_is_scalar(x_702)) {
 x_705 = lean_alloc_ctor(0, 1, 0);
} else {
 x_705 = x_702;
}
lean_ctor_set(x_705, 0, x_704);
return x_705;
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; 
lean_dec(x_702);
x_706 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
lean_inc_ref(x_27);
x_707 = l_Lean_mkApp3(x_706, x_27, x_24, x_695);
x_708 = l_Lean_Meta_Sym_shareCommon___redArg(x_707, x_7);
if (lean_obj_tag(x_708) == 0)
{
lean_object* x_709; lean_object* x_710; 
x_709 = lean_ctor_get(x_708, 0);
lean_inc(x_709);
lean_dec_ref(x_708);
x_710 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; uint8_t x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; uint8_t x_720; uint8_t x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_711 = lean_ctor_get(x_710, 0);
lean_inc(x_711);
lean_dec_ref(x_710);
x_712 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_713 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_714 = 0;
x_715 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_716 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_709);
lean_inc(x_711);
lean_inc_ref(x_27);
x_717 = l_Lean_mkApp4(x_715, x_27, x_711, x_709, x_716);
x_718 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_719 = lean_array_push(x_718, x_717);
x_720 = lean_unbox(x_698);
x_721 = lean_unbox(x_698);
x_722 = l_Lean_Expr_betaRev(x_21, x_719, x_720, x_721);
lean_dec_ref(x_719);
lean_inc(x_711);
x_723 = l_Lean_mkLambda(x_713, x_714, x_711, x_722);
x_724 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_723, x_7);
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; uint8_t x_730; uint8_t x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
lean_dec_ref(x_724);
lean_inc(x_711);
x_726 = l_Lean_mkNot(x_711);
x_727 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12);
lean_inc(x_709);
lean_inc(x_711);
x_728 = l_Lean_mkApp4(x_727, x_27, x_711, x_709, x_716);
x_729 = lean_array_push(x_718, x_728);
x_730 = lean_unbox(x_698);
x_731 = lean_unbox(x_698);
x_732 = l_Lean_Expr_betaRev(x_18, x_729, x_730, x_731);
lean_dec_ref(x_729);
x_733 = l_Lean_mkLambda(x_713, x_714, x_726, x_732);
x_734 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_733, x_7);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_735 = lean_ctor_get(x_734, 0);
lean_inc(x_735);
lean_dec_ref(x_734);
x_736 = lean_unsigned_to_nat(4u);
x_737 = l_Lean_Expr_getBoundedAppFn(x_736, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_735);
lean_inc(x_725);
lean_inc(x_711);
x_738 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_737, x_711, x_712, x_725, x_735, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_739; lean_object* x_740; uint8_t x_741; uint8_t x_742; lean_object* x_743; lean_object* x_744; 
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
lean_dec_ref(x_738);
x_740 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16);
x_741 = lean_unbox(x_698);
x_742 = lean_unbox(x_698);
lean_inc(x_735);
x_743 = l_Lean_Expr_betaRev(x_735, x_740, x_741, x_742);
x_744 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_743, x_7);
if (lean_obj_tag(x_744) == 0)
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_745 = lean_ctor_get(x_744, 0);
lean_inc(x_745);
lean_dec_ref(x_744);
x_746 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_747 = l_Lean_Expr_replaceFn(x_2, x_746);
x_748 = l_Lean_mkApp3(x_747, x_711, x_712, x_709);
x_749 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_750 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_751 = l_Lean_mkConst(x_749, x_750);
x_752 = l_Lean_mkApp3(x_751, x_30, x_725, x_735);
lean_inc(x_745);
x_753 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_739, x_748, x_745, x_752, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_753) == 0)
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; uint8_t x_757; lean_object* x_758; 
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 x_755 = x_753;
} else {
 lean_dec_ref(x_753);
 x_755 = lean_box(0);
}
if (lean_is_scalar(x_696)) {
 x_756 = lean_alloc_ctor(1, 2, 1);
} else {
 x_756 = x_696;
}
lean_ctor_set(x_756, 0, x_745);
lean_ctor_set(x_756, 1, x_754);
x_757 = lean_unbox(x_698);
lean_dec(x_698);
lean_ctor_set_uint8(x_756, sizeof(void*)*2, x_757);
if (lean_is_scalar(x_755)) {
 x_758 = lean_alloc_ctor(0, 1, 0);
} else {
 x_758 = x_755;
}
lean_ctor_set(x_758, 0, x_756);
return x_758;
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; 
lean_dec(x_745);
lean_dec(x_698);
lean_dec(x_696);
x_759 = lean_ctor_get(x_753, 0);
lean_inc(x_759);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 x_760 = x_753;
} else {
 lean_dec_ref(x_753);
 x_760 = lean_box(0);
}
if (lean_is_scalar(x_760)) {
 x_761 = lean_alloc_ctor(1, 1, 0);
} else {
 x_761 = x_760;
}
lean_ctor_set(x_761, 0, x_759);
return x_761;
}
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; 
lean_dec(x_739);
lean_dec(x_735);
lean_dec(x_725);
lean_dec(x_711);
lean_dec(x_709);
lean_dec(x_698);
lean_dec(x_696);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_762 = lean_ctor_get(x_744, 0);
lean_inc(x_762);
if (lean_is_exclusive(x_744)) {
 lean_ctor_release(x_744, 0);
 x_763 = x_744;
} else {
 lean_dec_ref(x_744);
 x_763 = lean_box(0);
}
if (lean_is_scalar(x_763)) {
 x_764 = lean_alloc_ctor(1, 1, 0);
} else {
 x_764 = x_763;
}
lean_ctor_set(x_764, 0, x_762);
return x_764;
}
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; 
lean_dec(x_735);
lean_dec(x_725);
lean_dec(x_711);
lean_dec(x_709);
lean_dec(x_698);
lean_dec(x_696);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_765 = lean_ctor_get(x_738, 0);
lean_inc(x_765);
if (lean_is_exclusive(x_738)) {
 lean_ctor_release(x_738, 0);
 x_766 = x_738;
} else {
 lean_dec_ref(x_738);
 x_766 = lean_box(0);
}
if (lean_is_scalar(x_766)) {
 x_767 = lean_alloc_ctor(1, 1, 0);
} else {
 x_767 = x_766;
}
lean_ctor_set(x_767, 0, x_765);
return x_767;
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
lean_dec(x_725);
lean_dec(x_711);
lean_dec(x_709);
lean_dec(x_698);
lean_dec(x_696);
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
x_768 = lean_ctor_get(x_734, 0);
lean_inc(x_768);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 x_769 = x_734;
} else {
 lean_dec_ref(x_734);
 x_769 = lean_box(0);
}
if (lean_is_scalar(x_769)) {
 x_770 = lean_alloc_ctor(1, 1, 0);
} else {
 x_770 = x_769;
}
lean_ctor_set(x_770, 0, x_768);
return x_770;
}
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
lean_dec(x_711);
lean_dec(x_709);
lean_dec(x_698);
lean_dec(x_696);
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
x_771 = lean_ctor_get(x_724, 0);
lean_inc(x_771);
if (lean_is_exclusive(x_724)) {
 lean_ctor_release(x_724, 0);
 x_772 = x_724;
} else {
 lean_dec_ref(x_724);
 x_772 = lean_box(0);
}
if (lean_is_scalar(x_772)) {
 x_773 = lean_alloc_ctor(1, 1, 0);
} else {
 x_773 = x_772;
}
lean_ctor_set(x_773, 0, x_771);
return x_773;
}
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; 
lean_dec(x_709);
lean_dec(x_698);
lean_dec(x_696);
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
x_774 = lean_ctor_get(x_710, 0);
lean_inc(x_774);
if (lean_is_exclusive(x_710)) {
 lean_ctor_release(x_710, 0);
 x_775 = x_710;
} else {
 lean_dec_ref(x_710);
 x_775 = lean_box(0);
}
if (lean_is_scalar(x_775)) {
 x_776 = lean_alloc_ctor(1, 1, 0);
} else {
 x_776 = x_775;
}
lean_ctor_set(x_776, 0, x_774);
return x_776;
}
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; 
lean_dec(x_698);
lean_dec(x_696);
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
x_777 = lean_ctor_get(x_708, 0);
lean_inc(x_777);
if (lean_is_exclusive(x_708)) {
 lean_ctor_release(x_708, 0);
 x_778 = x_708;
} else {
 lean_dec_ref(x_708);
 x_778 = lean_box(0);
}
if (lean_is_scalar(x_778)) {
 x_779 = lean_alloc_ctor(1, 1, 0);
} else {
 x_779 = x_778;
}
lean_ctor_set(x_779, 0, x_777);
return x_779;
}
}
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; 
lean_dec(x_698);
lean_dec(x_696);
lean_dec_ref(x_695);
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
x_780 = lean_ctor_get(x_700, 0);
lean_inc(x_780);
if (lean_is_exclusive(x_700)) {
 lean_ctor_release(x_700, 0);
 x_781 = x_700;
} else {
 lean_dec_ref(x_700);
 x_781 = lean_box(0);
}
if (lean_is_scalar(x_781)) {
 x_782 = lean_alloc_ctor(1, 1, 0);
} else {
 x_782 = x_781;
}
lean_ctor_set(x_782, 0, x_780);
return x_782;
}
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; 
lean_dec(x_698);
lean_dec_ref(x_694);
x_783 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20);
lean_inc_ref(x_27);
x_784 = l_Lean_mkApp3(x_783, x_27, x_24, x_695);
x_785 = l_Lean_Meta_Sym_shareCommon___redArg(x_784, x_7);
if (lean_obj_tag(x_785) == 0)
{
lean_object* x_786; lean_object* x_787; 
x_786 = lean_ctor_get(x_785, 0);
lean_inc(x_786);
lean_dec_ref(x_785);
x_787 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; uint8_t x_797; uint8_t x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_788 = lean_ctor_get(x_787, 0);
lean_inc(x_788);
lean_dec_ref(x_787);
x_789 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23);
x_790 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_791 = 0;
x_792 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_793 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_786);
lean_inc(x_788);
lean_inc_ref(x_27);
x_794 = l_Lean_mkApp4(x_792, x_27, x_788, x_786, x_793);
x_795 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_796 = lean_array_push(x_795, x_794);
x_797 = lean_unbox(x_683);
x_798 = lean_unbox(x_683);
x_799 = l_Lean_Expr_betaRev(x_21, x_796, x_797, x_798);
lean_dec_ref(x_796);
lean_inc(x_788);
x_800 = l_Lean_mkLambda(x_790, x_791, x_788, x_799);
x_801 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_800, x_7);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; uint8_t x_807; uint8_t x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
lean_dec_ref(x_801);
lean_inc(x_788);
x_803 = l_Lean_mkNot(x_788);
x_804 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12);
lean_inc(x_786);
lean_inc(x_788);
x_805 = l_Lean_mkApp4(x_804, x_27, x_788, x_786, x_793);
x_806 = lean_array_push(x_795, x_805);
x_807 = lean_unbox(x_683);
x_808 = lean_unbox(x_683);
x_809 = l_Lean_Expr_betaRev(x_18, x_806, x_807, x_808);
lean_dec_ref(x_806);
x_810 = l_Lean_mkLambda(x_790, x_791, x_803, x_809);
x_811 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_810, x_7);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
lean_dec_ref(x_811);
x_813 = lean_unsigned_to_nat(4u);
x_814 = l_Lean_Expr_getBoundedAppFn(x_813, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_812);
lean_inc(x_802);
lean_inc(x_788);
x_815 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_814, x_788, x_789, x_802, x_812, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; lean_object* x_817; uint8_t x_818; uint8_t x_819; lean_object* x_820; lean_object* x_821; 
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
lean_dec_ref(x_815);
x_817 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25);
x_818 = lean_unbox(x_683);
x_819 = lean_unbox(x_683);
lean_inc(x_802);
x_820 = l_Lean_Expr_betaRev(x_802, x_817, x_818, x_819);
x_821 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_820, x_7);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_822 = lean_ctor_get(x_821, 0);
lean_inc(x_822);
lean_dec_ref(x_821);
x_823 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_824 = l_Lean_Expr_replaceFn(x_2, x_823);
x_825 = l_Lean_mkApp3(x_824, x_788, x_789, x_786);
x_826 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_827 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_828 = l_Lean_mkConst(x_826, x_827);
x_829 = l_Lean_mkApp3(x_828, x_30, x_802, x_812);
lean_inc(x_822);
x_830 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_816, x_825, x_822, x_829, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_830) == 0)
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; uint8_t x_834; lean_object* x_835; 
x_831 = lean_ctor_get(x_830, 0);
lean_inc(x_831);
if (lean_is_exclusive(x_830)) {
 lean_ctor_release(x_830, 0);
 x_832 = x_830;
} else {
 lean_dec_ref(x_830);
 x_832 = lean_box(0);
}
if (lean_is_scalar(x_696)) {
 x_833 = lean_alloc_ctor(1, 2, 1);
} else {
 x_833 = x_696;
}
lean_ctor_set(x_833, 0, x_822);
lean_ctor_set(x_833, 1, x_831);
x_834 = lean_unbox(x_683);
lean_dec(x_683);
lean_ctor_set_uint8(x_833, sizeof(void*)*2, x_834);
if (lean_is_scalar(x_832)) {
 x_835 = lean_alloc_ctor(0, 1, 0);
} else {
 x_835 = x_832;
}
lean_ctor_set(x_835, 0, x_833);
return x_835;
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; 
lean_dec(x_822);
lean_dec(x_696);
lean_dec(x_683);
x_836 = lean_ctor_get(x_830, 0);
lean_inc(x_836);
if (lean_is_exclusive(x_830)) {
 lean_ctor_release(x_830, 0);
 x_837 = x_830;
} else {
 lean_dec_ref(x_830);
 x_837 = lean_box(0);
}
if (lean_is_scalar(x_837)) {
 x_838 = lean_alloc_ctor(1, 1, 0);
} else {
 x_838 = x_837;
}
lean_ctor_set(x_838, 0, x_836);
return x_838;
}
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; 
lean_dec(x_816);
lean_dec(x_812);
lean_dec(x_802);
lean_dec(x_788);
lean_dec(x_786);
lean_dec(x_696);
lean_dec(x_683);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_839 = lean_ctor_get(x_821, 0);
lean_inc(x_839);
if (lean_is_exclusive(x_821)) {
 lean_ctor_release(x_821, 0);
 x_840 = x_821;
} else {
 lean_dec_ref(x_821);
 x_840 = lean_box(0);
}
if (lean_is_scalar(x_840)) {
 x_841 = lean_alloc_ctor(1, 1, 0);
} else {
 x_841 = x_840;
}
lean_ctor_set(x_841, 0, x_839);
return x_841;
}
}
else
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; 
lean_dec(x_812);
lean_dec(x_802);
lean_dec(x_788);
lean_dec(x_786);
lean_dec(x_696);
lean_dec(x_683);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_842 = lean_ctor_get(x_815, 0);
lean_inc(x_842);
if (lean_is_exclusive(x_815)) {
 lean_ctor_release(x_815, 0);
 x_843 = x_815;
} else {
 lean_dec_ref(x_815);
 x_843 = lean_box(0);
}
if (lean_is_scalar(x_843)) {
 x_844 = lean_alloc_ctor(1, 1, 0);
} else {
 x_844 = x_843;
}
lean_ctor_set(x_844, 0, x_842);
return x_844;
}
}
else
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; 
lean_dec(x_802);
lean_dec(x_788);
lean_dec(x_786);
lean_dec(x_696);
lean_dec(x_683);
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
x_845 = lean_ctor_get(x_811, 0);
lean_inc(x_845);
if (lean_is_exclusive(x_811)) {
 lean_ctor_release(x_811, 0);
 x_846 = x_811;
} else {
 lean_dec_ref(x_811);
 x_846 = lean_box(0);
}
if (lean_is_scalar(x_846)) {
 x_847 = lean_alloc_ctor(1, 1, 0);
} else {
 x_847 = x_846;
}
lean_ctor_set(x_847, 0, x_845);
return x_847;
}
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; 
lean_dec(x_788);
lean_dec(x_786);
lean_dec(x_696);
lean_dec(x_683);
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
x_848 = lean_ctor_get(x_801, 0);
lean_inc(x_848);
if (lean_is_exclusive(x_801)) {
 lean_ctor_release(x_801, 0);
 x_849 = x_801;
} else {
 lean_dec_ref(x_801);
 x_849 = lean_box(0);
}
if (lean_is_scalar(x_849)) {
 x_850 = lean_alloc_ctor(1, 1, 0);
} else {
 x_850 = x_849;
}
lean_ctor_set(x_850, 0, x_848);
return x_850;
}
}
else
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; 
lean_dec(x_786);
lean_dec(x_696);
lean_dec(x_683);
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
x_851 = lean_ctor_get(x_787, 0);
lean_inc(x_851);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 x_852 = x_787;
} else {
 lean_dec_ref(x_787);
 x_852 = lean_box(0);
}
if (lean_is_scalar(x_852)) {
 x_853 = lean_alloc_ctor(1, 1, 0);
} else {
 x_853 = x_852;
}
lean_ctor_set(x_853, 0, x_851);
return x_853;
}
}
else
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_696);
lean_dec(x_683);
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
x_854 = lean_ctor_get(x_785, 0);
lean_inc(x_854);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 x_855 = x_785;
} else {
 lean_dec_ref(x_785);
 x_855 = lean_box(0);
}
if (lean_is_scalar(x_855)) {
 x_856 = lean_alloc_ctor(1, 1, 0);
} else {
 x_856 = x_855;
}
lean_ctor_set(x_856, 0, x_854);
return x_856;
}
}
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; 
lean_dec(x_696);
lean_dec_ref(x_695);
lean_dec_ref(x_694);
lean_dec(x_683);
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
x_857 = lean_ctor_get(x_697, 0);
lean_inc(x_857);
if (lean_is_exclusive(x_697)) {
 lean_ctor_release(x_697, 0);
 x_858 = x_697;
} else {
 lean_dec_ref(x_697);
 x_858 = lean_box(0);
}
if (lean_is_scalar(x_858)) {
 x_859 = lean_alloc_ctor(1, 1, 0);
} else {
 x_859 = x_858;
}
lean_ctor_set(x_859, 0, x_857);
return x_859;
}
}
}
else
{
lean_dec(x_683);
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
return x_688;
}
}
else
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; 
lean_dec(x_683);
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
x_860 = lean_ctor_get(x_686, 0);
lean_inc(x_860);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 x_861 = x_686;
} else {
 lean_dec_ref(x_686);
 x_861 = lean_box(0);
}
if (lean_is_scalar(x_861)) {
 x_862 = lean_alloc_ctor(1, 1, 0);
} else {
 x_862 = x_861;
}
lean_ctor_set(x_862, 0, x_860);
return x_862;
}
}
else
{
lean_object* x_863; uint8_t x_864; uint8_t x_865; lean_object* x_866; lean_object* x_867; 
lean_dec(x_683);
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
x_863 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16);
x_864 = lean_unbox(x_680);
x_865 = lean_unbox(x_680);
lean_inc_ref(x_18);
x_866 = l_Lean_Expr_betaRev(x_18, x_863, x_864, x_865);
x_867 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_866, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_867) == 0)
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; uint8_t x_875; lean_object* x_876; 
x_868 = lean_ctor_get(x_867, 0);
lean_inc(x_868);
if (lean_is_exclusive(x_867)) {
 lean_ctor_release(x_867, 0);
 x_869 = x_867;
} else {
 lean_dec_ref(x_867);
 x_869 = lean_box(0);
}
x_870 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_871 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_872 = l_Lean_mkConst(x_870, x_871);
x_873 = l_Lean_mkApp3(x_872, x_30, x_21, x_18);
x_874 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_874, 0, x_868);
lean_ctor_set(x_874, 1, x_873);
x_875 = lean_unbox(x_680);
lean_dec(x_680);
lean_ctor_set_uint8(x_874, sizeof(void*)*2, x_875);
if (lean_is_scalar(x_869)) {
 x_876 = lean_alloc_ctor(0, 1, 0);
} else {
 x_876 = x_869;
}
lean_ctor_set(x_876, 0, x_874);
return x_876;
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; 
lean_dec(x_680);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_877 = lean_ctor_get(x_867, 0);
lean_inc(x_877);
if (lean_is_exclusive(x_867)) {
 lean_ctor_release(x_867, 0);
 x_878 = x_867;
} else {
 lean_dec_ref(x_867);
 x_878 = lean_box(0);
}
if (lean_is_scalar(x_878)) {
 x_879 = lean_alloc_ctor(1, 1, 0);
} else {
 x_879 = x_878;
}
lean_ctor_set(x_879, 0, x_877);
return x_879;
}
}
}
else
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; 
lean_dec(x_680);
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
x_880 = lean_ctor_get(x_682, 0);
lean_inc(x_880);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 x_881 = x_682;
} else {
 lean_dec_ref(x_682);
 x_881 = lean_box(0);
}
if (lean_is_scalar(x_881)) {
 x_882 = lean_alloc_ctor(1, 1, 0);
} else {
 x_882 = x_881;
}
lean_ctor_set(x_882, 0, x_880);
return x_882;
}
}
else
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; 
lean_dec(x_680);
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
x_883 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25);
lean_inc_ref(x_21);
x_884 = l_Lean_Expr_betaRev(x_21, x_883, x_1, x_1);
x_885 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_884, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_885) == 0)
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_886 = lean_ctor_get(x_885, 0);
lean_inc(x_886);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 x_887 = x_885;
} else {
 lean_dec_ref(x_885);
 x_887 = lean_box(0);
}
x_888 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_889 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_890 = l_Lean_mkConst(x_888, x_889);
x_891 = l_Lean_mkApp3(x_890, x_30, x_21, x_18);
x_892 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_892, 0, x_886);
lean_ctor_set(x_892, 1, x_891);
lean_ctor_set_uint8(x_892, sizeof(void*)*2, x_1);
if (lean_is_scalar(x_887)) {
 x_893 = lean_alloc_ctor(0, 1, 0);
} else {
 x_893 = x_887;
}
lean_ctor_set(x_893, 0, x_892);
return x_893;
}
else
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_894 = lean_ctor_get(x_885, 0);
lean_inc(x_894);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 x_895 = x_885;
} else {
 lean_dec_ref(x_885);
 x_895 = lean_box(0);
}
if (lean_is_scalar(x_895)) {
 x_896 = lean_alloc_ctor(1, 1, 0);
} else {
 x_896 = x_895;
}
lean_ctor_set(x_896, 0, x_894);
return x_896;
}
}
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; 
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
x_897 = lean_ctor_get(x_679, 0);
lean_inc(x_897);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 x_898 = x_679;
} else {
 lean_dec_ref(x_679);
 x_898 = lean_box(0);
}
if (lean_is_scalar(x_898)) {
 x_899 = lean_alloc_ctor(1, 1, 0);
} else {
 x_899 = x_898;
}
lean_ctor_set(x_899, 0, x_897);
return x_899;
}
}
}
else
{
uint8_t x_900; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
x_900 = !lean_is_exclusive(x_35);
if (x_900 == 0)
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; 
x_901 = lean_ctor_get(x_35, 0);
x_902 = lean_ctor_get(x_35, 1);
x_903 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_901, x_6);
if (lean_obj_tag(x_903) == 0)
{
lean_object* x_904; uint8_t x_905; 
x_904 = lean_ctor_get(x_903, 0);
lean_inc(x_904);
lean_dec_ref(x_903);
x_905 = lean_unbox(x_904);
if (x_905 == 0)
{
lean_object* x_906; 
x_906 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_901, x_6);
if (lean_obj_tag(x_906) == 0)
{
lean_object* x_907; uint8_t x_908; 
x_907 = lean_ctor_get(x_906, 0);
lean_inc(x_907);
lean_dec_ref(x_906);
x_908 = lean_unbox(x_907);
if (x_908 == 0)
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; 
lean_dec(x_904);
x_909 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28);
lean_inc_ref(x_902);
lean_inc_ref(x_901);
lean_inc_ref(x_27);
x_910 = l_Lean_mkApp4(x_909, x_27, x_901, x_24, x_902);
x_911 = l_Lean_Meta_Sym_shareCommon___redArg(x_902, x_7);
if (lean_obj_tag(x_911) == 0)
{
lean_object* x_912; lean_object* x_913; uint8_t x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; uint8_t x_920; uint8_t x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; 
x_912 = lean_ctor_get(x_911, 0);
lean_inc(x_912);
lean_dec_ref(x_911);
x_913 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_914 = 0;
x_915 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_916 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_912);
lean_inc_ref(x_901);
lean_inc_ref(x_27);
x_917 = l_Lean_mkApp4(x_915, x_27, x_901, x_912, x_916);
x_918 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_919 = lean_array_push(x_918, x_917);
x_920 = lean_unbox(x_907);
x_921 = lean_unbox(x_907);
x_922 = l_Lean_Expr_betaRev(x_21, x_919, x_920, x_921);
lean_dec_ref(x_919);
lean_inc_ref(x_901);
x_923 = l_Lean_mkLambda(x_913, x_914, x_901, x_922);
x_924 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_923, x_7);
if (lean_obj_tag(x_924) == 0)
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; uint8_t x_930; uint8_t x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
x_925 = lean_ctor_get(x_924, 0);
lean_inc(x_925);
lean_dec_ref(x_924);
lean_inc_ref(x_901);
x_926 = l_Lean_mkNot(x_901);
x_927 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12);
lean_inc(x_912);
lean_inc_ref(x_901);
x_928 = l_Lean_mkApp4(x_927, x_27, x_901, x_912, x_916);
x_929 = lean_array_push(x_918, x_928);
x_930 = lean_unbox(x_907);
x_931 = lean_unbox(x_907);
x_932 = l_Lean_Expr_betaRev(x_18, x_929, x_930, x_931);
lean_dec_ref(x_929);
x_933 = l_Lean_mkLambda(x_913, x_914, x_926, x_932);
x_934 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_933, x_7);
if (lean_obj_tag(x_934) == 0)
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_935 = lean_ctor_get(x_934, 0);
lean_inc(x_935);
lean_dec_ref(x_934);
x_936 = lean_unsigned_to_nat(4u);
x_937 = l_Lean_Expr_getBoundedAppFn(x_936, x_2);
lean_inc_ref(x_910);
lean_inc_ref(x_901);
x_938 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_937, x_901, x_910, x_925, x_935, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_938) == 0)
{
uint8_t x_939; 
x_939 = !lean_is_exclusive(x_938);
if (x_939 == 0)
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; uint8_t x_944; 
x_940 = lean_ctor_get(x_938, 0);
x_941 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
x_942 = l_Lean_Expr_replaceFn(x_2, x_941);
x_943 = l_Lean_mkApp3(x_942, x_901, x_910, x_912);
lean_ctor_set(x_35, 1, x_943);
lean_ctor_set(x_35, 0, x_940);
x_944 = lean_unbox(x_907);
lean_dec(x_907);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_944);
lean_ctor_set(x_938, 0, x_35);
return x_938;
}
else
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; uint8_t x_949; lean_object* x_950; 
x_945 = lean_ctor_get(x_938, 0);
lean_inc(x_945);
lean_dec(x_938);
x_946 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
x_947 = l_Lean_Expr_replaceFn(x_2, x_946);
x_948 = l_Lean_mkApp3(x_947, x_901, x_910, x_912);
lean_ctor_set(x_35, 1, x_948);
lean_ctor_set(x_35, 0, x_945);
x_949 = lean_unbox(x_907);
lean_dec(x_907);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_949);
x_950 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_950, 0, x_35);
return x_950;
}
}
else
{
uint8_t x_951; 
lean_dec(x_912);
lean_dec_ref(x_910);
lean_dec(x_907);
lean_free_object(x_35);
lean_dec_ref(x_901);
lean_dec_ref(x_2);
x_951 = !lean_is_exclusive(x_938);
if (x_951 == 0)
{
return x_938;
}
else
{
lean_object* x_952; lean_object* x_953; 
x_952 = lean_ctor_get(x_938, 0);
lean_inc(x_952);
lean_dec(x_938);
x_953 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_953, 0, x_952);
return x_953;
}
}
}
else
{
uint8_t x_954; 
lean_dec(x_925);
lean_dec(x_912);
lean_dec_ref(x_910);
lean_dec(x_907);
lean_free_object(x_35);
lean_dec_ref(x_901);
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
x_954 = !lean_is_exclusive(x_934);
if (x_954 == 0)
{
return x_934;
}
else
{
lean_object* x_955; lean_object* x_956; 
x_955 = lean_ctor_get(x_934, 0);
lean_inc(x_955);
lean_dec(x_934);
x_956 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_956, 0, x_955);
return x_956;
}
}
}
else
{
uint8_t x_957; 
lean_dec(x_912);
lean_dec_ref(x_910);
lean_dec(x_907);
lean_free_object(x_35);
lean_dec_ref(x_901);
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
x_957 = !lean_is_exclusive(x_924);
if (x_957 == 0)
{
return x_924;
}
else
{
lean_object* x_958; lean_object* x_959; 
x_958 = lean_ctor_get(x_924, 0);
lean_inc(x_958);
lean_dec(x_924);
x_959 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_959, 0, x_958);
return x_959;
}
}
}
else
{
uint8_t x_960; 
lean_dec_ref(x_910);
lean_dec(x_907);
lean_free_object(x_35);
lean_dec_ref(x_901);
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
x_960 = !lean_is_exclusive(x_911);
if (x_960 == 0)
{
return x_911;
}
else
{
lean_object* x_961; lean_object* x_962; 
x_961 = lean_ctor_get(x_911, 0);
lean_inc(x_961);
lean_dec(x_911);
x_962 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_962, 0, x_961);
return x_962;
}
}
}
else
{
lean_object* x_963; lean_object* x_964; 
lean_dec(x_907);
lean_dec_ref(x_901);
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
lean_inc_ref(x_902);
x_963 = l_Lean_Meta_mkOfEqFalseCore(x_27, x_902);
x_964 = l_Lean_Meta_Sym_shareCommon___redArg(x_963, x_7);
if (lean_obj_tag(x_964) == 0)
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; uint8_t x_968; uint8_t x_969; lean_object* x_970; lean_object* x_971; 
x_965 = lean_ctor_get(x_964, 0);
lean_inc(x_965);
lean_dec_ref(x_964);
x_966 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_967 = lean_array_push(x_966, x_965);
x_968 = lean_unbox(x_904);
x_969 = lean_unbox(x_904);
x_970 = l_Lean_Expr_betaRev(x_18, x_967, x_968, x_969);
lean_dec_ref(x_967);
x_971 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_970, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_971) == 0)
{
uint8_t x_972; 
x_972 = !lean_is_exclusive(x_971);
if (x_972 == 0)
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; uint8_t x_977; 
x_973 = lean_ctor_get(x_971, 0);
x_974 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29));
x_975 = l_Lean_Expr_replaceFn(x_2, x_974);
x_976 = l_Lean_Expr_app___override(x_975, x_902);
lean_ctor_set(x_35, 1, x_976);
lean_ctor_set(x_35, 0, x_973);
x_977 = lean_unbox(x_904);
lean_dec(x_904);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_977);
lean_ctor_set(x_971, 0, x_35);
return x_971;
}
else
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; uint8_t x_982; lean_object* x_983; 
x_978 = lean_ctor_get(x_971, 0);
lean_inc(x_978);
lean_dec(x_971);
x_979 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29));
x_980 = l_Lean_Expr_replaceFn(x_2, x_979);
x_981 = l_Lean_Expr_app___override(x_980, x_902);
lean_ctor_set(x_35, 1, x_981);
lean_ctor_set(x_35, 0, x_978);
x_982 = lean_unbox(x_904);
lean_dec(x_904);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_982);
x_983 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_983, 0, x_35);
return x_983;
}
}
else
{
uint8_t x_984; 
lean_dec(x_904);
lean_free_object(x_35);
lean_dec_ref(x_902);
lean_dec_ref(x_2);
x_984 = !lean_is_exclusive(x_971);
if (x_984 == 0)
{
return x_971;
}
else
{
lean_object* x_985; lean_object* x_986; 
x_985 = lean_ctor_get(x_971, 0);
lean_inc(x_985);
lean_dec(x_971);
x_986 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_986, 0, x_985);
return x_986;
}
}
}
else
{
uint8_t x_987; 
lean_dec(x_904);
lean_free_object(x_35);
lean_dec_ref(x_902);
lean_dec_ref(x_18);
lean_dec(x_7);
lean_dec_ref(x_2);
x_987 = !lean_is_exclusive(x_964);
if (x_987 == 0)
{
return x_964;
}
else
{
lean_object* x_988; lean_object* x_989; 
x_988 = lean_ctor_get(x_964, 0);
lean_inc(x_988);
lean_dec(x_964);
x_989 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_989, 0, x_988);
return x_989;
}
}
}
}
else
{
uint8_t x_990; 
lean_dec(x_904);
lean_free_object(x_35);
lean_dec_ref(x_902);
lean_dec_ref(x_901);
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
x_990 = !lean_is_exclusive(x_906);
if (x_990 == 0)
{
return x_906;
}
else
{
lean_object* x_991; lean_object* x_992; 
x_991 = lean_ctor_get(x_906, 0);
lean_inc(x_991);
lean_dec(x_906);
x_992 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_992, 0, x_991);
return x_992;
}
}
}
else
{
lean_object* x_993; lean_object* x_994; 
lean_dec(x_904);
lean_dec_ref(x_901);
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
lean_inc_ref(x_902);
x_993 = l_Lean_Meta_mkOfEqTrueCore(x_27, x_902);
x_994 = l_Lean_Meta_Sym_shareCommon___redArg(x_993, x_7);
if (lean_obj_tag(x_994) == 0)
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; 
x_995 = lean_ctor_get(x_994, 0);
lean_inc(x_995);
lean_dec_ref(x_994);
x_996 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_997 = lean_array_push(x_996, x_995);
x_998 = l_Lean_Expr_betaRev(x_21, x_997, x_1, x_1);
lean_dec_ref(x_997);
x_999 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_998, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_999) == 0)
{
uint8_t x_1000; 
x_1000 = !lean_is_exclusive(x_999);
if (x_1000 == 0)
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
x_1001 = lean_ctor_get(x_999, 0);
x_1002 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__31));
x_1003 = l_Lean_Expr_replaceFn(x_2, x_1002);
x_1004 = l_Lean_Expr_app___override(x_1003, x_902);
lean_ctor_set(x_35, 1, x_1004);
lean_ctor_set(x_35, 0, x_1001);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_1);
lean_ctor_set(x_999, 0, x_35);
return x_999;
}
else
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
x_1005 = lean_ctor_get(x_999, 0);
lean_inc(x_1005);
lean_dec(x_999);
x_1006 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__31));
x_1007 = l_Lean_Expr_replaceFn(x_2, x_1006);
x_1008 = l_Lean_Expr_app___override(x_1007, x_902);
lean_ctor_set(x_35, 1, x_1008);
lean_ctor_set(x_35, 0, x_1005);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_1);
x_1009 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1009, 0, x_35);
return x_1009;
}
}
else
{
uint8_t x_1010; 
lean_free_object(x_35);
lean_dec_ref(x_902);
lean_dec_ref(x_2);
x_1010 = !lean_is_exclusive(x_999);
if (x_1010 == 0)
{
return x_999;
}
else
{
lean_object* x_1011; lean_object* x_1012; 
x_1011 = lean_ctor_get(x_999, 0);
lean_inc(x_1011);
lean_dec(x_999);
x_1012 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1012, 0, x_1011);
return x_1012;
}
}
}
else
{
uint8_t x_1013; 
lean_free_object(x_35);
lean_dec_ref(x_902);
lean_dec_ref(x_21);
lean_dec(x_7);
lean_dec_ref(x_2);
x_1013 = !lean_is_exclusive(x_994);
if (x_1013 == 0)
{
return x_994;
}
else
{
lean_object* x_1014; lean_object* x_1015; 
x_1014 = lean_ctor_get(x_994, 0);
lean_inc(x_1014);
lean_dec(x_994);
x_1015 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1015, 0, x_1014);
return x_1015;
}
}
}
}
else
{
uint8_t x_1016; 
lean_free_object(x_35);
lean_dec_ref(x_902);
lean_dec_ref(x_901);
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
x_1016 = !lean_is_exclusive(x_903);
if (x_1016 == 0)
{
return x_903;
}
else
{
lean_object* x_1017; lean_object* x_1018; 
x_1017 = lean_ctor_get(x_903, 0);
lean_inc(x_1017);
lean_dec(x_903);
x_1018 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1018, 0, x_1017);
return x_1018;
}
}
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1019 = lean_ctor_get(x_35, 0);
x_1020 = lean_ctor_get(x_35, 1);
lean_inc(x_1020);
lean_inc(x_1019);
lean_dec(x_35);
x_1021 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_1019, x_6);
if (lean_obj_tag(x_1021) == 0)
{
lean_object* x_1022; uint8_t x_1023; 
x_1022 = lean_ctor_get(x_1021, 0);
lean_inc(x_1022);
lean_dec_ref(x_1021);
x_1023 = lean_unbox(x_1022);
if (x_1023 == 0)
{
lean_object* x_1024; 
x_1024 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_1019, x_6);
if (lean_obj_tag(x_1024) == 0)
{
lean_object* x_1025; uint8_t x_1026; 
x_1025 = lean_ctor_get(x_1024, 0);
lean_inc(x_1025);
lean_dec_ref(x_1024);
x_1026 = lean_unbox(x_1025);
if (x_1026 == 0)
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
lean_dec(x_1022);
x_1027 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28);
lean_inc_ref(x_1020);
lean_inc_ref(x_1019);
lean_inc_ref(x_27);
x_1028 = l_Lean_mkApp4(x_1027, x_27, x_1019, x_24, x_1020);
x_1029 = l_Lean_Meta_Sym_shareCommon___redArg(x_1020, x_7);
if (lean_obj_tag(x_1029) == 0)
{
lean_object* x_1030; lean_object* x_1031; uint8_t x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; uint8_t x_1038; uint8_t x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
x_1030 = lean_ctor_get(x_1029, 0);
lean_inc(x_1030);
lean_dec_ref(x_1029);
x_1031 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_1032 = 0;
x_1033 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_1034 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_1030);
lean_inc_ref(x_1019);
lean_inc_ref(x_27);
x_1035 = l_Lean_mkApp4(x_1033, x_27, x_1019, x_1030, x_1034);
x_1036 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_1037 = lean_array_push(x_1036, x_1035);
x_1038 = lean_unbox(x_1025);
x_1039 = lean_unbox(x_1025);
x_1040 = l_Lean_Expr_betaRev(x_21, x_1037, x_1038, x_1039);
lean_dec_ref(x_1037);
lean_inc_ref(x_1019);
x_1041 = l_Lean_mkLambda(x_1031, x_1032, x_1019, x_1040);
x_1042 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1041, x_7);
if (lean_obj_tag(x_1042) == 0)
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; uint8_t x_1048; uint8_t x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
x_1043 = lean_ctor_get(x_1042, 0);
lean_inc(x_1043);
lean_dec_ref(x_1042);
lean_inc_ref(x_1019);
x_1044 = l_Lean_mkNot(x_1019);
x_1045 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12);
lean_inc(x_1030);
lean_inc_ref(x_1019);
x_1046 = l_Lean_mkApp4(x_1045, x_27, x_1019, x_1030, x_1034);
x_1047 = lean_array_push(x_1036, x_1046);
x_1048 = lean_unbox(x_1025);
x_1049 = lean_unbox(x_1025);
x_1050 = l_Lean_Expr_betaRev(x_18, x_1047, x_1048, x_1049);
lean_dec_ref(x_1047);
x_1051 = l_Lean_mkLambda(x_1031, x_1032, x_1044, x_1050);
x_1052 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1051, x_7);
if (lean_obj_tag(x_1052) == 0)
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
x_1053 = lean_ctor_get(x_1052, 0);
lean_inc(x_1053);
lean_dec_ref(x_1052);
x_1054 = lean_unsigned_to_nat(4u);
x_1055 = l_Lean_Expr_getBoundedAppFn(x_1054, x_2);
lean_inc_ref(x_1028);
lean_inc_ref(x_1019);
x_1056 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_1055, x_1019, x_1028, x_1043, x_1053, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_1056) == 0)
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; uint8_t x_1063; lean_object* x_1064; 
x_1057 = lean_ctor_get(x_1056, 0);
lean_inc(x_1057);
if (lean_is_exclusive(x_1056)) {
 lean_ctor_release(x_1056, 0);
 x_1058 = x_1056;
} else {
 lean_dec_ref(x_1056);
 x_1058 = lean_box(0);
}
x_1059 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
x_1060 = l_Lean_Expr_replaceFn(x_2, x_1059);
x_1061 = l_Lean_mkApp3(x_1060, x_1019, x_1028, x_1030);
x_1062 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_1062, 0, x_1057);
lean_ctor_set(x_1062, 1, x_1061);
x_1063 = lean_unbox(x_1025);
lean_dec(x_1025);
lean_ctor_set_uint8(x_1062, sizeof(void*)*2, x_1063);
if (lean_is_scalar(x_1058)) {
 x_1064 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1064 = x_1058;
}
lean_ctor_set(x_1064, 0, x_1062);
return x_1064;
}
else
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; 
lean_dec(x_1030);
lean_dec_ref(x_1028);
lean_dec(x_1025);
lean_dec_ref(x_1019);
lean_dec_ref(x_2);
x_1065 = lean_ctor_get(x_1056, 0);
lean_inc(x_1065);
if (lean_is_exclusive(x_1056)) {
 lean_ctor_release(x_1056, 0);
 x_1066 = x_1056;
} else {
 lean_dec_ref(x_1056);
 x_1066 = lean_box(0);
}
if (lean_is_scalar(x_1066)) {
 x_1067 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1067 = x_1066;
}
lean_ctor_set(x_1067, 0, x_1065);
return x_1067;
}
}
else
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
lean_dec(x_1043);
lean_dec(x_1030);
lean_dec_ref(x_1028);
lean_dec(x_1025);
lean_dec_ref(x_1019);
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
x_1068 = lean_ctor_get(x_1052, 0);
lean_inc(x_1068);
if (lean_is_exclusive(x_1052)) {
 lean_ctor_release(x_1052, 0);
 x_1069 = x_1052;
} else {
 lean_dec_ref(x_1052);
 x_1069 = lean_box(0);
}
if (lean_is_scalar(x_1069)) {
 x_1070 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1070 = x_1069;
}
lean_ctor_set(x_1070, 0, x_1068);
return x_1070;
}
}
else
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; 
lean_dec(x_1030);
lean_dec_ref(x_1028);
lean_dec(x_1025);
lean_dec_ref(x_1019);
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
x_1071 = lean_ctor_get(x_1042, 0);
lean_inc(x_1071);
if (lean_is_exclusive(x_1042)) {
 lean_ctor_release(x_1042, 0);
 x_1072 = x_1042;
} else {
 lean_dec_ref(x_1042);
 x_1072 = lean_box(0);
}
if (lean_is_scalar(x_1072)) {
 x_1073 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1073 = x_1072;
}
lean_ctor_set(x_1073, 0, x_1071);
return x_1073;
}
}
else
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
lean_dec_ref(x_1028);
lean_dec(x_1025);
lean_dec_ref(x_1019);
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
x_1074 = lean_ctor_get(x_1029, 0);
lean_inc(x_1074);
if (lean_is_exclusive(x_1029)) {
 lean_ctor_release(x_1029, 0);
 x_1075 = x_1029;
} else {
 lean_dec_ref(x_1029);
 x_1075 = lean_box(0);
}
if (lean_is_scalar(x_1075)) {
 x_1076 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1076 = x_1075;
}
lean_ctor_set(x_1076, 0, x_1074);
return x_1076;
}
}
else
{
lean_object* x_1077; lean_object* x_1078; 
lean_dec(x_1025);
lean_dec_ref(x_1019);
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
lean_inc_ref(x_1020);
x_1077 = l_Lean_Meta_mkOfEqFalseCore(x_27, x_1020);
x_1078 = l_Lean_Meta_Sym_shareCommon___redArg(x_1077, x_7);
if (lean_obj_tag(x_1078) == 0)
{
lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; uint8_t x_1082; uint8_t x_1083; lean_object* x_1084; lean_object* x_1085; 
x_1079 = lean_ctor_get(x_1078, 0);
lean_inc(x_1079);
lean_dec_ref(x_1078);
x_1080 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_1081 = lean_array_push(x_1080, x_1079);
x_1082 = lean_unbox(x_1022);
x_1083 = lean_unbox(x_1022);
x_1084 = l_Lean_Expr_betaRev(x_18, x_1081, x_1082, x_1083);
lean_dec_ref(x_1081);
x_1085 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1084, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_1085) == 0)
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; uint8_t x_1092; lean_object* x_1093; 
x_1086 = lean_ctor_get(x_1085, 0);
lean_inc(x_1086);
if (lean_is_exclusive(x_1085)) {
 lean_ctor_release(x_1085, 0);
 x_1087 = x_1085;
} else {
 lean_dec_ref(x_1085);
 x_1087 = lean_box(0);
}
x_1088 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29));
x_1089 = l_Lean_Expr_replaceFn(x_2, x_1088);
x_1090 = l_Lean_Expr_app___override(x_1089, x_1020);
x_1091 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_1091, 0, x_1086);
lean_ctor_set(x_1091, 1, x_1090);
x_1092 = lean_unbox(x_1022);
lean_dec(x_1022);
lean_ctor_set_uint8(x_1091, sizeof(void*)*2, x_1092);
if (lean_is_scalar(x_1087)) {
 x_1093 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1093 = x_1087;
}
lean_ctor_set(x_1093, 0, x_1091);
return x_1093;
}
else
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
lean_dec(x_1022);
lean_dec_ref(x_1020);
lean_dec_ref(x_2);
x_1094 = lean_ctor_get(x_1085, 0);
lean_inc(x_1094);
if (lean_is_exclusive(x_1085)) {
 lean_ctor_release(x_1085, 0);
 x_1095 = x_1085;
} else {
 lean_dec_ref(x_1085);
 x_1095 = lean_box(0);
}
if (lean_is_scalar(x_1095)) {
 x_1096 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1096 = x_1095;
}
lean_ctor_set(x_1096, 0, x_1094);
return x_1096;
}
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
lean_dec(x_1022);
lean_dec_ref(x_1020);
lean_dec_ref(x_18);
lean_dec(x_7);
lean_dec_ref(x_2);
x_1097 = lean_ctor_get(x_1078, 0);
lean_inc(x_1097);
if (lean_is_exclusive(x_1078)) {
 lean_ctor_release(x_1078, 0);
 x_1098 = x_1078;
} else {
 lean_dec_ref(x_1078);
 x_1098 = lean_box(0);
}
if (lean_is_scalar(x_1098)) {
 x_1099 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1099 = x_1098;
}
lean_ctor_set(x_1099, 0, x_1097);
return x_1099;
}
}
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; 
lean_dec(x_1022);
lean_dec_ref(x_1020);
lean_dec_ref(x_1019);
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
x_1100 = lean_ctor_get(x_1024, 0);
lean_inc(x_1100);
if (lean_is_exclusive(x_1024)) {
 lean_ctor_release(x_1024, 0);
 x_1101 = x_1024;
} else {
 lean_dec_ref(x_1024);
 x_1101 = lean_box(0);
}
if (lean_is_scalar(x_1101)) {
 x_1102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1102 = x_1101;
}
lean_ctor_set(x_1102, 0, x_1100);
return x_1102;
}
}
else
{
lean_object* x_1103; lean_object* x_1104; 
lean_dec(x_1022);
lean_dec_ref(x_1019);
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
lean_inc_ref(x_1020);
x_1103 = l_Lean_Meta_mkOfEqTrueCore(x_27, x_1020);
x_1104 = l_Lean_Meta_Sym_shareCommon___redArg(x_1103, x_7);
if (lean_obj_tag(x_1104) == 0)
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
x_1105 = lean_ctor_get(x_1104, 0);
lean_inc(x_1105);
lean_dec_ref(x_1104);
x_1106 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_1107 = lean_array_push(x_1106, x_1105);
x_1108 = l_Lean_Expr_betaRev(x_21, x_1107, x_1, x_1);
lean_dec_ref(x_1107);
x_1109 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1108, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_1109) == 0)
{
lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; 
x_1110 = lean_ctor_get(x_1109, 0);
lean_inc(x_1110);
if (lean_is_exclusive(x_1109)) {
 lean_ctor_release(x_1109, 0);
 x_1111 = x_1109;
} else {
 lean_dec_ref(x_1109);
 x_1111 = lean_box(0);
}
x_1112 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__31));
x_1113 = l_Lean_Expr_replaceFn(x_2, x_1112);
x_1114 = l_Lean_Expr_app___override(x_1113, x_1020);
x_1115 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_1115, 0, x_1110);
lean_ctor_set(x_1115, 1, x_1114);
lean_ctor_set_uint8(x_1115, sizeof(void*)*2, x_1);
if (lean_is_scalar(x_1111)) {
 x_1116 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1116 = x_1111;
}
lean_ctor_set(x_1116, 0, x_1115);
return x_1116;
}
else
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; 
lean_dec_ref(x_1020);
lean_dec_ref(x_2);
x_1117 = lean_ctor_get(x_1109, 0);
lean_inc(x_1117);
if (lean_is_exclusive(x_1109)) {
 lean_ctor_release(x_1109, 0);
 x_1118 = x_1109;
} else {
 lean_dec_ref(x_1109);
 x_1118 = lean_box(0);
}
if (lean_is_scalar(x_1118)) {
 x_1119 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1119 = x_1118;
}
lean_ctor_set(x_1119, 0, x_1117);
return x_1119;
}
}
else
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
lean_dec_ref(x_1020);
lean_dec_ref(x_21);
lean_dec(x_7);
lean_dec_ref(x_2);
x_1120 = lean_ctor_get(x_1104, 0);
lean_inc(x_1120);
if (lean_is_exclusive(x_1104)) {
 lean_ctor_release(x_1104, 0);
 x_1121 = x_1104;
} else {
 lean_dec_ref(x_1104);
 x_1121 = lean_box(0);
}
if (lean_is_scalar(x_1121)) {
 x_1122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1122 = x_1121;
}
lean_ctor_set(x_1122, 0, x_1120);
return x_1122;
}
}
}
else
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; 
lean_dec_ref(x_1020);
lean_dec_ref(x_1019);
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
x_1123 = lean_ctor_get(x_1021, 0);
lean_inc(x_1123);
if (lean_is_exclusive(x_1021)) {
 lean_ctor_release(x_1021, 0);
 x_1124 = x_1021;
} else {
 lean_dec_ref(x_1021);
 x_1124 = lean_box(0);
}
if (lean_is_scalar(x_1124)) {
 x_1125 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1125 = x_1124;
}
lean_ctor_set(x_1125, 0, x_1123);
return x_1125;
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
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(x_1, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 2)
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 2)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = 1;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
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
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = 1;
x_15 = lean_box(x_14);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
case 1:
{
lean_object* x_19; 
lean_dec_ref(x_8);
x_19 = l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(x_7, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; 
lean_dec(x_9);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_ctor_set(x_19, 0, x_9);
return x_19;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_9);
return x_30;
}
}
}
else
{
lean_dec(x_9);
return x_19;
}
}
default: 
{
uint8_t x_31; 
lean_dec(x_9);
lean_dec_ref(x_4);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; 
x_32 = lean_ctor_get(x_8, 0);
lean_dec(x_32);
x_33 = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(x_7, x_5);
lean_dec(x_5);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = 0;
x_37 = lean_unbox(x_34);
x_38 = l_Lean_instBEqReducibilityStatus_beq(x_37, x_36);
x_39 = 1;
if (x_38 == 0)
{
uint8_t x_46; uint8_t x_47; 
lean_free_object(x_8);
x_46 = 3;
x_47 = l_Lean_Meta_instBEqTransparencyMode_beq(x_11, x_46);
if (x_47 == 0)
{
lean_dec(x_34);
x_40 = x_47;
goto block_45;
}
else
{
uint8_t x_48; uint8_t x_49; uint8_t x_50; 
x_48 = 3;
x_49 = lean_unbox(x_34);
lean_dec(x_34);
x_50 = l_Lean_instBEqReducibilityStatus_beq(x_49, x_48);
x_40 = x_50;
goto block_45;
}
}
else
{
lean_object* x_51; 
lean_dec(x_35);
lean_dec(x_34);
x_51 = lean_box(x_39);
lean_ctor_set(x_8, 0, x_51);
return x_8;
}
block_45:
{
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(x_40);
if (lean_is_scalar(x_35)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_35;
}
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_box(x_39);
if (lean_is_scalar(x_35)) {
 x_44 = lean_alloc_ctor(0, 1, 0);
} else {
 x_44 = x_35;
}
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; 
lean_dec(x_8);
x_52 = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(x_7, x_5);
lean_dec(x_5);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = 0;
x_56 = lean_unbox(x_53);
x_57 = l_Lean_instBEqReducibilityStatus_beq(x_56, x_55);
x_58 = 1;
if (x_57 == 0)
{
uint8_t x_65; uint8_t x_66; 
x_65 = 3;
x_66 = l_Lean_Meta_instBEqTransparencyMode_beq(x_11, x_65);
if (x_66 == 0)
{
lean_dec(x_53);
x_59 = x_66;
goto block_64;
}
else
{
uint8_t x_67; uint8_t x_68; uint8_t x_69; 
x_67 = 3;
x_68 = lean_unbox(x_53);
lean_dec(x_53);
x_69 = l_Lean_instBEqReducibilityStatus_beq(x_68, x_67);
x_59 = x_69;
goto block_64;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_54);
lean_dec(x_53);
x_70 = lean_box(x_58);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
block_64:
{
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_box(x_59);
if (lean_is_scalar(x_54)) {
 x_61 = lean_alloc_ctor(0, 1, 0);
} else {
 x_61 = x_54;
}
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_box(x_58);
if (lean_is_scalar(x_54)) {
 x_63 = lean_alloc_ctor(0, 1, 0);
} else {
 x_63 = x_54;
}
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_72 = lean_ctor_get(x_1, 0);
lean_inc(x_72);
lean_dec_ref(x_1);
x_73 = lean_apply_5(x_72, x_2, x_3, x_4, x_5, lean_box(0));
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_8);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_8, 0);
lean_dec(x_75);
x_76 = 0;
x_77 = lean_box(x_76);
lean_ctor_set(x_8, 0, x_77);
return x_8;
}
else
{
uint8_t x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_8);
x_78 = 0;
x_79 = lean_box(x_78);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
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
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 6);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_2, 6, x_10);
x_11 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_ctor_get(x_2, 3);
x_17 = lean_ctor_get(x_2, 4);
x_18 = lean_ctor_get(x_2, 5);
x_19 = lean_ctor_get(x_2, 6);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_dec(x_2);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_23, 0, x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_14);
lean_ctor_set(x_25, 2, x_15);
lean_ctor_set(x_25, 3, x_16);
lean_ctor_set(x_25, 4, x_17);
lean_ctor_set(x_25, 5, x_18);
lean_ctor_set(x_25, 6, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*7, x_13);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 1, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 2, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 3, x_22);
x_26 = lean_apply_5(x_1, x_25, x_3, x_4, x_5, lean_box(0));
return x_26;
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
uint8_t x_17; 
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
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_12);
x_13 = l_Lean_Meta_Sym_mkEqRefl___redArg(x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = 0;
x_17 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = 0;
x_20 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_12);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_25 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
lean_ctor_set(x_9, 0, x_25);
return x_9;
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
lean_dec(x_9);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_inc(x_27);
x_28 = l_Lean_Meta_Sym_mkEqRefl___redArg(x_27, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = 0;
x_32 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_31);
if (lean_is_scalar(x_30)) {
 x_33 = lean_alloc_ctor(0, 1, 0);
} else {
 x_33 = x_30;
}
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_35 = x_28;
} else {
 lean_dec_ref(x_28);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_37 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
return x_9;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_9, 0);
lean_inc(x_40);
lean_dec(x_9);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
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
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_22);
x_23 = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(x_22, x_10);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_27, x_29);
lean_dec(x_27);
x_31 = lean_nat_add(x_30, x_28);
lean_dec(x_28);
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
x_32 = l_Lean_Meta_Sym_Simp_simpAppArgRange(x_1, x_30, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_31);
lean_dec(x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_33, 0);
lean_dec_ref(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec_ref(x_32);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_1);
x_35 = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(x_22, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = x_35;
goto block_16;
}
else
{
lean_dec(x_22);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_12 = x_32;
goto block_16;
}
}
else
{
uint8_t x_36; 
x_36 = lean_ctor_get_uint8(x_33, sizeof(void*)*2);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec_ref(x_32);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_38);
x_40 = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(x_22, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_43 = lean_ctor_get_uint8(x_42, 0);
lean_dec_ref(x_42);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_43);
lean_ctor_set(x_40, 0, x_33);
return x_40;
}
else
{
uint8_t x_44; 
lean_free_object(x_40);
lean_free_object(x_33);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_ctor_get(x_42, 1);
lean_inc_ref(x_45);
x_47 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_1, x_38, x_39, x_45, x_46, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_ctor_set(x_42, 1, x_49);
lean_ctor_set(x_47, 0, x_42);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
lean_ctor_set(x_42, 1, x_50);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_42);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_free_object(x_42);
lean_dec_ref(x_45);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_42, 0);
x_56 = lean_ctor_get(x_42, 1);
x_57 = lean_ctor_get_uint8(x_42, sizeof(void*)*2);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_42);
lean_inc_ref(x_55);
x_58 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_1, x_38, x_39, x_55, x_56, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_57);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_55);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_64 = x_58;
} else {
 lean_dec_ref(x_58);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
}
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_40, 0);
lean_inc(x_66);
lean_dec(x_40);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; lean_object* x_68; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_67 = lean_ctor_get_uint8(x_66, 0);
lean_dec_ref(x_66);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_67);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_33);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; 
lean_free_object(x_33);
x_69 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_66, 1);
lean_inc_ref(x_70);
x_71 = lean_ctor_get_uint8(x_66, sizeof(void*)*2);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_72 = x_66;
} else {
 lean_dec_ref(x_66);
 x_72 = lean_box(0);
}
lean_inc_ref(x_69);
x_73 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_1, x_38, x_39, x_69, x_70, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 2, 1);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_71);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 1, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_72);
lean_dec_ref(x_69);
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_79 = x_73;
} else {
 lean_dec_ref(x_73);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
}
}
}
else
{
lean_free_object(x_33);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
x_12 = x_40;
goto block_16;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_33, 0);
x_82 = lean_ctor_get(x_33, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_33);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_81);
x_83 = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(x_22, x_81, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_86 = lean_ctor_get_uint8(x_84, 0);
lean_dec_ref(x_84);
x_87 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_82);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_86);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 1, 0);
} else {
 x_88 = x_85;
}
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_85);
x_89 = lean_ctor_get(x_84, 0);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc_ref(x_90);
x_91 = lean_ctor_get_uint8(x_84, sizeof(void*)*2);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_92 = x_84;
} else {
 lean_dec_ref(x_84);
 x_92 = lean_box(0);
}
lean_inc_ref(x_89);
x_93 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_1, x_81, x_82, x_89, x_90, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_96 = lean_alloc_ctor(1, 2, 1);
} else {
 x_96 = x_92;
}
lean_ctor_set(x_96, 0, x_89);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*2, x_91);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 1, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_92);
lean_dec_ref(x_89);
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_99 = x_93;
} else {
 lean_dec_ref(x_93);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_98);
return x_100;
}
}
}
else
{
lean_dec_ref(x_82);
lean_dec_ref(x_81);
x_12 = x_83;
goto block_16;
}
}
}
else
{
lean_dec_ref(x_33);
lean_dec(x_22);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_12 = x_32;
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
x_12 = x_32;
goto block_16;
}
}
else
{
lean_object* x_101; 
lean_dec(x_25);
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
x_101 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
lean_ctor_set(x_23, 0, x_101);
return x_23;
}
}
else
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_23, 0);
lean_inc(x_102);
lean_dec(x_23);
if (lean_obj_tag(x_102) == 1)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_104, x_106);
lean_dec(x_104);
x_108 = lean_nat_add(x_107, x_105);
lean_dec(x_105);
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
x_109 = l_Lean_Meta_Sym_Simp_simpAppArgRange(x_1, x_107, x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_108);
lean_dec(x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
x_111 = lean_ctor_get_uint8(x_110, 0);
lean_dec_ref(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec_ref(x_109);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_1);
x_112 = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(x_22, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = x_112;
goto block_16;
}
else
{
lean_dec(x_22);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_12 = x_109;
goto block_16;
}
}
else
{
uint8_t x_113; 
x_113 = lean_ctor_get_uint8(x_110, sizeof(void*)*2);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_109);
x_114 = lean_ctor_get(x_110, 0);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_110, 1);
lean_inc_ref(x_115);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_116 = x_110;
} else {
 lean_dec_ref(x_110);
 x_116 = lean_box(0);
}
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_114);
x_117 = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(x_22, x_114, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_120 = lean_ctor_get_uint8(x_118, 0);
lean_dec_ref(x_118);
if (lean_is_scalar(x_116)) {
 x_121 = lean_alloc_ctor(1, 2, 1);
} else {
 x_121 = x_116;
}
lean_ctor_set(x_121, 0, x_114);
lean_ctor_set(x_121, 1, x_115);
lean_ctor_set_uint8(x_121, sizeof(void*)*2, x_120);
if (lean_is_scalar(x_119)) {
 x_122 = lean_alloc_ctor(0, 1, 0);
} else {
 x_122 = x_119;
}
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_119);
lean_dec(x_116);
x_123 = lean_ctor_get(x_118, 0);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_118, 1);
lean_inc_ref(x_124);
x_125 = lean_ctor_get_uint8(x_118, sizeof(void*)*2);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_126 = x_118;
} else {
 lean_dec_ref(x_118);
 x_126 = lean_box(0);
}
lean_inc_ref(x_123);
x_127 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_1, x_114, x_115, x_123, x_124, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_129 = x_127;
} else {
 lean_dec_ref(x_127);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_130 = lean_alloc_ctor(1, 2, 1);
} else {
 x_130 = x_126;
}
lean_ctor_set(x_130, 0, x_123);
lean_ctor_set(x_130, 1, x_128);
lean_ctor_set_uint8(x_130, sizeof(void*)*2, x_125);
if (lean_is_scalar(x_129)) {
 x_131 = lean_alloc_ctor(0, 1, 0);
} else {
 x_131 = x_129;
}
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_126);
lean_dec_ref(x_123);
x_132 = lean_ctor_get(x_127, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_133 = x_127;
} else {
 lean_dec_ref(x_127);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 1, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_132);
return x_134;
}
}
}
else
{
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec_ref(x_114);
x_12 = x_117;
goto block_16;
}
}
else
{
lean_dec_ref(x_110);
lean_dec(x_22);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_12 = x_109;
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
x_12 = x_109;
goto block_16;
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_102);
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
x_135 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; 
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
x_137 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
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
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4, &l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4);
x_24 = lean_box(x_19);
x_25 = lean_array_push(x_23, x_24);
x_26 = lean_box(x_19);
x_27 = lean_array_push(x_25, x_26);
x_28 = lean_box(x_21);
x_29 = lean_array_push(x_27, x_28);
x_30 = lean_box(x_21);
x_31 = lean_array_push(x_29, x_30);
x_32 = lean_box(x_21);
x_33 = lean_array_push(x_31, x_32);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_1);
x_34 = l_Lean_Meta_Sym_Simp_simpInterlaced(x_1, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = lean_ctor_get_uint8(x_35, 0);
lean_dec_ref(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec_ref(x_34);
x_37 = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(x_1, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_37;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_34;
}
}
else
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_35, sizeof(void*)*2);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec_ref(x_34);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_40);
x_42 = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(x_40, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
lean_dec_ref(x_44);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_45 = 0;
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_45);
lean_ctor_set(x_42, 0, x_35);
return x_42;
}
else
{
uint8_t x_46; 
lean_free_object(x_42);
lean_free_object(x_35);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
x_49 = 0;
lean_inc_ref(x_47);
x_50 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_1, x_40, x_41, x_47, x_48, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_ctor_set(x_44, 1, x_52);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_49);
lean_ctor_set(x_50, 0, x_44);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec(x_50);
lean_ctor_set(x_44, 1, x_53);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_49);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_44);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_free_object(x_44);
lean_dec_ref(x_47);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_44, 0);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_44);
x_60 = 0;
lean_inc_ref(x_58);
x_61 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_1, x_40, x_41, x_58, x_59, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_60);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 1, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_58);
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_67 = x_61;
} else {
 lean_dec_ref(x_61);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_66);
return x_68;
}
}
}
}
else
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_42, 0);
lean_inc(x_69);
lean_dec(x_42);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; lean_object* x_71; 
lean_dec_ref(x_69);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_70 = 0;
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_70);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_35);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
lean_free_object(x_35);
x_72 = lean_ctor_get(x_69, 0);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_73);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_74 = x_69;
} else {
 lean_dec_ref(x_69);
 x_74 = lean_box(0);
}
x_75 = 0;
lean_inc_ref(x_72);
x_76 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_1, x_40, x_41, x_72, x_73, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_79 = lean_alloc_ctor(1, 2, 1);
} else {
 x_79 = x_74;
}
lean_ctor_set(x_79, 0, x_72);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_75);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_74);
lean_dec_ref(x_72);
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_82 = x_76;
} else {
 lean_dec_ref(x_76);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
return x_83;
}
}
}
}
else
{
lean_free_object(x_35);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_42;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_35, 0);
x_85 = lean_ctor_get(x_35, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_35);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_84);
x_86 = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(x_84, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_89; lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_87);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_89 = 0;
x_90 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_85);
lean_ctor_set_uint8(x_90, sizeof(void*)*2, x_89);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 1, 0);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
lean_dec(x_88);
x_92 = lean_ctor_get(x_87, 0);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_87, 1);
lean_inc_ref(x_93);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_94 = x_87;
} else {
 lean_dec_ref(x_87);
 x_94 = lean_box(0);
}
x_95 = 0;
lean_inc_ref(x_92);
x_96 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_1, x_84, x_85, x_92, x_93, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_99 = lean_alloc_ctor(1, 2, 1);
} else {
 x_99 = x_94;
}
lean_ctor_set(x_99, 0, x_92);
lean_ctor_set(x_99, 1, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*2, x_95);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 1, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_94);
lean_dec_ref(x_92);
x_101 = lean_ctor_get(x_96, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 x_102 = x_96;
} else {
 lean_dec_ref(x_96);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 1, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_101);
return x_103;
}
}
}
else
{
lean_dec_ref(x_85);
lean_dec_ref(x_84);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_86;
}
}
}
else
{
lean_dec_ref(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_34;
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
return x_34;
}
}
}
else
{
lean_object* x_104; 
lean_dec(x_13);
x_104 = l_Lean_Meta_Sym_Simp_simpDIteCbv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_104;
}
}
else
{
lean_object* x_105; 
lean_dec(x_13);
x_105 = l_Lean_Meta_Sym_Simp_simpCond(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_105;
}
}
else
{
lean_object* x_106; 
lean_dec(x_13);
x_106 = l_Lean_Meta_Sym_Simp_simpIteCbv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; 
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
x_107 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
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
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Sym_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
