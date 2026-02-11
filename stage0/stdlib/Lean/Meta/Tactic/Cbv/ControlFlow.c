// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.ControlFlow
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.Simp.Result import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.Simp.ControlFlow import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.InferType import Lean.Meta.Sym.Simp.App import Lean.Meta.SynthInstance import Lean.Meta.WHNF import Lean.Meta.AppBuilder import Init.Sym.Lemmas import Lean.Meta.Tactic.Cbv.TheoremsLookup
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
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__3_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__6_value;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_false_of_decide"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(171, 157, 112, 124, 91, 52, 64, 56)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__9_value;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instDecidableFalse"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(49, 216, 212, 175, 154, 176, 165, 174)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__12_value;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__14_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ite_cond_congr"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__16 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__16_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(149, 115, 5, 135, 85, 70, 205, 95)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ite_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__18 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(217, 231, 214, 152, 207, 100, 121, 38)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "eq_true_of_decide"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(10, 132, 193, 70, 136, 209, 66, 149)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__21 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__21_value;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "instDecidableTrue"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_value),LEAN_SCALAR_PTR_LITERAL(45, 239, 189, 64, 160, 216, 116, 23)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__24 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__24_value;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ite_true"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__26 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(28, 219, 17, 217, 43, 100, 109, 98)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ite_cond_eq_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28_value),LEAN_SCALAR_PTR_LITERAL(4, 35, 104, 204, 105, 138, 171, 217)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__29 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__29_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ite_cond_eq_true"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30_value),LEAN_SCALAR_PTR_LITERAL(217, 214, 153, 207, 191, 74, 245, 103)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__31 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__31_value;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFn(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
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
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
lean_object* l_Lean_mkBVar(lean_object*);
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mpr_not"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(121, 56, 250, 51, 9, 123, 141, 181)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_value;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(155, 21, 178, 198, 97, 164, 246, 137)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_value;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dite_cond_congr"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
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
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24;
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
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0_value;
lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0_value;
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*6);
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
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__3));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__6));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__9));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__12));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__21));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__24));
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
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
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
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_26);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_29);
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_31 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__1));
x_32 = l_Lean_Expr_isConstOf(x_30, x_31);
if (x_32 == 0)
{
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
lean_object* x_33; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_26);
x_33 = lean_sym_simp(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_26, x_6);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_unbox(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_free_object(x_36);
x_40 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_26, x_6);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_40);
lean_dec(x_38);
x_44 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4;
lean_inc_ref(x_26);
x_45 = l_Lean_Expr_app___override(x_44, x_26);
x_46 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_47 = l_Lean_Meta_trySynthInstance(x_45, x_46, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
if (lean_obj_tag(x_49) == 1)
{
lean_object* x_50; lean_object* x_51; 
lean_free_object(x_47);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = l_Lean_Meta_Sym_shareCommon___redArg(x_50, x_7);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_52);
lean_inc_ref(x_26);
x_54 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_53, x_26, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_56 = lean_sym_simp(x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
lean_dec(x_52);
lean_dec(x_42);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_ctor_set_uint8(x_58, 0, x_32);
return x_56;
}
else
{
lean_object* x_60; 
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_60, 0, x_32);
lean_ctor_set(x_56, 0, x_60);
return x_56;
}
}
else
{
uint8_t x_61; 
lean_free_object(x_56);
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
x_64 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_62, x_6);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = lean_unbox(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_42);
x_67 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_62, x_6);
lean_dec_ref(x_62);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_dec(x_65);
lean_free_object(x_58);
lean_dec_ref(x_63);
lean_dec(x_52);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
lean_ctor_set_uint8(x_34, 0, x_32);
lean_ctor_set(x_67, 0, x_34);
return x_67;
}
else
{
lean_object* x_71; 
lean_free_object(x_67);
lean_free_object(x_34);
x_71 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10;
x_74 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13;
x_75 = lean_unsigned_to_nat(4u);
x_76 = l_Lean_Expr_getBoundedAppFn(x_75, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_72);
x_77 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_76, x_72, x_74, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = l_Lean_mkApp3(x_73, x_26, x_52, x_63);
x_80 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_81 = l_Lean_Expr_replaceFn(x_2, x_80);
x_82 = l_Lean_mkApp3(x_81, x_72, x_74, x_79);
x_83 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19));
x_84 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_85 = l_Lean_mkConst(x_83, x_84);
lean_inc_ref(x_18);
x_86 = l_Lean_mkApp3(x_85, x_29, x_21, x_18);
lean_inc_ref(x_18);
x_87 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_78, x_82, x_18, x_86, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_87, 0);
lean_ctor_set(x_58, 1, x_89);
lean_ctor_set(x_58, 0, x_18);
x_90 = lean_unbox(x_65);
lean_dec(x_65);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_90);
lean_ctor_set(x_87, 0, x_58);
return x_87;
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
lean_dec(x_87);
lean_ctor_set(x_58, 1, x_91);
lean_ctor_set(x_58, 0, x_18);
x_92 = lean_unbox(x_65);
lean_dec(x_65);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_92);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_58);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_65);
lean_free_object(x_58);
lean_dec_ref(x_18);
x_94 = !lean_is_exclusive(x_87);
if (x_94 == 0)
{
return x_87;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_87, 0);
lean_inc(x_95);
lean_dec(x_87);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_72);
lean_dec(x_65);
lean_free_object(x_58);
lean_dec_ref(x_63);
lean_dec(x_52);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_97 = !lean_is_exclusive(x_77);
if (x_97 == 0)
{
return x_77;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_77, 0);
lean_inc(x_98);
lean_dec(x_77);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_65);
lean_free_object(x_58);
lean_dec_ref(x_63);
lean_dec(x_52);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_100 = !lean_is_exclusive(x_71);
if (x_100 == 0)
{
return x_71;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_71, 0);
lean_inc(x_101);
lean_dec(x_71);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
}
else
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_67, 0);
lean_inc(x_103);
lean_dec(x_67);
x_104 = lean_unbox(x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_65);
lean_free_object(x_58);
lean_dec_ref(x_63);
lean_dec(x_52);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
lean_ctor_set_uint8(x_34, 0, x_32);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_34);
return x_105;
}
else
{
lean_object* x_106; 
lean_free_object(x_34);
x_106 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10;
x_109 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13;
x_110 = lean_unsigned_to_nat(4u);
x_111 = l_Lean_Expr_getBoundedAppFn(x_110, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_107);
x_112 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_111, x_107, x_109, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = l_Lean_mkApp3(x_108, x_26, x_52, x_63);
x_115 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_116 = l_Lean_Expr_replaceFn(x_2, x_115);
x_117 = l_Lean_mkApp3(x_116, x_107, x_109, x_114);
x_118 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19));
x_119 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_120 = l_Lean_mkConst(x_118, x_119);
lean_inc_ref(x_18);
x_121 = l_Lean_mkApp3(x_120, x_29, x_21, x_18);
lean_inc_ref(x_18);
x_122 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_113, x_117, x_18, x_121, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
lean_ctor_set(x_58, 1, x_123);
lean_ctor_set(x_58, 0, x_18);
x_125 = lean_unbox(x_65);
lean_dec(x_65);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_125);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 1, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_58);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_65);
lean_free_object(x_58);
lean_dec_ref(x_18);
x_127 = lean_ctor_get(x_122, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_128 = x_122;
} else {
 lean_dec_ref(x_122);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_107);
lean_dec(x_65);
lean_free_object(x_58);
lean_dec_ref(x_63);
lean_dec(x_52);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_130 = lean_ctor_get(x_112, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_131 = x_112;
} else {
 lean_dec_ref(x_112);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_130);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_65);
lean_free_object(x_58);
lean_dec_ref(x_63);
lean_dec(x_52);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_133 = lean_ctor_get(x_106, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_134 = x_106;
} else {
 lean_dec_ref(x_106);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_133);
return x_135;
}
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_65);
lean_free_object(x_58);
lean_dec_ref(x_63);
lean_dec(x_52);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_136 = !lean_is_exclusive(x_67);
if (x_136 == 0)
{
return x_67;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_67, 0);
lean_inc(x_137);
lean_dec(x_67);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; 
lean_dec(x_65);
lean_dec_ref(x_62);
lean_free_object(x_34);
x_139 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22;
x_142 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25;
x_143 = lean_unsigned_to_nat(4u);
x_144 = l_Lean_Expr_getBoundedAppFn(x_143, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_140);
x_145 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_144, x_140, x_142, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = l_Lean_mkApp3(x_141, x_26, x_52, x_63);
x_148 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_149 = l_Lean_Expr_replaceFn(x_2, x_148);
x_150 = l_Lean_mkApp3(x_149, x_140, x_142, x_147);
x_151 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27));
x_152 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_153 = l_Lean_mkConst(x_151, x_152);
lean_inc_ref(x_21);
x_154 = l_Lean_mkApp3(x_153, x_29, x_21, x_18);
lean_inc_ref(x_21);
x_155 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_146, x_150, x_21, x_154, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_ctor_get(x_155, 0);
lean_ctor_set(x_58, 1, x_157);
lean_ctor_set(x_58, 0, x_21);
x_158 = lean_unbox(x_42);
lean_dec(x_42);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_158);
lean_ctor_set(x_155, 0, x_58);
return x_155;
}
else
{
lean_object* x_159; uint8_t x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_155, 0);
lean_inc(x_159);
lean_dec(x_155);
lean_ctor_set(x_58, 1, x_159);
lean_ctor_set(x_58, 0, x_21);
x_160 = lean_unbox(x_42);
lean_dec(x_42);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_160);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_58);
return x_161;
}
}
else
{
uint8_t x_162; 
lean_free_object(x_58);
lean_dec(x_42);
lean_dec_ref(x_21);
x_162 = !lean_is_exclusive(x_155);
if (x_162 == 0)
{
return x_155;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_155, 0);
lean_inc(x_163);
lean_dec(x_155);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_140);
lean_free_object(x_58);
lean_dec_ref(x_63);
lean_dec(x_52);
lean_dec(x_42);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_165 = !lean_is_exclusive(x_145);
if (x_165 == 0)
{
return x_145;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_145, 0);
lean_inc(x_166);
lean_dec(x_145);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
}
}
else
{
uint8_t x_168; 
lean_free_object(x_58);
lean_dec_ref(x_63);
lean_dec(x_52);
lean_dec(x_42);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_168 = !lean_is_exclusive(x_139);
if (x_168 == 0)
{
return x_139;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_139, 0);
lean_inc(x_169);
lean_dec(x_139);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
return x_170;
}
}
}
}
else
{
uint8_t x_171; 
lean_free_object(x_58);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec(x_52);
lean_dec(x_42);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_171 = !lean_is_exclusive(x_64);
if (x_171 == 0)
{
return x_64;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_64, 0);
lean_inc(x_172);
lean_dec(x_64);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_58, 0);
x_175 = lean_ctor_get(x_58, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_58);
x_176 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_174, x_6);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; uint8_t x_178; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec_ref(x_176);
x_178 = lean_unbox(x_177);
if (x_178 == 0)
{
lean_object* x_179; 
lean_dec(x_42);
x_179 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_174, x_6);
lean_dec_ref(x_174);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
x_182 = lean_unbox(x_180);
lean_dec(x_180);
if (x_182 == 0)
{
lean_object* x_183; 
lean_dec(x_177);
lean_dec_ref(x_175);
lean_dec(x_52);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
lean_ctor_set_uint8(x_34, 0, x_32);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 1, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_34);
return x_183;
}
else
{
lean_object* x_184; 
lean_dec(x_181);
lean_free_object(x_34);
x_184 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10;
x_187 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13;
x_188 = lean_unsigned_to_nat(4u);
x_189 = l_Lean_Expr_getBoundedAppFn(x_188, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_185);
x_190 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_189, x_185, x_187, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec_ref(x_190);
x_192 = l_Lean_mkApp3(x_186, x_26, x_52, x_175);
x_193 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_194 = l_Lean_Expr_replaceFn(x_2, x_193);
x_195 = l_Lean_mkApp3(x_194, x_185, x_187, x_192);
x_196 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19));
x_197 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_198 = l_Lean_mkConst(x_196, x_197);
lean_inc_ref(x_18);
x_199 = l_Lean_mkApp3(x_198, x_29, x_21, x_18);
lean_inc_ref(x_18);
x_200 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_191, x_195, x_18, x_199, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 x_202 = x_200;
} else {
 lean_dec_ref(x_200);
 x_202 = lean_box(0);
}
x_203 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_203, 0, x_18);
lean_ctor_set(x_203, 1, x_201);
x_204 = lean_unbox(x_177);
lean_dec(x_177);
lean_ctor_set_uint8(x_203, sizeof(void*)*2, x_204);
if (lean_is_scalar(x_202)) {
 x_205 = lean_alloc_ctor(0, 1, 0);
} else {
 x_205 = x_202;
}
lean_ctor_set(x_205, 0, x_203);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_177);
lean_dec_ref(x_18);
x_206 = lean_ctor_get(x_200, 0);
lean_inc(x_206);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 x_207 = x_200;
} else {
 lean_dec_ref(x_200);
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
lean_dec(x_185);
lean_dec(x_177);
lean_dec_ref(x_175);
lean_dec(x_52);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_209 = lean_ctor_get(x_190, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 x_210 = x_190;
} else {
 lean_dec_ref(x_190);
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
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_177);
lean_dec_ref(x_175);
lean_dec(x_52);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_212 = lean_ctor_get(x_184, 0);
lean_inc(x_212);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 x_213 = x_184;
} else {
 lean_dec_ref(x_184);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 1, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_212);
return x_214;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_177);
lean_dec_ref(x_175);
lean_dec(x_52);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_215 = lean_ctor_get(x_179, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 x_216 = x_179;
} else {
 lean_dec_ref(x_179);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_215);
return x_217;
}
}
else
{
lean_object* x_218; 
lean_dec(x_177);
lean_dec_ref(x_174);
lean_free_object(x_34);
x_218 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec_ref(x_218);
x_220 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22;
x_221 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25;
x_222 = lean_unsigned_to_nat(4u);
x_223 = l_Lean_Expr_getBoundedAppFn(x_222, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_219);
x_224 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_223, x_219, x_221, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
lean_dec_ref(x_224);
x_226 = l_Lean_mkApp3(x_220, x_26, x_52, x_175);
x_227 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_228 = l_Lean_Expr_replaceFn(x_2, x_227);
x_229 = l_Lean_mkApp3(x_228, x_219, x_221, x_226);
x_230 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27));
x_231 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_232 = l_Lean_mkConst(x_230, x_231);
lean_inc_ref(x_21);
x_233 = l_Lean_mkApp3(x_232, x_29, x_21, x_18);
lean_inc_ref(x_21);
x_234 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_225, x_229, x_21, x_233, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 x_236 = x_234;
} else {
 lean_dec_ref(x_234);
 x_236 = lean_box(0);
}
x_237 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_237, 0, x_21);
lean_ctor_set(x_237, 1, x_235);
x_238 = lean_unbox(x_42);
lean_dec(x_42);
lean_ctor_set_uint8(x_237, sizeof(void*)*2, x_238);
if (lean_is_scalar(x_236)) {
 x_239 = lean_alloc_ctor(0, 1, 0);
} else {
 x_239 = x_236;
}
lean_ctor_set(x_239, 0, x_237);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_42);
lean_dec_ref(x_21);
x_240 = lean_ctor_get(x_234, 0);
lean_inc(x_240);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 x_241 = x_234;
} else {
 lean_dec_ref(x_234);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 1, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_240);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_219);
lean_dec_ref(x_175);
lean_dec(x_52);
lean_dec(x_42);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_243 = lean_ctor_get(x_224, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 x_244 = x_224;
} else {
 lean_dec_ref(x_224);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 1, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_243);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec_ref(x_175);
lean_dec(x_52);
lean_dec(x_42);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_246 = lean_ctor_get(x_218, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 x_247 = x_218;
} else {
 lean_dec_ref(x_218);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 1, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_246);
return x_248;
}
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec_ref(x_175);
lean_dec_ref(x_174);
lean_dec(x_52);
lean_dec(x_42);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_249 = lean_ctor_get(x_176, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_250 = x_176;
} else {
 lean_dec_ref(x_176);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 1, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_249);
return x_251;
}
}
}
}
else
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_56, 0);
lean_inc(x_252);
lean_dec(x_56);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_52);
lean_dec(x_42);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
if (lean_is_exclusive(x_252)) {
 x_253 = x_252;
} else {
 lean_dec_ref(x_252);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(0, 0, 1);
} else {
 x_254 = x_253;
}
lean_ctor_set_uint8(x_254, 0, x_32);
x_255 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_255, 0, x_254);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_256 = lean_ctor_get(x_252, 0);
lean_inc_ref(x_256);
x_257 = lean_ctor_get(x_252, 1);
lean_inc_ref(x_257);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_258 = x_252;
} else {
 lean_dec_ref(x_252);
 x_258 = lean_box(0);
}
x_259 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_256, x_6);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
lean_dec_ref(x_259);
x_261 = lean_unbox(x_260);
if (x_261 == 0)
{
lean_object* x_262; 
lean_dec(x_42);
x_262 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_256, x_6);
lean_dec_ref(x_256);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 x_264 = x_262;
} else {
 lean_dec_ref(x_262);
 x_264 = lean_box(0);
}
x_265 = lean_unbox(x_263);
lean_dec(x_263);
if (x_265 == 0)
{
lean_object* x_266; 
lean_dec(x_260);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_52);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
lean_ctor_set_uint8(x_34, 0, x_32);
if (lean_is_scalar(x_264)) {
 x_266 = lean_alloc_ctor(0, 1, 0);
} else {
 x_266 = x_264;
}
lean_ctor_set(x_266, 0, x_34);
return x_266;
}
else
{
lean_object* x_267; 
lean_dec(x_264);
lean_free_object(x_34);
x_267 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
lean_dec_ref(x_267);
x_269 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10;
x_270 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13;
x_271 = lean_unsigned_to_nat(4u);
x_272 = l_Lean_Expr_getBoundedAppFn(x_271, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_268);
x_273 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_272, x_268, x_270, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
lean_dec_ref(x_273);
x_275 = l_Lean_mkApp3(x_269, x_26, x_52, x_257);
x_276 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_277 = l_Lean_Expr_replaceFn(x_2, x_276);
x_278 = l_Lean_mkApp3(x_277, x_268, x_270, x_275);
x_279 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19));
x_280 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_281 = l_Lean_mkConst(x_279, x_280);
lean_inc_ref(x_18);
x_282 = l_Lean_mkApp3(x_281, x_29, x_21, x_18);
lean_inc_ref(x_18);
x_283 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_274, x_278, x_18, x_282, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 x_285 = x_283;
} else {
 lean_dec_ref(x_283);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_286 = lean_alloc_ctor(1, 2, 1);
} else {
 x_286 = x_258;
}
lean_ctor_set(x_286, 0, x_18);
lean_ctor_set(x_286, 1, x_284);
x_287 = lean_unbox(x_260);
lean_dec(x_260);
lean_ctor_set_uint8(x_286, sizeof(void*)*2, x_287);
if (lean_is_scalar(x_285)) {
 x_288 = lean_alloc_ctor(0, 1, 0);
} else {
 x_288 = x_285;
}
lean_ctor_set(x_288, 0, x_286);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_260);
lean_dec(x_258);
lean_dec_ref(x_18);
x_289 = lean_ctor_get(x_283, 0);
lean_inc(x_289);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 x_290 = x_283;
} else {
 lean_dec_ref(x_283);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 1, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_289);
return x_291;
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_268);
lean_dec(x_260);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_52);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_292 = lean_ctor_get(x_273, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_293 = x_273;
} else {
 lean_dec_ref(x_273);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 1, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_292);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_260);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_52);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_295 = lean_ctor_get(x_267, 0);
lean_inc(x_295);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 x_296 = x_267;
} else {
 lean_dec_ref(x_267);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 1, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_295);
return x_297;
}
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_260);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_52);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_298 = lean_ctor_get(x_262, 0);
lean_inc(x_298);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 x_299 = x_262;
} else {
 lean_dec_ref(x_262);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 1, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_298);
return x_300;
}
}
else
{
lean_object* x_301; 
lean_dec(x_260);
lean_dec_ref(x_256);
lean_free_object(x_34);
x_301 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
lean_dec_ref(x_301);
x_303 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22;
x_304 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25;
x_305 = lean_unsigned_to_nat(4u);
x_306 = l_Lean_Expr_getBoundedAppFn(x_305, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_302);
x_307 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_306, x_302, x_304, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
lean_dec_ref(x_307);
x_309 = l_Lean_mkApp3(x_303, x_26, x_52, x_257);
x_310 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_311 = l_Lean_Expr_replaceFn(x_2, x_310);
x_312 = l_Lean_mkApp3(x_311, x_302, x_304, x_309);
x_313 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27));
x_314 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_315 = l_Lean_mkConst(x_313, x_314);
lean_inc_ref(x_21);
x_316 = l_Lean_mkApp3(x_315, x_29, x_21, x_18);
lean_inc_ref(x_21);
x_317 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_308, x_312, x_21, x_316, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 x_319 = x_317;
} else {
 lean_dec_ref(x_317);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_320 = lean_alloc_ctor(1, 2, 1);
} else {
 x_320 = x_258;
}
lean_ctor_set(x_320, 0, x_21);
lean_ctor_set(x_320, 1, x_318);
x_321 = lean_unbox(x_42);
lean_dec(x_42);
lean_ctor_set_uint8(x_320, sizeof(void*)*2, x_321);
if (lean_is_scalar(x_319)) {
 x_322 = lean_alloc_ctor(0, 1, 0);
} else {
 x_322 = x_319;
}
lean_ctor_set(x_322, 0, x_320);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_258);
lean_dec(x_42);
lean_dec_ref(x_21);
x_323 = lean_ctor_get(x_317, 0);
lean_inc(x_323);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 x_324 = x_317;
} else {
 lean_dec_ref(x_317);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 1, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_323);
return x_325;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_302);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_52);
lean_dec(x_42);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_326 = lean_ctor_get(x_307, 0);
lean_inc(x_326);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 x_327 = x_307;
} else {
 lean_dec_ref(x_307);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(1, 1, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_326);
return x_328;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_52);
lean_dec(x_42);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_329 = lean_ctor_get(x_301, 0);
lean_inc(x_329);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 x_330 = x_301;
} else {
 lean_dec_ref(x_301);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(1, 1, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_329);
return x_331;
}
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec_ref(x_256);
lean_dec(x_52);
lean_dec(x_42);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_332 = lean_ctor_get(x_259, 0);
lean_inc(x_332);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_333 = x_259;
} else {
 lean_dec_ref(x_259);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 1, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_332);
return x_334;
}
}
}
}
else
{
lean_dec(x_52);
lean_dec(x_42);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
return x_56;
}
}
else
{
uint8_t x_335; 
lean_dec(x_52);
lean_dec(x_42);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_335 = !lean_is_exclusive(x_54);
if (x_335 == 0)
{
return x_54;
}
else
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_54, 0);
lean_inc(x_336);
lean_dec(x_54);
x_337 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_337, 0, x_336);
return x_337;
}
}
}
else
{
uint8_t x_338; 
lean_dec(x_42);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_338 = !lean_is_exclusive(x_51);
if (x_338 == 0)
{
return x_51;
}
else
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_ctor_get(x_51, 0);
lean_inc(x_339);
lean_dec(x_51);
x_340 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_340, 0, x_339);
return x_340;
}
}
}
else
{
uint8_t x_341; 
lean_dec(x_49);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_341 = lean_unbox(x_42);
lean_dec(x_42);
lean_ctor_set_uint8(x_34, 0, x_341);
lean_ctor_set(x_47, 0, x_34);
return x_47;
}
}
else
{
lean_object* x_342; 
x_342 = lean_ctor_get(x_47, 0);
lean_inc(x_342);
lean_dec(x_47);
if (lean_obj_tag(x_342) == 1)
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
lean_dec_ref(x_342);
x_344 = l_Lean_Meta_Sym_shareCommon___redArg(x_343, x_7);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
lean_dec_ref(x_344);
x_346 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_345);
lean_inc_ref(x_26);
x_347 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_346, x_26, x_345, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
lean_dec_ref(x_347);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_349 = lean_sym_simp(x_348, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 x_351 = x_349;
} else {
 lean_dec_ref(x_349);
 x_351 = lean_box(0);
}
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_345);
lean_dec(x_42);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
if (lean_is_exclusive(x_350)) {
 x_352 = x_350;
} else {
 lean_dec_ref(x_350);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(0, 0, 1);
} else {
 x_353 = x_352;
}
lean_ctor_set_uint8(x_353, 0, x_32);
if (lean_is_scalar(x_351)) {
 x_354 = lean_alloc_ctor(0, 1, 0);
} else {
 x_354 = x_351;
}
lean_ctor_set(x_354, 0, x_353);
return x_354;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_351);
x_355 = lean_ctor_get(x_350, 0);
lean_inc_ref(x_355);
x_356 = lean_ctor_get(x_350, 1);
lean_inc_ref(x_356);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_357 = x_350;
} else {
 lean_dec_ref(x_350);
 x_357 = lean_box(0);
}
x_358 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_355, x_6);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; uint8_t x_360; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
lean_dec_ref(x_358);
x_360 = lean_unbox(x_359);
if (x_360 == 0)
{
lean_object* x_361; 
lean_dec(x_42);
x_361 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_355, x_6);
lean_dec_ref(x_355);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 x_363 = x_361;
} else {
 lean_dec_ref(x_361);
 x_363 = lean_box(0);
}
x_364 = lean_unbox(x_362);
lean_dec(x_362);
if (x_364 == 0)
{
lean_object* x_365; 
lean_dec(x_359);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_345);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
lean_ctor_set_uint8(x_34, 0, x_32);
if (lean_is_scalar(x_363)) {
 x_365 = lean_alloc_ctor(0, 1, 0);
} else {
 x_365 = x_363;
}
lean_ctor_set(x_365, 0, x_34);
return x_365;
}
else
{
lean_object* x_366; 
lean_dec(x_363);
lean_free_object(x_34);
x_366 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
lean_dec_ref(x_366);
x_368 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10;
x_369 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13;
x_370 = lean_unsigned_to_nat(4u);
x_371 = l_Lean_Expr_getBoundedAppFn(x_370, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_367);
x_372 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_371, x_367, x_369, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
lean_dec_ref(x_372);
x_374 = l_Lean_mkApp3(x_368, x_26, x_345, x_356);
x_375 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_376 = l_Lean_Expr_replaceFn(x_2, x_375);
x_377 = l_Lean_mkApp3(x_376, x_367, x_369, x_374);
x_378 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19));
x_379 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_380 = l_Lean_mkConst(x_378, x_379);
lean_inc_ref(x_18);
x_381 = l_Lean_mkApp3(x_380, x_29, x_21, x_18);
lean_inc_ref(x_18);
x_382 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_373, x_377, x_18, x_381, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_387; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 x_384 = x_382;
} else {
 lean_dec_ref(x_382);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_385 = lean_alloc_ctor(1, 2, 1);
} else {
 x_385 = x_357;
}
lean_ctor_set(x_385, 0, x_18);
lean_ctor_set(x_385, 1, x_383);
x_386 = lean_unbox(x_359);
lean_dec(x_359);
lean_ctor_set_uint8(x_385, sizeof(void*)*2, x_386);
if (lean_is_scalar(x_384)) {
 x_387 = lean_alloc_ctor(0, 1, 0);
} else {
 x_387 = x_384;
}
lean_ctor_set(x_387, 0, x_385);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_359);
lean_dec(x_357);
lean_dec_ref(x_18);
x_388 = lean_ctor_get(x_382, 0);
lean_inc(x_388);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 x_389 = x_382;
} else {
 lean_dec_ref(x_382);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(1, 1, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_388);
return x_390;
}
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_367);
lean_dec(x_359);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_345);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_391 = lean_ctor_get(x_372, 0);
lean_inc(x_391);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 x_392 = x_372;
} else {
 lean_dec_ref(x_372);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 1, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_391);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_359);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_345);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_394 = lean_ctor_get(x_366, 0);
lean_inc(x_394);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 x_395 = x_366;
} else {
 lean_dec_ref(x_366);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 1, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_394);
return x_396;
}
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_359);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_345);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_397 = lean_ctor_get(x_361, 0);
lean_inc(x_397);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 x_398 = x_361;
} else {
 lean_dec_ref(x_361);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 1, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_397);
return x_399;
}
}
else
{
lean_object* x_400; 
lean_dec(x_359);
lean_dec_ref(x_355);
lean_free_object(x_34);
x_400 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec_ref(x_400);
x_402 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22;
x_403 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25;
x_404 = lean_unsigned_to_nat(4u);
x_405 = l_Lean_Expr_getBoundedAppFn(x_404, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_401);
x_406 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_405, x_401, x_403, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
lean_dec_ref(x_406);
x_408 = l_Lean_mkApp3(x_402, x_26, x_345, x_356);
x_409 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_410 = l_Lean_Expr_replaceFn(x_2, x_409);
x_411 = l_Lean_mkApp3(x_410, x_401, x_403, x_408);
x_412 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27));
x_413 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_414 = l_Lean_mkConst(x_412, x_413);
lean_inc_ref(x_21);
x_415 = l_Lean_mkApp3(x_414, x_29, x_21, x_18);
lean_inc_ref(x_21);
x_416 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_407, x_411, x_21, x_415, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; lean_object* x_421; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_418 = x_416;
} else {
 lean_dec_ref(x_416);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_419 = lean_alloc_ctor(1, 2, 1);
} else {
 x_419 = x_357;
}
lean_ctor_set(x_419, 0, x_21);
lean_ctor_set(x_419, 1, x_417);
x_420 = lean_unbox(x_42);
lean_dec(x_42);
lean_ctor_set_uint8(x_419, sizeof(void*)*2, x_420);
if (lean_is_scalar(x_418)) {
 x_421 = lean_alloc_ctor(0, 1, 0);
} else {
 x_421 = x_418;
}
lean_ctor_set(x_421, 0, x_419);
return x_421;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_357);
lean_dec(x_42);
lean_dec_ref(x_21);
x_422 = lean_ctor_get(x_416, 0);
lean_inc(x_422);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_423 = x_416;
} else {
 lean_dec_ref(x_416);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(1, 1, 0);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_422);
return x_424;
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_401);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_345);
lean_dec(x_42);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_425 = lean_ctor_get(x_406, 0);
lean_inc(x_425);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 x_426 = x_406;
} else {
 lean_dec_ref(x_406);
 x_426 = lean_box(0);
}
if (lean_is_scalar(x_426)) {
 x_427 = lean_alloc_ctor(1, 1, 0);
} else {
 x_427 = x_426;
}
lean_ctor_set(x_427, 0, x_425);
return x_427;
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_345);
lean_dec(x_42);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_428 = lean_ctor_get(x_400, 0);
lean_inc(x_428);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 x_429 = x_400;
} else {
 lean_dec_ref(x_400);
 x_429 = lean_box(0);
}
if (lean_is_scalar(x_429)) {
 x_430 = lean_alloc_ctor(1, 1, 0);
} else {
 x_430 = x_429;
}
lean_ctor_set(x_430, 0, x_428);
return x_430;
}
}
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_355);
lean_dec(x_345);
lean_dec(x_42);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_431 = lean_ctor_get(x_358, 0);
lean_inc(x_431);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 x_432 = x_358;
} else {
 lean_dec_ref(x_358);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(1, 1, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_431);
return x_433;
}
}
}
else
{
lean_dec(x_345);
lean_dec(x_42);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
return x_349;
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_345);
lean_dec(x_42);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_434 = lean_ctor_get(x_347, 0);
lean_inc(x_434);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 x_435 = x_347;
} else {
 lean_dec_ref(x_347);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(1, 1, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_434);
return x_436;
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_42);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_437 = lean_ctor_get(x_344, 0);
lean_inc(x_437);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 x_438 = x_344;
} else {
 lean_dec_ref(x_344);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 1, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_437);
return x_439;
}
}
else
{
uint8_t x_440; lean_object* x_441; 
lean_dec(x_342);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_440 = lean_unbox(x_42);
lean_dec(x_42);
lean_ctor_set_uint8(x_34, 0, x_440);
x_441 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_441, 0, x_34);
return x_441;
}
}
}
else
{
uint8_t x_442; 
lean_dec(x_42);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_442 = !lean_is_exclusive(x_47);
if (x_442 == 0)
{
return x_47;
}
else
{
lean_object* x_443; lean_object* x_444; 
x_443 = lean_ctor_get(x_47, 0);
lean_inc(x_443);
lean_dec(x_47);
x_444 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_444, 0, x_443);
return x_444;
}
}
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; 
lean_dec(x_42);
lean_free_object(x_34);
lean_dec_ref(x_26);
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
x_445 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19));
x_446 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_447 = l_Lean_mkConst(x_445, x_446);
lean_inc_ref(x_18);
x_448 = l_Lean_mkApp3(x_447, x_29, x_21, x_18);
x_449 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_449, 0, x_18);
lean_ctor_set(x_449, 1, x_448);
x_450 = lean_unbox(x_38);
lean_dec(x_38);
lean_ctor_set_uint8(x_449, sizeof(void*)*2, x_450);
lean_ctor_set(x_40, 0, x_449);
return x_40;
}
}
else
{
lean_object* x_451; uint8_t x_452; 
x_451 = lean_ctor_get(x_40, 0);
lean_inc(x_451);
lean_dec(x_40);
x_452 = lean_unbox(x_451);
if (x_452 == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_38);
x_453 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4;
lean_inc_ref(x_26);
x_454 = l_Lean_Expr_app___override(x_453, x_26);
x_455 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_456 = l_Lean_Meta_trySynthInstance(x_454, x_455, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 x_458 = x_456;
} else {
 lean_dec_ref(x_456);
 x_458 = lean_box(0);
}
if (lean_obj_tag(x_457) == 1)
{
lean_object* x_459; lean_object* x_460; 
lean_dec(x_458);
x_459 = lean_ctor_get(x_457, 0);
lean_inc(x_459);
lean_dec_ref(x_457);
x_460 = l_Lean_Meta_Sym_shareCommon___redArg(x_459, x_7);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
lean_dec_ref(x_460);
x_462 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_461);
lean_inc_ref(x_26);
x_463 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_462, x_26, x_461, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
lean_dec_ref(x_463);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_465 = lean_sym_simp(x_464, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 x_467 = x_465;
} else {
 lean_dec_ref(x_465);
 x_467 = lean_box(0);
}
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec(x_461);
lean_dec(x_451);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
if (lean_is_exclusive(x_466)) {
 x_468 = x_466;
} else {
 lean_dec_ref(x_466);
 x_468 = lean_box(0);
}
if (lean_is_scalar(x_468)) {
 x_469 = lean_alloc_ctor(0, 0, 1);
} else {
 x_469 = x_468;
}
lean_ctor_set_uint8(x_469, 0, x_32);
if (lean_is_scalar(x_467)) {
 x_470 = lean_alloc_ctor(0, 1, 0);
} else {
 x_470 = x_467;
}
lean_ctor_set(x_470, 0, x_469);
return x_470;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_467);
x_471 = lean_ctor_get(x_466, 0);
lean_inc_ref(x_471);
x_472 = lean_ctor_get(x_466, 1);
lean_inc_ref(x_472);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_473 = x_466;
} else {
 lean_dec_ref(x_466);
 x_473 = lean_box(0);
}
x_474 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_471, x_6);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; uint8_t x_476; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
lean_dec_ref(x_474);
x_476 = lean_unbox(x_475);
if (x_476 == 0)
{
lean_object* x_477; 
lean_dec(x_451);
x_477 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_471, x_6);
lean_dec_ref(x_471);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; lean_object* x_479; uint8_t x_480; 
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 x_479 = x_477;
} else {
 lean_dec_ref(x_477);
 x_479 = lean_box(0);
}
x_480 = lean_unbox(x_478);
lean_dec(x_478);
if (x_480 == 0)
{
lean_object* x_481; 
lean_dec(x_475);
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_461);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
lean_ctor_set_uint8(x_34, 0, x_32);
if (lean_is_scalar(x_479)) {
 x_481 = lean_alloc_ctor(0, 1, 0);
} else {
 x_481 = x_479;
}
lean_ctor_set(x_481, 0, x_34);
return x_481;
}
else
{
lean_object* x_482; 
lean_dec(x_479);
lean_free_object(x_34);
x_482 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
lean_dec_ref(x_482);
x_484 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10;
x_485 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13;
x_486 = lean_unsigned_to_nat(4u);
x_487 = l_Lean_Expr_getBoundedAppFn(x_486, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_483);
x_488 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_487, x_483, x_485, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
lean_dec_ref(x_488);
x_490 = l_Lean_mkApp3(x_484, x_26, x_461, x_472);
x_491 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_492 = l_Lean_Expr_replaceFn(x_2, x_491);
x_493 = l_Lean_mkApp3(x_492, x_483, x_485, x_490);
x_494 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19));
x_495 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_496 = l_Lean_mkConst(x_494, x_495);
lean_inc_ref(x_18);
x_497 = l_Lean_mkApp3(x_496, x_29, x_21, x_18);
lean_inc_ref(x_18);
x_498 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_489, x_493, x_18, x_497, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; lean_object* x_503; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 x_500 = x_498;
} else {
 lean_dec_ref(x_498);
 x_500 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_501 = lean_alloc_ctor(1, 2, 1);
} else {
 x_501 = x_473;
}
lean_ctor_set(x_501, 0, x_18);
lean_ctor_set(x_501, 1, x_499);
x_502 = lean_unbox(x_475);
lean_dec(x_475);
lean_ctor_set_uint8(x_501, sizeof(void*)*2, x_502);
if (lean_is_scalar(x_500)) {
 x_503 = lean_alloc_ctor(0, 1, 0);
} else {
 x_503 = x_500;
}
lean_ctor_set(x_503, 0, x_501);
return x_503;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_475);
lean_dec(x_473);
lean_dec_ref(x_18);
x_504 = lean_ctor_get(x_498, 0);
lean_inc(x_504);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 x_505 = x_498;
} else {
 lean_dec_ref(x_498);
 x_505 = lean_box(0);
}
if (lean_is_scalar(x_505)) {
 x_506 = lean_alloc_ctor(1, 1, 0);
} else {
 x_506 = x_505;
}
lean_ctor_set(x_506, 0, x_504);
return x_506;
}
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_483);
lean_dec(x_475);
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_461);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_507 = lean_ctor_get(x_488, 0);
lean_inc(x_507);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 x_508 = x_488;
} else {
 lean_dec_ref(x_488);
 x_508 = lean_box(0);
}
if (lean_is_scalar(x_508)) {
 x_509 = lean_alloc_ctor(1, 1, 0);
} else {
 x_509 = x_508;
}
lean_ctor_set(x_509, 0, x_507);
return x_509;
}
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_475);
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_461);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_510 = lean_ctor_get(x_482, 0);
lean_inc(x_510);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 x_511 = x_482;
} else {
 lean_dec_ref(x_482);
 x_511 = lean_box(0);
}
if (lean_is_scalar(x_511)) {
 x_512 = lean_alloc_ctor(1, 1, 0);
} else {
 x_512 = x_511;
}
lean_ctor_set(x_512, 0, x_510);
return x_512;
}
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_475);
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_461);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_513 = lean_ctor_get(x_477, 0);
lean_inc(x_513);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 x_514 = x_477;
} else {
 lean_dec_ref(x_477);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(1, 1, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_513);
return x_515;
}
}
else
{
lean_object* x_516; 
lean_dec(x_475);
lean_dec_ref(x_471);
lean_free_object(x_34);
x_516 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
lean_dec_ref(x_516);
x_518 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22;
x_519 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25;
x_520 = lean_unsigned_to_nat(4u);
x_521 = l_Lean_Expr_getBoundedAppFn(x_520, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_517);
x_522 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_521, x_517, x_519, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
lean_dec_ref(x_522);
x_524 = l_Lean_mkApp3(x_518, x_26, x_461, x_472);
x_525 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_526 = l_Lean_Expr_replaceFn(x_2, x_525);
x_527 = l_Lean_mkApp3(x_526, x_517, x_519, x_524);
x_528 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27));
x_529 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_530 = l_Lean_mkConst(x_528, x_529);
lean_inc_ref(x_21);
x_531 = l_Lean_mkApp3(x_530, x_29, x_21, x_18);
lean_inc_ref(x_21);
x_532 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_523, x_527, x_21, x_531, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; lean_object* x_537; 
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 x_534 = x_532;
} else {
 lean_dec_ref(x_532);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_535 = lean_alloc_ctor(1, 2, 1);
} else {
 x_535 = x_473;
}
lean_ctor_set(x_535, 0, x_21);
lean_ctor_set(x_535, 1, x_533);
x_536 = lean_unbox(x_451);
lean_dec(x_451);
lean_ctor_set_uint8(x_535, sizeof(void*)*2, x_536);
if (lean_is_scalar(x_534)) {
 x_537 = lean_alloc_ctor(0, 1, 0);
} else {
 x_537 = x_534;
}
lean_ctor_set(x_537, 0, x_535);
return x_537;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_473);
lean_dec(x_451);
lean_dec_ref(x_21);
x_538 = lean_ctor_get(x_532, 0);
lean_inc(x_538);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 x_539 = x_532;
} else {
 lean_dec_ref(x_532);
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
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_517);
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_461);
lean_dec(x_451);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_541 = lean_ctor_get(x_522, 0);
lean_inc(x_541);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 x_542 = x_522;
} else {
 lean_dec_ref(x_522);
 x_542 = lean_box(0);
}
if (lean_is_scalar(x_542)) {
 x_543 = lean_alloc_ctor(1, 1, 0);
} else {
 x_543 = x_542;
}
lean_ctor_set(x_543, 0, x_541);
return x_543;
}
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; 
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_461);
lean_dec(x_451);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_544 = lean_ctor_get(x_516, 0);
lean_inc(x_544);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 x_545 = x_516;
} else {
 lean_dec_ref(x_516);
 x_545 = lean_box(0);
}
if (lean_is_scalar(x_545)) {
 x_546 = lean_alloc_ctor(1, 1, 0);
} else {
 x_546 = x_545;
}
lean_ctor_set(x_546, 0, x_544);
return x_546;
}
}
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec_ref(x_471);
lean_dec(x_461);
lean_dec(x_451);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_547 = lean_ctor_get(x_474, 0);
lean_inc(x_547);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 x_548 = x_474;
} else {
 lean_dec_ref(x_474);
 x_548 = lean_box(0);
}
if (lean_is_scalar(x_548)) {
 x_549 = lean_alloc_ctor(1, 1, 0);
} else {
 x_549 = x_548;
}
lean_ctor_set(x_549, 0, x_547);
return x_549;
}
}
}
else
{
lean_dec(x_461);
lean_dec(x_451);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
return x_465;
}
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_461);
lean_dec(x_451);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_550 = lean_ctor_get(x_463, 0);
lean_inc(x_550);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 x_551 = x_463;
} else {
 lean_dec_ref(x_463);
 x_551 = lean_box(0);
}
if (lean_is_scalar(x_551)) {
 x_552 = lean_alloc_ctor(1, 1, 0);
} else {
 x_552 = x_551;
}
lean_ctor_set(x_552, 0, x_550);
return x_552;
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
lean_dec(x_451);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_553 = lean_ctor_get(x_460, 0);
lean_inc(x_553);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 x_554 = x_460;
} else {
 lean_dec_ref(x_460);
 x_554 = lean_box(0);
}
if (lean_is_scalar(x_554)) {
 x_555 = lean_alloc_ctor(1, 1, 0);
} else {
 x_555 = x_554;
}
lean_ctor_set(x_555, 0, x_553);
return x_555;
}
}
else
{
uint8_t x_556; lean_object* x_557; 
lean_dec(x_457);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_556 = lean_unbox(x_451);
lean_dec(x_451);
lean_ctor_set_uint8(x_34, 0, x_556);
if (lean_is_scalar(x_458)) {
 x_557 = lean_alloc_ctor(0, 1, 0);
} else {
 x_557 = x_458;
}
lean_ctor_set(x_557, 0, x_34);
return x_557;
}
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_dec(x_451);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_558 = lean_ctor_get(x_456, 0);
lean_inc(x_558);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 x_559 = x_456;
} else {
 lean_dec_ref(x_456);
 x_559 = lean_box(0);
}
if (lean_is_scalar(x_559)) {
 x_560 = lean_alloc_ctor(1, 1, 0);
} else {
 x_560 = x_559;
}
lean_ctor_set(x_560, 0, x_558);
return x_560;
}
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; uint8_t x_566; lean_object* x_567; 
lean_dec(x_451);
lean_free_object(x_34);
lean_dec_ref(x_26);
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
x_561 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19));
x_562 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_563 = l_Lean_mkConst(x_561, x_562);
lean_inc_ref(x_18);
x_564 = l_Lean_mkApp3(x_563, x_29, x_21, x_18);
x_565 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_565, 0, x_18);
lean_ctor_set(x_565, 1, x_564);
x_566 = lean_unbox(x_38);
lean_dec(x_38);
lean_ctor_set_uint8(x_565, sizeof(void*)*2, x_566);
x_567 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_567, 0, x_565);
return x_567;
}
}
}
else
{
uint8_t x_568; 
lean_dec(x_38);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_568 = !lean_is_exclusive(x_40);
if (x_568 == 0)
{
return x_40;
}
else
{
lean_object* x_569; lean_object* x_570; 
x_569 = lean_ctor_get(x_40, 0);
lean_inc(x_569);
lean_dec(x_40);
x_570 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_570, 0, x_569);
return x_570;
}
}
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
lean_dec(x_38);
lean_free_object(x_34);
lean_dec_ref(x_26);
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
x_571 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27));
x_572 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_573 = l_Lean_mkConst(x_571, x_572);
lean_inc_ref(x_21);
x_574 = l_Lean_mkApp3(x_573, x_29, x_21, x_18);
x_575 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_575, 0, x_21);
lean_ctor_set(x_575, 1, x_574);
lean_ctor_set_uint8(x_575, sizeof(void*)*2, x_1);
lean_ctor_set(x_36, 0, x_575);
return x_36;
}
}
else
{
lean_object* x_576; uint8_t x_577; 
x_576 = lean_ctor_get(x_36, 0);
lean_inc(x_576);
lean_dec(x_36);
x_577 = lean_unbox(x_576);
if (x_577 == 0)
{
lean_object* x_578; 
x_578 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_26, x_6);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; lean_object* x_580; uint8_t x_581; 
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 x_580 = x_578;
} else {
 lean_dec_ref(x_578);
 x_580 = lean_box(0);
}
x_581 = lean_unbox(x_579);
if (x_581 == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
lean_dec(x_580);
lean_dec(x_576);
x_582 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4;
lean_inc_ref(x_26);
x_583 = l_Lean_Expr_app___override(x_582, x_26);
x_584 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_585 = l_Lean_Meta_trySynthInstance(x_583, x_584, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; lean_object* x_587; 
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 x_587 = x_585;
} else {
 lean_dec_ref(x_585);
 x_587 = lean_box(0);
}
if (lean_obj_tag(x_586) == 1)
{
lean_object* x_588; lean_object* x_589; 
lean_dec(x_587);
x_588 = lean_ctor_get(x_586, 0);
lean_inc(x_588);
lean_dec_ref(x_586);
x_589 = l_Lean_Meta_Sym_shareCommon___redArg(x_588, x_7);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
lean_dec_ref(x_589);
x_591 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_590);
lean_inc_ref(x_26);
x_592 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_591, x_26, x_590, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_593; lean_object* x_594; 
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
lean_dec_ref(x_592);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_594 = lean_sym_simp(x_593, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; 
x_595 = lean_ctor_get(x_594, 0);
lean_inc(x_595);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 x_596 = x_594;
} else {
 lean_dec_ref(x_594);
 x_596 = lean_box(0);
}
if (lean_obj_tag(x_595) == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_590);
lean_dec(x_579);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
if (lean_is_exclusive(x_595)) {
 x_597 = x_595;
} else {
 lean_dec_ref(x_595);
 x_597 = lean_box(0);
}
if (lean_is_scalar(x_597)) {
 x_598 = lean_alloc_ctor(0, 0, 1);
} else {
 x_598 = x_597;
}
lean_ctor_set_uint8(x_598, 0, x_32);
if (lean_is_scalar(x_596)) {
 x_599 = lean_alloc_ctor(0, 1, 0);
} else {
 x_599 = x_596;
}
lean_ctor_set(x_599, 0, x_598);
return x_599;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_596);
x_600 = lean_ctor_get(x_595, 0);
lean_inc_ref(x_600);
x_601 = lean_ctor_get(x_595, 1);
lean_inc_ref(x_601);
if (lean_is_exclusive(x_595)) {
 lean_ctor_release(x_595, 0);
 lean_ctor_release(x_595, 1);
 x_602 = x_595;
} else {
 lean_dec_ref(x_595);
 x_602 = lean_box(0);
}
x_603 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_600, x_6);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; uint8_t x_605; 
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
lean_dec_ref(x_603);
x_605 = lean_unbox(x_604);
if (x_605 == 0)
{
lean_object* x_606; 
lean_dec(x_579);
x_606 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_600, x_6);
lean_dec_ref(x_600);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; uint8_t x_609; 
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 x_608 = x_606;
} else {
 lean_dec_ref(x_606);
 x_608 = lean_box(0);
}
x_609 = lean_unbox(x_607);
lean_dec(x_607);
if (x_609 == 0)
{
lean_object* x_610; 
lean_dec(x_604);
lean_dec(x_602);
lean_dec_ref(x_601);
lean_dec(x_590);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
lean_ctor_set_uint8(x_34, 0, x_32);
if (lean_is_scalar(x_608)) {
 x_610 = lean_alloc_ctor(0, 1, 0);
} else {
 x_610 = x_608;
}
lean_ctor_set(x_610, 0, x_34);
return x_610;
}
else
{
lean_object* x_611; 
lean_dec(x_608);
lean_free_object(x_34);
x_611 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
lean_dec_ref(x_611);
x_613 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10;
x_614 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13;
x_615 = lean_unsigned_to_nat(4u);
x_616 = l_Lean_Expr_getBoundedAppFn(x_615, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_612);
x_617 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_616, x_612, x_614, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
lean_dec_ref(x_617);
x_619 = l_Lean_mkApp3(x_613, x_26, x_590, x_601);
x_620 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_621 = l_Lean_Expr_replaceFn(x_2, x_620);
x_622 = l_Lean_mkApp3(x_621, x_612, x_614, x_619);
x_623 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19));
x_624 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_625 = l_Lean_mkConst(x_623, x_624);
lean_inc_ref(x_18);
x_626 = l_Lean_mkApp3(x_625, x_29, x_21, x_18);
lean_inc_ref(x_18);
x_627 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_618, x_622, x_18, x_626, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_627) == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; lean_object* x_632; 
x_628 = lean_ctor_get(x_627, 0);
lean_inc(x_628);
if (lean_is_exclusive(x_627)) {
 lean_ctor_release(x_627, 0);
 x_629 = x_627;
} else {
 lean_dec_ref(x_627);
 x_629 = lean_box(0);
}
if (lean_is_scalar(x_602)) {
 x_630 = lean_alloc_ctor(1, 2, 1);
} else {
 x_630 = x_602;
}
lean_ctor_set(x_630, 0, x_18);
lean_ctor_set(x_630, 1, x_628);
x_631 = lean_unbox(x_604);
lean_dec(x_604);
lean_ctor_set_uint8(x_630, sizeof(void*)*2, x_631);
if (lean_is_scalar(x_629)) {
 x_632 = lean_alloc_ctor(0, 1, 0);
} else {
 x_632 = x_629;
}
lean_ctor_set(x_632, 0, x_630);
return x_632;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
lean_dec(x_604);
lean_dec(x_602);
lean_dec_ref(x_18);
x_633 = lean_ctor_get(x_627, 0);
lean_inc(x_633);
if (lean_is_exclusive(x_627)) {
 lean_ctor_release(x_627, 0);
 x_634 = x_627;
} else {
 lean_dec_ref(x_627);
 x_634 = lean_box(0);
}
if (lean_is_scalar(x_634)) {
 x_635 = lean_alloc_ctor(1, 1, 0);
} else {
 x_635 = x_634;
}
lean_ctor_set(x_635, 0, x_633);
return x_635;
}
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; 
lean_dec(x_612);
lean_dec(x_604);
lean_dec(x_602);
lean_dec_ref(x_601);
lean_dec(x_590);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_636 = lean_ctor_get(x_617, 0);
lean_inc(x_636);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 x_637 = x_617;
} else {
 lean_dec_ref(x_617);
 x_637 = lean_box(0);
}
if (lean_is_scalar(x_637)) {
 x_638 = lean_alloc_ctor(1, 1, 0);
} else {
 x_638 = x_637;
}
lean_ctor_set(x_638, 0, x_636);
return x_638;
}
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; 
lean_dec(x_604);
lean_dec(x_602);
lean_dec_ref(x_601);
lean_dec(x_590);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_639 = lean_ctor_get(x_611, 0);
lean_inc(x_639);
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 x_640 = x_611;
} else {
 lean_dec_ref(x_611);
 x_640 = lean_box(0);
}
if (lean_is_scalar(x_640)) {
 x_641 = lean_alloc_ctor(1, 1, 0);
} else {
 x_641 = x_640;
}
lean_ctor_set(x_641, 0, x_639);
return x_641;
}
}
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; 
lean_dec(x_604);
lean_dec(x_602);
lean_dec_ref(x_601);
lean_dec(x_590);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_642 = lean_ctor_get(x_606, 0);
lean_inc(x_642);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 x_643 = x_606;
} else {
 lean_dec_ref(x_606);
 x_643 = lean_box(0);
}
if (lean_is_scalar(x_643)) {
 x_644 = lean_alloc_ctor(1, 1, 0);
} else {
 x_644 = x_643;
}
lean_ctor_set(x_644, 0, x_642);
return x_644;
}
}
else
{
lean_object* x_645; 
lean_dec(x_604);
lean_dec_ref(x_600);
lean_free_object(x_34);
x_645 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_645) == 0)
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_646 = lean_ctor_get(x_645, 0);
lean_inc(x_646);
lean_dec_ref(x_645);
x_647 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22;
x_648 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25;
x_649 = lean_unsigned_to_nat(4u);
x_650 = l_Lean_Expr_getBoundedAppFn(x_649, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_646);
x_651 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_650, x_646, x_648, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
lean_dec_ref(x_651);
x_653 = l_Lean_mkApp3(x_647, x_26, x_590, x_601);
x_654 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_655 = l_Lean_Expr_replaceFn(x_2, x_654);
x_656 = l_Lean_mkApp3(x_655, x_646, x_648, x_653);
x_657 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27));
x_658 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_659 = l_Lean_mkConst(x_657, x_658);
lean_inc_ref(x_21);
x_660 = l_Lean_mkApp3(x_659, x_29, x_21, x_18);
lean_inc_ref(x_21);
x_661 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_652, x_656, x_21, x_660, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; lean_object* x_666; 
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 x_663 = x_661;
} else {
 lean_dec_ref(x_661);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_602)) {
 x_664 = lean_alloc_ctor(1, 2, 1);
} else {
 x_664 = x_602;
}
lean_ctor_set(x_664, 0, x_21);
lean_ctor_set(x_664, 1, x_662);
x_665 = lean_unbox(x_579);
lean_dec(x_579);
lean_ctor_set_uint8(x_664, sizeof(void*)*2, x_665);
if (lean_is_scalar(x_663)) {
 x_666 = lean_alloc_ctor(0, 1, 0);
} else {
 x_666 = x_663;
}
lean_ctor_set(x_666, 0, x_664);
return x_666;
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_602);
lean_dec(x_579);
lean_dec_ref(x_21);
x_667 = lean_ctor_get(x_661, 0);
lean_inc(x_667);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 x_668 = x_661;
} else {
 lean_dec_ref(x_661);
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
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
lean_dec(x_646);
lean_dec(x_602);
lean_dec_ref(x_601);
lean_dec(x_590);
lean_dec(x_579);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_670 = lean_ctor_get(x_651, 0);
lean_inc(x_670);
if (lean_is_exclusive(x_651)) {
 lean_ctor_release(x_651, 0);
 x_671 = x_651;
} else {
 lean_dec_ref(x_651);
 x_671 = lean_box(0);
}
if (lean_is_scalar(x_671)) {
 x_672 = lean_alloc_ctor(1, 1, 0);
} else {
 x_672 = x_671;
}
lean_ctor_set(x_672, 0, x_670);
return x_672;
}
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
lean_dec(x_602);
lean_dec_ref(x_601);
lean_dec(x_590);
lean_dec(x_579);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_673 = lean_ctor_get(x_645, 0);
lean_inc(x_673);
if (lean_is_exclusive(x_645)) {
 lean_ctor_release(x_645, 0);
 x_674 = x_645;
} else {
 lean_dec_ref(x_645);
 x_674 = lean_box(0);
}
if (lean_is_scalar(x_674)) {
 x_675 = lean_alloc_ctor(1, 1, 0);
} else {
 x_675 = x_674;
}
lean_ctor_set(x_675, 0, x_673);
return x_675;
}
}
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_dec(x_602);
lean_dec_ref(x_601);
lean_dec_ref(x_600);
lean_dec(x_590);
lean_dec(x_579);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_676 = lean_ctor_get(x_603, 0);
lean_inc(x_676);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 x_677 = x_603;
} else {
 lean_dec_ref(x_603);
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
lean_dec(x_590);
lean_dec(x_579);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
return x_594;
}
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; 
lean_dec(x_590);
lean_dec(x_579);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_679 = lean_ctor_get(x_592, 0);
lean_inc(x_679);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 x_680 = x_592;
} else {
 lean_dec_ref(x_592);
 x_680 = lean_box(0);
}
if (lean_is_scalar(x_680)) {
 x_681 = lean_alloc_ctor(1, 1, 0);
} else {
 x_681 = x_680;
}
lean_ctor_set(x_681, 0, x_679);
return x_681;
}
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_579);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_682 = lean_ctor_get(x_589, 0);
lean_inc(x_682);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 x_683 = x_589;
} else {
 lean_dec_ref(x_589);
 x_683 = lean_box(0);
}
if (lean_is_scalar(x_683)) {
 x_684 = lean_alloc_ctor(1, 1, 0);
} else {
 x_684 = x_683;
}
lean_ctor_set(x_684, 0, x_682);
return x_684;
}
}
else
{
uint8_t x_685; lean_object* x_686; 
lean_dec(x_586);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_685 = lean_unbox(x_579);
lean_dec(x_579);
lean_ctor_set_uint8(x_34, 0, x_685);
if (lean_is_scalar(x_587)) {
 x_686 = lean_alloc_ctor(0, 1, 0);
} else {
 x_686 = x_587;
}
lean_ctor_set(x_686, 0, x_34);
return x_686;
}
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_579);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_687 = lean_ctor_get(x_585, 0);
lean_inc(x_687);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 x_688 = x_585;
} else {
 lean_dec_ref(x_585);
 x_688 = lean_box(0);
}
if (lean_is_scalar(x_688)) {
 x_689 = lean_alloc_ctor(1, 1, 0);
} else {
 x_689 = x_688;
}
lean_ctor_set(x_689, 0, x_687);
return x_689;
}
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; uint8_t x_695; lean_object* x_696; 
lean_dec(x_579);
lean_free_object(x_34);
lean_dec_ref(x_26);
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
x_690 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19));
x_691 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_692 = l_Lean_mkConst(x_690, x_691);
lean_inc_ref(x_18);
x_693 = l_Lean_mkApp3(x_692, x_29, x_21, x_18);
x_694 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_694, 0, x_18);
lean_ctor_set(x_694, 1, x_693);
x_695 = lean_unbox(x_576);
lean_dec(x_576);
lean_ctor_set_uint8(x_694, sizeof(void*)*2, x_695);
if (lean_is_scalar(x_580)) {
 x_696 = lean_alloc_ctor(0, 1, 0);
} else {
 x_696 = x_580;
}
lean_ctor_set(x_696, 0, x_694);
return x_696;
}
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec(x_576);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_697 = lean_ctor_get(x_578, 0);
lean_inc(x_697);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 x_698 = x_578;
} else {
 lean_dec_ref(x_578);
 x_698 = lean_box(0);
}
if (lean_is_scalar(x_698)) {
 x_699 = lean_alloc_ctor(1, 1, 0);
} else {
 x_699 = x_698;
}
lean_ctor_set(x_699, 0, x_697);
return x_699;
}
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
lean_dec(x_576);
lean_free_object(x_34);
lean_dec_ref(x_26);
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
x_700 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27));
x_701 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_702 = l_Lean_mkConst(x_700, x_701);
lean_inc_ref(x_21);
x_703 = l_Lean_mkApp3(x_702, x_29, x_21, x_18);
x_704 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_704, 0, x_21);
lean_ctor_set(x_704, 1, x_703);
lean_ctor_set_uint8(x_704, sizeof(void*)*2, x_1);
x_705 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_705, 0, x_704);
return x_705;
}
}
}
else
{
uint8_t x_706; 
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_706 = !lean_is_exclusive(x_36);
if (x_706 == 0)
{
return x_36;
}
else
{
lean_object* x_707; lean_object* x_708; 
x_707 = lean_ctor_get(x_36, 0);
lean_inc(x_707);
lean_dec(x_36);
x_708 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_708, 0, x_707);
return x_708;
}
}
}
else
{
lean_object* x_709; 
lean_dec(x_34);
x_709 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_26, x_6);
if (lean_obj_tag(x_709) == 0)
{
lean_object* x_710; lean_object* x_711; uint8_t x_712; 
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 x_711 = x_709;
} else {
 lean_dec_ref(x_709);
 x_711 = lean_box(0);
}
x_712 = lean_unbox(x_710);
if (x_712 == 0)
{
lean_object* x_713; 
lean_dec(x_711);
x_713 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_26, x_6);
if (lean_obj_tag(x_713) == 0)
{
lean_object* x_714; lean_object* x_715; uint8_t x_716; 
x_714 = lean_ctor_get(x_713, 0);
lean_inc(x_714);
if (lean_is_exclusive(x_713)) {
 lean_ctor_release(x_713, 0);
 x_715 = x_713;
} else {
 lean_dec_ref(x_713);
 x_715 = lean_box(0);
}
x_716 = lean_unbox(x_714);
if (x_716 == 0)
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_715);
lean_dec(x_710);
x_717 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4;
lean_inc_ref(x_26);
x_718 = l_Lean_Expr_app___override(x_717, x_26);
x_719 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_720 = l_Lean_Meta_trySynthInstance(x_718, x_719, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_720) == 0)
{
lean_object* x_721; lean_object* x_722; 
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 x_722 = x_720;
} else {
 lean_dec_ref(x_720);
 x_722 = lean_box(0);
}
if (lean_obj_tag(x_721) == 1)
{
lean_object* x_723; lean_object* x_724; 
lean_dec(x_722);
x_723 = lean_ctor_get(x_721, 0);
lean_inc(x_723);
lean_dec_ref(x_721);
x_724 = l_Lean_Meta_Sym_shareCommon___redArg(x_723, x_7);
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
lean_dec_ref(x_724);
x_726 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_725);
lean_inc_ref(x_26);
x_727 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_726, x_26, x_725, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; 
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
lean_dec_ref(x_727);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_729 = lean_sym_simp(x_728, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
if (lean_is_exclusive(x_729)) {
 lean_ctor_release(x_729, 0);
 x_731 = x_729;
} else {
 lean_dec_ref(x_729);
 x_731 = lean_box(0);
}
if (lean_obj_tag(x_730) == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; 
lean_dec(x_725);
lean_dec(x_714);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
if (lean_is_exclusive(x_730)) {
 x_732 = x_730;
} else {
 lean_dec_ref(x_730);
 x_732 = lean_box(0);
}
if (lean_is_scalar(x_732)) {
 x_733 = lean_alloc_ctor(0, 0, 1);
} else {
 x_733 = x_732;
}
lean_ctor_set_uint8(x_733, 0, x_32);
if (lean_is_scalar(x_731)) {
 x_734 = lean_alloc_ctor(0, 1, 0);
} else {
 x_734 = x_731;
}
lean_ctor_set(x_734, 0, x_733);
return x_734;
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
lean_dec(x_731);
x_735 = lean_ctor_get(x_730, 0);
lean_inc_ref(x_735);
x_736 = lean_ctor_get(x_730, 1);
lean_inc_ref(x_736);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 x_737 = x_730;
} else {
 lean_dec_ref(x_730);
 x_737 = lean_box(0);
}
x_738 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_735, x_6);
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_739; uint8_t x_740; 
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
lean_dec_ref(x_738);
x_740 = lean_unbox(x_739);
if (x_740 == 0)
{
lean_object* x_741; 
lean_dec(x_714);
x_741 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_735, x_6);
lean_dec_ref(x_735);
if (lean_obj_tag(x_741) == 0)
{
lean_object* x_742; lean_object* x_743; uint8_t x_744; 
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
if (lean_is_exclusive(x_741)) {
 lean_ctor_release(x_741, 0);
 x_743 = x_741;
} else {
 lean_dec_ref(x_741);
 x_743 = lean_box(0);
}
x_744 = lean_unbox(x_742);
lean_dec(x_742);
if (x_744 == 0)
{
lean_object* x_745; lean_object* x_746; 
lean_dec(x_739);
lean_dec(x_737);
lean_dec_ref(x_736);
lean_dec(x_725);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_745 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_745, 0, x_32);
if (lean_is_scalar(x_743)) {
 x_746 = lean_alloc_ctor(0, 1, 0);
} else {
 x_746 = x_743;
}
lean_ctor_set(x_746, 0, x_745);
return x_746;
}
else
{
lean_object* x_747; 
lean_dec(x_743);
x_747 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_747) == 0)
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_748 = lean_ctor_get(x_747, 0);
lean_inc(x_748);
lean_dec_ref(x_747);
x_749 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10;
x_750 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13;
x_751 = lean_unsigned_to_nat(4u);
x_752 = l_Lean_Expr_getBoundedAppFn(x_751, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_748);
x_753 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_752, x_748, x_750, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_753) == 0)
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; 
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
lean_dec_ref(x_753);
x_755 = l_Lean_mkApp3(x_749, x_26, x_725, x_736);
x_756 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_757 = l_Lean_Expr_replaceFn(x_2, x_756);
x_758 = l_Lean_mkApp3(x_757, x_748, x_750, x_755);
x_759 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19));
x_760 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_761 = l_Lean_mkConst(x_759, x_760);
lean_inc_ref(x_18);
x_762 = l_Lean_mkApp3(x_761, x_29, x_21, x_18);
lean_inc_ref(x_18);
x_763 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_754, x_758, x_18, x_762, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_763) == 0)
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; uint8_t x_767; lean_object* x_768; 
x_764 = lean_ctor_get(x_763, 0);
lean_inc(x_764);
if (lean_is_exclusive(x_763)) {
 lean_ctor_release(x_763, 0);
 x_765 = x_763;
} else {
 lean_dec_ref(x_763);
 x_765 = lean_box(0);
}
if (lean_is_scalar(x_737)) {
 x_766 = lean_alloc_ctor(1, 2, 1);
} else {
 x_766 = x_737;
}
lean_ctor_set(x_766, 0, x_18);
lean_ctor_set(x_766, 1, x_764);
x_767 = lean_unbox(x_739);
lean_dec(x_739);
lean_ctor_set_uint8(x_766, sizeof(void*)*2, x_767);
if (lean_is_scalar(x_765)) {
 x_768 = lean_alloc_ctor(0, 1, 0);
} else {
 x_768 = x_765;
}
lean_ctor_set(x_768, 0, x_766);
return x_768;
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; 
lean_dec(x_739);
lean_dec(x_737);
lean_dec_ref(x_18);
x_769 = lean_ctor_get(x_763, 0);
lean_inc(x_769);
if (lean_is_exclusive(x_763)) {
 lean_ctor_release(x_763, 0);
 x_770 = x_763;
} else {
 lean_dec_ref(x_763);
 x_770 = lean_box(0);
}
if (lean_is_scalar(x_770)) {
 x_771 = lean_alloc_ctor(1, 1, 0);
} else {
 x_771 = x_770;
}
lean_ctor_set(x_771, 0, x_769);
return x_771;
}
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
lean_dec(x_748);
lean_dec(x_739);
lean_dec(x_737);
lean_dec_ref(x_736);
lean_dec(x_725);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_772 = lean_ctor_get(x_753, 0);
lean_inc(x_772);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 x_773 = x_753;
} else {
 lean_dec_ref(x_753);
 x_773 = lean_box(0);
}
if (lean_is_scalar(x_773)) {
 x_774 = lean_alloc_ctor(1, 1, 0);
} else {
 x_774 = x_773;
}
lean_ctor_set(x_774, 0, x_772);
return x_774;
}
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; 
lean_dec(x_739);
lean_dec(x_737);
lean_dec_ref(x_736);
lean_dec(x_725);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_775 = lean_ctor_get(x_747, 0);
lean_inc(x_775);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 x_776 = x_747;
} else {
 lean_dec_ref(x_747);
 x_776 = lean_box(0);
}
if (lean_is_scalar(x_776)) {
 x_777 = lean_alloc_ctor(1, 1, 0);
} else {
 x_777 = x_776;
}
lean_ctor_set(x_777, 0, x_775);
return x_777;
}
}
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
lean_dec(x_739);
lean_dec(x_737);
lean_dec_ref(x_736);
lean_dec(x_725);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_778 = lean_ctor_get(x_741, 0);
lean_inc(x_778);
if (lean_is_exclusive(x_741)) {
 lean_ctor_release(x_741, 0);
 x_779 = x_741;
} else {
 lean_dec_ref(x_741);
 x_779 = lean_box(0);
}
if (lean_is_scalar(x_779)) {
 x_780 = lean_alloc_ctor(1, 1, 0);
} else {
 x_780 = x_779;
}
lean_ctor_set(x_780, 0, x_778);
return x_780;
}
}
else
{
lean_object* x_781; 
lean_dec(x_739);
lean_dec_ref(x_735);
x_781 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_781) == 0)
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_782 = lean_ctor_get(x_781, 0);
lean_inc(x_782);
lean_dec_ref(x_781);
x_783 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22;
x_784 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25;
x_785 = lean_unsigned_to_nat(4u);
x_786 = l_Lean_Expr_getBoundedAppFn(x_785, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_782);
x_787 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_786, x_782, x_784, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_788 = lean_ctor_get(x_787, 0);
lean_inc(x_788);
lean_dec_ref(x_787);
x_789 = l_Lean_mkApp3(x_783, x_26, x_725, x_736);
x_790 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
lean_inc_ref(x_2);
x_791 = l_Lean_Expr_replaceFn(x_2, x_790);
x_792 = l_Lean_mkApp3(x_791, x_782, x_784, x_789);
x_793 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27));
x_794 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_795 = l_Lean_mkConst(x_793, x_794);
lean_inc_ref(x_21);
x_796 = l_Lean_mkApp3(x_795, x_29, x_21, x_18);
lean_inc_ref(x_21);
x_797 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_788, x_792, x_21, x_796, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_797) == 0)
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; uint8_t x_801; lean_object* x_802; 
x_798 = lean_ctor_get(x_797, 0);
lean_inc(x_798);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 x_799 = x_797;
} else {
 lean_dec_ref(x_797);
 x_799 = lean_box(0);
}
if (lean_is_scalar(x_737)) {
 x_800 = lean_alloc_ctor(1, 2, 1);
} else {
 x_800 = x_737;
}
lean_ctor_set(x_800, 0, x_21);
lean_ctor_set(x_800, 1, x_798);
x_801 = lean_unbox(x_714);
lean_dec(x_714);
lean_ctor_set_uint8(x_800, sizeof(void*)*2, x_801);
if (lean_is_scalar(x_799)) {
 x_802 = lean_alloc_ctor(0, 1, 0);
} else {
 x_802 = x_799;
}
lean_ctor_set(x_802, 0, x_800);
return x_802;
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; 
lean_dec(x_737);
lean_dec(x_714);
lean_dec_ref(x_21);
x_803 = lean_ctor_get(x_797, 0);
lean_inc(x_803);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 x_804 = x_797;
} else {
 lean_dec_ref(x_797);
 x_804 = lean_box(0);
}
if (lean_is_scalar(x_804)) {
 x_805 = lean_alloc_ctor(1, 1, 0);
} else {
 x_805 = x_804;
}
lean_ctor_set(x_805, 0, x_803);
return x_805;
}
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; 
lean_dec(x_782);
lean_dec(x_737);
lean_dec_ref(x_736);
lean_dec(x_725);
lean_dec(x_714);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_806 = lean_ctor_get(x_787, 0);
lean_inc(x_806);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 x_807 = x_787;
} else {
 lean_dec_ref(x_787);
 x_807 = lean_box(0);
}
if (lean_is_scalar(x_807)) {
 x_808 = lean_alloc_ctor(1, 1, 0);
} else {
 x_808 = x_807;
}
lean_ctor_set(x_808, 0, x_806);
return x_808;
}
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
lean_dec(x_737);
lean_dec_ref(x_736);
lean_dec(x_725);
lean_dec(x_714);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_809 = lean_ctor_get(x_781, 0);
lean_inc(x_809);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 x_810 = x_781;
} else {
 lean_dec_ref(x_781);
 x_810 = lean_box(0);
}
if (lean_is_scalar(x_810)) {
 x_811 = lean_alloc_ctor(1, 1, 0);
} else {
 x_811 = x_810;
}
lean_ctor_set(x_811, 0, x_809);
return x_811;
}
}
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; 
lean_dec(x_737);
lean_dec_ref(x_736);
lean_dec_ref(x_735);
lean_dec(x_725);
lean_dec(x_714);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_812 = lean_ctor_get(x_738, 0);
lean_inc(x_812);
if (lean_is_exclusive(x_738)) {
 lean_ctor_release(x_738, 0);
 x_813 = x_738;
} else {
 lean_dec_ref(x_738);
 x_813 = lean_box(0);
}
if (lean_is_scalar(x_813)) {
 x_814 = lean_alloc_ctor(1, 1, 0);
} else {
 x_814 = x_813;
}
lean_ctor_set(x_814, 0, x_812);
return x_814;
}
}
}
else
{
lean_dec(x_725);
lean_dec(x_714);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
return x_729;
}
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; 
lean_dec(x_725);
lean_dec(x_714);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_815 = lean_ctor_get(x_727, 0);
lean_inc(x_815);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 x_816 = x_727;
} else {
 lean_dec_ref(x_727);
 x_816 = lean_box(0);
}
if (lean_is_scalar(x_816)) {
 x_817 = lean_alloc_ctor(1, 1, 0);
} else {
 x_817 = x_816;
}
lean_ctor_set(x_817, 0, x_815);
return x_817;
}
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; 
lean_dec(x_714);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_818 = lean_ctor_get(x_724, 0);
lean_inc(x_818);
if (lean_is_exclusive(x_724)) {
 lean_ctor_release(x_724, 0);
 x_819 = x_724;
} else {
 lean_dec_ref(x_724);
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
else
{
lean_object* x_821; uint8_t x_822; lean_object* x_823; 
lean_dec(x_721);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_821 = lean_alloc_ctor(0, 0, 1);
x_822 = lean_unbox(x_714);
lean_dec(x_714);
lean_ctor_set_uint8(x_821, 0, x_822);
if (lean_is_scalar(x_722)) {
 x_823 = lean_alloc_ctor(0, 1, 0);
} else {
 x_823 = x_722;
}
lean_ctor_set(x_823, 0, x_821);
return x_823;
}
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; 
lean_dec(x_714);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_824 = lean_ctor_get(x_720, 0);
lean_inc(x_824);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 x_825 = x_720;
} else {
 lean_dec_ref(x_720);
 x_825 = lean_box(0);
}
if (lean_is_scalar(x_825)) {
 x_826 = lean_alloc_ctor(1, 1, 0);
} else {
 x_826 = x_825;
}
lean_ctor_set(x_826, 0, x_824);
return x_826;
}
}
else
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; uint8_t x_832; lean_object* x_833; 
lean_dec(x_714);
lean_dec_ref(x_26);
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
x_827 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19));
x_828 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_829 = l_Lean_mkConst(x_827, x_828);
lean_inc_ref(x_18);
x_830 = l_Lean_mkApp3(x_829, x_29, x_21, x_18);
x_831 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_831, 0, x_18);
lean_ctor_set(x_831, 1, x_830);
x_832 = lean_unbox(x_710);
lean_dec(x_710);
lean_ctor_set_uint8(x_831, sizeof(void*)*2, x_832);
if (lean_is_scalar(x_715)) {
 x_833 = lean_alloc_ctor(0, 1, 0);
} else {
 x_833 = x_715;
}
lean_ctor_set(x_833, 0, x_831);
return x_833;
}
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; 
lean_dec(x_710);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_834 = lean_ctor_get(x_713, 0);
lean_inc(x_834);
if (lean_is_exclusive(x_713)) {
 lean_ctor_release(x_713, 0);
 x_835 = x_713;
} else {
 lean_dec_ref(x_713);
 x_835 = lean_box(0);
}
if (lean_is_scalar(x_835)) {
 x_836 = lean_alloc_ctor(1, 1, 0);
} else {
 x_836 = x_835;
}
lean_ctor_set(x_836, 0, x_834);
return x_836;
}
}
else
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_dec(x_710);
lean_dec_ref(x_26);
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
x_837 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27));
x_838 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_839 = l_Lean_mkConst(x_837, x_838);
lean_inc_ref(x_21);
x_840 = l_Lean_mkApp3(x_839, x_29, x_21, x_18);
x_841 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_841, 0, x_21);
lean_ctor_set(x_841, 1, x_840);
lean_ctor_set_uint8(x_841, sizeof(void*)*2, x_1);
if (lean_is_scalar(x_711)) {
 x_842 = lean_alloc_ctor(0, 1, 0);
} else {
 x_842 = x_711;
}
lean_ctor_set(x_842, 0, x_841);
return x_842;
}
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_843 = lean_ctor_get(x_709, 0);
lean_inc(x_843);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 x_844 = x_709;
} else {
 lean_dec_ref(x_709);
 x_844 = lean_box(0);
}
if (lean_is_scalar(x_844)) {
 x_845 = lean_alloc_ctor(1, 1, 0);
} else {
 x_845 = x_844;
}
lean_ctor_set(x_845, 0, x_843);
return x_845;
}
}
}
else
{
uint8_t x_846; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
x_846 = !lean_is_exclusive(x_34);
if (x_846 == 0)
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; 
x_847 = lean_ctor_get(x_34, 0);
x_848 = lean_ctor_get(x_34, 1);
x_849 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_847, x_6);
if (lean_obj_tag(x_849) == 0)
{
uint8_t x_850; 
x_850 = !lean_is_exclusive(x_849);
if (x_850 == 0)
{
lean_object* x_851; uint8_t x_852; 
x_851 = lean_ctor_get(x_849, 0);
x_852 = lean_unbox(x_851);
if (x_852 == 0)
{
lean_object* x_853; 
lean_free_object(x_849);
x_853 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_847, x_6);
if (lean_obj_tag(x_853) == 0)
{
uint8_t x_854; 
x_854 = !lean_is_exclusive(x_853);
if (x_854 == 0)
{
lean_object* x_855; uint8_t x_856; 
x_855 = lean_ctor_get(x_853, 0);
x_856 = lean_unbox(x_855);
if (x_856 == 0)
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; 
lean_free_object(x_853);
lean_dec(x_851);
x_857 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4;
lean_inc_ref(x_847);
x_858 = l_Lean_Expr_app___override(x_857, x_847);
x_859 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_860 = l_Lean_Meta_trySynthInstance(x_858, x_859, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_860) == 0)
{
uint8_t x_861; 
x_861 = !lean_is_exclusive(x_860);
if (x_861 == 0)
{
lean_object* x_862; 
x_862 = lean_ctor_get(x_860, 0);
if (lean_obj_tag(x_862) == 1)
{
lean_object* x_863; lean_object* x_864; 
lean_free_object(x_860);
x_863 = lean_ctor_get(x_862, 0);
lean_inc(x_863);
lean_dec_ref(x_862);
x_864 = l_Lean_Meta_Sym_shareCommon___redArg(x_863, x_7);
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
lean_dec_ref(x_864);
x_866 = lean_unsigned_to_nat(4u);
x_867 = l_Lean_Expr_getBoundedAppFn(x_866, x_2);
lean_inc(x_865);
lean_inc_ref(x_847);
x_868 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_867, x_847, x_865, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_868) == 0)
{
uint8_t x_869; 
x_869 = !lean_is_exclusive(x_868);
if (x_869 == 0)
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; uint8_t x_874; 
x_870 = lean_ctor_get(x_868, 0);
x_871 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_872 = l_Lean_Expr_replaceFn(x_2, x_871);
x_873 = l_Lean_mkApp3(x_872, x_847, x_865, x_848);
lean_ctor_set(x_34, 1, x_873);
lean_ctor_set(x_34, 0, x_870);
x_874 = lean_unbox(x_855);
lean_dec(x_855);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_874);
lean_ctor_set(x_868, 0, x_34);
return x_868;
}
else
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; uint8_t x_879; lean_object* x_880; 
x_875 = lean_ctor_get(x_868, 0);
lean_inc(x_875);
lean_dec(x_868);
x_876 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_877 = l_Lean_Expr_replaceFn(x_2, x_876);
x_878 = l_Lean_mkApp3(x_877, x_847, x_865, x_848);
lean_ctor_set(x_34, 1, x_878);
lean_ctor_set(x_34, 0, x_875);
x_879 = lean_unbox(x_855);
lean_dec(x_855);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_879);
x_880 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_880, 0, x_34);
return x_880;
}
}
else
{
uint8_t x_881; 
lean_dec(x_865);
lean_dec(x_855);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
lean_dec_ref(x_2);
x_881 = !lean_is_exclusive(x_868);
if (x_881 == 0)
{
return x_868;
}
else
{
lean_object* x_882; lean_object* x_883; 
x_882 = lean_ctor_get(x_868, 0);
lean_inc(x_882);
lean_dec(x_868);
x_883 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_883, 0, x_882);
return x_883;
}
}
}
else
{
uint8_t x_884; 
lean_dec(x_855);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
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
x_884 = !lean_is_exclusive(x_864);
if (x_884 == 0)
{
return x_864;
}
else
{
lean_object* x_885; lean_object* x_886; 
x_885 = lean_ctor_get(x_864, 0);
lean_inc(x_885);
lean_dec(x_864);
x_886 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_886, 0, x_885);
return x_886;
}
}
}
else
{
lean_object* x_887; uint8_t x_888; 
lean_dec(x_862);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
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
x_887 = lean_alloc_ctor(0, 0, 1);
x_888 = lean_unbox(x_855);
lean_dec(x_855);
lean_ctor_set_uint8(x_887, 0, x_888);
lean_ctor_set(x_860, 0, x_887);
return x_860;
}
}
else
{
lean_object* x_889; 
x_889 = lean_ctor_get(x_860, 0);
lean_inc(x_889);
lean_dec(x_860);
if (lean_obj_tag(x_889) == 1)
{
lean_object* x_890; lean_object* x_891; 
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
lean_dec_ref(x_889);
x_891 = l_Lean_Meta_Sym_shareCommon___redArg(x_890, x_7);
if (lean_obj_tag(x_891) == 0)
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; 
x_892 = lean_ctor_get(x_891, 0);
lean_inc(x_892);
lean_dec_ref(x_891);
x_893 = lean_unsigned_to_nat(4u);
x_894 = l_Lean_Expr_getBoundedAppFn(x_893, x_2);
lean_inc(x_892);
lean_inc_ref(x_847);
x_895 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_894, x_847, x_892, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_895) == 0)
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; uint8_t x_901; lean_object* x_902; 
x_896 = lean_ctor_get(x_895, 0);
lean_inc(x_896);
if (lean_is_exclusive(x_895)) {
 lean_ctor_release(x_895, 0);
 x_897 = x_895;
} else {
 lean_dec_ref(x_895);
 x_897 = lean_box(0);
}
x_898 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_899 = l_Lean_Expr_replaceFn(x_2, x_898);
x_900 = l_Lean_mkApp3(x_899, x_847, x_892, x_848);
lean_ctor_set(x_34, 1, x_900);
lean_ctor_set(x_34, 0, x_896);
x_901 = lean_unbox(x_855);
lean_dec(x_855);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_901);
if (lean_is_scalar(x_897)) {
 x_902 = lean_alloc_ctor(0, 1, 0);
} else {
 x_902 = x_897;
}
lean_ctor_set(x_902, 0, x_34);
return x_902;
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; 
lean_dec(x_892);
lean_dec(x_855);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
lean_dec_ref(x_2);
x_903 = lean_ctor_get(x_895, 0);
lean_inc(x_903);
if (lean_is_exclusive(x_895)) {
 lean_ctor_release(x_895, 0);
 x_904 = x_895;
} else {
 lean_dec_ref(x_895);
 x_904 = lean_box(0);
}
if (lean_is_scalar(x_904)) {
 x_905 = lean_alloc_ctor(1, 1, 0);
} else {
 x_905 = x_904;
}
lean_ctor_set(x_905, 0, x_903);
return x_905;
}
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; 
lean_dec(x_855);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
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
x_906 = lean_ctor_get(x_891, 0);
lean_inc(x_906);
if (lean_is_exclusive(x_891)) {
 lean_ctor_release(x_891, 0);
 x_907 = x_891;
} else {
 lean_dec_ref(x_891);
 x_907 = lean_box(0);
}
if (lean_is_scalar(x_907)) {
 x_908 = lean_alloc_ctor(1, 1, 0);
} else {
 x_908 = x_907;
}
lean_ctor_set(x_908, 0, x_906);
return x_908;
}
}
else
{
lean_object* x_909; uint8_t x_910; lean_object* x_911; 
lean_dec(x_889);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
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
x_909 = lean_alloc_ctor(0, 0, 1);
x_910 = lean_unbox(x_855);
lean_dec(x_855);
lean_ctor_set_uint8(x_909, 0, x_910);
x_911 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_911, 0, x_909);
return x_911;
}
}
}
else
{
uint8_t x_912; 
lean_dec(x_855);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
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
x_912 = !lean_is_exclusive(x_860);
if (x_912 == 0)
{
return x_860;
}
else
{
lean_object* x_913; lean_object* x_914; 
x_913 = lean_ctor_get(x_860, 0);
lean_inc(x_913);
lean_dec(x_860);
x_914 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_914, 0, x_913);
return x_914;
}
}
}
else
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; uint8_t x_918; 
lean_dec(x_855);
lean_dec_ref(x_847);
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
x_915 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__29));
x_916 = l_Lean_Expr_replaceFn(x_2, x_915);
x_917 = l_Lean_Expr_app___override(x_916, x_848);
lean_ctor_set(x_34, 1, x_917);
lean_ctor_set(x_34, 0, x_18);
x_918 = lean_unbox(x_851);
lean_dec(x_851);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_918);
lean_ctor_set(x_853, 0, x_34);
return x_853;
}
}
else
{
lean_object* x_919; uint8_t x_920; 
x_919 = lean_ctor_get(x_853, 0);
lean_inc(x_919);
lean_dec(x_853);
x_920 = lean_unbox(x_919);
if (x_920 == 0)
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; 
lean_dec(x_851);
x_921 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4;
lean_inc_ref(x_847);
x_922 = l_Lean_Expr_app___override(x_921, x_847);
x_923 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_924 = l_Lean_Meta_trySynthInstance(x_922, x_923, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_924) == 0)
{
lean_object* x_925; lean_object* x_926; 
x_925 = lean_ctor_get(x_924, 0);
lean_inc(x_925);
if (lean_is_exclusive(x_924)) {
 lean_ctor_release(x_924, 0);
 x_926 = x_924;
} else {
 lean_dec_ref(x_924);
 x_926 = lean_box(0);
}
if (lean_obj_tag(x_925) == 1)
{
lean_object* x_927; lean_object* x_928; 
lean_dec(x_926);
x_927 = lean_ctor_get(x_925, 0);
lean_inc(x_927);
lean_dec_ref(x_925);
x_928 = l_Lean_Meta_Sym_shareCommon___redArg(x_927, x_7);
if (lean_obj_tag(x_928) == 0)
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; 
x_929 = lean_ctor_get(x_928, 0);
lean_inc(x_929);
lean_dec_ref(x_928);
x_930 = lean_unsigned_to_nat(4u);
x_931 = l_Lean_Expr_getBoundedAppFn(x_930, x_2);
lean_inc(x_929);
lean_inc_ref(x_847);
x_932 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_931, x_847, x_929, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_932) == 0)
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; uint8_t x_938; lean_object* x_939; 
x_933 = lean_ctor_get(x_932, 0);
lean_inc(x_933);
if (lean_is_exclusive(x_932)) {
 lean_ctor_release(x_932, 0);
 x_934 = x_932;
} else {
 lean_dec_ref(x_932);
 x_934 = lean_box(0);
}
x_935 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_936 = l_Lean_Expr_replaceFn(x_2, x_935);
x_937 = l_Lean_mkApp3(x_936, x_847, x_929, x_848);
lean_ctor_set(x_34, 1, x_937);
lean_ctor_set(x_34, 0, x_933);
x_938 = lean_unbox(x_919);
lean_dec(x_919);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_938);
if (lean_is_scalar(x_934)) {
 x_939 = lean_alloc_ctor(0, 1, 0);
} else {
 x_939 = x_934;
}
lean_ctor_set(x_939, 0, x_34);
return x_939;
}
else
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; 
lean_dec(x_929);
lean_dec(x_919);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
lean_dec_ref(x_2);
x_940 = lean_ctor_get(x_932, 0);
lean_inc(x_940);
if (lean_is_exclusive(x_932)) {
 lean_ctor_release(x_932, 0);
 x_941 = x_932;
} else {
 lean_dec_ref(x_932);
 x_941 = lean_box(0);
}
if (lean_is_scalar(x_941)) {
 x_942 = lean_alloc_ctor(1, 1, 0);
} else {
 x_942 = x_941;
}
lean_ctor_set(x_942, 0, x_940);
return x_942;
}
}
else
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; 
lean_dec(x_919);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
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
x_943 = lean_ctor_get(x_928, 0);
lean_inc(x_943);
if (lean_is_exclusive(x_928)) {
 lean_ctor_release(x_928, 0);
 x_944 = x_928;
} else {
 lean_dec_ref(x_928);
 x_944 = lean_box(0);
}
if (lean_is_scalar(x_944)) {
 x_945 = lean_alloc_ctor(1, 1, 0);
} else {
 x_945 = x_944;
}
lean_ctor_set(x_945, 0, x_943);
return x_945;
}
}
else
{
lean_object* x_946; uint8_t x_947; lean_object* x_948; 
lean_dec(x_925);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
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
x_946 = lean_alloc_ctor(0, 0, 1);
x_947 = lean_unbox(x_919);
lean_dec(x_919);
lean_ctor_set_uint8(x_946, 0, x_947);
if (lean_is_scalar(x_926)) {
 x_948 = lean_alloc_ctor(0, 1, 0);
} else {
 x_948 = x_926;
}
lean_ctor_set(x_948, 0, x_946);
return x_948;
}
}
else
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; 
lean_dec(x_919);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
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
x_949 = lean_ctor_get(x_924, 0);
lean_inc(x_949);
if (lean_is_exclusive(x_924)) {
 lean_ctor_release(x_924, 0);
 x_950 = x_924;
} else {
 lean_dec_ref(x_924);
 x_950 = lean_box(0);
}
if (lean_is_scalar(x_950)) {
 x_951 = lean_alloc_ctor(1, 1, 0);
} else {
 x_951 = x_950;
}
lean_ctor_set(x_951, 0, x_949);
return x_951;
}
}
else
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; uint8_t x_955; lean_object* x_956; 
lean_dec(x_919);
lean_dec_ref(x_847);
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
x_952 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__29));
x_953 = l_Lean_Expr_replaceFn(x_2, x_952);
x_954 = l_Lean_Expr_app___override(x_953, x_848);
lean_ctor_set(x_34, 1, x_954);
lean_ctor_set(x_34, 0, x_18);
x_955 = lean_unbox(x_851);
lean_dec(x_851);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_955);
x_956 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_956, 0, x_34);
return x_956;
}
}
}
else
{
uint8_t x_957; 
lean_dec(x_851);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
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
x_957 = !lean_is_exclusive(x_853);
if (x_957 == 0)
{
return x_853;
}
else
{
lean_object* x_958; lean_object* x_959; 
x_958 = lean_ctor_get(x_853, 0);
lean_inc(x_958);
lean_dec(x_853);
x_959 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_959, 0, x_958);
return x_959;
}
}
}
else
{
lean_object* x_960; lean_object* x_961; lean_object* x_962; 
lean_dec(x_851);
lean_dec_ref(x_847);
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
x_960 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__31));
x_961 = l_Lean_Expr_replaceFn(x_2, x_960);
x_962 = l_Lean_Expr_app___override(x_961, x_848);
lean_ctor_set(x_34, 1, x_962);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_1);
lean_ctor_set(x_849, 0, x_34);
return x_849;
}
}
else
{
lean_object* x_963; uint8_t x_964; 
x_963 = lean_ctor_get(x_849, 0);
lean_inc(x_963);
lean_dec(x_849);
x_964 = lean_unbox(x_963);
if (x_964 == 0)
{
lean_object* x_965; 
x_965 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_847, x_6);
if (lean_obj_tag(x_965) == 0)
{
lean_object* x_966; lean_object* x_967; uint8_t x_968; 
x_966 = lean_ctor_get(x_965, 0);
lean_inc(x_966);
if (lean_is_exclusive(x_965)) {
 lean_ctor_release(x_965, 0);
 x_967 = x_965;
} else {
 lean_dec_ref(x_965);
 x_967 = lean_box(0);
}
x_968 = lean_unbox(x_966);
if (x_968 == 0)
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; 
lean_dec(x_967);
lean_dec(x_963);
x_969 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4;
lean_inc_ref(x_847);
x_970 = l_Lean_Expr_app___override(x_969, x_847);
x_971 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_972 = l_Lean_Meta_trySynthInstance(x_970, x_971, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_972) == 0)
{
lean_object* x_973; lean_object* x_974; 
x_973 = lean_ctor_get(x_972, 0);
lean_inc(x_973);
if (lean_is_exclusive(x_972)) {
 lean_ctor_release(x_972, 0);
 x_974 = x_972;
} else {
 lean_dec_ref(x_972);
 x_974 = lean_box(0);
}
if (lean_obj_tag(x_973) == 1)
{
lean_object* x_975; lean_object* x_976; 
lean_dec(x_974);
x_975 = lean_ctor_get(x_973, 0);
lean_inc(x_975);
lean_dec_ref(x_973);
x_976 = l_Lean_Meta_Sym_shareCommon___redArg(x_975, x_7);
if (lean_obj_tag(x_976) == 0)
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; 
x_977 = lean_ctor_get(x_976, 0);
lean_inc(x_977);
lean_dec_ref(x_976);
x_978 = lean_unsigned_to_nat(4u);
x_979 = l_Lean_Expr_getBoundedAppFn(x_978, x_2);
lean_inc(x_977);
lean_inc_ref(x_847);
x_980 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_979, x_847, x_977, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; uint8_t x_986; lean_object* x_987; 
x_981 = lean_ctor_get(x_980, 0);
lean_inc(x_981);
if (lean_is_exclusive(x_980)) {
 lean_ctor_release(x_980, 0);
 x_982 = x_980;
} else {
 lean_dec_ref(x_980);
 x_982 = lean_box(0);
}
x_983 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_984 = l_Lean_Expr_replaceFn(x_2, x_983);
x_985 = l_Lean_mkApp3(x_984, x_847, x_977, x_848);
lean_ctor_set(x_34, 1, x_985);
lean_ctor_set(x_34, 0, x_981);
x_986 = lean_unbox(x_966);
lean_dec(x_966);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_986);
if (lean_is_scalar(x_982)) {
 x_987 = lean_alloc_ctor(0, 1, 0);
} else {
 x_987 = x_982;
}
lean_ctor_set(x_987, 0, x_34);
return x_987;
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; 
lean_dec(x_977);
lean_dec(x_966);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
lean_dec_ref(x_2);
x_988 = lean_ctor_get(x_980, 0);
lean_inc(x_988);
if (lean_is_exclusive(x_980)) {
 lean_ctor_release(x_980, 0);
 x_989 = x_980;
} else {
 lean_dec_ref(x_980);
 x_989 = lean_box(0);
}
if (lean_is_scalar(x_989)) {
 x_990 = lean_alloc_ctor(1, 1, 0);
} else {
 x_990 = x_989;
}
lean_ctor_set(x_990, 0, x_988);
return x_990;
}
}
else
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; 
lean_dec(x_966);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
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
x_991 = lean_ctor_get(x_976, 0);
lean_inc(x_991);
if (lean_is_exclusive(x_976)) {
 lean_ctor_release(x_976, 0);
 x_992 = x_976;
} else {
 lean_dec_ref(x_976);
 x_992 = lean_box(0);
}
if (lean_is_scalar(x_992)) {
 x_993 = lean_alloc_ctor(1, 1, 0);
} else {
 x_993 = x_992;
}
lean_ctor_set(x_993, 0, x_991);
return x_993;
}
}
else
{
lean_object* x_994; uint8_t x_995; lean_object* x_996; 
lean_dec(x_973);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
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
x_994 = lean_alloc_ctor(0, 0, 1);
x_995 = lean_unbox(x_966);
lean_dec(x_966);
lean_ctor_set_uint8(x_994, 0, x_995);
if (lean_is_scalar(x_974)) {
 x_996 = lean_alloc_ctor(0, 1, 0);
} else {
 x_996 = x_974;
}
lean_ctor_set(x_996, 0, x_994);
return x_996;
}
}
else
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; 
lean_dec(x_966);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
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
x_997 = lean_ctor_get(x_972, 0);
lean_inc(x_997);
if (lean_is_exclusive(x_972)) {
 lean_ctor_release(x_972, 0);
 x_998 = x_972;
} else {
 lean_dec_ref(x_972);
 x_998 = lean_box(0);
}
if (lean_is_scalar(x_998)) {
 x_999 = lean_alloc_ctor(1, 1, 0);
} else {
 x_999 = x_998;
}
lean_ctor_set(x_999, 0, x_997);
return x_999;
}
}
else
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; uint8_t x_1003; lean_object* x_1004; 
lean_dec(x_966);
lean_dec_ref(x_847);
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
x_1000 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__29));
x_1001 = l_Lean_Expr_replaceFn(x_2, x_1000);
x_1002 = l_Lean_Expr_app___override(x_1001, x_848);
lean_ctor_set(x_34, 1, x_1002);
lean_ctor_set(x_34, 0, x_18);
x_1003 = lean_unbox(x_963);
lean_dec(x_963);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_1003);
if (lean_is_scalar(x_967)) {
 x_1004 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1004 = x_967;
}
lean_ctor_set(x_1004, 0, x_34);
return x_1004;
}
}
else
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; 
lean_dec(x_963);
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
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
x_1005 = lean_ctor_get(x_965, 0);
lean_inc(x_1005);
if (lean_is_exclusive(x_965)) {
 lean_ctor_release(x_965, 0);
 x_1006 = x_965;
} else {
 lean_dec_ref(x_965);
 x_1006 = lean_box(0);
}
if (lean_is_scalar(x_1006)) {
 x_1007 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1007 = x_1006;
}
lean_ctor_set(x_1007, 0, x_1005);
return x_1007;
}
}
else
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
lean_dec(x_963);
lean_dec_ref(x_847);
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
x_1008 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__31));
x_1009 = l_Lean_Expr_replaceFn(x_2, x_1008);
x_1010 = l_Lean_Expr_app___override(x_1009, x_848);
lean_ctor_set(x_34, 1, x_1010);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_1);
x_1011 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1011, 0, x_34);
return x_1011;
}
}
}
else
{
uint8_t x_1012; 
lean_free_object(x_34);
lean_dec_ref(x_848);
lean_dec_ref(x_847);
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
x_1012 = !lean_is_exclusive(x_849);
if (x_1012 == 0)
{
return x_849;
}
else
{
lean_object* x_1013; lean_object* x_1014; 
x_1013 = lean_ctor_get(x_849, 0);
lean_inc(x_1013);
lean_dec(x_849);
x_1014 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1014, 0, x_1013);
return x_1014;
}
}
}
else
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
x_1015 = lean_ctor_get(x_34, 0);
x_1016 = lean_ctor_get(x_34, 1);
lean_inc(x_1016);
lean_inc(x_1015);
lean_dec(x_34);
x_1017 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_1015, x_6);
if (lean_obj_tag(x_1017) == 0)
{
lean_object* x_1018; lean_object* x_1019; uint8_t x_1020; 
x_1018 = lean_ctor_get(x_1017, 0);
lean_inc(x_1018);
if (lean_is_exclusive(x_1017)) {
 lean_ctor_release(x_1017, 0);
 x_1019 = x_1017;
} else {
 lean_dec_ref(x_1017);
 x_1019 = lean_box(0);
}
x_1020 = lean_unbox(x_1018);
if (x_1020 == 0)
{
lean_object* x_1021; 
lean_dec(x_1019);
x_1021 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_1015, x_6);
if (lean_obj_tag(x_1021) == 0)
{
lean_object* x_1022; lean_object* x_1023; uint8_t x_1024; 
x_1022 = lean_ctor_get(x_1021, 0);
lean_inc(x_1022);
if (lean_is_exclusive(x_1021)) {
 lean_ctor_release(x_1021, 0);
 x_1023 = x_1021;
} else {
 lean_dec_ref(x_1021);
 x_1023 = lean_box(0);
}
x_1024 = lean_unbox(x_1022);
if (x_1024 == 0)
{
lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
lean_dec(x_1023);
lean_dec(x_1018);
x_1025 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4;
lean_inc_ref(x_1015);
x_1026 = l_Lean_Expr_app___override(x_1025, x_1015);
x_1027 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_1028 = l_Lean_Meta_trySynthInstance(x_1026, x_1027, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1028) == 0)
{
lean_object* x_1029; lean_object* x_1030; 
x_1029 = lean_ctor_get(x_1028, 0);
lean_inc(x_1029);
if (lean_is_exclusive(x_1028)) {
 lean_ctor_release(x_1028, 0);
 x_1030 = x_1028;
} else {
 lean_dec_ref(x_1028);
 x_1030 = lean_box(0);
}
if (lean_obj_tag(x_1029) == 1)
{
lean_object* x_1031; lean_object* x_1032; 
lean_dec(x_1030);
x_1031 = lean_ctor_get(x_1029, 0);
lean_inc(x_1031);
lean_dec_ref(x_1029);
x_1032 = l_Lean_Meta_Sym_shareCommon___redArg(x_1031, x_7);
if (lean_obj_tag(x_1032) == 0)
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
x_1033 = lean_ctor_get(x_1032, 0);
lean_inc(x_1033);
lean_dec_ref(x_1032);
x_1034 = lean_unsigned_to_nat(4u);
x_1035 = l_Lean_Expr_getBoundedAppFn(x_1034, x_2);
lean_inc(x_1033);
lean_inc_ref(x_1015);
x_1036 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_1035, x_1015, x_1033, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_1036) == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; uint8_t x_1043; lean_object* x_1044; 
x_1037 = lean_ctor_get(x_1036, 0);
lean_inc(x_1037);
if (lean_is_exclusive(x_1036)) {
 lean_ctor_release(x_1036, 0);
 x_1038 = x_1036;
} else {
 lean_dec_ref(x_1036);
 x_1038 = lean_box(0);
}
x_1039 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_1040 = l_Lean_Expr_replaceFn(x_2, x_1039);
x_1041 = l_Lean_mkApp3(x_1040, x_1015, x_1033, x_1016);
x_1042 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_1042, 0, x_1037);
lean_ctor_set(x_1042, 1, x_1041);
x_1043 = lean_unbox(x_1022);
lean_dec(x_1022);
lean_ctor_set_uint8(x_1042, sizeof(void*)*2, x_1043);
if (lean_is_scalar(x_1038)) {
 x_1044 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1044 = x_1038;
}
lean_ctor_set(x_1044, 0, x_1042);
return x_1044;
}
else
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
lean_dec(x_1033);
lean_dec(x_1022);
lean_dec_ref(x_1016);
lean_dec_ref(x_1015);
lean_dec_ref(x_2);
x_1045 = lean_ctor_get(x_1036, 0);
lean_inc(x_1045);
if (lean_is_exclusive(x_1036)) {
 lean_ctor_release(x_1036, 0);
 x_1046 = x_1036;
} else {
 lean_dec_ref(x_1036);
 x_1046 = lean_box(0);
}
if (lean_is_scalar(x_1046)) {
 x_1047 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1047 = x_1046;
}
lean_ctor_set(x_1047, 0, x_1045);
return x_1047;
}
}
else
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; 
lean_dec(x_1022);
lean_dec_ref(x_1016);
lean_dec_ref(x_1015);
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
x_1048 = lean_ctor_get(x_1032, 0);
lean_inc(x_1048);
if (lean_is_exclusive(x_1032)) {
 lean_ctor_release(x_1032, 0);
 x_1049 = x_1032;
} else {
 lean_dec_ref(x_1032);
 x_1049 = lean_box(0);
}
if (lean_is_scalar(x_1049)) {
 x_1050 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1050 = x_1049;
}
lean_ctor_set(x_1050, 0, x_1048);
return x_1050;
}
}
else
{
lean_object* x_1051; uint8_t x_1052; lean_object* x_1053; 
lean_dec(x_1029);
lean_dec_ref(x_1016);
lean_dec_ref(x_1015);
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
x_1051 = lean_alloc_ctor(0, 0, 1);
x_1052 = lean_unbox(x_1022);
lean_dec(x_1022);
lean_ctor_set_uint8(x_1051, 0, x_1052);
if (lean_is_scalar(x_1030)) {
 x_1053 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1053 = x_1030;
}
lean_ctor_set(x_1053, 0, x_1051);
return x_1053;
}
}
else
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
lean_dec(x_1022);
lean_dec_ref(x_1016);
lean_dec_ref(x_1015);
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
x_1054 = lean_ctor_get(x_1028, 0);
lean_inc(x_1054);
if (lean_is_exclusive(x_1028)) {
 lean_ctor_release(x_1028, 0);
 x_1055 = x_1028;
} else {
 lean_dec_ref(x_1028);
 x_1055 = lean_box(0);
}
if (lean_is_scalar(x_1055)) {
 x_1056 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1056 = x_1055;
}
lean_ctor_set(x_1056, 0, x_1054);
return x_1056;
}
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; uint8_t x_1061; lean_object* x_1062; 
lean_dec(x_1022);
lean_dec_ref(x_1015);
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
x_1057 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__29));
x_1058 = l_Lean_Expr_replaceFn(x_2, x_1057);
x_1059 = l_Lean_Expr_app___override(x_1058, x_1016);
x_1060 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_1060, 0, x_18);
lean_ctor_set(x_1060, 1, x_1059);
x_1061 = lean_unbox(x_1018);
lean_dec(x_1018);
lean_ctor_set_uint8(x_1060, sizeof(void*)*2, x_1061);
if (lean_is_scalar(x_1023)) {
 x_1062 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1062 = x_1023;
}
lean_ctor_set(x_1062, 0, x_1060);
return x_1062;
}
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
lean_dec(x_1018);
lean_dec_ref(x_1016);
lean_dec_ref(x_1015);
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
x_1063 = lean_ctor_get(x_1021, 0);
lean_inc(x_1063);
if (lean_is_exclusive(x_1021)) {
 lean_ctor_release(x_1021, 0);
 x_1064 = x_1021;
} else {
 lean_dec_ref(x_1021);
 x_1064 = lean_box(0);
}
if (lean_is_scalar(x_1064)) {
 x_1065 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1065 = x_1064;
}
lean_ctor_set(x_1065, 0, x_1063);
return x_1065;
}
}
else
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
lean_dec(x_1018);
lean_dec_ref(x_1015);
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
x_1066 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__31));
x_1067 = l_Lean_Expr_replaceFn(x_2, x_1066);
x_1068 = l_Lean_Expr_app___override(x_1067, x_1016);
x_1069 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_1069, 0, x_21);
lean_ctor_set(x_1069, 1, x_1068);
lean_ctor_set_uint8(x_1069, sizeof(void*)*2, x_1);
if (lean_is_scalar(x_1019)) {
 x_1070 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1070 = x_1019;
}
lean_ctor_set(x_1070, 0, x_1069);
return x_1070;
}
}
else
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; 
lean_dec_ref(x_1016);
lean_dec_ref(x_1015);
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
x_1071 = lean_ctor_get(x_1017, 0);
lean_inc(x_1071);
if (lean_is_exclusive(x_1017)) {
 lean_ctor_release(x_1017, 0);
 x_1072 = x_1017;
} else {
 lean_dec_ref(x_1017);
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
}
}
else
{
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
return x_33;
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
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkBVar(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15;
x_2 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24;
x_2 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
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
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
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
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_26);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_29);
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_31 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1));
x_32 = l_Lean_Expr_isConstOf(x_30, x_31);
if (x_32 == 0)
{
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
lean_object* x_33; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_26);
x_33 = lean_sym_simp(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_26, x_6);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_26, x_6);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_unbox(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_37);
x_42 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4;
lean_inc_ref(x_26);
x_43 = l_Lean_Expr_app___override(x_42, x_26);
x_44 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_45 = l_Lean_Meta_trySynthInstance(x_43, x_44, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
if (lean_obj_tag(x_47) == 1)
{
lean_object* x_48; lean_object* x_49; 
lean_free_object(x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l_Lean_Meta_Sym_shareCommon___redArg(x_48, x_7);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_50);
lean_inc_ref(x_26);
x_52 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_51, x_26, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_54 = lean_sym_simp(x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
lean_dec(x_50);
lean_dec(x_40);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_ctor_set_uint8(x_56, 0, x_32);
return x_54;
}
else
{
lean_object* x_58; 
lean_dec(x_56);
x_58 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_58, 0, x_32);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
}
else
{
uint8_t x_59; 
lean_free_object(x_54);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
x_62 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_60, x_6);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_unbox(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_40);
x_65 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_60, x_6);
lean_dec_ref(x_60);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_dec(x_63);
lean_free_object(x_56);
lean_dec_ref(x_61);
lean_dec(x_50);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
lean_ctor_set_uint8(x_34, 0, x_32);
lean_ctor_set(x_65, 0, x_34);
return x_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_free_object(x_65);
lean_free_object(x_34);
x_69 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10;
lean_inc_ref(x_26);
x_70 = l_Lean_mkApp3(x_69, x_26, x_50, x_61);
x_71 = l_Lean_Meta_Sym_shareCommon___redArg(x_70, x_7);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13;
x_76 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_77 = 0;
x_78 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
x_79 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_inc(x_72);
lean_inc(x_74);
lean_inc_ref(x_26);
x_80 = l_Lean_mkApp4(x_78, x_26, x_74, x_72, x_79);
x_81 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_82 = lean_array_push(x_81, x_80);
x_83 = lean_unbox(x_63);
x_84 = lean_unbox(x_63);
x_85 = l_Lean_Expr_betaRev(x_21, x_82, x_83, x_84);
lean_dec_ref(x_82);
lean_inc(x_74);
x_86 = l_Lean_mkLambda(x_76, x_77, x_74, x_85);
x_87 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_86, x_7);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
lean_inc(x_74);
x_89 = l_Lean_mkNot(x_74);
x_90 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
lean_inc(x_72);
lean_inc(x_74);
x_91 = l_Lean_mkApp4(x_90, x_26, x_74, x_72, x_79);
x_92 = lean_array_push(x_81, x_91);
x_93 = lean_unbox(x_63);
x_94 = lean_unbox(x_63);
x_95 = l_Lean_Expr_betaRev(x_18, x_92, x_93, x_94);
lean_dec_ref(x_92);
x_96 = l_Lean_mkLambda(x_76, x_77, x_89, x_95);
x_97 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_96, x_7);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = lean_unsigned_to_nat(4u);
x_100 = l_Lean_Expr_getBoundedAppFn(x_99, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_98);
lean_inc(x_88);
lean_inc(x_74);
x_101 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_100, x_74, x_75, x_88, x_98, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16;
x_104 = lean_unbox(x_63);
x_105 = lean_unbox(x_63);
lean_inc(x_98);
x_106 = l_Lean_Expr_betaRev(x_98, x_103, x_104, x_105);
x_107 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_106, x_7);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_110 = l_Lean_Expr_replaceFn(x_2, x_109);
x_111 = l_Lean_mkApp3(x_110, x_74, x_75, x_72);
x_112 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_113 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_114 = l_Lean_mkConst(x_112, x_113);
x_115 = l_Lean_mkApp3(x_114, x_29, x_88, x_98);
lean_inc(x_108);
x_116 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_102, x_111, x_108, x_115, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_116, 0);
lean_ctor_set(x_56, 1, x_118);
lean_ctor_set(x_56, 0, x_108);
x_119 = lean_unbox(x_63);
lean_dec(x_63);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_119);
lean_ctor_set(x_116, 0, x_56);
return x_116;
}
else
{
lean_object* x_120; uint8_t x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_116, 0);
lean_inc(x_120);
lean_dec(x_116);
lean_ctor_set(x_56, 1, x_120);
lean_ctor_set(x_56, 0, x_108);
x_121 = lean_unbox(x_63);
lean_dec(x_63);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_121);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_56);
return x_122;
}
}
else
{
uint8_t x_123; 
lean_dec(x_108);
lean_dec(x_63);
lean_free_object(x_56);
x_123 = !lean_is_exclusive(x_116);
if (x_123 == 0)
{
return x_116;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_116, 0);
lean_inc(x_124);
lean_dec(x_116);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_102);
lean_dec(x_98);
lean_dec(x_88);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_63);
lean_free_object(x_56);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_126 = !lean_is_exclusive(x_107);
if (x_126 == 0)
{
return x_107;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_107, 0);
lean_inc(x_127);
lean_dec(x_107);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_98);
lean_dec(x_88);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_63);
lean_free_object(x_56);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_129 = !lean_is_exclusive(x_101);
if (x_129 == 0)
{
return x_101;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_101, 0);
lean_inc(x_130);
lean_dec(x_101);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_88);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_63);
lean_free_object(x_56);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
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
x_132 = !lean_is_exclusive(x_97);
if (x_132 == 0)
{
return x_97;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_97, 0);
lean_inc(x_133);
lean_dec(x_97);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_63);
lean_free_object(x_56);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_135 = !lean_is_exclusive(x_87);
if (x_135 == 0)
{
return x_87;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_87, 0);
lean_inc(x_136);
lean_dec(x_87);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_72);
lean_dec(x_63);
lean_free_object(x_56);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_138 = !lean_is_exclusive(x_73);
if (x_138 == 0)
{
return x_73;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_73, 0);
lean_inc(x_139);
lean_dec(x_73);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_63);
lean_free_object(x_56);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_141 = !lean_is_exclusive(x_71);
if (x_141 == 0)
{
return x_71;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_71, 0);
lean_inc(x_142);
lean_dec(x_71);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
}
}
}
else
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_65, 0);
lean_inc(x_144);
lean_dec(x_65);
x_145 = lean_unbox(x_144);
lean_dec(x_144);
if (x_145 == 0)
{
lean_object* x_146; 
lean_dec(x_63);
lean_free_object(x_56);
lean_dec_ref(x_61);
lean_dec(x_50);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
lean_ctor_set_uint8(x_34, 0, x_32);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_34);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_free_object(x_34);
x_147 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10;
lean_inc_ref(x_26);
x_148 = l_Lean_mkApp3(x_147, x_26, x_50, x_61);
x_149 = l_Lean_Meta_Sym_shareCommon___redArg(x_148, x_7);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec_ref(x_149);
x_151 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec_ref(x_151);
x_153 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13;
x_154 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_155 = 0;
x_156 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
x_157 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_inc(x_150);
lean_inc(x_152);
lean_inc_ref(x_26);
x_158 = l_Lean_mkApp4(x_156, x_26, x_152, x_150, x_157);
x_159 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_160 = lean_array_push(x_159, x_158);
x_161 = lean_unbox(x_63);
x_162 = lean_unbox(x_63);
x_163 = l_Lean_Expr_betaRev(x_21, x_160, x_161, x_162);
lean_dec_ref(x_160);
lean_inc(x_152);
x_164 = l_Lean_mkLambda(x_154, x_155, x_152, x_163);
x_165 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_164, x_7);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
lean_dec_ref(x_165);
lean_inc(x_152);
x_167 = l_Lean_mkNot(x_152);
x_168 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
lean_inc(x_150);
lean_inc(x_152);
x_169 = l_Lean_mkApp4(x_168, x_26, x_152, x_150, x_157);
x_170 = lean_array_push(x_159, x_169);
x_171 = lean_unbox(x_63);
x_172 = lean_unbox(x_63);
x_173 = l_Lean_Expr_betaRev(x_18, x_170, x_171, x_172);
lean_dec_ref(x_170);
x_174 = l_Lean_mkLambda(x_154, x_155, x_167, x_173);
x_175 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_174, x_7);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_177 = lean_unsigned_to_nat(4u);
x_178 = l_Lean_Expr_getBoundedAppFn(x_177, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_176);
lean_inc(x_166);
lean_inc(x_152);
x_179 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_178, x_152, x_153, x_166, x_176, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec_ref(x_179);
x_181 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16;
x_182 = lean_unbox(x_63);
x_183 = lean_unbox(x_63);
lean_inc(x_176);
x_184 = l_Lean_Expr_betaRev(x_176, x_181, x_182, x_183);
x_185 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_184, x_7);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec_ref(x_185);
x_187 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_188 = l_Lean_Expr_replaceFn(x_2, x_187);
x_189 = l_Lean_mkApp3(x_188, x_152, x_153, x_150);
x_190 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_191 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_192 = l_Lean_mkConst(x_190, x_191);
x_193 = l_Lean_mkApp3(x_192, x_29, x_166, x_176);
lean_inc(x_186);
x_194 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_180, x_189, x_186, x_193, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_196 = x_194;
} else {
 lean_dec_ref(x_194);
 x_196 = lean_box(0);
}
lean_ctor_set(x_56, 1, x_195);
lean_ctor_set(x_56, 0, x_186);
x_197 = lean_unbox(x_63);
lean_dec(x_63);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_197);
if (lean_is_scalar(x_196)) {
 x_198 = lean_alloc_ctor(0, 1, 0);
} else {
 x_198 = x_196;
}
lean_ctor_set(x_198, 0, x_56);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_186);
lean_dec(x_63);
lean_free_object(x_56);
x_199 = lean_ctor_get(x_194, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_200 = x_194;
} else {
 lean_dec_ref(x_194);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 1, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_199);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_180);
lean_dec(x_176);
lean_dec(x_166);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_63);
lean_free_object(x_56);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_202 = lean_ctor_get(x_185, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_203 = x_185;
} else {
 lean_dec_ref(x_185);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_176);
lean_dec(x_166);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_63);
lean_free_object(x_56);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_205 = lean_ctor_get(x_179, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 x_206 = x_179;
} else {
 lean_dec_ref(x_179);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_205);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_166);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_63);
lean_free_object(x_56);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
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
x_208 = lean_ctor_get(x_175, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_209 = x_175;
} else {
 lean_dec_ref(x_175);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 1, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_63);
lean_free_object(x_56);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_211 = lean_ctor_get(x_165, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_212 = x_165;
} else {
 lean_dec_ref(x_165);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 1, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_150);
lean_dec(x_63);
lean_free_object(x_56);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_214 = lean_ctor_get(x_151, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_215 = x_151;
} else {
 lean_dec_ref(x_151);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 1, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_214);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_63);
lean_free_object(x_56);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_217 = lean_ctor_get(x_149, 0);
lean_inc(x_217);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_218 = x_149;
} else {
 lean_dec_ref(x_149);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 1, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_217);
return x_219;
}
}
}
}
else
{
uint8_t x_220; 
lean_dec(x_63);
lean_free_object(x_56);
lean_dec_ref(x_61);
lean_dec(x_50);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_220 = !lean_is_exclusive(x_65);
if (x_220 == 0)
{
return x_65;
}
else
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_65, 0);
lean_inc(x_221);
lean_dec(x_65);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_221);
return x_222;
}
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_63);
lean_dec_ref(x_60);
lean_free_object(x_34);
x_223 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22;
lean_inc_ref(x_26);
x_224 = l_Lean_mkApp3(x_223, x_26, x_50, x_61);
x_225 = l_Lean_Meta_Sym_shareCommon___redArg(x_224, x_7);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec_ref(x_225);
x_227 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
lean_dec_ref(x_227);
x_229 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25;
x_230 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_231 = 0;
x_232 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
x_233 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_inc(x_226);
lean_inc(x_228);
lean_inc_ref(x_26);
x_234 = l_Lean_mkApp4(x_232, x_26, x_228, x_226, x_233);
x_235 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_236 = lean_array_push(x_235, x_234);
x_237 = lean_unbox(x_40);
x_238 = lean_unbox(x_40);
x_239 = l_Lean_Expr_betaRev(x_21, x_236, x_237, x_238);
lean_dec_ref(x_236);
lean_inc(x_228);
x_240 = l_Lean_mkLambda(x_230, x_231, x_228, x_239);
x_241 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_240, x_7);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
lean_dec_ref(x_241);
lean_inc(x_228);
x_243 = l_Lean_mkNot(x_228);
x_244 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
lean_inc(x_226);
lean_inc(x_228);
x_245 = l_Lean_mkApp4(x_244, x_26, x_228, x_226, x_233);
x_246 = lean_array_push(x_235, x_245);
x_247 = lean_unbox(x_40);
x_248 = lean_unbox(x_40);
x_249 = l_Lean_Expr_betaRev(x_18, x_246, x_247, x_248);
lean_dec_ref(x_246);
x_250 = l_Lean_mkLambda(x_230, x_231, x_243, x_249);
x_251 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_250, x_7);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
lean_dec_ref(x_251);
x_253 = lean_unsigned_to_nat(4u);
x_254 = l_Lean_Expr_getBoundedAppFn(x_253, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_252);
lean_inc(x_242);
lean_inc(x_228);
x_255 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_254, x_228, x_229, x_242, x_252, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec_ref(x_255);
x_257 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25;
x_258 = lean_unbox(x_40);
x_259 = lean_unbox(x_40);
lean_inc(x_242);
x_260 = l_Lean_Expr_betaRev(x_242, x_257, x_258, x_259);
x_261 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_260, x_7);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec_ref(x_261);
x_263 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_264 = l_Lean_Expr_replaceFn(x_2, x_263);
x_265 = l_Lean_mkApp3(x_264, x_228, x_229, x_226);
x_266 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_267 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_268 = l_Lean_mkConst(x_266, x_267);
x_269 = l_Lean_mkApp3(x_268, x_29, x_242, x_252);
lean_inc(x_262);
x_270 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_256, x_265, x_262, x_269, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_270) == 0)
{
uint8_t x_271; 
x_271 = !lean_is_exclusive(x_270);
if (x_271 == 0)
{
lean_object* x_272; uint8_t x_273; 
x_272 = lean_ctor_get(x_270, 0);
lean_ctor_set(x_56, 1, x_272);
lean_ctor_set(x_56, 0, x_262);
x_273 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_273);
lean_ctor_set(x_270, 0, x_56);
return x_270;
}
else
{
lean_object* x_274; uint8_t x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_270, 0);
lean_inc(x_274);
lean_dec(x_270);
lean_ctor_set(x_56, 1, x_274);
lean_ctor_set(x_56, 0, x_262);
x_275 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_275);
x_276 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_276, 0, x_56);
return x_276;
}
}
else
{
uint8_t x_277; 
lean_dec(x_262);
lean_free_object(x_56);
lean_dec(x_40);
x_277 = !lean_is_exclusive(x_270);
if (x_277 == 0)
{
return x_270;
}
else
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_270, 0);
lean_inc(x_278);
lean_dec(x_270);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_278);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_256);
lean_dec(x_252);
lean_dec(x_242);
lean_dec(x_228);
lean_dec(x_226);
lean_free_object(x_56);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_280 = !lean_is_exclusive(x_261);
if (x_280 == 0)
{
return x_261;
}
else
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_261, 0);
lean_inc(x_281);
lean_dec(x_261);
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_281);
return x_282;
}
}
}
else
{
uint8_t x_283; 
lean_dec(x_252);
lean_dec(x_242);
lean_dec(x_228);
lean_dec(x_226);
lean_free_object(x_56);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_283 = !lean_is_exclusive(x_255);
if (x_283 == 0)
{
return x_255;
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_255, 0);
lean_inc(x_284);
lean_dec(x_255);
x_285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_285, 0, x_284);
return x_285;
}
}
}
else
{
uint8_t x_286; 
lean_dec(x_242);
lean_dec(x_228);
lean_dec(x_226);
lean_free_object(x_56);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
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
x_286 = !lean_is_exclusive(x_251);
if (x_286 == 0)
{
return x_251;
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_251, 0);
lean_inc(x_287);
lean_dec(x_251);
x_288 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_288, 0, x_287);
return x_288;
}
}
}
else
{
uint8_t x_289; 
lean_dec(x_228);
lean_dec(x_226);
lean_free_object(x_56);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_289 = !lean_is_exclusive(x_241);
if (x_289 == 0)
{
return x_241;
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_241, 0);
lean_inc(x_290);
lean_dec(x_241);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_290);
return x_291;
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_226);
lean_free_object(x_56);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_292 = !lean_is_exclusive(x_227);
if (x_292 == 0)
{
return x_227;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_227, 0);
lean_inc(x_293);
lean_dec(x_227);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_293);
return x_294;
}
}
}
else
{
uint8_t x_295; 
lean_free_object(x_56);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_295 = !lean_is_exclusive(x_225);
if (x_295 == 0)
{
return x_225;
}
else
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_225, 0);
lean_inc(x_296);
lean_dec(x_225);
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_296);
return x_297;
}
}
}
}
else
{
uint8_t x_298; 
lean_free_object(x_56);
lean_dec_ref(x_61);
lean_dec_ref(x_60);
lean_dec(x_50);
lean_dec(x_40);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_298 = !lean_is_exclusive(x_62);
if (x_298 == 0)
{
return x_62;
}
else
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_62, 0);
lean_inc(x_299);
lean_dec(x_62);
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_299);
return x_300;
}
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_56, 0);
x_302 = lean_ctor_get(x_56, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_56);
x_303 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_301, x_6);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; uint8_t x_305; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
lean_dec_ref(x_303);
x_305 = lean_unbox(x_304);
if (x_305 == 0)
{
lean_object* x_306; 
lean_dec(x_40);
x_306 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_301, x_6);
lean_dec_ref(x_301);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 x_308 = x_306;
} else {
 lean_dec_ref(x_306);
 x_308 = lean_box(0);
}
x_309 = lean_unbox(x_307);
lean_dec(x_307);
if (x_309 == 0)
{
lean_object* x_310; 
lean_dec(x_304);
lean_dec_ref(x_302);
lean_dec(x_50);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
lean_ctor_set_uint8(x_34, 0, x_32);
if (lean_is_scalar(x_308)) {
 x_310 = lean_alloc_ctor(0, 1, 0);
} else {
 x_310 = x_308;
}
lean_ctor_set(x_310, 0, x_34);
return x_310;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_308);
lean_free_object(x_34);
x_311 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10;
lean_inc_ref(x_26);
x_312 = l_Lean_mkApp3(x_311, x_26, x_50, x_302);
x_313 = l_Lean_Meta_Sym_shareCommon___redArg(x_312, x_7);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
lean_dec_ref(x_313);
x_315 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; uint8_t x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec_ref(x_315);
x_317 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13;
x_318 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_319 = 0;
x_320 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
x_321 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_inc(x_314);
lean_inc(x_316);
lean_inc_ref(x_26);
x_322 = l_Lean_mkApp4(x_320, x_26, x_316, x_314, x_321);
x_323 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_324 = lean_array_push(x_323, x_322);
x_325 = lean_unbox(x_304);
x_326 = lean_unbox(x_304);
x_327 = l_Lean_Expr_betaRev(x_21, x_324, x_325, x_326);
lean_dec_ref(x_324);
lean_inc(x_316);
x_328 = l_Lean_mkLambda(x_318, x_319, x_316, x_327);
x_329 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_328, x_7);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
lean_dec_ref(x_329);
lean_inc(x_316);
x_331 = l_Lean_mkNot(x_316);
x_332 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
lean_inc(x_314);
lean_inc(x_316);
x_333 = l_Lean_mkApp4(x_332, x_26, x_316, x_314, x_321);
x_334 = lean_array_push(x_323, x_333);
x_335 = lean_unbox(x_304);
x_336 = lean_unbox(x_304);
x_337 = l_Lean_Expr_betaRev(x_18, x_334, x_335, x_336);
lean_dec_ref(x_334);
x_338 = l_Lean_mkLambda(x_318, x_319, x_331, x_337);
x_339 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_338, x_7);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
lean_dec_ref(x_339);
x_341 = lean_unsigned_to_nat(4u);
x_342 = l_Lean_Expr_getBoundedAppFn(x_341, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_340);
lean_inc(x_330);
lean_inc(x_316);
x_343 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_342, x_316, x_317, x_330, x_340, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; uint8_t x_346; uint8_t x_347; lean_object* x_348; lean_object* x_349; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
lean_dec_ref(x_343);
x_345 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16;
x_346 = lean_unbox(x_304);
x_347 = lean_unbox(x_304);
lean_inc(x_340);
x_348 = l_Lean_Expr_betaRev(x_340, x_345, x_346, x_347);
x_349 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_348, x_7);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
lean_dec_ref(x_349);
x_351 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_352 = l_Lean_Expr_replaceFn(x_2, x_351);
x_353 = l_Lean_mkApp3(x_352, x_316, x_317, x_314);
x_354 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_355 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_356 = l_Lean_mkConst(x_354, x_355);
x_357 = l_Lean_mkApp3(x_356, x_29, x_330, x_340);
lean_inc(x_350);
x_358 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_344, x_353, x_350, x_357, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 x_360 = x_358;
} else {
 lean_dec_ref(x_358);
 x_360 = lean_box(0);
}
x_361 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_361, 0, x_350);
lean_ctor_set(x_361, 1, x_359);
x_362 = lean_unbox(x_304);
lean_dec(x_304);
lean_ctor_set_uint8(x_361, sizeof(void*)*2, x_362);
if (lean_is_scalar(x_360)) {
 x_363 = lean_alloc_ctor(0, 1, 0);
} else {
 x_363 = x_360;
}
lean_ctor_set(x_363, 0, x_361);
return x_363;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_350);
lean_dec(x_304);
x_364 = lean_ctor_get(x_358, 0);
lean_inc(x_364);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 x_365 = x_358;
} else {
 lean_dec_ref(x_358);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 1, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_364);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_330);
lean_dec(x_316);
lean_dec(x_314);
lean_dec(x_304);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_367 = lean_ctor_get(x_349, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 x_368 = x_349;
} else {
 lean_dec_ref(x_349);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(1, 1, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_367);
return x_369;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_340);
lean_dec(x_330);
lean_dec(x_316);
lean_dec(x_314);
lean_dec(x_304);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_370 = lean_ctor_get(x_343, 0);
lean_inc(x_370);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 x_371 = x_343;
} else {
 lean_dec_ref(x_343);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(1, 1, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_370);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_330);
lean_dec(x_316);
lean_dec(x_314);
lean_dec(x_304);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
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
x_373 = lean_ctor_get(x_339, 0);
lean_inc(x_373);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 x_374 = x_339;
} else {
 lean_dec_ref(x_339);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(1, 1, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_373);
return x_375;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_316);
lean_dec(x_314);
lean_dec(x_304);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_376 = lean_ctor_get(x_329, 0);
lean_inc(x_376);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 x_377 = x_329;
} else {
 lean_dec_ref(x_329);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(1, 1, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_376);
return x_378;
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_314);
lean_dec(x_304);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_379 = lean_ctor_get(x_315, 0);
lean_inc(x_379);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 x_380 = x_315;
} else {
 lean_dec_ref(x_315);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(1, 1, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_379);
return x_381;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_304);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_382 = lean_ctor_get(x_313, 0);
lean_inc(x_382);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 x_383 = x_313;
} else {
 lean_dec_ref(x_313);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 1, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_382);
return x_384;
}
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_304);
lean_dec_ref(x_302);
lean_dec(x_50);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_385 = lean_ctor_get(x_306, 0);
lean_inc(x_385);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 x_386 = x_306;
} else {
 lean_dec_ref(x_306);
 x_386 = lean_box(0);
}
if (lean_is_scalar(x_386)) {
 x_387 = lean_alloc_ctor(1, 1, 0);
} else {
 x_387 = x_386;
}
lean_ctor_set(x_387, 0, x_385);
return x_387;
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_304);
lean_dec_ref(x_301);
lean_free_object(x_34);
x_388 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22;
lean_inc_ref(x_26);
x_389 = l_Lean_mkApp3(x_388, x_26, x_50, x_302);
x_390 = l_Lean_Meta_Sym_shareCommon___redArg(x_389, x_7);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
lean_dec_ref(x_390);
x_392 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
lean_dec_ref(x_392);
x_394 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25;
x_395 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_396 = 0;
x_397 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
x_398 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_inc(x_391);
lean_inc(x_393);
lean_inc_ref(x_26);
x_399 = l_Lean_mkApp4(x_397, x_26, x_393, x_391, x_398);
x_400 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_401 = lean_array_push(x_400, x_399);
x_402 = lean_unbox(x_40);
x_403 = lean_unbox(x_40);
x_404 = l_Lean_Expr_betaRev(x_21, x_401, x_402, x_403);
lean_dec_ref(x_401);
lean_inc(x_393);
x_405 = l_Lean_mkLambda(x_395, x_396, x_393, x_404);
x_406 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_405, x_7);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; uint8_t x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
lean_dec_ref(x_406);
lean_inc(x_393);
x_408 = l_Lean_mkNot(x_393);
x_409 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
lean_inc(x_391);
lean_inc(x_393);
x_410 = l_Lean_mkApp4(x_409, x_26, x_393, x_391, x_398);
x_411 = lean_array_push(x_400, x_410);
x_412 = lean_unbox(x_40);
x_413 = lean_unbox(x_40);
x_414 = l_Lean_Expr_betaRev(x_18, x_411, x_412, x_413);
lean_dec_ref(x_411);
x_415 = l_Lean_mkLambda(x_395, x_396, x_408, x_414);
x_416 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_415, x_7);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
lean_dec_ref(x_416);
x_418 = lean_unsigned_to_nat(4u);
x_419 = l_Lean_Expr_getBoundedAppFn(x_418, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_417);
lean_inc(x_407);
lean_inc(x_393);
x_420 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_419, x_393, x_394, x_407, x_417, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; uint8_t x_423; uint8_t x_424; lean_object* x_425; lean_object* x_426; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
lean_dec_ref(x_420);
x_422 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25;
x_423 = lean_unbox(x_40);
x_424 = lean_unbox(x_40);
lean_inc(x_407);
x_425 = l_Lean_Expr_betaRev(x_407, x_422, x_423, x_424);
x_426 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_425, x_7);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
lean_dec_ref(x_426);
x_428 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_429 = l_Lean_Expr_replaceFn(x_2, x_428);
x_430 = l_Lean_mkApp3(x_429, x_393, x_394, x_391);
x_431 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_432 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_433 = l_Lean_mkConst(x_431, x_432);
x_434 = l_Lean_mkApp3(x_433, x_29, x_407, x_417);
lean_inc(x_427);
x_435 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_421, x_430, x_427, x_434, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; lean_object* x_440; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 x_437 = x_435;
} else {
 lean_dec_ref(x_435);
 x_437 = lean_box(0);
}
x_438 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_438, 0, x_427);
lean_ctor_set(x_438, 1, x_436);
x_439 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_438, sizeof(void*)*2, x_439);
if (lean_is_scalar(x_437)) {
 x_440 = lean_alloc_ctor(0, 1, 0);
} else {
 x_440 = x_437;
}
lean_ctor_set(x_440, 0, x_438);
return x_440;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_427);
lean_dec(x_40);
x_441 = lean_ctor_get(x_435, 0);
lean_inc(x_441);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 x_442 = x_435;
} else {
 lean_dec_ref(x_435);
 x_442 = lean_box(0);
}
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 1, 0);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_441);
return x_443;
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_421);
lean_dec(x_417);
lean_dec(x_407);
lean_dec(x_393);
lean_dec(x_391);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_444 = lean_ctor_get(x_426, 0);
lean_inc(x_444);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 x_445 = x_426;
} else {
 lean_dec_ref(x_426);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(1, 1, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_444);
return x_446;
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_417);
lean_dec(x_407);
lean_dec(x_393);
lean_dec(x_391);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_447 = lean_ctor_get(x_420, 0);
lean_inc(x_447);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 x_448 = x_420;
} else {
 lean_dec_ref(x_420);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 1, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_447);
return x_449;
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_407);
lean_dec(x_393);
lean_dec(x_391);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
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
x_450 = lean_ctor_get(x_416, 0);
lean_inc(x_450);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_451 = x_416;
} else {
 lean_dec_ref(x_416);
 x_451 = lean_box(0);
}
if (lean_is_scalar(x_451)) {
 x_452 = lean_alloc_ctor(1, 1, 0);
} else {
 x_452 = x_451;
}
lean_ctor_set(x_452, 0, x_450);
return x_452;
}
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_393);
lean_dec(x_391);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_453 = lean_ctor_get(x_406, 0);
lean_inc(x_453);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 x_454 = x_406;
} else {
 lean_dec_ref(x_406);
 x_454 = lean_box(0);
}
if (lean_is_scalar(x_454)) {
 x_455 = lean_alloc_ctor(1, 1, 0);
} else {
 x_455 = x_454;
}
lean_ctor_set(x_455, 0, x_453);
return x_455;
}
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_391);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_456 = lean_ctor_get(x_392, 0);
lean_inc(x_456);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 x_457 = x_392;
} else {
 lean_dec_ref(x_392);
 x_457 = lean_box(0);
}
if (lean_is_scalar(x_457)) {
 x_458 = lean_alloc_ctor(1, 1, 0);
} else {
 x_458 = x_457;
}
lean_ctor_set(x_458, 0, x_456);
return x_458;
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_459 = lean_ctor_get(x_390, 0);
lean_inc(x_459);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 x_460 = x_390;
} else {
 lean_dec_ref(x_390);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(1, 1, 0);
} else {
 x_461 = x_460;
}
lean_ctor_set(x_461, 0, x_459);
return x_461;
}
}
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec_ref(x_302);
lean_dec_ref(x_301);
lean_dec(x_50);
lean_dec(x_40);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_462 = lean_ctor_get(x_303, 0);
lean_inc(x_462);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 x_463 = x_303;
} else {
 lean_dec_ref(x_303);
 x_463 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 1, 0);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_462);
return x_464;
}
}
}
}
else
{
lean_object* x_465; 
x_465 = lean_ctor_get(x_54, 0);
lean_inc(x_465);
lean_dec(x_54);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
lean_dec(x_50);
lean_dec(x_40);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
if (lean_is_exclusive(x_465)) {
 x_466 = x_465;
} else {
 lean_dec_ref(x_465);
 x_466 = lean_box(0);
}
if (lean_is_scalar(x_466)) {
 x_467 = lean_alloc_ctor(0, 0, 1);
} else {
 x_467 = x_466;
}
lean_ctor_set_uint8(x_467, 0, x_32);
x_468 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_468, 0, x_467);
return x_468;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_469 = lean_ctor_get(x_465, 0);
lean_inc_ref(x_469);
x_470 = lean_ctor_get(x_465, 1);
lean_inc_ref(x_470);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_471 = x_465;
} else {
 lean_dec_ref(x_465);
 x_471 = lean_box(0);
}
x_472 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_469, x_6);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; uint8_t x_474; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
lean_dec_ref(x_472);
x_474 = lean_unbox(x_473);
if (x_474 == 0)
{
lean_object* x_475; 
lean_dec(x_40);
x_475 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_469, x_6);
lean_dec_ref(x_469);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; uint8_t x_478; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 x_477 = x_475;
} else {
 lean_dec_ref(x_475);
 x_477 = lean_box(0);
}
x_478 = lean_unbox(x_476);
lean_dec(x_476);
if (x_478 == 0)
{
lean_object* x_479; 
lean_dec(x_473);
lean_dec(x_471);
lean_dec_ref(x_470);
lean_dec(x_50);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
lean_ctor_set_uint8(x_34, 0, x_32);
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(0, 1, 0);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_34);
return x_479;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_477);
lean_free_object(x_34);
x_480 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10;
lean_inc_ref(x_26);
x_481 = l_Lean_mkApp3(x_480, x_26, x_50, x_470);
x_482 = l_Lean_Meta_Sym_shareCommon___redArg(x_481, x_7);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
lean_dec_ref(x_482);
x_484 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; uint8_t x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
lean_dec_ref(x_484);
x_486 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13;
x_487 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_488 = 0;
x_489 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
x_490 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_inc(x_483);
lean_inc(x_485);
lean_inc_ref(x_26);
x_491 = l_Lean_mkApp4(x_489, x_26, x_485, x_483, x_490);
x_492 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_493 = lean_array_push(x_492, x_491);
x_494 = lean_unbox(x_473);
x_495 = lean_unbox(x_473);
x_496 = l_Lean_Expr_betaRev(x_21, x_493, x_494, x_495);
lean_dec_ref(x_493);
lean_inc(x_485);
x_497 = l_Lean_mkLambda(x_487, x_488, x_485, x_496);
x_498 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_497, x_7);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; uint8_t x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
lean_dec_ref(x_498);
lean_inc(x_485);
x_500 = l_Lean_mkNot(x_485);
x_501 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
lean_inc(x_483);
lean_inc(x_485);
x_502 = l_Lean_mkApp4(x_501, x_26, x_485, x_483, x_490);
x_503 = lean_array_push(x_492, x_502);
x_504 = lean_unbox(x_473);
x_505 = lean_unbox(x_473);
x_506 = l_Lean_Expr_betaRev(x_18, x_503, x_504, x_505);
lean_dec_ref(x_503);
x_507 = l_Lean_mkLambda(x_487, x_488, x_500, x_506);
x_508 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_507, x_7);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
lean_dec_ref(x_508);
x_510 = lean_unsigned_to_nat(4u);
x_511 = l_Lean_Expr_getBoundedAppFn(x_510, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_509);
lean_inc(x_499);
lean_inc(x_485);
x_512 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_511, x_485, x_486, x_499, x_509, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; uint8_t x_515; uint8_t x_516; lean_object* x_517; lean_object* x_518; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
lean_dec_ref(x_512);
x_514 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16;
x_515 = lean_unbox(x_473);
x_516 = lean_unbox(x_473);
lean_inc(x_509);
x_517 = l_Lean_Expr_betaRev(x_509, x_514, x_515, x_516);
x_518 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_517, x_7);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
lean_dec_ref(x_518);
x_520 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_521 = l_Lean_Expr_replaceFn(x_2, x_520);
x_522 = l_Lean_mkApp3(x_521, x_485, x_486, x_483);
x_523 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_524 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_525 = l_Lean_mkConst(x_523, x_524);
x_526 = l_Lean_mkApp3(x_525, x_29, x_499, x_509);
lean_inc(x_519);
x_527 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_513, x_522, x_519, x_526, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; uint8_t x_531; lean_object* x_532; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 x_529 = x_527;
} else {
 lean_dec_ref(x_527);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_471)) {
 x_530 = lean_alloc_ctor(1, 2, 1);
} else {
 x_530 = x_471;
}
lean_ctor_set(x_530, 0, x_519);
lean_ctor_set(x_530, 1, x_528);
x_531 = lean_unbox(x_473);
lean_dec(x_473);
lean_ctor_set_uint8(x_530, sizeof(void*)*2, x_531);
if (lean_is_scalar(x_529)) {
 x_532 = lean_alloc_ctor(0, 1, 0);
} else {
 x_532 = x_529;
}
lean_ctor_set(x_532, 0, x_530);
return x_532;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_519);
lean_dec(x_473);
lean_dec(x_471);
x_533 = lean_ctor_get(x_527, 0);
lean_inc(x_533);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 x_534 = x_527;
} else {
 lean_dec_ref(x_527);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(1, 1, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_533);
return x_535;
}
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec(x_513);
lean_dec(x_509);
lean_dec(x_499);
lean_dec(x_485);
lean_dec(x_483);
lean_dec(x_473);
lean_dec(x_471);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_536 = lean_ctor_get(x_518, 0);
lean_inc(x_536);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 x_537 = x_518;
} else {
 lean_dec_ref(x_518);
 x_537 = lean_box(0);
}
if (lean_is_scalar(x_537)) {
 x_538 = lean_alloc_ctor(1, 1, 0);
} else {
 x_538 = x_537;
}
lean_ctor_set(x_538, 0, x_536);
return x_538;
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_509);
lean_dec(x_499);
lean_dec(x_485);
lean_dec(x_483);
lean_dec(x_473);
lean_dec(x_471);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_539 = lean_ctor_get(x_512, 0);
lean_inc(x_539);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 x_540 = x_512;
} else {
 lean_dec_ref(x_512);
 x_540 = lean_box(0);
}
if (lean_is_scalar(x_540)) {
 x_541 = lean_alloc_ctor(1, 1, 0);
} else {
 x_541 = x_540;
}
lean_ctor_set(x_541, 0, x_539);
return x_541;
}
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
lean_dec(x_499);
lean_dec(x_485);
lean_dec(x_483);
lean_dec(x_473);
lean_dec(x_471);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
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
x_542 = lean_ctor_get(x_508, 0);
lean_inc(x_542);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 x_543 = x_508;
} else {
 lean_dec_ref(x_508);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(1, 1, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_542);
return x_544;
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_485);
lean_dec(x_483);
lean_dec(x_473);
lean_dec(x_471);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_545 = lean_ctor_get(x_498, 0);
lean_inc(x_545);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 x_546 = x_498;
} else {
 lean_dec_ref(x_498);
 x_546 = lean_box(0);
}
if (lean_is_scalar(x_546)) {
 x_547 = lean_alloc_ctor(1, 1, 0);
} else {
 x_547 = x_546;
}
lean_ctor_set(x_547, 0, x_545);
return x_547;
}
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_483);
lean_dec(x_473);
lean_dec(x_471);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_548 = lean_ctor_get(x_484, 0);
lean_inc(x_548);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 x_549 = x_484;
} else {
 lean_dec_ref(x_484);
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
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
lean_dec(x_473);
lean_dec(x_471);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_551 = lean_ctor_get(x_482, 0);
lean_inc(x_551);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 x_552 = x_482;
} else {
 lean_dec_ref(x_482);
 x_552 = lean_box(0);
}
if (lean_is_scalar(x_552)) {
 x_553 = lean_alloc_ctor(1, 1, 0);
} else {
 x_553 = x_552;
}
lean_ctor_set(x_553, 0, x_551);
return x_553;
}
}
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; 
lean_dec(x_473);
lean_dec(x_471);
lean_dec_ref(x_470);
lean_dec(x_50);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_554 = lean_ctor_get(x_475, 0);
lean_inc(x_554);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 x_555 = x_475;
} else {
 lean_dec_ref(x_475);
 x_555 = lean_box(0);
}
if (lean_is_scalar(x_555)) {
 x_556 = lean_alloc_ctor(1, 1, 0);
} else {
 x_556 = x_555;
}
lean_ctor_set(x_556, 0, x_554);
return x_556;
}
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_dec(x_473);
lean_dec_ref(x_469);
lean_free_object(x_34);
x_557 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22;
lean_inc_ref(x_26);
x_558 = l_Lean_mkApp3(x_557, x_26, x_50, x_470);
x_559 = l_Lean_Meta_Sym_shareCommon___redArg(x_558, x_7);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; 
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
lean_dec_ref(x_559);
x_561 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; uint8_t x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; uint8_t x_571; uint8_t x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
lean_dec_ref(x_561);
x_563 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25;
x_564 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_565 = 0;
x_566 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
x_567 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_inc(x_560);
lean_inc(x_562);
lean_inc_ref(x_26);
x_568 = l_Lean_mkApp4(x_566, x_26, x_562, x_560, x_567);
x_569 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_570 = lean_array_push(x_569, x_568);
x_571 = lean_unbox(x_40);
x_572 = lean_unbox(x_40);
x_573 = l_Lean_Expr_betaRev(x_21, x_570, x_571, x_572);
lean_dec_ref(x_570);
lean_inc(x_562);
x_574 = l_Lean_mkLambda(x_564, x_565, x_562, x_573);
x_575 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_574, x_7);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; uint8_t x_581; uint8_t x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_576 = lean_ctor_get(x_575, 0);
lean_inc(x_576);
lean_dec_ref(x_575);
lean_inc(x_562);
x_577 = l_Lean_mkNot(x_562);
x_578 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
lean_inc(x_560);
lean_inc(x_562);
x_579 = l_Lean_mkApp4(x_578, x_26, x_562, x_560, x_567);
x_580 = lean_array_push(x_569, x_579);
x_581 = lean_unbox(x_40);
x_582 = lean_unbox(x_40);
x_583 = l_Lean_Expr_betaRev(x_18, x_580, x_581, x_582);
lean_dec_ref(x_580);
x_584 = l_Lean_mkLambda(x_564, x_565, x_577, x_583);
x_585 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_584, x_7);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
lean_dec_ref(x_585);
x_587 = lean_unsigned_to_nat(4u);
x_588 = l_Lean_Expr_getBoundedAppFn(x_587, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_586);
lean_inc(x_576);
lean_inc(x_562);
x_589 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_588, x_562, x_563, x_576, x_586, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; uint8_t x_592; uint8_t x_593; lean_object* x_594; lean_object* x_595; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
lean_dec_ref(x_589);
x_591 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25;
x_592 = lean_unbox(x_40);
x_593 = lean_unbox(x_40);
lean_inc(x_576);
x_594 = l_Lean_Expr_betaRev(x_576, x_591, x_592, x_593);
x_595 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_594, x_7);
if (lean_obj_tag(x_595) == 0)
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
lean_dec_ref(x_595);
x_597 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_598 = l_Lean_Expr_replaceFn(x_2, x_597);
x_599 = l_Lean_mkApp3(x_598, x_562, x_563, x_560);
x_600 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_601 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_602 = l_Lean_mkConst(x_600, x_601);
x_603 = l_Lean_mkApp3(x_602, x_29, x_576, x_586);
lean_inc(x_596);
x_604 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_590, x_599, x_596, x_603, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_604) == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; uint8_t x_608; lean_object* x_609; 
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 x_606 = x_604;
} else {
 lean_dec_ref(x_604);
 x_606 = lean_box(0);
}
if (lean_is_scalar(x_471)) {
 x_607 = lean_alloc_ctor(1, 2, 1);
} else {
 x_607 = x_471;
}
lean_ctor_set(x_607, 0, x_596);
lean_ctor_set(x_607, 1, x_605);
x_608 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_607, sizeof(void*)*2, x_608);
if (lean_is_scalar(x_606)) {
 x_609 = lean_alloc_ctor(0, 1, 0);
} else {
 x_609 = x_606;
}
lean_ctor_set(x_609, 0, x_607);
return x_609;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_596);
lean_dec(x_471);
lean_dec(x_40);
x_610 = lean_ctor_get(x_604, 0);
lean_inc(x_610);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 x_611 = x_604;
} else {
 lean_dec_ref(x_604);
 x_611 = lean_box(0);
}
if (lean_is_scalar(x_611)) {
 x_612 = lean_alloc_ctor(1, 1, 0);
} else {
 x_612 = x_611;
}
lean_ctor_set(x_612, 0, x_610);
return x_612;
}
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec(x_590);
lean_dec(x_586);
lean_dec(x_576);
lean_dec(x_562);
lean_dec(x_560);
lean_dec(x_471);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_613 = lean_ctor_get(x_595, 0);
lean_inc(x_613);
if (lean_is_exclusive(x_595)) {
 lean_ctor_release(x_595, 0);
 x_614 = x_595;
} else {
 lean_dec_ref(x_595);
 x_614 = lean_box(0);
}
if (lean_is_scalar(x_614)) {
 x_615 = lean_alloc_ctor(1, 1, 0);
} else {
 x_615 = x_614;
}
lean_ctor_set(x_615, 0, x_613);
return x_615;
}
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
lean_dec(x_586);
lean_dec(x_576);
lean_dec(x_562);
lean_dec(x_560);
lean_dec(x_471);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_616 = lean_ctor_get(x_589, 0);
lean_inc(x_616);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 x_617 = x_589;
} else {
 lean_dec_ref(x_589);
 x_617 = lean_box(0);
}
if (lean_is_scalar(x_617)) {
 x_618 = lean_alloc_ctor(1, 1, 0);
} else {
 x_618 = x_617;
}
lean_ctor_set(x_618, 0, x_616);
return x_618;
}
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_576);
lean_dec(x_562);
lean_dec(x_560);
lean_dec(x_471);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
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
x_619 = lean_ctor_get(x_585, 0);
lean_inc(x_619);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 x_620 = x_585;
} else {
 lean_dec_ref(x_585);
 x_620 = lean_box(0);
}
if (lean_is_scalar(x_620)) {
 x_621 = lean_alloc_ctor(1, 1, 0);
} else {
 x_621 = x_620;
}
lean_ctor_set(x_621, 0, x_619);
return x_621;
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_562);
lean_dec(x_560);
lean_dec(x_471);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_622 = lean_ctor_get(x_575, 0);
lean_inc(x_622);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 x_623 = x_575;
} else {
 lean_dec_ref(x_575);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(1, 1, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_622);
return x_624;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; 
lean_dec(x_560);
lean_dec(x_471);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_625 = lean_ctor_get(x_561, 0);
lean_inc(x_625);
if (lean_is_exclusive(x_561)) {
 lean_ctor_release(x_561, 0);
 x_626 = x_561;
} else {
 lean_dec_ref(x_561);
 x_626 = lean_box(0);
}
if (lean_is_scalar(x_626)) {
 x_627 = lean_alloc_ctor(1, 1, 0);
} else {
 x_627 = x_626;
}
lean_ctor_set(x_627, 0, x_625);
return x_627;
}
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
lean_dec(x_471);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_628 = lean_ctor_get(x_559, 0);
lean_inc(x_628);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 x_629 = x_559;
} else {
 lean_dec_ref(x_559);
 x_629 = lean_box(0);
}
if (lean_is_scalar(x_629)) {
 x_630 = lean_alloc_ctor(1, 1, 0);
} else {
 x_630 = x_629;
}
lean_ctor_set(x_630, 0, x_628);
return x_630;
}
}
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; 
lean_dec(x_471);
lean_dec_ref(x_470);
lean_dec_ref(x_469);
lean_dec(x_50);
lean_dec(x_40);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_631 = lean_ctor_get(x_472, 0);
lean_inc(x_631);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 x_632 = x_472;
} else {
 lean_dec_ref(x_472);
 x_632 = lean_box(0);
}
if (lean_is_scalar(x_632)) {
 x_633 = lean_alloc_ctor(1, 1, 0);
} else {
 x_633 = x_632;
}
lean_ctor_set(x_633, 0, x_631);
return x_633;
}
}
}
}
else
{
lean_dec(x_50);
lean_dec(x_40);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
return x_54;
}
}
else
{
uint8_t x_634; 
lean_dec(x_50);
lean_dec(x_40);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_634 = !lean_is_exclusive(x_52);
if (x_634 == 0)
{
return x_52;
}
else
{
lean_object* x_635; lean_object* x_636; 
x_635 = lean_ctor_get(x_52, 0);
lean_inc(x_635);
lean_dec(x_52);
x_636 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_636, 0, x_635);
return x_636;
}
}
}
else
{
uint8_t x_637; 
lean_dec(x_40);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_637 = !lean_is_exclusive(x_49);
if (x_637 == 0)
{
return x_49;
}
else
{
lean_object* x_638; lean_object* x_639; 
x_638 = lean_ctor_get(x_49, 0);
lean_inc(x_638);
lean_dec(x_49);
x_639 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_639, 0, x_638);
return x_639;
}
}
}
else
{
uint8_t x_640; 
lean_dec(x_47);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_640 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_34, 0, x_640);
lean_ctor_set(x_45, 0, x_34);
return x_45;
}
}
else
{
lean_object* x_641; 
x_641 = lean_ctor_get(x_45, 0);
lean_inc(x_641);
lean_dec(x_45);
if (lean_obj_tag(x_641) == 1)
{
lean_object* x_642; lean_object* x_643; 
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
lean_dec_ref(x_641);
x_643 = l_Lean_Meta_Sym_shareCommon___redArg(x_642, x_7);
if (lean_obj_tag(x_643) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
lean_dec_ref(x_643);
x_645 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_644);
lean_inc_ref(x_26);
x_646 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_645, x_26, x_644, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; lean_object* x_648; 
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
lean_dec_ref(x_646);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_648 = lean_sym_simp(x_647, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; 
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 x_650 = x_648;
} else {
 lean_dec_ref(x_648);
 x_650 = lean_box(0);
}
if (lean_obj_tag(x_649) == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_644);
lean_dec(x_40);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
if (lean_is_exclusive(x_649)) {
 x_651 = x_649;
} else {
 lean_dec_ref(x_649);
 x_651 = lean_box(0);
}
if (lean_is_scalar(x_651)) {
 x_652 = lean_alloc_ctor(0, 0, 1);
} else {
 x_652 = x_651;
}
lean_ctor_set_uint8(x_652, 0, x_32);
if (lean_is_scalar(x_650)) {
 x_653 = lean_alloc_ctor(0, 1, 0);
} else {
 x_653 = x_650;
}
lean_ctor_set(x_653, 0, x_652);
return x_653;
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_650);
x_654 = lean_ctor_get(x_649, 0);
lean_inc_ref(x_654);
x_655 = lean_ctor_get(x_649, 1);
lean_inc_ref(x_655);
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 lean_ctor_release(x_649, 1);
 x_656 = x_649;
} else {
 lean_dec_ref(x_649);
 x_656 = lean_box(0);
}
x_657 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_654, x_6);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; uint8_t x_659; 
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
lean_dec_ref(x_657);
x_659 = lean_unbox(x_658);
if (x_659 == 0)
{
lean_object* x_660; 
lean_dec(x_40);
x_660 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_654, x_6);
lean_dec_ref(x_654);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; lean_object* x_662; uint8_t x_663; 
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 x_662 = x_660;
} else {
 lean_dec_ref(x_660);
 x_662 = lean_box(0);
}
x_663 = lean_unbox(x_661);
lean_dec(x_661);
if (x_663 == 0)
{
lean_object* x_664; 
lean_dec(x_658);
lean_dec(x_656);
lean_dec_ref(x_655);
lean_dec(x_644);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
lean_ctor_set_uint8(x_34, 0, x_32);
if (lean_is_scalar(x_662)) {
 x_664 = lean_alloc_ctor(0, 1, 0);
} else {
 x_664 = x_662;
}
lean_ctor_set(x_664, 0, x_34);
return x_664;
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
lean_dec(x_662);
lean_free_object(x_34);
x_665 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10;
lean_inc_ref(x_26);
x_666 = l_Lean_mkApp3(x_665, x_26, x_644, x_655);
x_667 = l_Lean_Meta_Sym_shareCommon___redArg(x_666, x_7);
if (lean_obj_tag(x_667) == 0)
{
lean_object* x_668; lean_object* x_669; 
x_668 = lean_ctor_get(x_667, 0);
lean_inc(x_668);
lean_dec_ref(x_667);
x_669 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; uint8_t x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; uint8_t x_679; uint8_t x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
lean_dec_ref(x_669);
x_671 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13;
x_672 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_673 = 0;
x_674 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
x_675 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_inc(x_668);
lean_inc(x_670);
lean_inc_ref(x_26);
x_676 = l_Lean_mkApp4(x_674, x_26, x_670, x_668, x_675);
x_677 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_678 = lean_array_push(x_677, x_676);
x_679 = lean_unbox(x_658);
x_680 = lean_unbox(x_658);
x_681 = l_Lean_Expr_betaRev(x_21, x_678, x_679, x_680);
lean_dec_ref(x_678);
lean_inc(x_670);
x_682 = l_Lean_mkLambda(x_672, x_673, x_670, x_681);
x_683 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_682, x_7);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; uint8_t x_689; uint8_t x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
lean_dec_ref(x_683);
lean_inc(x_670);
x_685 = l_Lean_mkNot(x_670);
x_686 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
lean_inc(x_668);
lean_inc(x_670);
x_687 = l_Lean_mkApp4(x_686, x_26, x_670, x_668, x_675);
x_688 = lean_array_push(x_677, x_687);
x_689 = lean_unbox(x_658);
x_690 = lean_unbox(x_658);
x_691 = l_Lean_Expr_betaRev(x_18, x_688, x_689, x_690);
lean_dec_ref(x_688);
x_692 = l_Lean_mkLambda(x_672, x_673, x_685, x_691);
x_693 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_692, x_7);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
lean_dec_ref(x_693);
x_695 = lean_unsigned_to_nat(4u);
x_696 = l_Lean_Expr_getBoundedAppFn(x_695, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_694);
lean_inc(x_684);
lean_inc(x_670);
x_697 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_696, x_670, x_671, x_684, x_694, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_697) == 0)
{
lean_object* x_698; lean_object* x_699; uint8_t x_700; uint8_t x_701; lean_object* x_702; lean_object* x_703; 
x_698 = lean_ctor_get(x_697, 0);
lean_inc(x_698);
lean_dec_ref(x_697);
x_699 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16;
x_700 = lean_unbox(x_658);
x_701 = lean_unbox(x_658);
lean_inc(x_694);
x_702 = l_Lean_Expr_betaRev(x_694, x_699, x_700, x_701);
x_703 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_702, x_7);
if (lean_obj_tag(x_703) == 0)
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_704 = lean_ctor_get(x_703, 0);
lean_inc(x_704);
lean_dec_ref(x_703);
x_705 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_706 = l_Lean_Expr_replaceFn(x_2, x_705);
x_707 = l_Lean_mkApp3(x_706, x_670, x_671, x_668);
x_708 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_709 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_710 = l_Lean_mkConst(x_708, x_709);
x_711 = l_Lean_mkApp3(x_710, x_29, x_684, x_694);
lean_inc(x_704);
x_712 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_698, x_707, x_704, x_711, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; uint8_t x_716; lean_object* x_717; 
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
if (lean_is_exclusive(x_712)) {
 lean_ctor_release(x_712, 0);
 x_714 = x_712;
} else {
 lean_dec_ref(x_712);
 x_714 = lean_box(0);
}
if (lean_is_scalar(x_656)) {
 x_715 = lean_alloc_ctor(1, 2, 1);
} else {
 x_715 = x_656;
}
lean_ctor_set(x_715, 0, x_704);
lean_ctor_set(x_715, 1, x_713);
x_716 = lean_unbox(x_658);
lean_dec(x_658);
lean_ctor_set_uint8(x_715, sizeof(void*)*2, x_716);
if (lean_is_scalar(x_714)) {
 x_717 = lean_alloc_ctor(0, 1, 0);
} else {
 x_717 = x_714;
}
lean_ctor_set(x_717, 0, x_715);
return x_717;
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_704);
lean_dec(x_658);
lean_dec(x_656);
x_718 = lean_ctor_get(x_712, 0);
lean_inc(x_718);
if (lean_is_exclusive(x_712)) {
 lean_ctor_release(x_712, 0);
 x_719 = x_712;
} else {
 lean_dec_ref(x_712);
 x_719 = lean_box(0);
}
if (lean_is_scalar(x_719)) {
 x_720 = lean_alloc_ctor(1, 1, 0);
} else {
 x_720 = x_719;
}
lean_ctor_set(x_720, 0, x_718);
return x_720;
}
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; 
lean_dec(x_698);
lean_dec(x_694);
lean_dec(x_684);
lean_dec(x_670);
lean_dec(x_668);
lean_dec(x_658);
lean_dec(x_656);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_721 = lean_ctor_get(x_703, 0);
lean_inc(x_721);
if (lean_is_exclusive(x_703)) {
 lean_ctor_release(x_703, 0);
 x_722 = x_703;
} else {
 lean_dec_ref(x_703);
 x_722 = lean_box(0);
}
if (lean_is_scalar(x_722)) {
 x_723 = lean_alloc_ctor(1, 1, 0);
} else {
 x_723 = x_722;
}
lean_ctor_set(x_723, 0, x_721);
return x_723;
}
}
else
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; 
lean_dec(x_694);
lean_dec(x_684);
lean_dec(x_670);
lean_dec(x_668);
lean_dec(x_658);
lean_dec(x_656);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_724 = lean_ctor_get(x_697, 0);
lean_inc(x_724);
if (lean_is_exclusive(x_697)) {
 lean_ctor_release(x_697, 0);
 x_725 = x_697;
} else {
 lean_dec_ref(x_697);
 x_725 = lean_box(0);
}
if (lean_is_scalar(x_725)) {
 x_726 = lean_alloc_ctor(1, 1, 0);
} else {
 x_726 = x_725;
}
lean_ctor_set(x_726, 0, x_724);
return x_726;
}
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; 
lean_dec(x_684);
lean_dec(x_670);
lean_dec(x_668);
lean_dec(x_658);
lean_dec(x_656);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
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
x_727 = lean_ctor_get(x_693, 0);
lean_inc(x_727);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 x_728 = x_693;
} else {
 lean_dec_ref(x_693);
 x_728 = lean_box(0);
}
if (lean_is_scalar(x_728)) {
 x_729 = lean_alloc_ctor(1, 1, 0);
} else {
 x_729 = x_728;
}
lean_ctor_set(x_729, 0, x_727);
return x_729;
}
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; 
lean_dec(x_670);
lean_dec(x_668);
lean_dec(x_658);
lean_dec(x_656);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_730 = lean_ctor_get(x_683, 0);
lean_inc(x_730);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 x_731 = x_683;
} else {
 lean_dec_ref(x_683);
 x_731 = lean_box(0);
}
if (lean_is_scalar(x_731)) {
 x_732 = lean_alloc_ctor(1, 1, 0);
} else {
 x_732 = x_731;
}
lean_ctor_set(x_732, 0, x_730);
return x_732;
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; 
lean_dec(x_668);
lean_dec(x_658);
lean_dec(x_656);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_733 = lean_ctor_get(x_669, 0);
lean_inc(x_733);
if (lean_is_exclusive(x_669)) {
 lean_ctor_release(x_669, 0);
 x_734 = x_669;
} else {
 lean_dec_ref(x_669);
 x_734 = lean_box(0);
}
if (lean_is_scalar(x_734)) {
 x_735 = lean_alloc_ctor(1, 1, 0);
} else {
 x_735 = x_734;
}
lean_ctor_set(x_735, 0, x_733);
return x_735;
}
}
else
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; 
lean_dec(x_658);
lean_dec(x_656);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_736 = lean_ctor_get(x_667, 0);
lean_inc(x_736);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 x_737 = x_667;
} else {
 lean_dec_ref(x_667);
 x_737 = lean_box(0);
}
if (lean_is_scalar(x_737)) {
 x_738 = lean_alloc_ctor(1, 1, 0);
} else {
 x_738 = x_737;
}
lean_ctor_set(x_738, 0, x_736);
return x_738;
}
}
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; 
lean_dec(x_658);
lean_dec(x_656);
lean_dec_ref(x_655);
lean_dec(x_644);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_739 = lean_ctor_get(x_660, 0);
lean_inc(x_739);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 x_740 = x_660;
} else {
 lean_dec_ref(x_660);
 x_740 = lean_box(0);
}
if (lean_is_scalar(x_740)) {
 x_741 = lean_alloc_ctor(1, 1, 0);
} else {
 x_741 = x_740;
}
lean_ctor_set(x_741, 0, x_739);
return x_741;
}
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; 
lean_dec(x_658);
lean_dec_ref(x_654);
lean_free_object(x_34);
x_742 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22;
lean_inc_ref(x_26);
x_743 = l_Lean_mkApp3(x_742, x_26, x_644, x_655);
x_744 = l_Lean_Meta_Sym_shareCommon___redArg(x_743, x_7);
if (lean_obj_tag(x_744) == 0)
{
lean_object* x_745; lean_object* x_746; 
x_745 = lean_ctor_get(x_744, 0);
lean_inc(x_745);
lean_dec_ref(x_744);
x_746 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_746) == 0)
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; uint8_t x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; uint8_t x_756; uint8_t x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
x_747 = lean_ctor_get(x_746, 0);
lean_inc(x_747);
lean_dec_ref(x_746);
x_748 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25;
x_749 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_750 = 0;
x_751 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
x_752 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_inc(x_745);
lean_inc(x_747);
lean_inc_ref(x_26);
x_753 = l_Lean_mkApp4(x_751, x_26, x_747, x_745, x_752);
x_754 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_755 = lean_array_push(x_754, x_753);
x_756 = lean_unbox(x_40);
x_757 = lean_unbox(x_40);
x_758 = l_Lean_Expr_betaRev(x_21, x_755, x_756, x_757);
lean_dec_ref(x_755);
lean_inc(x_747);
x_759 = l_Lean_mkLambda(x_749, x_750, x_747, x_758);
x_760 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_759, x_7);
if (lean_obj_tag(x_760) == 0)
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; uint8_t x_766; uint8_t x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_761 = lean_ctor_get(x_760, 0);
lean_inc(x_761);
lean_dec_ref(x_760);
lean_inc(x_747);
x_762 = l_Lean_mkNot(x_747);
x_763 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
lean_inc(x_745);
lean_inc(x_747);
x_764 = l_Lean_mkApp4(x_763, x_26, x_747, x_745, x_752);
x_765 = lean_array_push(x_754, x_764);
x_766 = lean_unbox(x_40);
x_767 = lean_unbox(x_40);
x_768 = l_Lean_Expr_betaRev(x_18, x_765, x_766, x_767);
lean_dec_ref(x_765);
x_769 = l_Lean_mkLambda(x_749, x_750, x_762, x_768);
x_770 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_769, x_7);
if (lean_obj_tag(x_770) == 0)
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_771 = lean_ctor_get(x_770, 0);
lean_inc(x_771);
lean_dec_ref(x_770);
x_772 = lean_unsigned_to_nat(4u);
x_773 = l_Lean_Expr_getBoundedAppFn(x_772, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_771);
lean_inc(x_761);
lean_inc(x_747);
x_774 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_773, x_747, x_748, x_761, x_771, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; lean_object* x_776; uint8_t x_777; uint8_t x_778; lean_object* x_779; lean_object* x_780; 
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
lean_dec_ref(x_774);
x_776 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25;
x_777 = lean_unbox(x_40);
x_778 = lean_unbox(x_40);
lean_inc(x_761);
x_779 = l_Lean_Expr_betaRev(x_761, x_776, x_777, x_778);
x_780 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_779, x_7);
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
lean_dec_ref(x_780);
x_782 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_783 = l_Lean_Expr_replaceFn(x_2, x_782);
x_784 = l_Lean_mkApp3(x_783, x_747, x_748, x_745);
x_785 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_786 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_787 = l_Lean_mkConst(x_785, x_786);
x_788 = l_Lean_mkApp3(x_787, x_29, x_761, x_771);
lean_inc(x_781);
x_789 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_775, x_784, x_781, x_788, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; uint8_t x_793; lean_object* x_794; 
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 x_791 = x_789;
} else {
 lean_dec_ref(x_789);
 x_791 = lean_box(0);
}
if (lean_is_scalar(x_656)) {
 x_792 = lean_alloc_ctor(1, 2, 1);
} else {
 x_792 = x_656;
}
lean_ctor_set(x_792, 0, x_781);
lean_ctor_set(x_792, 1, x_790);
x_793 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_792, sizeof(void*)*2, x_793);
if (lean_is_scalar(x_791)) {
 x_794 = lean_alloc_ctor(0, 1, 0);
} else {
 x_794 = x_791;
}
lean_ctor_set(x_794, 0, x_792);
return x_794;
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; 
lean_dec(x_781);
lean_dec(x_656);
lean_dec(x_40);
x_795 = lean_ctor_get(x_789, 0);
lean_inc(x_795);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 x_796 = x_789;
} else {
 lean_dec_ref(x_789);
 x_796 = lean_box(0);
}
if (lean_is_scalar(x_796)) {
 x_797 = lean_alloc_ctor(1, 1, 0);
} else {
 x_797 = x_796;
}
lean_ctor_set(x_797, 0, x_795);
return x_797;
}
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; 
lean_dec(x_775);
lean_dec(x_771);
lean_dec(x_761);
lean_dec(x_747);
lean_dec(x_745);
lean_dec(x_656);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_798 = lean_ctor_get(x_780, 0);
lean_inc(x_798);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 x_799 = x_780;
} else {
 lean_dec_ref(x_780);
 x_799 = lean_box(0);
}
if (lean_is_scalar(x_799)) {
 x_800 = lean_alloc_ctor(1, 1, 0);
} else {
 x_800 = x_799;
}
lean_ctor_set(x_800, 0, x_798);
return x_800;
}
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; 
lean_dec(x_771);
lean_dec(x_761);
lean_dec(x_747);
lean_dec(x_745);
lean_dec(x_656);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_801 = lean_ctor_get(x_774, 0);
lean_inc(x_801);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 x_802 = x_774;
} else {
 lean_dec_ref(x_774);
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
lean_object* x_804; lean_object* x_805; lean_object* x_806; 
lean_dec(x_761);
lean_dec(x_747);
lean_dec(x_745);
lean_dec(x_656);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
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
x_804 = lean_ctor_get(x_770, 0);
lean_inc(x_804);
if (lean_is_exclusive(x_770)) {
 lean_ctor_release(x_770, 0);
 x_805 = x_770;
} else {
 lean_dec_ref(x_770);
 x_805 = lean_box(0);
}
if (lean_is_scalar(x_805)) {
 x_806 = lean_alloc_ctor(1, 1, 0);
} else {
 x_806 = x_805;
}
lean_ctor_set(x_806, 0, x_804);
return x_806;
}
}
else
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; 
lean_dec(x_747);
lean_dec(x_745);
lean_dec(x_656);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_807 = lean_ctor_get(x_760, 0);
lean_inc(x_807);
if (lean_is_exclusive(x_760)) {
 lean_ctor_release(x_760, 0);
 x_808 = x_760;
} else {
 lean_dec_ref(x_760);
 x_808 = lean_box(0);
}
if (lean_is_scalar(x_808)) {
 x_809 = lean_alloc_ctor(1, 1, 0);
} else {
 x_809 = x_808;
}
lean_ctor_set(x_809, 0, x_807);
return x_809;
}
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; 
lean_dec(x_745);
lean_dec(x_656);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_810 = lean_ctor_get(x_746, 0);
lean_inc(x_810);
if (lean_is_exclusive(x_746)) {
 lean_ctor_release(x_746, 0);
 x_811 = x_746;
} else {
 lean_dec_ref(x_746);
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
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
lean_dec(x_656);
lean_dec(x_40);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_813 = lean_ctor_get(x_744, 0);
lean_inc(x_813);
if (lean_is_exclusive(x_744)) {
 lean_ctor_release(x_744, 0);
 x_814 = x_744;
} else {
 lean_dec_ref(x_744);
 x_814 = lean_box(0);
}
if (lean_is_scalar(x_814)) {
 x_815 = lean_alloc_ctor(1, 1, 0);
} else {
 x_815 = x_814;
}
lean_ctor_set(x_815, 0, x_813);
return x_815;
}
}
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; 
lean_dec(x_656);
lean_dec_ref(x_655);
lean_dec_ref(x_654);
lean_dec(x_644);
lean_dec(x_40);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_816 = lean_ctor_get(x_657, 0);
lean_inc(x_816);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 x_817 = x_657;
} else {
 lean_dec_ref(x_657);
 x_817 = lean_box(0);
}
if (lean_is_scalar(x_817)) {
 x_818 = lean_alloc_ctor(1, 1, 0);
} else {
 x_818 = x_817;
}
lean_ctor_set(x_818, 0, x_816);
return x_818;
}
}
}
else
{
lean_dec(x_644);
lean_dec(x_40);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
return x_648;
}
}
else
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; 
lean_dec(x_644);
lean_dec(x_40);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_819 = lean_ctor_get(x_646, 0);
lean_inc(x_819);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 x_820 = x_646;
} else {
 lean_dec_ref(x_646);
 x_820 = lean_box(0);
}
if (lean_is_scalar(x_820)) {
 x_821 = lean_alloc_ctor(1, 1, 0);
} else {
 x_821 = x_820;
}
lean_ctor_set(x_821, 0, x_819);
return x_821;
}
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; 
lean_dec(x_40);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_822 = lean_ctor_get(x_643, 0);
lean_inc(x_822);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 x_823 = x_643;
} else {
 lean_dec_ref(x_643);
 x_823 = lean_box(0);
}
if (lean_is_scalar(x_823)) {
 x_824 = lean_alloc_ctor(1, 1, 0);
} else {
 x_824 = x_823;
}
lean_ctor_set(x_824, 0, x_822);
return x_824;
}
}
else
{
uint8_t x_825; lean_object* x_826; 
lean_dec(x_641);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_825 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_34, 0, x_825);
x_826 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_826, 0, x_34);
return x_826;
}
}
}
else
{
uint8_t x_827; 
lean_dec(x_40);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_827 = !lean_is_exclusive(x_45);
if (x_827 == 0)
{
return x_45;
}
else
{
lean_object* x_828; lean_object* x_829; 
x_828 = lean_ctor_get(x_45, 0);
lean_inc(x_828);
lean_dec(x_45);
x_829 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_829, 0, x_828);
return x_829;
}
}
}
else
{
lean_object* x_830; uint8_t x_831; uint8_t x_832; lean_object* x_833; lean_object* x_834; 
lean_dec(x_40);
lean_free_object(x_34);
lean_dec_ref(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_830 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16;
x_831 = lean_unbox(x_37);
x_832 = lean_unbox(x_37);
lean_inc_ref(x_18);
x_833 = l_Lean_Expr_betaRev(x_18, x_830, x_831, x_832);
x_834 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_833, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_834) == 0)
{
uint8_t x_835; 
x_835 = !lean_is_exclusive(x_834);
if (x_835 == 0)
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; uint8_t x_842; 
x_836 = lean_ctor_get(x_834, 0);
x_837 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_838 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_839 = l_Lean_mkConst(x_837, x_838);
x_840 = l_Lean_mkApp3(x_839, x_29, x_21, x_18);
x_841 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_841, 0, x_836);
lean_ctor_set(x_841, 1, x_840);
x_842 = lean_unbox(x_37);
lean_dec(x_37);
lean_ctor_set_uint8(x_841, sizeof(void*)*2, x_842);
lean_ctor_set(x_834, 0, x_841);
return x_834;
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; uint8_t x_849; lean_object* x_850; 
x_843 = lean_ctor_get(x_834, 0);
lean_inc(x_843);
lean_dec(x_834);
x_844 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_845 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_846 = l_Lean_mkConst(x_844, x_845);
x_847 = l_Lean_mkApp3(x_846, x_29, x_21, x_18);
x_848 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_848, 0, x_843);
lean_ctor_set(x_848, 1, x_847);
x_849 = lean_unbox(x_37);
lean_dec(x_37);
lean_ctor_set_uint8(x_848, sizeof(void*)*2, x_849);
x_850 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_850, 0, x_848);
return x_850;
}
}
else
{
uint8_t x_851; 
lean_dec(x_37);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_851 = !lean_is_exclusive(x_834);
if (x_851 == 0)
{
return x_834;
}
else
{
lean_object* x_852; lean_object* x_853; 
x_852 = lean_ctor_get(x_834, 0);
lean_inc(x_852);
lean_dec(x_834);
x_853 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_853, 0, x_852);
return x_853;
}
}
}
}
else
{
uint8_t x_854; 
lean_dec(x_37);
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_854 = !lean_is_exclusive(x_39);
if (x_854 == 0)
{
return x_39;
}
else
{
lean_object* x_855; lean_object* x_856; 
x_855 = lean_ctor_get(x_39, 0);
lean_inc(x_855);
lean_dec(x_39);
x_856 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_856, 0, x_855);
return x_856;
}
}
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; 
lean_dec(x_37);
lean_free_object(x_34);
lean_dec_ref(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_857 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25;
lean_inc_ref(x_21);
x_858 = l_Lean_Expr_betaRev(x_21, x_857, x_1, x_1);
x_859 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_858, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_859) == 0)
{
uint8_t x_860; 
x_860 = !lean_is_exclusive(x_859);
if (x_860 == 0)
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; 
x_861 = lean_ctor_get(x_859, 0);
x_862 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_863 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_864 = l_Lean_mkConst(x_862, x_863);
x_865 = l_Lean_mkApp3(x_864, x_29, x_21, x_18);
x_866 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_866, 0, x_861);
lean_ctor_set(x_866, 1, x_865);
lean_ctor_set_uint8(x_866, sizeof(void*)*2, x_1);
lean_ctor_set(x_859, 0, x_866);
return x_859;
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; 
x_867 = lean_ctor_get(x_859, 0);
lean_inc(x_867);
lean_dec(x_859);
x_868 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_869 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_870 = l_Lean_mkConst(x_868, x_869);
x_871 = l_Lean_mkApp3(x_870, x_29, x_21, x_18);
x_872 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_872, 0, x_867);
lean_ctor_set(x_872, 1, x_871);
lean_ctor_set_uint8(x_872, sizeof(void*)*2, x_1);
x_873 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_873, 0, x_872);
return x_873;
}
}
else
{
uint8_t x_874; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_874 = !lean_is_exclusive(x_859);
if (x_874 == 0)
{
return x_859;
}
else
{
lean_object* x_875; lean_object* x_876; 
x_875 = lean_ctor_get(x_859, 0);
lean_inc(x_875);
lean_dec(x_859);
x_876 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_876, 0, x_875);
return x_876;
}
}
}
}
else
{
uint8_t x_877; 
lean_free_object(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_877 = !lean_is_exclusive(x_36);
if (x_877 == 0)
{
return x_36;
}
else
{
lean_object* x_878; lean_object* x_879; 
x_878 = lean_ctor_get(x_36, 0);
lean_inc(x_878);
lean_dec(x_36);
x_879 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_879, 0, x_878);
return x_879;
}
}
}
else
{
lean_object* x_880; 
lean_dec(x_34);
x_880 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_26, x_6);
if (lean_obj_tag(x_880) == 0)
{
lean_object* x_881; uint8_t x_882; 
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
lean_dec_ref(x_880);
x_882 = lean_unbox(x_881);
if (x_882 == 0)
{
lean_object* x_883; 
x_883 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_26, x_6);
if (lean_obj_tag(x_883) == 0)
{
lean_object* x_884; uint8_t x_885; 
x_884 = lean_ctor_get(x_883, 0);
lean_inc(x_884);
lean_dec_ref(x_883);
x_885 = lean_unbox(x_884);
if (x_885 == 0)
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; 
lean_dec(x_881);
x_886 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4;
lean_inc_ref(x_26);
x_887 = l_Lean_Expr_app___override(x_886, x_26);
x_888 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_889 = l_Lean_Meta_trySynthInstance(x_887, x_888, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_889) == 0)
{
lean_object* x_890; lean_object* x_891; 
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 x_891 = x_889;
} else {
 lean_dec_ref(x_889);
 x_891 = lean_box(0);
}
if (lean_obj_tag(x_890) == 1)
{
lean_object* x_892; lean_object* x_893; 
lean_dec(x_891);
x_892 = lean_ctor_get(x_890, 0);
lean_inc(x_892);
lean_dec_ref(x_890);
x_893 = l_Lean_Meta_Sym_shareCommon___redArg(x_892, x_7);
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; 
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
lean_dec_ref(x_893);
x_895 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_894);
lean_inc_ref(x_26);
x_896 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_895, x_26, x_894, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_896) == 0)
{
lean_object* x_897; lean_object* x_898; 
x_897 = lean_ctor_get(x_896, 0);
lean_inc(x_897);
lean_dec_ref(x_896);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_898 = lean_sym_simp(x_897, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_898) == 0)
{
lean_object* x_899; lean_object* x_900; 
x_899 = lean_ctor_get(x_898, 0);
lean_inc(x_899);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 x_900 = x_898;
} else {
 lean_dec_ref(x_898);
 x_900 = lean_box(0);
}
if (lean_obj_tag(x_899) == 0)
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; 
lean_dec(x_894);
lean_dec(x_884);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
if (lean_is_exclusive(x_899)) {
 x_901 = x_899;
} else {
 lean_dec_ref(x_899);
 x_901 = lean_box(0);
}
if (lean_is_scalar(x_901)) {
 x_902 = lean_alloc_ctor(0, 0, 1);
} else {
 x_902 = x_901;
}
lean_ctor_set_uint8(x_902, 0, x_32);
if (lean_is_scalar(x_900)) {
 x_903 = lean_alloc_ctor(0, 1, 0);
} else {
 x_903 = x_900;
}
lean_ctor_set(x_903, 0, x_902);
return x_903;
}
else
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; 
lean_dec(x_900);
x_904 = lean_ctor_get(x_899, 0);
lean_inc_ref(x_904);
x_905 = lean_ctor_get(x_899, 1);
lean_inc_ref(x_905);
if (lean_is_exclusive(x_899)) {
 lean_ctor_release(x_899, 0);
 lean_ctor_release(x_899, 1);
 x_906 = x_899;
} else {
 lean_dec_ref(x_899);
 x_906 = lean_box(0);
}
x_907 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_904, x_6);
if (lean_obj_tag(x_907) == 0)
{
lean_object* x_908; uint8_t x_909; 
x_908 = lean_ctor_get(x_907, 0);
lean_inc(x_908);
lean_dec_ref(x_907);
x_909 = lean_unbox(x_908);
if (x_909 == 0)
{
lean_object* x_910; 
lean_dec(x_884);
x_910 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_904, x_6);
lean_dec_ref(x_904);
if (lean_obj_tag(x_910) == 0)
{
lean_object* x_911; lean_object* x_912; uint8_t x_913; 
x_911 = lean_ctor_get(x_910, 0);
lean_inc(x_911);
if (lean_is_exclusive(x_910)) {
 lean_ctor_release(x_910, 0);
 x_912 = x_910;
} else {
 lean_dec_ref(x_910);
 x_912 = lean_box(0);
}
x_913 = lean_unbox(x_911);
lean_dec(x_911);
if (x_913 == 0)
{
lean_object* x_914; lean_object* x_915; 
lean_dec(x_908);
lean_dec(x_906);
lean_dec_ref(x_905);
lean_dec(x_894);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_914 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_914, 0, x_32);
if (lean_is_scalar(x_912)) {
 x_915 = lean_alloc_ctor(0, 1, 0);
} else {
 x_915 = x_912;
}
lean_ctor_set(x_915, 0, x_914);
return x_915;
}
else
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; 
lean_dec(x_912);
x_916 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10;
lean_inc_ref(x_26);
x_917 = l_Lean_mkApp3(x_916, x_26, x_894, x_905);
x_918 = l_Lean_Meta_Sym_shareCommon___redArg(x_917, x_7);
if (lean_obj_tag(x_918) == 0)
{
lean_object* x_919; lean_object* x_920; 
x_919 = lean_ctor_get(x_918, 0);
lean_inc(x_919);
lean_dec_ref(x_918);
x_920 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_920) == 0)
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; uint8_t x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; uint8_t x_930; uint8_t x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
x_921 = lean_ctor_get(x_920, 0);
lean_inc(x_921);
lean_dec_ref(x_920);
x_922 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13;
x_923 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_924 = 0;
x_925 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
x_926 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_inc(x_919);
lean_inc(x_921);
lean_inc_ref(x_26);
x_927 = l_Lean_mkApp4(x_925, x_26, x_921, x_919, x_926);
x_928 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_929 = lean_array_push(x_928, x_927);
x_930 = lean_unbox(x_908);
x_931 = lean_unbox(x_908);
x_932 = l_Lean_Expr_betaRev(x_21, x_929, x_930, x_931);
lean_dec_ref(x_929);
lean_inc(x_921);
x_933 = l_Lean_mkLambda(x_923, x_924, x_921, x_932);
x_934 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_933, x_7);
if (lean_obj_tag(x_934) == 0)
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; uint8_t x_940; uint8_t x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; 
x_935 = lean_ctor_get(x_934, 0);
lean_inc(x_935);
lean_dec_ref(x_934);
lean_inc(x_921);
x_936 = l_Lean_mkNot(x_921);
x_937 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
lean_inc(x_919);
lean_inc(x_921);
x_938 = l_Lean_mkApp4(x_937, x_26, x_921, x_919, x_926);
x_939 = lean_array_push(x_928, x_938);
x_940 = lean_unbox(x_908);
x_941 = lean_unbox(x_908);
x_942 = l_Lean_Expr_betaRev(x_18, x_939, x_940, x_941);
lean_dec_ref(x_939);
x_943 = l_Lean_mkLambda(x_923, x_924, x_936, x_942);
x_944 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_943, x_7);
if (lean_obj_tag(x_944) == 0)
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; 
x_945 = lean_ctor_get(x_944, 0);
lean_inc(x_945);
lean_dec_ref(x_944);
x_946 = lean_unsigned_to_nat(4u);
x_947 = l_Lean_Expr_getBoundedAppFn(x_946, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_945);
lean_inc(x_935);
lean_inc(x_921);
x_948 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_947, x_921, x_922, x_935, x_945, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_948) == 0)
{
lean_object* x_949; lean_object* x_950; uint8_t x_951; uint8_t x_952; lean_object* x_953; lean_object* x_954; 
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
lean_dec_ref(x_948);
x_950 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16;
x_951 = lean_unbox(x_908);
x_952 = lean_unbox(x_908);
lean_inc(x_945);
x_953 = l_Lean_Expr_betaRev(x_945, x_950, x_951, x_952);
x_954 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_953, x_7);
if (lean_obj_tag(x_954) == 0)
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; 
x_955 = lean_ctor_get(x_954, 0);
lean_inc(x_955);
lean_dec_ref(x_954);
x_956 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_957 = l_Lean_Expr_replaceFn(x_2, x_956);
x_958 = l_Lean_mkApp3(x_957, x_921, x_922, x_919);
x_959 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_960 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_961 = l_Lean_mkConst(x_959, x_960);
x_962 = l_Lean_mkApp3(x_961, x_29, x_935, x_945);
lean_inc(x_955);
x_963 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_949, x_958, x_955, x_962, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_963) == 0)
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; uint8_t x_967; lean_object* x_968; 
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
if (lean_is_exclusive(x_963)) {
 lean_ctor_release(x_963, 0);
 x_965 = x_963;
} else {
 lean_dec_ref(x_963);
 x_965 = lean_box(0);
}
if (lean_is_scalar(x_906)) {
 x_966 = lean_alloc_ctor(1, 2, 1);
} else {
 x_966 = x_906;
}
lean_ctor_set(x_966, 0, x_955);
lean_ctor_set(x_966, 1, x_964);
x_967 = lean_unbox(x_908);
lean_dec(x_908);
lean_ctor_set_uint8(x_966, sizeof(void*)*2, x_967);
if (lean_is_scalar(x_965)) {
 x_968 = lean_alloc_ctor(0, 1, 0);
} else {
 x_968 = x_965;
}
lean_ctor_set(x_968, 0, x_966);
return x_968;
}
else
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; 
lean_dec(x_955);
lean_dec(x_908);
lean_dec(x_906);
x_969 = lean_ctor_get(x_963, 0);
lean_inc(x_969);
if (lean_is_exclusive(x_963)) {
 lean_ctor_release(x_963, 0);
 x_970 = x_963;
} else {
 lean_dec_ref(x_963);
 x_970 = lean_box(0);
}
if (lean_is_scalar(x_970)) {
 x_971 = lean_alloc_ctor(1, 1, 0);
} else {
 x_971 = x_970;
}
lean_ctor_set(x_971, 0, x_969);
return x_971;
}
}
else
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; 
lean_dec(x_949);
lean_dec(x_945);
lean_dec(x_935);
lean_dec(x_921);
lean_dec(x_919);
lean_dec(x_908);
lean_dec(x_906);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_972 = lean_ctor_get(x_954, 0);
lean_inc(x_972);
if (lean_is_exclusive(x_954)) {
 lean_ctor_release(x_954, 0);
 x_973 = x_954;
} else {
 lean_dec_ref(x_954);
 x_973 = lean_box(0);
}
if (lean_is_scalar(x_973)) {
 x_974 = lean_alloc_ctor(1, 1, 0);
} else {
 x_974 = x_973;
}
lean_ctor_set(x_974, 0, x_972);
return x_974;
}
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; 
lean_dec(x_945);
lean_dec(x_935);
lean_dec(x_921);
lean_dec(x_919);
lean_dec(x_908);
lean_dec(x_906);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_975 = lean_ctor_get(x_948, 0);
lean_inc(x_975);
if (lean_is_exclusive(x_948)) {
 lean_ctor_release(x_948, 0);
 x_976 = x_948;
} else {
 lean_dec_ref(x_948);
 x_976 = lean_box(0);
}
if (lean_is_scalar(x_976)) {
 x_977 = lean_alloc_ctor(1, 1, 0);
} else {
 x_977 = x_976;
}
lean_ctor_set(x_977, 0, x_975);
return x_977;
}
}
else
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; 
lean_dec(x_935);
lean_dec(x_921);
lean_dec(x_919);
lean_dec(x_908);
lean_dec(x_906);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
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
x_978 = lean_ctor_get(x_944, 0);
lean_inc(x_978);
if (lean_is_exclusive(x_944)) {
 lean_ctor_release(x_944, 0);
 x_979 = x_944;
} else {
 lean_dec_ref(x_944);
 x_979 = lean_box(0);
}
if (lean_is_scalar(x_979)) {
 x_980 = lean_alloc_ctor(1, 1, 0);
} else {
 x_980 = x_979;
}
lean_ctor_set(x_980, 0, x_978);
return x_980;
}
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; 
lean_dec(x_921);
lean_dec(x_919);
lean_dec(x_908);
lean_dec(x_906);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_981 = lean_ctor_get(x_934, 0);
lean_inc(x_981);
if (lean_is_exclusive(x_934)) {
 lean_ctor_release(x_934, 0);
 x_982 = x_934;
} else {
 lean_dec_ref(x_934);
 x_982 = lean_box(0);
}
if (lean_is_scalar(x_982)) {
 x_983 = lean_alloc_ctor(1, 1, 0);
} else {
 x_983 = x_982;
}
lean_ctor_set(x_983, 0, x_981);
return x_983;
}
}
else
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; 
lean_dec(x_919);
lean_dec(x_908);
lean_dec(x_906);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_984 = lean_ctor_get(x_920, 0);
lean_inc(x_984);
if (lean_is_exclusive(x_920)) {
 lean_ctor_release(x_920, 0);
 x_985 = x_920;
} else {
 lean_dec_ref(x_920);
 x_985 = lean_box(0);
}
if (lean_is_scalar(x_985)) {
 x_986 = lean_alloc_ctor(1, 1, 0);
} else {
 x_986 = x_985;
}
lean_ctor_set(x_986, 0, x_984);
return x_986;
}
}
else
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; 
lean_dec(x_908);
lean_dec(x_906);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_987 = lean_ctor_get(x_918, 0);
lean_inc(x_987);
if (lean_is_exclusive(x_918)) {
 lean_ctor_release(x_918, 0);
 x_988 = x_918;
} else {
 lean_dec_ref(x_918);
 x_988 = lean_box(0);
}
if (lean_is_scalar(x_988)) {
 x_989 = lean_alloc_ctor(1, 1, 0);
} else {
 x_989 = x_988;
}
lean_ctor_set(x_989, 0, x_987);
return x_989;
}
}
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; 
lean_dec(x_908);
lean_dec(x_906);
lean_dec_ref(x_905);
lean_dec(x_894);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_990 = lean_ctor_get(x_910, 0);
lean_inc(x_990);
if (lean_is_exclusive(x_910)) {
 lean_ctor_release(x_910, 0);
 x_991 = x_910;
} else {
 lean_dec_ref(x_910);
 x_991 = lean_box(0);
}
if (lean_is_scalar(x_991)) {
 x_992 = lean_alloc_ctor(1, 1, 0);
} else {
 x_992 = x_991;
}
lean_ctor_set(x_992, 0, x_990);
return x_992;
}
}
else
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; 
lean_dec(x_908);
lean_dec_ref(x_904);
x_993 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22;
lean_inc_ref(x_26);
x_994 = l_Lean_mkApp3(x_993, x_26, x_894, x_905);
x_995 = l_Lean_Meta_Sym_shareCommon___redArg(x_994, x_7);
if (lean_obj_tag(x_995) == 0)
{
lean_object* x_996; lean_object* x_997; 
x_996 = lean_ctor_get(x_995, 0);
lean_inc(x_996);
lean_dec_ref(x_995);
x_997 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_997) == 0)
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; uint8_t x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; uint8_t x_1007; uint8_t x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
x_998 = lean_ctor_get(x_997, 0);
lean_inc(x_998);
lean_dec_ref(x_997);
x_999 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25;
x_1000 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_1001 = 0;
x_1002 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
x_1003 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_inc(x_996);
lean_inc(x_998);
lean_inc_ref(x_26);
x_1004 = l_Lean_mkApp4(x_1002, x_26, x_998, x_996, x_1003);
x_1005 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_1006 = lean_array_push(x_1005, x_1004);
x_1007 = lean_unbox(x_884);
x_1008 = lean_unbox(x_884);
x_1009 = l_Lean_Expr_betaRev(x_21, x_1006, x_1007, x_1008);
lean_dec_ref(x_1006);
lean_inc(x_998);
x_1010 = l_Lean_mkLambda(x_1000, x_1001, x_998, x_1009);
x_1011 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1010, x_7);
if (lean_obj_tag(x_1011) == 0)
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; uint8_t x_1017; uint8_t x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1012 = lean_ctor_get(x_1011, 0);
lean_inc(x_1012);
lean_dec_ref(x_1011);
lean_inc(x_998);
x_1013 = l_Lean_mkNot(x_998);
x_1014 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
lean_inc(x_996);
lean_inc(x_998);
x_1015 = l_Lean_mkApp4(x_1014, x_26, x_998, x_996, x_1003);
x_1016 = lean_array_push(x_1005, x_1015);
x_1017 = lean_unbox(x_884);
x_1018 = lean_unbox(x_884);
x_1019 = l_Lean_Expr_betaRev(x_18, x_1016, x_1017, x_1018);
lean_dec_ref(x_1016);
x_1020 = l_Lean_mkLambda(x_1000, x_1001, x_1013, x_1019);
x_1021 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1020, x_7);
if (lean_obj_tag(x_1021) == 0)
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
x_1022 = lean_ctor_get(x_1021, 0);
lean_inc(x_1022);
lean_dec_ref(x_1021);
x_1023 = lean_unsigned_to_nat(4u);
x_1024 = l_Lean_Expr_getBoundedAppFn(x_1023, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_1022);
lean_inc(x_1012);
lean_inc(x_998);
x_1025 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_1024, x_998, x_999, x_1012, x_1022, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_1025) == 0)
{
lean_object* x_1026; lean_object* x_1027; uint8_t x_1028; uint8_t x_1029; lean_object* x_1030; lean_object* x_1031; 
x_1026 = lean_ctor_get(x_1025, 0);
lean_inc(x_1026);
lean_dec_ref(x_1025);
x_1027 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25;
x_1028 = lean_unbox(x_884);
x_1029 = lean_unbox(x_884);
lean_inc(x_1012);
x_1030 = l_Lean_Expr_betaRev(x_1012, x_1027, x_1028, x_1029);
x_1031 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1030, x_7);
if (lean_obj_tag(x_1031) == 0)
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
lean_dec_ref(x_1031);
x_1033 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_1034 = l_Lean_Expr_replaceFn(x_2, x_1033);
x_1035 = l_Lean_mkApp3(x_1034, x_998, x_999, x_996);
x_1036 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_1037 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_1038 = l_Lean_mkConst(x_1036, x_1037);
x_1039 = l_Lean_mkApp3(x_1038, x_29, x_1012, x_1022);
lean_inc(x_1032);
x_1040 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_1026, x_1035, x_1032, x_1039, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_1040) == 0)
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; uint8_t x_1044; lean_object* x_1045; 
x_1041 = lean_ctor_get(x_1040, 0);
lean_inc(x_1041);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 x_1042 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1042 = lean_box(0);
}
if (lean_is_scalar(x_906)) {
 x_1043 = lean_alloc_ctor(1, 2, 1);
} else {
 x_1043 = x_906;
}
lean_ctor_set(x_1043, 0, x_1032);
lean_ctor_set(x_1043, 1, x_1041);
x_1044 = lean_unbox(x_884);
lean_dec(x_884);
lean_ctor_set_uint8(x_1043, sizeof(void*)*2, x_1044);
if (lean_is_scalar(x_1042)) {
 x_1045 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1045 = x_1042;
}
lean_ctor_set(x_1045, 0, x_1043);
return x_1045;
}
else
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; 
lean_dec(x_1032);
lean_dec(x_906);
lean_dec(x_884);
x_1046 = lean_ctor_get(x_1040, 0);
lean_inc(x_1046);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 x_1047 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1047 = lean_box(0);
}
if (lean_is_scalar(x_1047)) {
 x_1048 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1048 = x_1047;
}
lean_ctor_set(x_1048, 0, x_1046);
return x_1048;
}
}
else
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
lean_dec(x_1026);
lean_dec(x_1022);
lean_dec(x_1012);
lean_dec(x_998);
lean_dec(x_996);
lean_dec(x_906);
lean_dec(x_884);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_1049 = lean_ctor_get(x_1031, 0);
lean_inc(x_1049);
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 x_1050 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1050 = lean_box(0);
}
if (lean_is_scalar(x_1050)) {
 x_1051 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1051 = x_1050;
}
lean_ctor_set(x_1051, 0, x_1049);
return x_1051;
}
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
lean_dec(x_1022);
lean_dec(x_1012);
lean_dec(x_998);
lean_dec(x_996);
lean_dec(x_906);
lean_dec(x_884);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_1052 = lean_ctor_get(x_1025, 0);
lean_inc(x_1052);
if (lean_is_exclusive(x_1025)) {
 lean_ctor_release(x_1025, 0);
 x_1053 = x_1025;
} else {
 lean_dec_ref(x_1025);
 x_1053 = lean_box(0);
}
if (lean_is_scalar(x_1053)) {
 x_1054 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1054 = x_1053;
}
lean_ctor_set(x_1054, 0, x_1052);
return x_1054;
}
}
else
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; 
lean_dec(x_1012);
lean_dec(x_998);
lean_dec(x_996);
lean_dec(x_906);
lean_dec(x_884);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
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
x_1055 = lean_ctor_get(x_1021, 0);
lean_inc(x_1055);
if (lean_is_exclusive(x_1021)) {
 lean_ctor_release(x_1021, 0);
 x_1056 = x_1021;
} else {
 lean_dec_ref(x_1021);
 x_1056 = lean_box(0);
}
if (lean_is_scalar(x_1056)) {
 x_1057 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1057 = x_1056;
}
lean_ctor_set(x_1057, 0, x_1055);
return x_1057;
}
}
else
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
lean_dec(x_998);
lean_dec(x_996);
lean_dec(x_906);
lean_dec(x_884);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_1058 = lean_ctor_get(x_1011, 0);
lean_inc(x_1058);
if (lean_is_exclusive(x_1011)) {
 lean_ctor_release(x_1011, 0);
 x_1059 = x_1011;
} else {
 lean_dec_ref(x_1011);
 x_1059 = lean_box(0);
}
if (lean_is_scalar(x_1059)) {
 x_1060 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1060 = x_1059;
}
lean_ctor_set(x_1060, 0, x_1058);
return x_1060;
}
}
else
{
lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; 
lean_dec(x_996);
lean_dec(x_906);
lean_dec(x_884);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_1061 = lean_ctor_get(x_997, 0);
lean_inc(x_1061);
if (lean_is_exclusive(x_997)) {
 lean_ctor_release(x_997, 0);
 x_1062 = x_997;
} else {
 lean_dec_ref(x_997);
 x_1062 = lean_box(0);
}
if (lean_is_scalar(x_1062)) {
 x_1063 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1063 = x_1062;
}
lean_ctor_set(x_1063, 0, x_1061);
return x_1063;
}
}
else
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
lean_dec(x_906);
lean_dec(x_884);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_1064 = lean_ctor_get(x_995, 0);
lean_inc(x_1064);
if (lean_is_exclusive(x_995)) {
 lean_ctor_release(x_995, 0);
 x_1065 = x_995;
} else {
 lean_dec_ref(x_995);
 x_1065 = lean_box(0);
}
if (lean_is_scalar(x_1065)) {
 x_1066 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1066 = x_1065;
}
lean_ctor_set(x_1066, 0, x_1064);
return x_1066;
}
}
}
else
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
lean_dec(x_906);
lean_dec_ref(x_905);
lean_dec_ref(x_904);
lean_dec(x_894);
lean_dec(x_884);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_1067 = lean_ctor_get(x_907, 0);
lean_inc(x_1067);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 x_1068 = x_907;
} else {
 lean_dec_ref(x_907);
 x_1068 = lean_box(0);
}
if (lean_is_scalar(x_1068)) {
 x_1069 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1069 = x_1068;
}
lean_ctor_set(x_1069, 0, x_1067);
return x_1069;
}
}
}
else
{
lean_dec(x_894);
lean_dec(x_884);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
return x_898;
}
}
else
{
lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; 
lean_dec(x_894);
lean_dec(x_884);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_1070 = lean_ctor_get(x_896, 0);
lean_inc(x_1070);
if (lean_is_exclusive(x_896)) {
 lean_ctor_release(x_896, 0);
 x_1071 = x_896;
} else {
 lean_dec_ref(x_896);
 x_1071 = lean_box(0);
}
if (lean_is_scalar(x_1071)) {
 x_1072 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1072 = x_1071;
}
lean_ctor_set(x_1072, 0, x_1070);
return x_1072;
}
}
else
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
lean_dec(x_884);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_1073 = lean_ctor_get(x_893, 0);
lean_inc(x_1073);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 x_1074 = x_893;
} else {
 lean_dec_ref(x_893);
 x_1074 = lean_box(0);
}
if (lean_is_scalar(x_1074)) {
 x_1075 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1075 = x_1074;
}
lean_ctor_set(x_1075, 0, x_1073);
return x_1075;
}
}
else
{
lean_object* x_1076; uint8_t x_1077; lean_object* x_1078; 
lean_dec(x_890);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_1076 = lean_alloc_ctor(0, 0, 1);
x_1077 = lean_unbox(x_884);
lean_dec(x_884);
lean_ctor_set_uint8(x_1076, 0, x_1077);
if (lean_is_scalar(x_891)) {
 x_1078 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1078 = x_891;
}
lean_ctor_set(x_1078, 0, x_1076);
return x_1078;
}
}
else
{
lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
lean_dec(x_884);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_1079 = lean_ctor_get(x_889, 0);
lean_inc(x_1079);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 x_1080 = x_889;
} else {
 lean_dec_ref(x_889);
 x_1080 = lean_box(0);
}
if (lean_is_scalar(x_1080)) {
 x_1081 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1081 = x_1080;
}
lean_ctor_set(x_1081, 0, x_1079);
return x_1081;
}
}
else
{
lean_object* x_1082; uint8_t x_1083; uint8_t x_1084; lean_object* x_1085; lean_object* x_1086; 
lean_dec(x_884);
lean_dec_ref(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1082 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16;
x_1083 = lean_unbox(x_881);
x_1084 = lean_unbox(x_881);
lean_inc_ref(x_18);
x_1085 = l_Lean_Expr_betaRev(x_18, x_1082, x_1083, x_1084);
x_1086 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1085, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_1086) == 0)
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; uint8_t x_1094; lean_object* x_1095; 
x_1087 = lean_ctor_get(x_1086, 0);
lean_inc(x_1087);
if (lean_is_exclusive(x_1086)) {
 lean_ctor_release(x_1086, 0);
 x_1088 = x_1086;
} else {
 lean_dec_ref(x_1086);
 x_1088 = lean_box(0);
}
x_1089 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_1090 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_1091 = l_Lean_mkConst(x_1089, x_1090);
x_1092 = l_Lean_mkApp3(x_1091, x_29, x_21, x_18);
x_1093 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_1093, 0, x_1087);
lean_ctor_set(x_1093, 1, x_1092);
x_1094 = lean_unbox(x_881);
lean_dec(x_881);
lean_ctor_set_uint8(x_1093, sizeof(void*)*2, x_1094);
if (lean_is_scalar(x_1088)) {
 x_1095 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1095 = x_1088;
}
lean_ctor_set(x_1095, 0, x_1093);
return x_1095;
}
else
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
lean_dec(x_881);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_1096 = lean_ctor_get(x_1086, 0);
lean_inc(x_1096);
if (lean_is_exclusive(x_1086)) {
 lean_ctor_release(x_1086, 0);
 x_1097 = x_1086;
} else {
 lean_dec_ref(x_1086);
 x_1097 = lean_box(0);
}
if (lean_is_scalar(x_1097)) {
 x_1098 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1098 = x_1097;
}
lean_ctor_set(x_1098, 0, x_1096);
return x_1098;
}
}
}
else
{
lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; 
lean_dec(x_881);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_1099 = lean_ctor_get(x_883, 0);
lean_inc(x_1099);
if (lean_is_exclusive(x_883)) {
 lean_ctor_release(x_883, 0);
 x_1100 = x_883;
} else {
 lean_dec_ref(x_883);
 x_1100 = lean_box(0);
}
if (lean_is_scalar(x_1100)) {
 x_1101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1101 = x_1100;
}
lean_ctor_set(x_1101, 0, x_1099);
return x_1101;
}
}
else
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; 
lean_dec(x_881);
lean_dec_ref(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1102 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25;
lean_inc_ref(x_21);
x_1103 = l_Lean_Expr_betaRev(x_21, x_1102, x_1, x_1);
x_1104 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1103, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_1104) == 0)
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; 
x_1105 = lean_ctor_get(x_1104, 0);
lean_inc(x_1105);
if (lean_is_exclusive(x_1104)) {
 lean_ctor_release(x_1104, 0);
 x_1106 = x_1104;
} else {
 lean_dec_ref(x_1104);
 x_1106 = lean_box(0);
}
x_1107 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_1108 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec_ref(x_30);
x_1109 = l_Lean_mkConst(x_1107, x_1108);
x_1110 = l_Lean_mkApp3(x_1109, x_29, x_21, x_18);
x_1111 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_1111, 0, x_1105);
lean_ctor_set(x_1111, 1, x_1110);
lean_ctor_set_uint8(x_1111, sizeof(void*)*2, x_1);
if (lean_is_scalar(x_1106)) {
 x_1112 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1112 = x_1106;
}
lean_ctor_set(x_1112, 0, x_1111);
return x_1112;
}
else
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_1113 = lean_ctor_get(x_1104, 0);
lean_inc(x_1113);
if (lean_is_exclusive(x_1104)) {
 lean_ctor_release(x_1104, 0);
 x_1114 = x_1104;
} else {
 lean_dec_ref(x_1104);
 x_1114 = lean_box(0);
}
if (lean_is_scalar(x_1114)) {
 x_1115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1115 = x_1114;
}
lean_ctor_set(x_1115, 0, x_1113);
return x_1115;
}
}
}
else
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
x_1116 = lean_ctor_get(x_880, 0);
lean_inc(x_1116);
if (lean_is_exclusive(x_880)) {
 lean_ctor_release(x_880, 0);
 x_1117 = x_880;
} else {
 lean_dec_ref(x_880);
 x_1117 = lean_box(0);
}
if (lean_is_scalar(x_1117)) {
 x_1118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1118 = x_1117;
}
lean_ctor_set(x_1118, 0, x_1116);
return x_1118;
}
}
}
else
{
uint8_t x_1119; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
x_1119 = !lean_is_exclusive(x_34);
if (x_1119 == 0)
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
x_1120 = lean_ctor_get(x_34, 0);
x_1121 = lean_ctor_get(x_34, 1);
x_1122 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_1120, x_6);
if (lean_obj_tag(x_1122) == 0)
{
lean_object* x_1123; uint8_t x_1124; 
x_1123 = lean_ctor_get(x_1122, 0);
lean_inc(x_1123);
lean_dec_ref(x_1122);
x_1124 = lean_unbox(x_1123);
if (x_1124 == 0)
{
lean_object* x_1125; 
x_1125 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_1120, x_6);
if (lean_obj_tag(x_1125) == 0)
{
lean_object* x_1126; uint8_t x_1127; 
x_1126 = lean_ctor_get(x_1125, 0);
lean_inc(x_1126);
lean_dec_ref(x_1125);
x_1127 = lean_unbox(x_1126);
if (x_1127 == 0)
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
lean_dec(x_1123);
x_1128 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4;
lean_inc_ref(x_1120);
x_1129 = l_Lean_Expr_app___override(x_1128, x_1120);
x_1130 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_1131 = l_Lean_Meta_trySynthInstance(x_1129, x_1130, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1131) == 0)
{
uint8_t x_1132; 
x_1132 = !lean_is_exclusive(x_1131);
if (x_1132 == 0)
{
lean_object* x_1133; 
x_1133 = lean_ctor_get(x_1131, 0);
if (lean_obj_tag(x_1133) == 1)
{
lean_object* x_1134; lean_object* x_1135; 
lean_free_object(x_1131);
x_1134 = lean_ctor_get(x_1133, 0);
lean_inc(x_1134);
lean_dec_ref(x_1133);
x_1135 = l_Lean_Meta_Sym_shareCommon___redArg(x_1134, x_7);
if (lean_obj_tag(x_1135) == 0)
{
lean_object* x_1136; lean_object* x_1137; 
x_1136 = lean_ctor_get(x_1135, 0);
lean_inc(x_1136);
lean_dec_ref(x_1135);
x_1137 = l_Lean_Meta_Sym_shareCommon___redArg(x_1121, x_7);
if (lean_obj_tag(x_1137) == 0)
{
lean_object* x_1138; lean_object* x_1139; uint8_t x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; uint8_t x_1146; uint8_t x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
x_1138 = lean_ctor_get(x_1137, 0);
lean_inc(x_1138);
lean_dec_ref(x_1137);
x_1139 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_1140 = 0;
x_1141 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
x_1142 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_inc(x_1138);
lean_inc_ref(x_1120);
lean_inc_ref(x_26);
x_1143 = l_Lean_mkApp4(x_1141, x_26, x_1120, x_1138, x_1142);
x_1144 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_1145 = lean_array_push(x_1144, x_1143);
x_1146 = lean_unbox(x_1126);
x_1147 = lean_unbox(x_1126);
x_1148 = l_Lean_Expr_betaRev(x_21, x_1145, x_1146, x_1147);
lean_dec_ref(x_1145);
lean_inc_ref(x_1120);
x_1149 = l_Lean_mkLambda(x_1139, x_1140, x_1120, x_1148);
x_1150 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1149, x_7);
if (lean_obj_tag(x_1150) == 0)
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; uint8_t x_1156; uint8_t x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; 
x_1151 = lean_ctor_get(x_1150, 0);
lean_inc(x_1151);
lean_dec_ref(x_1150);
lean_inc_ref(x_1120);
x_1152 = l_Lean_mkNot(x_1120);
x_1153 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
lean_inc(x_1138);
lean_inc_ref(x_1120);
x_1154 = l_Lean_mkApp4(x_1153, x_26, x_1120, x_1138, x_1142);
x_1155 = lean_array_push(x_1144, x_1154);
x_1156 = lean_unbox(x_1126);
x_1157 = lean_unbox(x_1126);
x_1158 = l_Lean_Expr_betaRev(x_18, x_1155, x_1156, x_1157);
lean_dec_ref(x_1155);
x_1159 = l_Lean_mkLambda(x_1139, x_1140, x_1152, x_1158);
x_1160 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1159, x_7);
if (lean_obj_tag(x_1160) == 0)
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
x_1161 = lean_ctor_get(x_1160, 0);
lean_inc(x_1161);
lean_dec_ref(x_1160);
x_1162 = lean_unsigned_to_nat(4u);
x_1163 = l_Lean_Expr_getBoundedAppFn(x_1162, x_2);
lean_inc(x_1136);
lean_inc_ref(x_1120);
x_1164 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_1163, x_1120, x_1136, x_1151, x_1161, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_1164) == 0)
{
uint8_t x_1165; 
x_1165 = !lean_is_exclusive(x_1164);
if (x_1165 == 0)
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; uint8_t x_1170; 
x_1166 = lean_ctor_get(x_1164, 0);
x_1167 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
x_1168 = l_Lean_Expr_replaceFn(x_2, x_1167);
x_1169 = l_Lean_mkApp3(x_1168, x_1120, x_1136, x_1138);
lean_ctor_set(x_34, 1, x_1169);
lean_ctor_set(x_34, 0, x_1166);
x_1170 = lean_unbox(x_1126);
lean_dec(x_1126);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_1170);
lean_ctor_set(x_1164, 0, x_34);
return x_1164;
}
else
{
lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; uint8_t x_1175; lean_object* x_1176; 
x_1171 = lean_ctor_get(x_1164, 0);
lean_inc(x_1171);
lean_dec(x_1164);
x_1172 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
x_1173 = l_Lean_Expr_replaceFn(x_2, x_1172);
x_1174 = l_Lean_mkApp3(x_1173, x_1120, x_1136, x_1138);
lean_ctor_set(x_34, 1, x_1174);
lean_ctor_set(x_34, 0, x_1171);
x_1175 = lean_unbox(x_1126);
lean_dec(x_1126);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_1175);
x_1176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1176, 0, x_34);
return x_1176;
}
}
else
{
uint8_t x_1177; 
lean_dec(x_1138);
lean_dec(x_1136);
lean_dec(x_1126);
lean_free_object(x_34);
lean_dec_ref(x_1120);
lean_dec_ref(x_2);
x_1177 = !lean_is_exclusive(x_1164);
if (x_1177 == 0)
{
return x_1164;
}
else
{
lean_object* x_1178; lean_object* x_1179; 
x_1178 = lean_ctor_get(x_1164, 0);
lean_inc(x_1178);
lean_dec(x_1164);
x_1179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1179, 0, x_1178);
return x_1179;
}
}
}
else
{
uint8_t x_1180; 
lean_dec(x_1151);
lean_dec(x_1138);
lean_dec(x_1136);
lean_dec(x_1126);
lean_free_object(x_34);
lean_dec_ref(x_1120);
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
x_1180 = !lean_is_exclusive(x_1160);
if (x_1180 == 0)
{
return x_1160;
}
else
{
lean_object* x_1181; lean_object* x_1182; 
x_1181 = lean_ctor_get(x_1160, 0);
lean_inc(x_1181);
lean_dec(x_1160);
x_1182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1182, 0, x_1181);
return x_1182;
}
}
}
else
{
uint8_t x_1183; 
lean_dec(x_1138);
lean_dec(x_1136);
lean_dec(x_1126);
lean_free_object(x_34);
lean_dec_ref(x_1120);
lean_dec_ref(x_26);
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
x_1183 = !lean_is_exclusive(x_1150);
if (x_1183 == 0)
{
return x_1150;
}
else
{
lean_object* x_1184; lean_object* x_1185; 
x_1184 = lean_ctor_get(x_1150, 0);
lean_inc(x_1184);
lean_dec(x_1150);
x_1185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1185, 0, x_1184);
return x_1185;
}
}
}
else
{
uint8_t x_1186; 
lean_dec(x_1136);
lean_dec(x_1126);
lean_free_object(x_34);
lean_dec_ref(x_1120);
lean_dec_ref(x_26);
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
x_1186 = !lean_is_exclusive(x_1137);
if (x_1186 == 0)
{
return x_1137;
}
else
{
lean_object* x_1187; lean_object* x_1188; 
x_1187 = lean_ctor_get(x_1137, 0);
lean_inc(x_1187);
lean_dec(x_1137);
x_1188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1188, 0, x_1187);
return x_1188;
}
}
}
else
{
uint8_t x_1189; 
lean_dec(x_1126);
lean_free_object(x_34);
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec_ref(x_26);
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
x_1189 = !lean_is_exclusive(x_1135);
if (x_1189 == 0)
{
return x_1135;
}
else
{
lean_object* x_1190; lean_object* x_1191; 
x_1190 = lean_ctor_get(x_1135, 0);
lean_inc(x_1190);
lean_dec(x_1135);
x_1191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1191, 0, x_1190);
return x_1191;
}
}
}
else
{
lean_object* x_1192; uint8_t x_1193; 
lean_dec(x_1133);
lean_free_object(x_34);
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec_ref(x_26);
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
x_1192 = lean_alloc_ctor(0, 0, 1);
x_1193 = lean_unbox(x_1126);
lean_dec(x_1126);
lean_ctor_set_uint8(x_1192, 0, x_1193);
lean_ctor_set(x_1131, 0, x_1192);
return x_1131;
}
}
else
{
lean_object* x_1194; 
x_1194 = lean_ctor_get(x_1131, 0);
lean_inc(x_1194);
lean_dec(x_1131);
if (lean_obj_tag(x_1194) == 1)
{
lean_object* x_1195; lean_object* x_1196; 
x_1195 = lean_ctor_get(x_1194, 0);
lean_inc(x_1195);
lean_dec_ref(x_1194);
x_1196 = l_Lean_Meta_Sym_shareCommon___redArg(x_1195, x_7);
if (lean_obj_tag(x_1196) == 0)
{
lean_object* x_1197; lean_object* x_1198; 
x_1197 = lean_ctor_get(x_1196, 0);
lean_inc(x_1197);
lean_dec_ref(x_1196);
x_1198 = l_Lean_Meta_Sym_shareCommon___redArg(x_1121, x_7);
if (lean_obj_tag(x_1198) == 0)
{
lean_object* x_1199; lean_object* x_1200; uint8_t x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; uint8_t x_1207; uint8_t x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; 
x_1199 = lean_ctor_get(x_1198, 0);
lean_inc(x_1199);
lean_dec_ref(x_1198);
x_1200 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_1201 = 0;
x_1202 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
x_1203 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_inc(x_1199);
lean_inc_ref(x_1120);
lean_inc_ref(x_26);
x_1204 = l_Lean_mkApp4(x_1202, x_26, x_1120, x_1199, x_1203);
x_1205 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_1206 = lean_array_push(x_1205, x_1204);
x_1207 = lean_unbox(x_1126);
x_1208 = lean_unbox(x_1126);
x_1209 = l_Lean_Expr_betaRev(x_21, x_1206, x_1207, x_1208);
lean_dec_ref(x_1206);
lean_inc_ref(x_1120);
x_1210 = l_Lean_mkLambda(x_1200, x_1201, x_1120, x_1209);
x_1211 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1210, x_7);
if (lean_obj_tag(x_1211) == 0)
{
lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; uint8_t x_1217; uint8_t x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; 
x_1212 = lean_ctor_get(x_1211, 0);
lean_inc(x_1212);
lean_dec_ref(x_1211);
lean_inc_ref(x_1120);
x_1213 = l_Lean_mkNot(x_1120);
x_1214 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
lean_inc(x_1199);
lean_inc_ref(x_1120);
x_1215 = l_Lean_mkApp4(x_1214, x_26, x_1120, x_1199, x_1203);
x_1216 = lean_array_push(x_1205, x_1215);
x_1217 = lean_unbox(x_1126);
x_1218 = lean_unbox(x_1126);
x_1219 = l_Lean_Expr_betaRev(x_18, x_1216, x_1217, x_1218);
lean_dec_ref(x_1216);
x_1220 = l_Lean_mkLambda(x_1200, x_1201, x_1213, x_1219);
x_1221 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1220, x_7);
if (lean_obj_tag(x_1221) == 0)
{
lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; 
x_1222 = lean_ctor_get(x_1221, 0);
lean_inc(x_1222);
lean_dec_ref(x_1221);
x_1223 = lean_unsigned_to_nat(4u);
x_1224 = l_Lean_Expr_getBoundedAppFn(x_1223, x_2);
lean_inc(x_1197);
lean_inc_ref(x_1120);
x_1225 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_1224, x_1120, x_1197, x_1212, x_1222, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_1225) == 0)
{
lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; uint8_t x_1231; lean_object* x_1232; 
x_1226 = lean_ctor_get(x_1225, 0);
lean_inc(x_1226);
if (lean_is_exclusive(x_1225)) {
 lean_ctor_release(x_1225, 0);
 x_1227 = x_1225;
} else {
 lean_dec_ref(x_1225);
 x_1227 = lean_box(0);
}
x_1228 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
x_1229 = l_Lean_Expr_replaceFn(x_2, x_1228);
x_1230 = l_Lean_mkApp3(x_1229, x_1120, x_1197, x_1199);
lean_ctor_set(x_34, 1, x_1230);
lean_ctor_set(x_34, 0, x_1226);
x_1231 = lean_unbox(x_1126);
lean_dec(x_1126);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_1231);
if (lean_is_scalar(x_1227)) {
 x_1232 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1232 = x_1227;
}
lean_ctor_set(x_1232, 0, x_34);
return x_1232;
}
else
{
lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; 
lean_dec(x_1199);
lean_dec(x_1197);
lean_dec(x_1126);
lean_free_object(x_34);
lean_dec_ref(x_1120);
lean_dec_ref(x_2);
x_1233 = lean_ctor_get(x_1225, 0);
lean_inc(x_1233);
if (lean_is_exclusive(x_1225)) {
 lean_ctor_release(x_1225, 0);
 x_1234 = x_1225;
} else {
 lean_dec_ref(x_1225);
 x_1234 = lean_box(0);
}
if (lean_is_scalar(x_1234)) {
 x_1235 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1235 = x_1234;
}
lean_ctor_set(x_1235, 0, x_1233);
return x_1235;
}
}
else
{
lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; 
lean_dec(x_1212);
lean_dec(x_1199);
lean_dec(x_1197);
lean_dec(x_1126);
lean_free_object(x_34);
lean_dec_ref(x_1120);
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
x_1236 = lean_ctor_get(x_1221, 0);
lean_inc(x_1236);
if (lean_is_exclusive(x_1221)) {
 lean_ctor_release(x_1221, 0);
 x_1237 = x_1221;
} else {
 lean_dec_ref(x_1221);
 x_1237 = lean_box(0);
}
if (lean_is_scalar(x_1237)) {
 x_1238 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1238 = x_1237;
}
lean_ctor_set(x_1238, 0, x_1236);
return x_1238;
}
}
else
{
lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; 
lean_dec(x_1199);
lean_dec(x_1197);
lean_dec(x_1126);
lean_free_object(x_34);
lean_dec_ref(x_1120);
lean_dec_ref(x_26);
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
x_1239 = lean_ctor_get(x_1211, 0);
lean_inc(x_1239);
if (lean_is_exclusive(x_1211)) {
 lean_ctor_release(x_1211, 0);
 x_1240 = x_1211;
} else {
 lean_dec_ref(x_1211);
 x_1240 = lean_box(0);
}
if (lean_is_scalar(x_1240)) {
 x_1241 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1241 = x_1240;
}
lean_ctor_set(x_1241, 0, x_1239);
return x_1241;
}
}
else
{
lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; 
lean_dec(x_1197);
lean_dec(x_1126);
lean_free_object(x_34);
lean_dec_ref(x_1120);
lean_dec_ref(x_26);
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
x_1242 = lean_ctor_get(x_1198, 0);
lean_inc(x_1242);
if (lean_is_exclusive(x_1198)) {
 lean_ctor_release(x_1198, 0);
 x_1243 = x_1198;
} else {
 lean_dec_ref(x_1198);
 x_1243 = lean_box(0);
}
if (lean_is_scalar(x_1243)) {
 x_1244 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1244 = x_1243;
}
lean_ctor_set(x_1244, 0, x_1242);
return x_1244;
}
}
else
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; 
lean_dec(x_1126);
lean_free_object(x_34);
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec_ref(x_26);
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
x_1245 = lean_ctor_get(x_1196, 0);
lean_inc(x_1245);
if (lean_is_exclusive(x_1196)) {
 lean_ctor_release(x_1196, 0);
 x_1246 = x_1196;
} else {
 lean_dec_ref(x_1196);
 x_1246 = lean_box(0);
}
if (lean_is_scalar(x_1246)) {
 x_1247 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1247 = x_1246;
}
lean_ctor_set(x_1247, 0, x_1245);
return x_1247;
}
}
else
{
lean_object* x_1248; uint8_t x_1249; lean_object* x_1250; 
lean_dec(x_1194);
lean_free_object(x_34);
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec_ref(x_26);
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
x_1248 = lean_alloc_ctor(0, 0, 1);
x_1249 = lean_unbox(x_1126);
lean_dec(x_1126);
lean_ctor_set_uint8(x_1248, 0, x_1249);
x_1250 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1250, 0, x_1248);
return x_1250;
}
}
}
else
{
uint8_t x_1251; 
lean_dec(x_1126);
lean_free_object(x_34);
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec_ref(x_26);
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
x_1251 = !lean_is_exclusive(x_1131);
if (x_1251 == 0)
{
return x_1131;
}
else
{
lean_object* x_1252; lean_object* x_1253; 
x_1252 = lean_ctor_get(x_1131, 0);
lean_inc(x_1252);
lean_dec(x_1131);
x_1253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1253, 0, x_1252);
return x_1253;
}
}
}
else
{
lean_object* x_1254; lean_object* x_1255; 
lean_dec(x_1126);
lean_dec_ref(x_1120);
lean_dec_ref(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_1121);
x_1254 = l_Lean_Meta_mkOfEqFalseCore(x_26, x_1121);
x_1255 = l_Lean_Meta_Sym_shareCommon___redArg(x_1254, x_7);
if (lean_obj_tag(x_1255) == 0)
{
lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; uint8_t x_1259; uint8_t x_1260; lean_object* x_1261; lean_object* x_1262; 
x_1256 = lean_ctor_get(x_1255, 0);
lean_inc(x_1256);
lean_dec_ref(x_1255);
x_1257 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_1258 = lean_array_push(x_1257, x_1256);
x_1259 = lean_unbox(x_1123);
x_1260 = lean_unbox(x_1123);
x_1261 = l_Lean_Expr_betaRev(x_18, x_1258, x_1259, x_1260);
lean_dec_ref(x_1258);
x_1262 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1261, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_1262) == 0)
{
uint8_t x_1263; 
x_1263 = !lean_is_exclusive(x_1262);
if (x_1263 == 0)
{
lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; uint8_t x_1268; 
x_1264 = lean_ctor_get(x_1262, 0);
x_1265 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29));
x_1266 = l_Lean_Expr_replaceFn(x_2, x_1265);
x_1267 = l_Lean_Expr_app___override(x_1266, x_1121);
lean_ctor_set(x_34, 1, x_1267);
lean_ctor_set(x_34, 0, x_1264);
x_1268 = lean_unbox(x_1123);
lean_dec(x_1123);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_1268);
lean_ctor_set(x_1262, 0, x_34);
return x_1262;
}
else
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; uint8_t x_1273; lean_object* x_1274; 
x_1269 = lean_ctor_get(x_1262, 0);
lean_inc(x_1269);
lean_dec(x_1262);
x_1270 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29));
x_1271 = l_Lean_Expr_replaceFn(x_2, x_1270);
x_1272 = l_Lean_Expr_app___override(x_1271, x_1121);
lean_ctor_set(x_34, 1, x_1272);
lean_ctor_set(x_34, 0, x_1269);
x_1273 = lean_unbox(x_1123);
lean_dec(x_1123);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_1273);
x_1274 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1274, 0, x_34);
return x_1274;
}
}
else
{
uint8_t x_1275; 
lean_dec(x_1123);
lean_free_object(x_34);
lean_dec_ref(x_1121);
lean_dec_ref(x_2);
x_1275 = !lean_is_exclusive(x_1262);
if (x_1275 == 0)
{
return x_1262;
}
else
{
lean_object* x_1276; lean_object* x_1277; 
x_1276 = lean_ctor_get(x_1262, 0);
lean_inc(x_1276);
lean_dec(x_1262);
x_1277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1277, 0, x_1276);
return x_1277;
}
}
}
else
{
uint8_t x_1278; 
lean_dec(x_1123);
lean_free_object(x_34);
lean_dec_ref(x_1121);
lean_dec_ref(x_18);
lean_dec(x_7);
lean_dec_ref(x_2);
x_1278 = !lean_is_exclusive(x_1255);
if (x_1278 == 0)
{
return x_1255;
}
else
{
lean_object* x_1279; lean_object* x_1280; 
x_1279 = lean_ctor_get(x_1255, 0);
lean_inc(x_1279);
lean_dec(x_1255);
x_1280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1280, 0, x_1279);
return x_1280;
}
}
}
}
else
{
uint8_t x_1281; 
lean_dec(x_1123);
lean_free_object(x_34);
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec_ref(x_26);
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
x_1281 = !lean_is_exclusive(x_1125);
if (x_1281 == 0)
{
return x_1125;
}
else
{
lean_object* x_1282; lean_object* x_1283; 
x_1282 = lean_ctor_get(x_1125, 0);
lean_inc(x_1282);
lean_dec(x_1125);
x_1283 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1283, 0, x_1282);
return x_1283;
}
}
}
else
{
lean_object* x_1284; lean_object* x_1285; 
lean_dec(x_1123);
lean_dec_ref(x_1120);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_1121);
x_1284 = l_Lean_Meta_mkOfEqTrueCore(x_26, x_1121);
x_1285 = l_Lean_Meta_Sym_shareCommon___redArg(x_1284, x_7);
if (lean_obj_tag(x_1285) == 0)
{
lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; 
x_1286 = lean_ctor_get(x_1285, 0);
lean_inc(x_1286);
lean_dec_ref(x_1285);
x_1287 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_1288 = lean_array_push(x_1287, x_1286);
x_1289 = l_Lean_Expr_betaRev(x_21, x_1288, x_1, x_1);
lean_dec_ref(x_1288);
x_1290 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1289, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_1290) == 0)
{
uint8_t x_1291; 
x_1291 = !lean_is_exclusive(x_1290);
if (x_1291 == 0)
{
lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; 
x_1292 = lean_ctor_get(x_1290, 0);
x_1293 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__31));
x_1294 = l_Lean_Expr_replaceFn(x_2, x_1293);
x_1295 = l_Lean_Expr_app___override(x_1294, x_1121);
lean_ctor_set(x_34, 1, x_1295);
lean_ctor_set(x_34, 0, x_1292);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_1);
lean_ctor_set(x_1290, 0, x_34);
return x_1290;
}
else
{
lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; 
x_1296 = lean_ctor_get(x_1290, 0);
lean_inc(x_1296);
lean_dec(x_1290);
x_1297 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__31));
x_1298 = l_Lean_Expr_replaceFn(x_2, x_1297);
x_1299 = l_Lean_Expr_app___override(x_1298, x_1121);
lean_ctor_set(x_34, 1, x_1299);
lean_ctor_set(x_34, 0, x_1296);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_1);
x_1300 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1300, 0, x_34);
return x_1300;
}
}
else
{
uint8_t x_1301; 
lean_free_object(x_34);
lean_dec_ref(x_1121);
lean_dec_ref(x_2);
x_1301 = !lean_is_exclusive(x_1290);
if (x_1301 == 0)
{
return x_1290;
}
else
{
lean_object* x_1302; lean_object* x_1303; 
x_1302 = lean_ctor_get(x_1290, 0);
lean_inc(x_1302);
lean_dec(x_1290);
x_1303 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1303, 0, x_1302);
return x_1303;
}
}
}
else
{
uint8_t x_1304; 
lean_free_object(x_34);
lean_dec_ref(x_1121);
lean_dec_ref(x_21);
lean_dec(x_7);
lean_dec_ref(x_2);
x_1304 = !lean_is_exclusive(x_1285);
if (x_1304 == 0)
{
return x_1285;
}
else
{
lean_object* x_1305; lean_object* x_1306; 
x_1305 = lean_ctor_get(x_1285, 0);
lean_inc(x_1305);
lean_dec(x_1285);
x_1306 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1306, 0, x_1305);
return x_1306;
}
}
}
}
else
{
uint8_t x_1307; 
lean_free_object(x_34);
lean_dec_ref(x_1121);
lean_dec_ref(x_1120);
lean_dec_ref(x_26);
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
x_1307 = !lean_is_exclusive(x_1122);
if (x_1307 == 0)
{
return x_1122;
}
else
{
lean_object* x_1308; lean_object* x_1309; 
x_1308 = lean_ctor_get(x_1122, 0);
lean_inc(x_1308);
lean_dec(x_1122);
x_1309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1309, 0, x_1308);
return x_1309;
}
}
}
else
{
lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; 
x_1310 = lean_ctor_get(x_34, 0);
x_1311 = lean_ctor_get(x_34, 1);
lean_inc(x_1311);
lean_inc(x_1310);
lean_dec(x_34);
x_1312 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_1310, x_6);
if (lean_obj_tag(x_1312) == 0)
{
lean_object* x_1313; uint8_t x_1314; 
x_1313 = lean_ctor_get(x_1312, 0);
lean_inc(x_1313);
lean_dec_ref(x_1312);
x_1314 = lean_unbox(x_1313);
if (x_1314 == 0)
{
lean_object* x_1315; 
x_1315 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_1310, x_6);
if (lean_obj_tag(x_1315) == 0)
{
lean_object* x_1316; uint8_t x_1317; 
x_1316 = lean_ctor_get(x_1315, 0);
lean_inc(x_1316);
lean_dec_ref(x_1315);
x_1317 = lean_unbox(x_1316);
if (x_1317 == 0)
{
lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; 
lean_dec(x_1313);
x_1318 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4;
lean_inc_ref(x_1310);
x_1319 = l_Lean_Expr_app___override(x_1318, x_1310);
x_1320 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_1321 = l_Lean_Meta_trySynthInstance(x_1319, x_1320, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1321) == 0)
{
lean_object* x_1322; lean_object* x_1323; 
x_1322 = lean_ctor_get(x_1321, 0);
lean_inc(x_1322);
if (lean_is_exclusive(x_1321)) {
 lean_ctor_release(x_1321, 0);
 x_1323 = x_1321;
} else {
 lean_dec_ref(x_1321);
 x_1323 = lean_box(0);
}
if (lean_obj_tag(x_1322) == 1)
{
lean_object* x_1324; lean_object* x_1325; 
lean_dec(x_1323);
x_1324 = lean_ctor_get(x_1322, 0);
lean_inc(x_1324);
lean_dec_ref(x_1322);
x_1325 = l_Lean_Meta_Sym_shareCommon___redArg(x_1324, x_7);
if (lean_obj_tag(x_1325) == 0)
{
lean_object* x_1326; lean_object* x_1327; 
x_1326 = lean_ctor_get(x_1325, 0);
lean_inc(x_1326);
lean_dec_ref(x_1325);
x_1327 = l_Lean_Meta_Sym_shareCommon___redArg(x_1311, x_7);
if (lean_obj_tag(x_1327) == 0)
{
lean_object* x_1328; lean_object* x_1329; uint8_t x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; uint8_t x_1336; uint8_t x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; 
x_1328 = lean_ctor_get(x_1327, 0);
lean_inc(x_1328);
lean_dec_ref(x_1327);
x_1329 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_1330 = 0;
x_1331 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
x_1332 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_inc(x_1328);
lean_inc_ref(x_1310);
lean_inc_ref(x_26);
x_1333 = l_Lean_mkApp4(x_1331, x_26, x_1310, x_1328, x_1332);
x_1334 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_1335 = lean_array_push(x_1334, x_1333);
x_1336 = lean_unbox(x_1316);
x_1337 = lean_unbox(x_1316);
x_1338 = l_Lean_Expr_betaRev(x_21, x_1335, x_1336, x_1337);
lean_dec_ref(x_1335);
lean_inc_ref(x_1310);
x_1339 = l_Lean_mkLambda(x_1329, x_1330, x_1310, x_1338);
x_1340 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1339, x_7);
if (lean_obj_tag(x_1340) == 0)
{
lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; uint8_t x_1346; uint8_t x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
x_1341 = lean_ctor_get(x_1340, 0);
lean_inc(x_1341);
lean_dec_ref(x_1340);
lean_inc_ref(x_1310);
x_1342 = l_Lean_mkNot(x_1310);
x_1343 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
lean_inc(x_1328);
lean_inc_ref(x_1310);
x_1344 = l_Lean_mkApp4(x_1343, x_26, x_1310, x_1328, x_1332);
x_1345 = lean_array_push(x_1334, x_1344);
x_1346 = lean_unbox(x_1316);
x_1347 = lean_unbox(x_1316);
x_1348 = l_Lean_Expr_betaRev(x_18, x_1345, x_1346, x_1347);
lean_dec_ref(x_1345);
x_1349 = l_Lean_mkLambda(x_1329, x_1330, x_1342, x_1348);
x_1350 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1349, x_7);
if (lean_obj_tag(x_1350) == 0)
{
lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; 
x_1351 = lean_ctor_get(x_1350, 0);
lean_inc(x_1351);
lean_dec_ref(x_1350);
x_1352 = lean_unsigned_to_nat(4u);
x_1353 = l_Lean_Expr_getBoundedAppFn(x_1352, x_2);
lean_inc(x_1326);
lean_inc_ref(x_1310);
x_1354 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_1353, x_1310, x_1326, x_1341, x_1351, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_1354) == 0)
{
lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; uint8_t x_1361; lean_object* x_1362; 
x_1355 = lean_ctor_get(x_1354, 0);
lean_inc(x_1355);
if (lean_is_exclusive(x_1354)) {
 lean_ctor_release(x_1354, 0);
 x_1356 = x_1354;
} else {
 lean_dec_ref(x_1354);
 x_1356 = lean_box(0);
}
x_1357 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
x_1358 = l_Lean_Expr_replaceFn(x_2, x_1357);
x_1359 = l_Lean_mkApp3(x_1358, x_1310, x_1326, x_1328);
x_1360 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_1360, 0, x_1355);
lean_ctor_set(x_1360, 1, x_1359);
x_1361 = lean_unbox(x_1316);
lean_dec(x_1316);
lean_ctor_set_uint8(x_1360, sizeof(void*)*2, x_1361);
if (lean_is_scalar(x_1356)) {
 x_1362 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1362 = x_1356;
}
lean_ctor_set(x_1362, 0, x_1360);
return x_1362;
}
else
{
lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; 
lean_dec(x_1328);
lean_dec(x_1326);
lean_dec(x_1316);
lean_dec_ref(x_1310);
lean_dec_ref(x_2);
x_1363 = lean_ctor_get(x_1354, 0);
lean_inc(x_1363);
if (lean_is_exclusive(x_1354)) {
 lean_ctor_release(x_1354, 0);
 x_1364 = x_1354;
} else {
 lean_dec_ref(x_1354);
 x_1364 = lean_box(0);
}
if (lean_is_scalar(x_1364)) {
 x_1365 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1365 = x_1364;
}
lean_ctor_set(x_1365, 0, x_1363);
return x_1365;
}
}
else
{
lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; 
lean_dec(x_1341);
lean_dec(x_1328);
lean_dec(x_1326);
lean_dec(x_1316);
lean_dec_ref(x_1310);
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
x_1366 = lean_ctor_get(x_1350, 0);
lean_inc(x_1366);
if (lean_is_exclusive(x_1350)) {
 lean_ctor_release(x_1350, 0);
 x_1367 = x_1350;
} else {
 lean_dec_ref(x_1350);
 x_1367 = lean_box(0);
}
if (lean_is_scalar(x_1367)) {
 x_1368 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1368 = x_1367;
}
lean_ctor_set(x_1368, 0, x_1366);
return x_1368;
}
}
else
{
lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; 
lean_dec(x_1328);
lean_dec(x_1326);
lean_dec(x_1316);
lean_dec_ref(x_1310);
lean_dec_ref(x_26);
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
x_1369 = lean_ctor_get(x_1340, 0);
lean_inc(x_1369);
if (lean_is_exclusive(x_1340)) {
 lean_ctor_release(x_1340, 0);
 x_1370 = x_1340;
} else {
 lean_dec_ref(x_1340);
 x_1370 = lean_box(0);
}
if (lean_is_scalar(x_1370)) {
 x_1371 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1371 = x_1370;
}
lean_ctor_set(x_1371, 0, x_1369);
return x_1371;
}
}
else
{
lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
lean_dec(x_1326);
lean_dec(x_1316);
lean_dec_ref(x_1310);
lean_dec_ref(x_26);
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
x_1372 = lean_ctor_get(x_1327, 0);
lean_inc(x_1372);
if (lean_is_exclusive(x_1327)) {
 lean_ctor_release(x_1327, 0);
 x_1373 = x_1327;
} else {
 lean_dec_ref(x_1327);
 x_1373 = lean_box(0);
}
if (lean_is_scalar(x_1373)) {
 x_1374 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1374 = x_1373;
}
lean_ctor_set(x_1374, 0, x_1372);
return x_1374;
}
}
else
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
lean_dec(x_1316);
lean_dec_ref(x_1311);
lean_dec_ref(x_1310);
lean_dec_ref(x_26);
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
x_1375 = lean_ctor_get(x_1325, 0);
lean_inc(x_1375);
if (lean_is_exclusive(x_1325)) {
 lean_ctor_release(x_1325, 0);
 x_1376 = x_1325;
} else {
 lean_dec_ref(x_1325);
 x_1376 = lean_box(0);
}
if (lean_is_scalar(x_1376)) {
 x_1377 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1377 = x_1376;
}
lean_ctor_set(x_1377, 0, x_1375);
return x_1377;
}
}
else
{
lean_object* x_1378; uint8_t x_1379; lean_object* x_1380; 
lean_dec(x_1322);
lean_dec_ref(x_1311);
lean_dec_ref(x_1310);
lean_dec_ref(x_26);
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
x_1378 = lean_alloc_ctor(0, 0, 1);
x_1379 = lean_unbox(x_1316);
lean_dec(x_1316);
lean_ctor_set_uint8(x_1378, 0, x_1379);
if (lean_is_scalar(x_1323)) {
 x_1380 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1380 = x_1323;
}
lean_ctor_set(x_1380, 0, x_1378);
return x_1380;
}
}
else
{
lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; 
lean_dec(x_1316);
lean_dec_ref(x_1311);
lean_dec_ref(x_1310);
lean_dec_ref(x_26);
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
x_1381 = lean_ctor_get(x_1321, 0);
lean_inc(x_1381);
if (lean_is_exclusive(x_1321)) {
 lean_ctor_release(x_1321, 0);
 x_1382 = x_1321;
} else {
 lean_dec_ref(x_1321);
 x_1382 = lean_box(0);
}
if (lean_is_scalar(x_1382)) {
 x_1383 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1383 = x_1382;
}
lean_ctor_set(x_1383, 0, x_1381);
return x_1383;
}
}
else
{
lean_object* x_1384; lean_object* x_1385; 
lean_dec(x_1316);
lean_dec_ref(x_1310);
lean_dec_ref(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_1311);
x_1384 = l_Lean_Meta_mkOfEqFalseCore(x_26, x_1311);
x_1385 = l_Lean_Meta_Sym_shareCommon___redArg(x_1384, x_7);
if (lean_obj_tag(x_1385) == 0)
{
lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; uint8_t x_1389; uint8_t x_1390; lean_object* x_1391; lean_object* x_1392; 
x_1386 = lean_ctor_get(x_1385, 0);
lean_inc(x_1386);
lean_dec_ref(x_1385);
x_1387 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_1388 = lean_array_push(x_1387, x_1386);
x_1389 = lean_unbox(x_1313);
x_1390 = lean_unbox(x_1313);
x_1391 = l_Lean_Expr_betaRev(x_18, x_1388, x_1389, x_1390);
lean_dec_ref(x_1388);
x_1392 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1391, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_1392) == 0)
{
lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; uint8_t x_1399; lean_object* x_1400; 
x_1393 = lean_ctor_get(x_1392, 0);
lean_inc(x_1393);
if (lean_is_exclusive(x_1392)) {
 lean_ctor_release(x_1392, 0);
 x_1394 = x_1392;
} else {
 lean_dec_ref(x_1392);
 x_1394 = lean_box(0);
}
x_1395 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29));
x_1396 = l_Lean_Expr_replaceFn(x_2, x_1395);
x_1397 = l_Lean_Expr_app___override(x_1396, x_1311);
x_1398 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_1398, 0, x_1393);
lean_ctor_set(x_1398, 1, x_1397);
x_1399 = lean_unbox(x_1313);
lean_dec(x_1313);
lean_ctor_set_uint8(x_1398, sizeof(void*)*2, x_1399);
if (lean_is_scalar(x_1394)) {
 x_1400 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1400 = x_1394;
}
lean_ctor_set(x_1400, 0, x_1398);
return x_1400;
}
else
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
lean_dec(x_1313);
lean_dec_ref(x_1311);
lean_dec_ref(x_2);
x_1401 = lean_ctor_get(x_1392, 0);
lean_inc(x_1401);
if (lean_is_exclusive(x_1392)) {
 lean_ctor_release(x_1392, 0);
 x_1402 = x_1392;
} else {
 lean_dec_ref(x_1392);
 x_1402 = lean_box(0);
}
if (lean_is_scalar(x_1402)) {
 x_1403 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1403 = x_1402;
}
lean_ctor_set(x_1403, 0, x_1401);
return x_1403;
}
}
else
{
lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; 
lean_dec(x_1313);
lean_dec_ref(x_1311);
lean_dec_ref(x_18);
lean_dec(x_7);
lean_dec_ref(x_2);
x_1404 = lean_ctor_get(x_1385, 0);
lean_inc(x_1404);
if (lean_is_exclusive(x_1385)) {
 lean_ctor_release(x_1385, 0);
 x_1405 = x_1385;
} else {
 lean_dec_ref(x_1385);
 x_1405 = lean_box(0);
}
if (lean_is_scalar(x_1405)) {
 x_1406 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1406 = x_1405;
}
lean_ctor_set(x_1406, 0, x_1404);
return x_1406;
}
}
}
else
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; 
lean_dec(x_1313);
lean_dec_ref(x_1311);
lean_dec_ref(x_1310);
lean_dec_ref(x_26);
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
x_1407 = lean_ctor_get(x_1315, 0);
lean_inc(x_1407);
if (lean_is_exclusive(x_1315)) {
 lean_ctor_release(x_1315, 0);
 x_1408 = x_1315;
} else {
 lean_dec_ref(x_1315);
 x_1408 = lean_box(0);
}
if (lean_is_scalar(x_1408)) {
 x_1409 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1409 = x_1408;
}
lean_ctor_set(x_1409, 0, x_1407);
return x_1409;
}
}
else
{
lean_object* x_1410; lean_object* x_1411; 
lean_dec(x_1313);
lean_dec_ref(x_1310);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_1311);
x_1410 = l_Lean_Meta_mkOfEqTrueCore(x_26, x_1311);
x_1411 = l_Lean_Meta_Sym_shareCommon___redArg(x_1410, x_7);
if (lean_obj_tag(x_1411) == 0)
{
lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; 
x_1412 = lean_ctor_get(x_1411, 0);
lean_inc(x_1412);
lean_dec_ref(x_1411);
x_1413 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
x_1414 = lean_array_push(x_1413, x_1412);
x_1415 = l_Lean_Expr_betaRev(x_21, x_1414, x_1, x_1);
lean_dec_ref(x_1414);
x_1416 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_1415, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_1416) == 0)
{
lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; 
x_1417 = lean_ctor_get(x_1416, 0);
lean_inc(x_1417);
if (lean_is_exclusive(x_1416)) {
 lean_ctor_release(x_1416, 0);
 x_1418 = x_1416;
} else {
 lean_dec_ref(x_1416);
 x_1418 = lean_box(0);
}
x_1419 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__31));
x_1420 = l_Lean_Expr_replaceFn(x_2, x_1419);
x_1421 = l_Lean_Expr_app___override(x_1420, x_1311);
x_1422 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_1422, 0, x_1417);
lean_ctor_set(x_1422, 1, x_1421);
lean_ctor_set_uint8(x_1422, sizeof(void*)*2, x_1);
if (lean_is_scalar(x_1418)) {
 x_1423 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1423 = x_1418;
}
lean_ctor_set(x_1423, 0, x_1422);
return x_1423;
}
else
{
lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; 
lean_dec_ref(x_1311);
lean_dec_ref(x_2);
x_1424 = lean_ctor_get(x_1416, 0);
lean_inc(x_1424);
if (lean_is_exclusive(x_1416)) {
 lean_ctor_release(x_1416, 0);
 x_1425 = x_1416;
} else {
 lean_dec_ref(x_1416);
 x_1425 = lean_box(0);
}
if (lean_is_scalar(x_1425)) {
 x_1426 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1426 = x_1425;
}
lean_ctor_set(x_1426, 0, x_1424);
return x_1426;
}
}
else
{
lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; 
lean_dec_ref(x_1311);
lean_dec_ref(x_21);
lean_dec(x_7);
lean_dec_ref(x_2);
x_1427 = lean_ctor_get(x_1411, 0);
lean_inc(x_1427);
if (lean_is_exclusive(x_1411)) {
 lean_ctor_release(x_1411, 0);
 x_1428 = x_1411;
} else {
 lean_dec_ref(x_1411);
 x_1428 = lean_box(0);
}
if (lean_is_scalar(x_1428)) {
 x_1429 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1429 = x_1428;
}
lean_ctor_set(x_1429, 0, x_1427);
return x_1429;
}
}
}
else
{
lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; 
lean_dec_ref(x_1311);
lean_dec_ref(x_1310);
lean_dec_ref(x_26);
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
x_1430 = lean_ctor_get(x_1312, 0);
lean_inc(x_1430);
if (lean_is_exclusive(x_1312)) {
 lean_ctor_release(x_1312, 0);
 x_1431 = x_1312;
} else {
 lean_dec_ref(x_1312);
 x_1431 = lean_box(0);
}
if (lean_is_scalar(x_1431)) {
 x_1432 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1432 = x_1431;
}
lean_ctor_set(x_1432, 0, x_1430);
return x_1432;
}
}
}
}
else
{
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
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
return x_33;
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
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = l_Lean_Meta_reduceRecMatcher_x3f(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_11);
x_12 = l_Lean_Meta_Sym_mkEqRefl___redArg(x_11, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = 0;
x_16 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = 0;
x_19 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_11);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_24 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
lean_ctor_set(x_8, 0, x_24);
return x_8;
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc(x_26);
x_27 = l_Lean_Meta_Sym_mkEqRefl___redArg(x_26, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = 0;
x_31 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_30);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 1, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_34 = x_27;
} else {
 lean_dec_ref(x_27);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 1, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_25);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_36 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_38 = !lean_is_exclusive(x_8);
if (x_38 == 0)
{
return x_8;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_8, 0);
lean_inc(x_39);
lean_dec(x_8);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
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
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4() {
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
x_23 = l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4;
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
l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4 = _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4);
l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7 = _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7);
l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10 = _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10);
l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13 = _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13);
l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22 = _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22);
l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25 = _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25);
l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7 = _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8 = _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9 = _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12 = _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12);
l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15 = _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15);
l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16 = _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16);
l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24 = _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24);
l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25 = _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25);
l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4 = _init_l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
