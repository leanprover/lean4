// Lean compiler output
// Module: Lean.Elab.Deriving.DecEq
// Imports: public import Lean.Data.Options import Lean.Meta.Inductive import Lean.Elab.Deriving.Basic import Lean.Elab.Deriving.Util import Lean.Meta.NatTable import Lean.Meta.Constructions.CtorIdx import Lean.Meta.Constructions.CasesOnSameCtor import Lean.Meta.SameCtorUtils import Init.Data.Array.OfFn
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
lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_DecEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deriving"};
static const lean_object* l_Lean_Elab_Deriving_DecEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Deriving_DecEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decEq"};
static const lean_object* l_Lean_Elab_Deriving_DecEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Deriving_DecEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "linear_construction_threshold"};
static const lean_object* l_Lean_Elab_Deriving_DecEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Deriving_DecEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(38, 127, 229, 132, 157, 42, 70, 134)}};
static const lean_ctor_object l_Lean_Elab_Deriving_DecEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(244, 240, 98, 96, 81, 191, 232, 197)}};
static const lean_ctor_object l_Lean_Elab_Deriving_DecEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(57, 231, 225, 77, 116, 1, 194, 143)}};
static const lean_object* l_Lean_Elab_Deriving_DecEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Deriving_DecEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 349, .m_capacity = 349, .m_length = 348, .m_data = "If the inductive data type has this many or more constructors, use a different implementation for deciding equality that avoids the quadratic code size produced by the default implementation.\n\nThe alternative construction compiles to less efficient code in some cases, so by default it is only used for inductive types with 10 or more constructors."};
static const lean_object* l_Lean_Elab_Deriving_DecEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Deriving_DecEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Elab_Deriving_DecEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Deriving_DecEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Deriving_DecEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Deriving_DecEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l_Lean_Elab_Deriving_DecEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Deriving_DecEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "DecEq"};
static const lean_object* l_Lean_Elab_Deriving_DecEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(178, 114, 31, 38, 23, 98, 169, 168)}};
static const lean_ctor_object l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(19, 88, 29, 117, 11, 240, 44, 115)}};
static const lean_ctor_object l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(229, 13, 135, 217, 248, 49, 202, 234)}};
static const lean_ctor_object l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value_aux_5),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(84, 125, 169, 202, 126, 158, 187, 229)}};
static const lean_object* l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_deriving_decEq_linear__construction__threshold;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "DecidableEq"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 163, 7, 138, 119, 67, 2, 253)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1_value;
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__2_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 166, 195, 152, 24, 103, 8, 2)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inst"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__15_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__16;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(170, 188, 240, 205, 110, 63, 170, 91)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__21_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__24_value;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__1;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 82, 240, 34, 69, 121, 64, 234)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__3_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 43, 53, 182, 5, 16, 39, 1)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "termDepIfThenElse"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 94, 17, 11, 145, 108, 236, 173)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_=_"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(167, 251, 107, 62, 223, 239, 203, 78)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "subst"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(72, 253, 96, 40, 175, 171, 7, 145)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__23_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__24_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__26_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(113, 70, 3, 12, 31, 103, 230, 247)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__28 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__28_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(21, 55, 194, 143, 15, 194, 124, 204)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__29 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__29_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__30 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__31 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__31_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__32 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__32_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__33_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__33_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__33_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__33 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__33_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__34 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__34_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__36 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__36_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__37 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__37_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__38 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__38_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__39 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__39_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__46_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__46 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__46_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__46_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__47 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__47_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__48 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__48_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__43 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__43_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__44_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__43_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__44 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__44_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__44_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__45 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__45_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__45_value),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__48_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__49 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__49_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__41_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__41_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__41_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(178, 114, 31, 38, 23, 98, 169, 168)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__41 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__41_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__41_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__42 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__42_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__42_value),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__49_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__50 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__50_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__51 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__51_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__52_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__52_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__52_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__51_value),LEAN_SCALAR_PTR_LITERAL(41, 145, 9, 18, 75, 146, 159, 78)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__52 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__52_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__53 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__53_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__54;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(85, 67, 188, 79, 172, 243, 130, 138)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__55 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__55_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "injection"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__56 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__56_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__57_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__57_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__57_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(118, 123, 69, 153, 82, 151, 103, 113)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__57 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__57_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__58 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__58_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__59_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__59_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__59_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__59_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__59 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__59_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__60 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__60_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__61_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__61_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__61_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__60_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__61 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__61_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__62 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__62_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assumption"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__63 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__63_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__64_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__64_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__64_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__63_value),LEAN_SCALAR_PTR_LITERAL(240, 50, 167, 190, 65, 82, 149, 231)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__64 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__64_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__65 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__65_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "have"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__66 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__66_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__67_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__67_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__67_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(55, 91, 239, 116, 115, 0, 62, 115)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__67 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__67_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__68 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__68_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__69_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__69_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__69_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__68_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__69 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__69_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__70 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__70_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__70_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__71 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__71_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "inaccessible"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 90, 7, 119, 108, 205, 19, 233)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_occursOrInType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__1_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__2_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__3_value;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__4;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__5_value;
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__45_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__3_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__4_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__42_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__4_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__5_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__6_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ellipsis"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__7_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__8_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(101, 52, 71, 179, 21, 116, 195, 217)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__8_value;
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__9_value;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_compatibleCtors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2;
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__2_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__4_value;
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__5 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__5_value;
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__6 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__6_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__6_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__7;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__4_value;
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_mkSameCtorRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_mkSameCtorRhs___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_mkSameCtorRhs___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_mkSameCtorRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(191, 24, 88, 245, 200, 250, 27, 217)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__5_value;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Elab.Deriving.DecEq"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "_private.Lean.Elab.Deriving.DecEq.0.Lean.Elab.Deriving.DecEq.mkMatchNew"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "assertion violation: header.targetNames.size == 2\n\n  "};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__3;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "match_on_same_ctor"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__4_value),LEAN_SCALAR_PTR_LITERAL(78, 38, 237, 47, 106, 10, 11, 248)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__6_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__8;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(173, 33, 189, 14, 17, 44, 93, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__12_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "h'"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__16;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__15_value),LEAN_SCALAR_PTR_LITERAL(84, 47, 156, 182, 35, 23, 117, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__19;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__18_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__22_value;
lean_object* l_mkCtorIdxName(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnSameCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatch_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatch_spec__0___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__0;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__1_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2_value),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__7_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__9_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__11_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__14_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__18_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__20_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__21_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "terminationBy"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__23_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__20_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__23_value),LEAN_SCALAR_PTR_LITERAL(20, 221, 175, 114, 26, 111, 13, 165)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termination_by"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structural"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__26_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 205, 8, 5, 164, 77, 17, 1)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg___closed__1_value;
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__1(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___closed__1_value;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(85, 216, 186, 166, 168, 89, 69, 16)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2;
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2_spec__3___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0___closed__1;
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_InductiveVal_isNested(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2_spec__3(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___lam__0___closed__0_value;
lean_object* l_mkNatLookupTable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__2;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ofNat_ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lam__0___closed__0_value;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__5_value;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__6;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__9;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__11;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(72, 55, 55, 9, 143, 73, 230, 150)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "x.ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__14;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(2, 247, 218, 116, 51, 159, 161, 152)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__16_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "y.ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__17_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__18;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(72, 55, 55, 9, 143, 73, 230, 150)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(85, 37, 232, 186, 208, 254, 208, 112)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__20_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__21_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__42_value),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__22_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__24_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__27 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__27_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "tacticHave__"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__28 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__28_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__29_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__29_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__28_value),LEAN_SCALAR_PTR_LITERAL(57, 244, 114, 225, 1, 158, 79, 25)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__29 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__29_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "aux"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__30 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__30_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__31;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__30_value),LEAN_SCALAR_PTR_LITERAL(186, 84, 7, 244, 187, 116, 107, 26)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__32 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__32_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rwSeq"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__33 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__33_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__34_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__34_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__34_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__33_value),LEAN_SCALAR_PTR_LITERAL(50, 16, 185, 246, 153, 187, 181, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__34 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__34_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "rw"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__35 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__35_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__36 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__36_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__37_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__37_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__37_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__36_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__37 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__37_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rwRuleSeq"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__38 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__38_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__39_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__39_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__38_value),LEAN_SCALAR_PTR_LITERAL(170, 212, 96, 120, 212, 17, 101, 100)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__39 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__39_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__40 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__40_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rwRule"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__41 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__41_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__42_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__42_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__42_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__41_value),LEAN_SCALAR_PTR_LITERAL(163, 12, 102, 31, 194, 63, 248, 122)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__42 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__42_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__43 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__43_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__44 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__44_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__45_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__45_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__45_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__44_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__45 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__45_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "at"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__46 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__46_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "locationHyp"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__47 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__47_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__48_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__48_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__48_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__47_value),LEAN_SCALAR_PTR_LITERAL(229, 146, 67, 234, 45, 36, 143, 176)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__48 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__48_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__49 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__49_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__50_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__50_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__50_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__49_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__50 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__50_value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "contradiction"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__51 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__51_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__52_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__52_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__52_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__51_value),LEAN_SCALAR_PTR_LITERAL(112, 219, 21, 122, 229, 107, 49, 36)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__52 = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__52_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler_spec__0(lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(190, 173, 250, 34, 110, 197, 245, 18)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(7, 208, 84, 215, 14, 208, 85, 76)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(122, 252, 191, 25, 219, 35, 212, 112)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(56, 19, 28, 113, 160, 89, 102, 8)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(234, 63, 144, 178, 98, 156, 177, 5)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(94, 159, 207, 101, 158, 138, 220, 148)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 228, 189, 88, 141, 152, 10, 14)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(38, 119, 1, 124, 117, 66, 52, 223)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(175, 75, 254, 2, 136, 76, 87, 29)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(17, 178, 101, 223, 172, 47, 24, 241)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 51, 117, 76, 154, 44, 57, 175)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_DecEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(167, 80, 27, 191, 135, 6, 30, 103)}};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_;
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_32; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
x_7 = x_2;
x_8 = x_32;
goto block_31;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_5);
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_6);
lean_inc(x_1);
x_11 = lean_register_option(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; uint8_t x_21; 
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_11, 0);
lean_dec(x_22);
x_12 = x_11;
x_13 = x_21;
goto block_20;
}
else
{
lean_dec(x_11);
x_12 = lean_box(0);
x_13 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_14; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_5);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_del_object(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_23 = lean_ctor_get(x_11, 0);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
x_24 = x_11;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__spec__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Elab_Deriving_DecEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_));
x_3 = ((lean_object*)(l_Lean_Elab_Deriving_DecEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_));
x_4 = ((lean_object*)(l_Lean_Elab_Deriving_DecEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1));
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Elab_Deriving_mkHeader(x_9, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__15));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_57; 
x_12 = lean_ctor_get(x_1, 0);
x_57 = !lean_is_exclusive(x_1);
if (x_57 == 0)
{
x_13 = x_1;
x_14 = x_57;
goto block_56;
}
else
{
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_15 = lean_ctor_get(x_9, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 10);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 11);
lean_inc(x_17);
lean_dec_ref(x_9);
x_18 = 0;
x_19 = l_Lean_SourceInfo_fromRef(x_15, x_18);
lean_dec(x_15);
x_20 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__2));
x_21 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__3));
lean_inc(x_19);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
x_23 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__5));
x_24 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_25 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
lean_inc(x_19);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
lean_inc_ref(x_26);
lean_inc(x_19);
x_27 = l_Lean_Syntax_node1(x_19, x_23, x_26);
x_28 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__10));
x_29 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__12));
x_30 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__14));
x_31 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__16, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__16_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__16);
x_32 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__17));
x_33 = l_Lean_addMacroScope(x_16, x_32, x_17);
x_34 = lean_box(0);
lean_inc(x_19);
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
lean_inc(x_19);
x_36 = l_Lean_Syntax_node1(x_19, x_30, x_35);
x_37 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__18));
lean_inc(x_19);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_19);
lean_ctor_set(x_38, 1, x_37);
x_39 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20));
x_40 = lean_mk_syntax_ident(x_12);
x_41 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22));
x_42 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__23));
lean_inc(x_19);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_19);
lean_ctor_set(x_43, 1, x_42);
lean_inc_ref(x_43);
lean_inc(x_19);
x_44 = l_Lean_Syntax_node2(x_19, x_41, x_43, x_2);
lean_inc(x_19);
x_45 = l_Lean_Syntax_node2(x_19, x_41, x_43, x_3);
lean_inc(x_19);
x_46 = l_Lean_Syntax_node2(x_19, x_24, x_44, x_45);
lean_inc(x_19);
x_47 = l_Lean_Syntax_node2(x_19, x_39, x_40, x_46);
lean_inc_ref(x_26);
lean_inc(x_19);
x_48 = l_Lean_Syntax_node5(x_19, x_29, x_36, x_26, x_26, x_38, x_47);
lean_inc(x_19);
x_49 = l_Lean_Syntax_node1(x_19, x_28, x_48);
x_50 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__24));
lean_inc(x_19);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_19);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Syntax_node5(x_19, x_21, x_22, x_27, x_49, x_51, x_4);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_52);
x_53 = x_13;
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
else
{
lean_object* x_58; 
lean_dec_ref(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_4);
return x_58;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__7));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__5));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__26));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__39));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__54(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__53));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_1 == 0)
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_13 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs(x_2, x_3, x_4, x_5, x_6, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_10, 5);
x_16 = lean_ctor_get(x_10, 10);
x_17 = lean_ctor_get(x_10, 11);
x_18 = l_Lean_SourceInfo_fromRef(x_15, x_1);
x_19 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__1));
x_20 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__2));
lean_inc(x_18);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__4));
x_23 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6);
x_24 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__7));
lean_inc(x_17);
lean_inc(x_16);
x_25 = l_Lean_addMacroScope(x_16, x_24, x_17);
x_26 = lean_box(0);
lean_inc(x_18);
x_27 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
lean_inc_ref(x_27);
lean_inc(x_18);
x_28 = l_Lean_Syntax_node1(x_18, x_22, x_27);
x_29 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__8));
lean_inc(x_18);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
x_31 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__10));
x_32 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22));
x_33 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__23));
lean_inc(x_18);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_33);
lean_inc_ref(x_34);
lean_inc(x_18);
x_35 = l_Lean_Syntax_node2(x_18, x_32, x_34, x_7);
x_36 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__11));
lean_inc(x_18);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_18);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_18);
x_38 = l_Lean_Syntax_node2(x_18, x_32, x_34, x_8);
lean_inc(x_18);
x_39 = l_Lean_Syntax_node3(x_18, x_31, x_35, x_37, x_38);
x_40 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__12));
lean_inc(x_18);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_18);
lean_ctor_set(x_41, 1, x_40);
x_42 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__14));
x_43 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__15));
lean_inc(x_18);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_18);
lean_ctor_set(x_44, 1, x_43);
x_45 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__18));
x_46 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__20));
x_47 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_48 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__21));
x_49 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__22));
lean_inc(x_18);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_18);
lean_ctor_set(x_50, 1, x_48);
lean_inc_ref(x_27);
lean_inc(x_18);
x_51 = l_Lean_Syntax_node1(x_18, x_47, x_27);
lean_inc(x_18);
x_52 = l_Lean_Syntax_node2(x_18, x_49, x_50, x_51);
x_53 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__24));
lean_inc(x_18);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_18);
lean_ctor_set(x_54, 1, x_53);
x_55 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__23));
x_56 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__24));
lean_inc(x_18);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_18);
lean_ctor_set(x_57, 1, x_55);
lean_inc(x_18);
x_58 = l_Lean_Syntax_node2(x_18, x_56, x_57, x_14);
lean_inc_ref(x_54);
lean_inc(x_18);
x_59 = l_Lean_Syntax_node3(x_18, x_47, x_52, x_54, x_58);
lean_inc(x_18);
x_60 = l_Lean_Syntax_node1(x_18, x_46, x_59);
lean_inc(x_18);
x_61 = l_Lean_Syntax_node1(x_18, x_45, x_60);
lean_inc_ref(x_44);
lean_inc(x_18);
x_62 = l_Lean_Syntax_node2(x_18, x_42, x_44, x_61);
x_63 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__25));
lean_inc(x_18);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_18);
lean_ctor_set(x_64, 1, x_63);
x_65 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20));
x_66 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27);
x_67 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__28));
lean_inc(x_17);
lean_inc(x_16);
x_68 = l_Lean_addMacroScope(x_16, x_67, x_17);
x_69 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__31));
lean_inc(x_18);
x_70 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_70, 0, x_18);
lean_ctor_set(x_70, 1, x_66);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_69);
x_71 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__33));
x_72 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35));
x_73 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__36));
lean_inc(x_18);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_18);
lean_ctor_set(x_74, 1, x_73);
x_75 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__38));
x_76 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40);
x_77 = lean_box(0);
lean_inc(x_17);
lean_inc(x_16);
x_78 = l_Lean_addMacroScope(x_16, x_77, x_17);
x_79 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__50));
lean_inc(x_18);
x_80 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_80, 0, x_18);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_78);
lean_ctor_set(x_80, 3, x_79);
lean_inc(x_18);
x_81 = l_Lean_Syntax_node1(x_18, x_75, x_80);
lean_inc(x_18);
x_82 = l_Lean_Syntax_node2(x_18, x_72, x_74, x_81);
x_83 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__51));
x_84 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__52));
lean_inc(x_18);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_18);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__54, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__54_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__54);
x_87 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__55));
lean_inc(x_17);
lean_inc(x_16);
x_88 = l_Lean_addMacroScope(x_16, x_87, x_17);
lean_inc(x_18);
x_89 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_89, 0, x_18);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_26);
lean_inc_ref(x_89);
lean_inc(x_18);
x_90 = l_Lean_Syntax_node1(x_18, x_47, x_89);
lean_inc(x_18);
x_91 = l_Lean_Syntax_node2(x_18, x_84, x_85, x_90);
x_92 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__56));
x_93 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__57));
lean_inc(x_18);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_18);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
lean_inc(x_18);
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_18);
lean_ctor_set(x_96, 1, x_47);
lean_ctor_set(x_96, 2, x_95);
lean_inc(x_18);
x_97 = l_Lean_Syntax_node3(x_18, x_93, x_94, x_89, x_96);
x_98 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__58));
x_99 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__59));
lean_inc(x_18);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_18);
lean_ctor_set(x_100, 1, x_98);
x_101 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__61));
x_102 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__62));
lean_inc(x_18);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_18);
lean_ctor_set(x_103, 1, x_102);
lean_inc(x_18);
x_104 = l_Lean_Syntax_node1(x_18, x_101, x_103);
lean_inc(x_18);
x_105 = l_Lean_Syntax_node1(x_18, x_47, x_104);
lean_inc(x_18);
x_106 = l_Lean_Syntax_node2(x_18, x_65, x_27, x_105);
lean_inc(x_18);
x_107 = l_Lean_Syntax_node2(x_18, x_99, x_100, x_106);
x_108 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__63));
x_109 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__64));
lean_inc(x_18);
x_110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_110, 0, x_18);
lean_ctor_set(x_110, 1, x_108);
lean_inc(x_18);
x_111 = l_Lean_Syntax_node1(x_18, x_109, x_110);
lean_inc_ref_n(x_54, 2);
lean_inc(x_18);
x_112 = l_Lean_Syntax_node7(x_18, x_47, x_91, x_54, x_97, x_54, x_107, x_54, x_111);
lean_inc(x_18);
x_113 = l_Lean_Syntax_node1(x_18, x_46, x_112);
lean_inc(x_18);
x_114 = l_Lean_Syntax_node1(x_18, x_45, x_113);
lean_inc(x_18);
x_115 = l_Lean_Syntax_node2(x_18, x_42, x_44, x_114);
x_116 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__65));
lean_inc(x_18);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_18);
lean_ctor_set(x_117, 1, x_116);
lean_inc(x_18);
x_118 = l_Lean_Syntax_node3(x_18, x_71, x_82, x_115, x_117);
lean_inc(x_18);
x_119 = l_Lean_Syntax_node1(x_18, x_47, x_118);
lean_inc(x_18);
x_120 = l_Lean_Syntax_node2(x_18, x_65, x_70, x_119);
x_121 = l_Lean_Syntax_node8(x_18, x_19, x_21, x_28, x_30, x_39, x_41, x_62, x_64, x_120);
x_122 = lean_apply_8(x_9, x_121, x_3, x_4, x_5, x_6, x_10, x_11, lean_box(0));
return x_122;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_13;
}
}
else
{
lean_object* x_123; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_123 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs(x_2, x_3, x_4, x_5, x_6, x_10, x_11);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = lean_ctor_get(x_10, 5);
x_126 = lean_ctor_get(x_10, 10);
x_127 = lean_ctor_get(x_10, 11);
x_128 = 0;
x_129 = l_Lean_SourceInfo_fromRef(x_125, x_128);
x_130 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__66));
x_131 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__67));
lean_inc(x_129);
x_132 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
x_133 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__5));
x_134 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_135 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
lean_inc(x_129);
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_129);
lean_ctor_set(x_136, 1, x_134);
lean_ctor_set(x_136, 2, x_135);
lean_inc_ref(x_136);
lean_inc(x_129);
x_137 = l_Lean_Syntax_node1(x_129, x_133, x_136);
x_138 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__10));
x_139 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__12));
x_140 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__14));
x_141 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6);
x_142 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__7));
lean_inc(x_127);
lean_inc(x_126);
x_143 = l_Lean_addMacroScope(x_126, x_142, x_127);
x_144 = lean_box(0);
lean_inc(x_129);
x_145 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_145, 0, x_129);
lean_ctor_set(x_145, 1, x_141);
lean_ctor_set(x_145, 2, x_143);
lean_ctor_set(x_145, 3, x_144);
lean_inc_ref(x_145);
lean_inc(x_129);
x_146 = l_Lean_Syntax_node1(x_129, x_140, x_145);
x_147 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__69));
x_148 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__8));
lean_inc(x_129);
x_149 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_149, 0, x_129);
lean_ctor_set(x_149, 1, x_148);
x_150 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__10));
x_151 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22));
x_152 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__23));
lean_inc(x_129);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_129);
lean_ctor_set(x_153, 1, x_152);
lean_inc_ref(x_153);
lean_inc(x_129);
x_154 = l_Lean_Syntax_node2(x_129, x_151, x_153, x_7);
x_155 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__11));
lean_inc(x_129);
x_156 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_156, 0, x_129);
lean_ctor_set(x_156, 1, x_155);
lean_inc(x_129);
x_157 = l_Lean_Syntax_node2(x_129, x_151, x_153, x_8);
lean_inc(x_129);
x_158 = l_Lean_Syntax_node3(x_129, x_150, x_154, x_156, x_157);
lean_inc(x_129);
x_159 = l_Lean_Syntax_node2(x_129, x_147, x_149, x_158);
lean_inc(x_129);
x_160 = l_Lean_Syntax_node1(x_129, x_134, x_159);
x_161 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__18));
lean_inc(x_129);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_129);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8);
x_164 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__9));
lean_inc(x_127);
lean_inc(x_126);
x_165 = l_Lean_addMacroScope(x_126, x_164, x_127);
x_166 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__71));
lean_inc(x_129);
x_167 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_167, 0, x_129);
lean_ctor_set(x_167, 1, x_163);
lean_ctor_set(x_167, 2, x_165);
lean_ctor_set(x_167, 3, x_166);
lean_inc(x_129);
x_168 = l_Lean_Syntax_node5(x_129, x_139, x_146, x_136, x_160, x_162, x_167);
lean_inc(x_129);
x_169 = l_Lean_Syntax_node1(x_129, x_138, x_168);
x_170 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__24));
lean_inc(x_129);
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_129);
lean_ctor_set(x_171, 1, x_170);
x_172 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__14));
x_173 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__15));
lean_inc(x_129);
x_174 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_174, 0, x_129);
lean_ctor_set(x_174, 1, x_173);
x_175 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__18));
x_176 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__20));
x_177 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__21));
x_178 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__22));
lean_inc(x_129);
x_179 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_179, 0, x_129);
lean_ctor_set(x_179, 1, x_177);
lean_inc(x_129);
x_180 = l_Lean_Syntax_node1(x_129, x_134, x_145);
lean_inc(x_129);
x_181 = l_Lean_Syntax_node2(x_129, x_178, x_179, x_180);
x_182 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__23));
x_183 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__24));
lean_inc(x_129);
x_184 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_184, 0, x_129);
lean_ctor_set(x_184, 1, x_182);
lean_inc(x_129);
x_185 = l_Lean_Syntax_node2(x_129, x_183, x_184, x_124);
lean_inc_ref(x_171);
lean_inc(x_129);
x_186 = l_Lean_Syntax_node3(x_129, x_134, x_181, x_171, x_185);
lean_inc(x_129);
x_187 = l_Lean_Syntax_node1(x_129, x_176, x_186);
lean_inc(x_129);
x_188 = l_Lean_Syntax_node1(x_129, x_175, x_187);
lean_inc(x_129);
x_189 = l_Lean_Syntax_node2(x_129, x_172, x_174, x_188);
x_190 = l_Lean_Syntax_node5(x_129, x_131, x_132, x_137, x_169, x_171, x_189);
x_191 = lean_apply_8(x_9, x_190, x_3, x_4, x_5, x_6, x_10, x_11, lean_box(0));
return x_191;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
x_14 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_6, 5);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 10);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 11);
lean_inc(x_11);
lean_dec_ref(x_6);
x_12 = 0;
x_13 = l_Lean_SourceInfo_fromRef(x_9, x_12);
lean_dec(x_9);
x_14 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20));
x_15 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__1, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__1_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__1);
x_16 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__2));
lean_inc(x_11);
lean_inc(x_10);
x_17 = l_Lean_addMacroScope(x_10, x_16, x_11);
x_18 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__6));
lean_inc(x_13);
x_19 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
x_20 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_21 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8);
x_22 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__9));
x_23 = l_Lean_addMacroScope(x_10, x_22, x_11);
x_24 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__11));
lean_inc(x_13);
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_24);
lean_inc(x_13);
x_26 = l_Lean_Syntax_node1(x_13, x_20, x_25);
x_27 = l_Lean_Syntax_node2(x_13, x_14, x_19, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_dec_ref(x_1);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
lean_inc(x_34);
lean_inc(x_33);
x_37 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___boxed), 11, 3);
lean_closure_set(x_37, 0, x_35);
lean_closure_set(x_37, 1, x_33);
lean_closure_set(x_37, 2, x_34);
x_38 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___boxed), 12, 9);
lean_closure_set(x_38, 0, x_36);
lean_closure_set(x_38, 1, x_32);
lean_closure_set(x_38, 2, x_2);
lean_closure_set(x_38, 3, x_3);
lean_closure_set(x_38, 4, x_4);
lean_closure_set(x_38, 5, x_5);
lean_closure_set(x_38, 6, x_33);
lean_closure_set(x_38, 7, x_34);
lean_closure_set(x_38, 8, x_37);
x_39 = l_Lean_Core_withFreshMacroScope___redArg(x_38, x_6, x_7);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), x_1, x_12, x_3, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
x_15 = x_13;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_4);
x_14 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___redArg(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
x_14 = lean_unbox(x_5);
x_15 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_4, 5);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__61));
x_12 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__62));
lean_inc(x_10);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Syntax_node1(x_10, x_11, x_13);
x_15 = lean_array_push(x_3, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
lean_dec(x_2);
x_2 = x_17;
x_3 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__5___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_28; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
x_10 = x_3;
x_11 = x_28;
goto block_27;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_4, 5);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_12, x_13);
x_15 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__61));
x_16 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__62));
lean_inc(x_14);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Syntax_node1(x_14, x_15, x_17);
lean_inc(x_18);
x_19 = lean_array_push(x_8, x_18);
x_20 = lean_array_push(x_9, x_18);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_20);
lean_ctor_set(x_10, 0, x_19);
x_21 = x_10;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_20);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
lean_dec(x_2);
x_2 = x_23;
x_3 = x_21;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__3___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_Expr_isAppOf(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_6, x_1);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_139; 
x_20 = lean_ctor_get(x_7, 1);
x_21 = lean_ctor_get(x_7, 0);
x_139 = !lean_is_exclusive(x_7);
if (x_139 == 0)
{
x_22 = x_7;
x_23 = x_139;
goto block_138;
}
else
{
lean_inc(x_20);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_box(0);
x_23 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_137; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
x_137 = !lean_is_exclusive(x_20);
if (x_137 == 0)
{
x_26 = x_20;
x_27 = x_137;
goto block_136;
}
else
{
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_8, 2);
x_29 = l_Lean_instInhabitedExpr;
x_30 = lean_nat_add(x_2, x_6);
x_31 = lean_array_get_borrowed(x_29, x_3, x_30);
lean_dec(x_30);
lean_inc(x_31);
lean_inc_ref(x_28);
x_32 = l_Lean_Meta_occursOrInType(x_28, x_31, x_4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__1));
lean_inc(x_11);
lean_inc_ref(x_10);
x_34 = l_Lean_Core_mkFreshUserName(x_33, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__3));
lean_inc(x_11);
lean_inc_ref(x_10);
x_37 = l_Lean_Core_mkFreshUserName(x_36, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_31);
x_39 = lean_infer_type(x_31, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_70; lean_object* x_71; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_ctor_get(x_5, 1);
x_42 = lean_ctor_get(x_5, 2);
lean_inc(x_40);
x_43 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_43, 0, x_40);
x_44 = lean_mk_syntax_ident(x_35);
x_45 = lean_mk_syntax_ident(x_38);
lean_inc(x_44);
x_46 = lean_array_push(x_21, x_44);
lean_inc(x_45);
x_47 = lean_array_push(x_24, x_45);
x_70 = lean_unsigned_to_nat(0u);
x_71 = l_Array_findIdx_x3f_loop___redArg(x_43, x_41, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_box(0);
x_48 = x_72;
goto block_69;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_82; 
x_73 = lean_ctor_get(x_71, 0);
x_82 = !lean_is_exclusive(x_71);
if (x_82 == 0)
{
x_74 = x_71;
x_75 = x_82;
goto block_81;
}
else
{
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_box(0);
x_75 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_box(0);
x_77 = lean_array_get_borrowed(x_76, x_42, x_73);
lean_dec(x_73);
lean_inc(x_77);
if (x_75 == 0)
{
lean_ctor_set(x_74, 0, x_77);
x_78 = x_74;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_77);
x_78 = x_80;
goto block_79;
}
block_79:
{
x_48 = x_78;
goto block_69;
}
}
}
block_69:
{
lean_object* x_49; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_49 = l_Lean_Meta_isProp(x_40, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_array_push(x_25, x_53);
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_54);
lean_ctor_set(x_26, 0, x_47);
x_55 = x_26;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_47);
lean_ctor_set(x_60, 1, x_54);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_55);
lean_ctor_set(x_22, 0, x_46);
x_56 = x_22;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_46);
lean_ctor_set(x_58, 1, x_55);
x_56 = x_58;
goto block_57;
}
block_57:
{
x_13 = x_56;
goto block_17;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_del_object(x_26);
lean_dec(x_25);
lean_del_object(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
x_61 = lean_ctor_get(x_49, 0);
x_68 = !lean_is_exclusive(x_49);
if (x_68 == 0)
{
x_62 = x_49;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_49);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_90; 
lean_dec(x_38);
lean_dec(x_35);
lean_del_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_del_object(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
x_83 = lean_ctor_get(x_39, 0);
x_90 = !lean_is_exclusive(x_39);
if (x_90 == 0)
{
x_84 = x_39;
x_85 = x_90;
goto block_89;
}
else
{
lean_inc(x_83);
lean_dec(x_39);
x_84 = lean_box(0);
x_85 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_86; 
if (x_85 == 0)
{
x_86 = x_84;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_83);
x_86 = x_88;
goto block_87;
}
block_87:
{
return x_86;
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_98; 
lean_dec(x_35);
lean_del_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_del_object(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
x_91 = lean_ctor_get(x_37, 0);
x_98 = !lean_is_exclusive(x_37);
if (x_98 == 0)
{
x_92 = x_37;
x_93 = x_98;
goto block_97;
}
else
{
lean_inc(x_91);
lean_dec(x_37);
x_92 = lean_box(0);
x_93 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_94; 
if (x_93 == 0)
{
x_94 = x_92;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_91);
x_94 = x_96;
goto block_95;
}
block_95:
{
return x_94;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_106; 
lean_del_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_del_object(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
x_99 = lean_ctor_get(x_34, 0);
x_106 = !lean_is_exclusive(x_34);
if (x_106 == 0)
{
x_100 = x_34;
x_101 = x_106;
goto block_105;
}
else
{
lean_inc(x_99);
lean_dec(x_34);
x_100 = lean_box(0);
x_101 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_102; 
if (x_101 == 0)
{
x_102 = x_100;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_99);
x_102 = x_104;
goto block_103;
}
block_103:
{
return x_102;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__1));
lean_inc(x_11);
lean_inc_ref(x_10);
x_108 = l_Lean_Core_mkFreshUserName(x_107, x_10, x_11);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = lean_ctor_get(x_10, 5);
x_111 = lean_mk_syntax_ident(x_109);
lean_inc(x_111);
x_112 = lean_array_push(x_21, x_111);
x_113 = 0;
x_114 = l_Lean_SourceInfo_fromRef(x_110, x_113);
x_115 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__5));
x_116 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__6));
lean_inc(x_114);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
x_118 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__65));
lean_inc(x_114);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_Syntax_node3(x_114, x_115, x_117, x_111, x_119);
x_121 = lean_array_push(x_24, x_120);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_121);
x_122 = x_26;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_121);
lean_ctor_set(x_127, 1, x_25);
x_122 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_123; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_122);
lean_ctor_set(x_22, 0, x_112);
x_123 = x_22;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_112);
lean_ctor_set(x_125, 1, x_122);
x_123 = x_125;
goto block_124;
}
block_124:
{
x_13 = x_123;
goto block_17;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_135; 
lean_del_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_del_object(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
x_128 = lean_ctor_get(x_108, 0);
x_135 = !lean_is_exclusive(x_108);
if (x_135 == 0)
{
x_129 = x_108;
x_130 = x_135;
goto block_134;
}
else
{
lean_inc(x_128);
lean_dec(x_108);
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
}
block_17:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_6 = x_15;
x_7 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__3));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
lean_inc(x_16);
lean_inc_ref(x_15);
x_18 = l_Lean_Core_betaReduce(x_10, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc_ref(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_1);
lean_inc(x_3);
x_21 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__3___redArg(x_2, x_3, x_20, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_124; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get(x_22, 1);
x_124 = !lean_is_exclusive(x_22);
if (x_124 == 0)
{
x_25 = x_22;
x_26 = x_124;
goto block_123;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_mk_empty_array_with_capacity(x_3);
if (x_26 == 0)
{
lean_ctor_set(x_25, 1, x_27);
lean_ctor_set(x_25, 0, x_24);
x_28 = x_25;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_24);
lean_ctor_set(x_122, 1, x_27);
x_28 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_30 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg(x_4, x_2, x_9, x_19, x_5, x_3, x_29, x_13, x_14, x_15, x_16);
lean_dec(x_19);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_112; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_ctor_get(x_31, 1);
x_33 = lean_ctor_get(x_31, 0);
x_112 = !lean_is_exclusive(x_31);
if (x_112 == 0)
{
x_34 = x_31;
x_35 = x_112;
goto block_111;
}
else
{
lean_inc(x_32);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_110; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
x_110 = !lean_is_exclusive(x_32);
if (x_110 == 0)
{
x_38 = x_32;
x_39 = x_110;
goto block_109;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_box(0);
x_39 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_15, 5);
lean_inc(x_40);
lean_inc_ref(x_6);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_41 = lean_apply_7(x_6, x_11, x_12, x_13, x_14, x_15, x_16, lean_box(0));
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_array_to_list(x_37);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_44 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs(x_43, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_apply_7(x_6, x_11, x_12, x_13, x_14, x_15, x_16, lean_box(0));
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_92; 
x_47 = lean_ctor_get(x_46, 0);
x_92 = !lean_is_exclusive(x_46);
if (x_92 == 0)
{
x_48 = x_46;
x_49 = x_92;
goto block_91;
}
else
{
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_box(0);
x_49 = x_92;
goto block_91;
}
block_91:
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = 0;
x_51 = l_Lean_SourceInfo_fromRef(x_40, x_50);
lean_dec(x_40);
x_52 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20));
x_53 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__23));
lean_inc(x_51);
if (x_39 == 0)
{
lean_ctor_set_tag(x_38, 2);
lean_ctor_set(x_38, 1, x_53);
lean_ctor_set(x_38, 0, x_51);
x_54 = x_38;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_51);
lean_ctor_set(x_90, 1, x_53);
x_54 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_mk_syntax_ident(x_7);
lean_inc(x_42);
if (x_35 == 0)
{
lean_ctor_set_tag(x_34, 2);
lean_ctor_set(x_34, 1, x_53);
lean_ctor_set(x_34, 0, x_42);
x_56 = x_34;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_42);
lean_ctor_set(x_88, 1, x_53);
x_56 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_57 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22));
lean_inc(x_55);
lean_inc(x_51);
x_58 = l_Lean_Syntax_node2(x_51, x_57, x_54, x_55);
lean_inc(x_42);
x_59 = l_Lean_Syntax_node2(x_42, x_57, x_56, x_55);
x_60 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_61 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
x_62 = l_Array_append___redArg(x_61, x_33);
lean_dec(x_33);
lean_inc(x_51);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_51);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_62);
x_64 = l_Array_append___redArg(x_61, x_36);
lean_dec(x_36);
lean_inc(x_42);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_42);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_65, 2, x_64);
x_66 = l_Lean_Syntax_node2(x_51, x_52, x_58, x_63);
x_67 = lean_array_push(x_8, x_66);
x_68 = l_Lean_Syntax_node2(x_42, x_52, x_59, x_65);
x_69 = lean_array_push(x_67, x_68);
x_70 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__1));
x_71 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__2));
lean_inc(x_47);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_47);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_array_size(x_69);
x_74 = 0;
x_75 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__1(x_73, x_74, x_69);
x_76 = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__4);
x_77 = l_Lean_mkSepArray(x_75, x_76);
lean_dec_ref(x_75);
x_78 = l_Array_append___redArg(x_61, x_77);
lean_dec_ref(x_77);
lean_inc(x_47);
x_79 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_79, 0, x_47);
lean_ctor_set(x_79, 1, x_60);
lean_ctor_set(x_79, 2, x_78);
lean_inc(x_47);
x_80 = l_Lean_Syntax_node1(x_47, x_60, x_79);
x_81 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__5));
lean_inc(x_47);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_47);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_Syntax_node4(x_47, x_70, x_72, x_80, x_82, x_45);
if (x_49 == 0)
{
lean_ctor_set(x_48, 0, x_83);
x_84 = x_48;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_83);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_100; 
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_40);
lean_del_object(x_38);
lean_dec(x_36);
lean_del_object(x_34);
lean_dec(x_33);
lean_dec_ref(x_8);
lean_dec(x_7);
x_93 = lean_ctor_get(x_46, 0);
x_100 = !lean_is_exclusive(x_46);
if (x_100 == 0)
{
x_94 = x_46;
x_95 = x_100;
goto block_99;
}
else
{
lean_inc(x_93);
lean_dec(x_46);
x_94 = lean_box(0);
x_95 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_96; 
if (x_95 == 0)
{
x_96 = x_94;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_93);
x_96 = x_98;
goto block_97;
}
block_97:
{
return x_96;
}
}
}
}
else
{
lean_dec(x_42);
lean_dec(x_40);
lean_del_object(x_38);
lean_dec(x_36);
lean_del_object(x_34);
lean_dec(x_33);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_44;
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_108; 
lean_dec(x_40);
lean_del_object(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_del_object(x_34);
lean_dec(x_33);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_101 = lean_ctor_get(x_41, 0);
x_108 = !lean_is_exclusive(x_41);
if (x_108 == 0)
{
x_102 = x_41;
x_103 = x_108;
goto block_107;
}
else
{
lean_inc(x_101);
lean_dec(x_41);
x_102 = lean_box(0);
x_103 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_104; 
if (x_103 == 0)
{
x_104 = x_102;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_120; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_113 = lean_ctor_get(x_30, 0);
x_120 = !lean_is_exclusive(x_30);
if (x_120 == 0)
{
x_114 = x_30;
x_115 = x_120;
goto block_119;
}
else
{
lean_inc(x_113);
lean_dec(x_30);
x_114 = lean_box(0);
x_115 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_116; 
if (x_115 == 0)
{
x_116 = x_114;
goto block_117;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_113);
x_116 = x_118;
goto block_117;
}
block_117:
{
return x_116;
}
}
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_132; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
x_125 = lean_ctor_get(x_21, 0);
x_132 = !lean_is_exclusive(x_21);
if (x_132 == 0)
{
x_126 = x_21;
x_127 = x_132;
goto block_131;
}
else
{
lean_inc(x_125);
lean_dec(x_21);
x_126 = lean_box(0);
x_127 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_128; 
if (x_127 == 0)
{
x_128 = x_126;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_125);
x_128 = x_130;
goto block_129;
}
block_129:
{
return x_128;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_140; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_133 = lean_ctor_get(x_18, 0);
x_140 = !lean_is_exclusive(x_18);
if (x_140 == 0)
{
x_134 = x_18;
x_135 = x_140;
goto block_139;
}
else
{
lean_inc(x_133);
lean_dec(x_18);
x_134 = lean_box(0);
x_135 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_136; 
if (x_135 == 0)
{
x_136 = x_134;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_133);
x_136 = x_138;
goto block_137;
}
block_137:
{
return x_136;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_SourceInfo_fromRef(x_9, x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_153; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_153 = !lean_is_exclusive(x_5);
if (x_153 == 0)
{
x_17 = x_5;
x_18 = x_153;
goto block_152;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__0));
x_23 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__5___redArg(x_20, x_21, x_22, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_name_eq(x_1, x_15);
if (x_25 == 0)
{
lean_object* x_26; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_15);
lean_inc(x_1);
x_26 = l_Lean_Meta_compatibleCtors(x_1, x_15, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_dec(x_24);
lean_del_object(x_17);
lean_dec(x_15);
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_30 = lean_ctor_get(x_11, 5);
x_31 = lean_ctor_get(x_11, 10);
x_32 = lean_ctor_get(x_11, 11);
x_33 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__0(x_25, x_7, x_8, x_9, x_10, x_11, x_12);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__0(x_25, x_7, x_8, x_9, x_10, x_11, x_12);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20));
x_38 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27);
x_39 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__28));
lean_inc(x_32);
lean_inc(x_31);
x_40 = l_Lean_addMacroScope(x_31, x_39, x_32);
x_41 = lean_box(0);
x_42 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__2));
lean_inc(x_36);
x_43 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_42);
x_44 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_45 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__33));
x_46 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35));
x_47 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__36));
lean_inc(x_36);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 1, x_47);
lean_ctor_set(x_17, 0, x_36);
x_48 = x_17;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_125, 0, x_36);
lean_ctor_set(x_125, 1, x_47);
x_48 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; size_t x_111; size_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_49 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__38));
x_50 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40);
x_51 = lean_box(0);
lean_inc(x_32);
lean_inc(x_31);
x_52 = l_Lean_addMacroScope(x_31, x_51, x_32);
x_53 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__5));
lean_inc(x_36);
x_54 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_53);
lean_inc(x_36);
x_55 = l_Lean_Syntax_node1(x_36, x_49, x_54);
lean_inc(x_36);
x_56 = l_Lean_Syntax_node2(x_36, x_46, x_48, x_55);
x_57 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__14));
x_58 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__15));
lean_inc(x_36);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_36);
lean_ctor_set(x_59, 1, x_58);
x_60 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__18));
x_61 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__20));
x_62 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__51));
x_63 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__52));
lean_inc(x_36);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_36);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6);
x_66 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__7));
lean_inc(x_32);
lean_inc(x_31);
x_67 = l_Lean_addMacroScope(x_31, x_66, x_32);
lean_inc(x_36);
x_68 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_68, 0, x_36);
lean_ctor_set(x_68, 1, x_65);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_41);
lean_inc_ref(x_68);
lean_inc(x_36);
x_69 = l_Lean_Syntax_node1(x_36, x_44, x_68);
lean_inc(x_36);
x_70 = l_Lean_Syntax_node2(x_36, x_63, x_64, x_69);
x_71 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__24));
lean_inc(x_36);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_36);
lean_ctor_set(x_72, 1, x_71);
x_73 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__56));
x_74 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__57));
lean_inc(x_36);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_36);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
lean_inc(x_36);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_36);
lean_ctor_set(x_77, 1, x_44);
lean_ctor_set(x_77, 2, x_76);
lean_inc(x_36);
x_78 = l_Lean_Syntax_node3(x_36, x_74, x_75, x_68, x_77);
lean_inc(x_36);
x_79 = l_Lean_Syntax_node3(x_36, x_44, x_70, x_72, x_78);
lean_inc(x_36);
x_80 = l_Lean_Syntax_node1(x_36, x_61, x_79);
lean_inc(x_36);
x_81 = l_Lean_Syntax_node1(x_36, x_60, x_80);
x_82 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__0(x_25, x_7, x_8, x_9, x_10, x_11, x_12);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = l_Lean_SourceInfo_fromRef(x_30, x_25);
x_85 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__6));
lean_inc(x_84);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
lean_inc(x_36);
x_87 = l_Lean_Syntax_node2(x_36, x_57, x_59, x_81);
lean_inc(x_34);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_34);
lean_ctor_set(x_88, 1, x_85);
x_89 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__65));
lean_inc(x_36);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_36);
lean_ctor_set(x_90, 1, x_89);
x_91 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__8));
lean_inc(x_84);
x_92 = l_Lean_Syntax_node1(x_84, x_91, x_86);
lean_inc(x_34);
x_93 = l_Lean_Syntax_node1(x_34, x_91, x_88);
lean_inc(x_36);
x_94 = l_Lean_Syntax_node3(x_36, x_45, x_56, x_87, x_90);
lean_inc(x_84);
x_95 = l_Lean_Syntax_node1(x_84, x_44, x_92);
lean_inc(x_34);
x_96 = l_Lean_Syntax_node1(x_34, x_44, x_93);
lean_inc(x_36);
x_97 = l_Lean_Syntax_node1(x_36, x_44, x_94);
lean_inc(x_1);
x_98 = lean_mk_syntax_ident(x_1);
x_99 = l_Lean_Syntax_node2(x_84, x_37, x_98, x_95);
x_100 = lean_mk_syntax_ident(x_15);
x_101 = l_Lean_Syntax_node2(x_34, x_37, x_100, x_96);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_mk_empty_array_with_capacity(x_102);
x_104 = lean_array_push(x_103, x_99);
x_105 = lean_array_push(x_104, x_101);
x_106 = l_Array_append___redArg(x_24, x_105);
lean_dec_ref(x_105);
x_107 = l_Lean_Syntax_node2(x_36, x_37, x_43, x_97);
x_108 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__1));
x_109 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__2));
lean_inc(x_83);
x_110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_110, 0, x_83);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_array_size(x_106);
x_112 = 0;
x_113 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__1(x_111, x_112, x_106);
x_114 = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__4);
x_115 = l_Lean_mkSepArray(x_113, x_114);
lean_dec_ref(x_113);
x_116 = l_Array_append___redArg(x_76, x_115);
lean_dec_ref(x_115);
lean_inc(x_83);
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_83);
lean_ctor_set(x_117, 1, x_44);
lean_ctor_set(x_117, 2, x_116);
lean_inc(x_83);
x_118 = l_Lean_Syntax_node1(x_83, x_44, x_117);
x_119 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__5));
lean_inc(x_83);
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_83);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_Syntax_node4(x_83, x_108, x_110, x_118, x_120, x_107);
x_122 = lean_array_push(x_6, x_121);
x_5 = x_16;
x_6 = x_122;
goto _start;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_133; 
lean_dec(x_24);
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_126 = lean_ctor_get(x_26, 0);
x_133 = !lean_is_exclusive(x_26);
if (x_133 == 0)
{
x_127 = x_26;
x_128 = x_133;
goto block_132;
}
else
{
lean_inc(x_126);
lean_dec(x_26);
x_127 = lean_box(0);
x_128 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_129; 
if (x_128 == 0)
{
x_129 = x_127;
goto block_130;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_126);
x_129 = x_131;
goto block_130;
}
block_130:
{
return x_129;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
lean_del_object(x_17);
lean_dec(x_15);
x_134 = lean_ctor_get(x_3, 0);
x_135 = lean_ctor_get(x_3, 4);
x_136 = lean_ctor_get(x_134, 2);
x_137 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__9));
lean_inc(x_1);
lean_inc_ref(x_4);
lean_inc(x_135);
lean_inc(x_19);
x_138 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___boxed), 17, 8);
lean_closure_set(x_138, 0, x_22);
lean_closure_set(x_138, 1, x_19);
lean_closure_set(x_138, 2, x_21);
lean_closure_set(x_138, 3, x_135);
lean_closure_set(x_138, 4, x_4);
lean_closure_set(x_138, 5, x_137);
lean_closure_set(x_138, 6, x_1);
lean_closure_set(x_138, 7, x_24);
x_139 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_136);
x_140 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___redArg(x_136, x_138, x_139, x_139, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = lean_array_push(x_6, x_141);
x_5 = x_16;
x_6 = x_142;
goto _start;
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_151; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_144 = lean_ctor_get(x_140, 0);
x_151 = !lean_is_exclusive(x_140);
if (x_151 == 0)
{
x_145 = x_140;
x_146 = x_151;
goto block_150;
}
else
{
lean_inc(x_144);
lean_dec(x_140);
x_145 = lean_box(0);
x_146 = x_151;
goto block_150;
}
block_150:
{
lean_object* x_147; 
if (x_146 == 0)
{
x_147 = x_145;
goto block_148;
}
else
{
lean_object* x_149; 
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_144);
x_147 = x_149;
goto block_148;
}
block_148:
{
return x_147;
}
}
}
}
}
else
{
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_26; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_5 = x_2;
x_6 = x_26;
goto block_25;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_23; 
x_7 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_3, 1);
lean_dec(x_24);
x_8 = x_3;
x_9 = x_23;
goto block_22;
}
else
{
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__0);
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_10);
lean_ctor_set(x_8, 0, x_1);
x_11 = x_8;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_10);
x_11 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__3);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_12);
lean_ctor_set(x_5, 0, x_11);
x_13 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_12);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_MessageData_ofSyntax(x_7);
x_15 = l_Lean_indentD(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_1 = x_16;
x_2 = x_4;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Elab_pp_macroStack;
x_7 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_26; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_10, 0);
lean_dec(x_27);
x_12 = x_10;
x_13 = x_26;
goto block_25;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__0);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_14);
lean_ctor_set(x_12, 0, x_1);
x_15 = x_12;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_14);
x_15 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_MessageData_ofSyntax(x_11);
x_19 = l_Lean_indentD(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13(x_20, x_2);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(x_1, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
lean_inc(x_12);
x_13 = l_Lean_Elab_getBetterRef(x_9, x_12);
x_14 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(x_11, x_12, x_6);
x_15 = lean_ctor_get(x_14, 0);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
x_16 = x_14;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_15);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_102; 
x_9 = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0);
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = lean_ctor_get(x_10, 0);
x_102 = !lean_is_exclusive(x_10);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_10, 1);
lean_dec(x_103);
x_12 = x_10;
x_13 = x_102;
goto block_101;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_99; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_99 = !lean_is_exclusive(x_11);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_11, 1);
lean_dec(x_100);
x_18 = x_11;
x_19 = x_99;
goto block_98;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__1));
x_21 = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__2));
lean_inc_ref(x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_17);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_16);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_15);
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_25);
lean_ctor_set(x_18, 3, x_26);
lean_ctor_set(x_18, 2, x_27);
lean_ctor_set(x_18, 1, x_20);
lean_ctor_set(x_18, 0, x_24);
x_28 = x_18;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_24);
lean_ctor_set(x_97, 1, x_20);
lean_ctor_set(x_97, 2, x_27);
lean_ctor_set(x_97, 3, x_26);
lean_ctor_set(x_97, 4, x_25);
x_28 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_29; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_28);
x_29 = x_12;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_28);
lean_ctor_set(x_95, 1, x_21);
x_29 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_92; 
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = lean_ctor_get(x_30, 0);
x_92 = !lean_is_exclusive(x_30);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_30, 1);
lean_dec(x_93);
x_32 = x_30;
x_33 = x_92;
goto block_91;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_89; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_89 = !lean_is_exclusive(x_31);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_31, 1);
lean_dec(x_90);
x_38 = x_31;
x_39 = x_89;
goto block_88;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__3));
x_41 = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__4));
lean_inc_ref(x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_45, 0, x_37);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_46, 0, x_36);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_47, 0, x_35);
if (x_39 == 0)
{
lean_ctor_set(x_38, 4, x_45);
lean_ctor_set(x_38, 3, x_46);
lean_ctor_set(x_38, 2, x_47);
lean_ctor_set(x_38, 1, x_40);
lean_ctor_set(x_38, 0, x_44);
x_48 = x_38;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_44);
lean_ctor_set(x_87, 1, x_40);
lean_ctor_set(x_87, 2, x_47);
lean_ctor_set(x_87, 3, x_46);
lean_ctor_set(x_87, 4, x_45);
x_48 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_49; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 1, x_41);
lean_ctor_set(x_32, 0, x_48);
x_49 = x_32;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_48);
lean_ctor_set(x_85, 1, x_41);
x_49 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_82; 
x_50 = l_ReaderT_instMonad___redArg(x_49);
x_51 = lean_ctor_get(x_50, 0);
x_82 = !lean_is_exclusive(x_50);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_50, 1);
lean_dec(x_83);
x_52 = x_50;
x_53 = x_82;
goto block_81;
}
else
{
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_79; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 2);
x_56 = lean_ctor_get(x_51, 3);
x_57 = lean_ctor_get(x_51, 4);
x_79 = !lean_is_exclusive(x_51);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_51, 1);
lean_dec(x_80);
x_58 = x_51;
x_59 = x_79;
goto block_78;
}
else
{
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_51);
x_58 = lean_box(0);
x_59 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__5));
x_61 = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__6));
lean_inc_ref(x_54);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_62, 0, x_54);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_63, 0, x_54);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_65, 0, x_57);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_66, 0, x_56);
x_67 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_67, 0, x_55);
if (x_59 == 0)
{
lean_ctor_set(x_58, 4, x_65);
lean_ctor_set(x_58, 3, x_66);
lean_ctor_set(x_58, 2, x_67);
lean_ctor_set(x_58, 1, x_60);
lean_ctor_set(x_58, 0, x_64);
x_68 = x_58;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_60);
lean_ctor_set(x_77, 2, x_67);
lean_ctor_set(x_77, 3, x_66);
lean_ctor_set(x_77, 4, x_65);
x_68 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_69; 
if (x_53 == 0)
{
lean_ctor_set(x_52, 1, x_61);
lean_ctor_set(x_52, 0, x_68);
x_69 = x_52;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_75, 1, x_61);
x_69 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_box(0);
x_71 = l_instInhabitedOfMonad___redArg(x_69, x_70);
x_72 = lean_panic_fn(x_71, x_1);
x_73 = lean_apply_7(x_72, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_73;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__6));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(121u);
x_4 = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__5));
x_5 = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_st_ref_get(x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = 0;
lean_inc(x_1);
x_20 = l_Lean_Environment_findAsync_x3f(x_18, x_1, x_19);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
if (x_22 == 6)
{
lean_object* x_23; 
x_23 = l_Lean_AsyncConstantInfo_toConstantInfo(x_21);
if (lean_obj_tag(x_23) == 6)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 0);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
x_25 = x_23;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_23);
x_32 = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__7);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_33 = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__1(x_32, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_42; 
x_34 = lean_ctor_get(x_33, 0);
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
x_35 = x_33;
x_36 = x_42;
goto block_41;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_42;
goto block_41;
}
block_41:
{
if (lean_obj_tag(x_34) == 0)
{
lean_del_object(x_35);
goto block_16;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec_ref(x_34);
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_37);
x_38 = x_35;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_43 = lean_ctor_get(x_33, 0);
x_50 = !lean_is_exclusive(x_33);
if (x_50 == 0)
{
x_44 = x_33;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_33);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
else
{
lean_dec(x_21);
goto block_16;
}
}
else
{
lean_dec(x_20);
goto block_16;
}
block_16:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__1);
x_10 = 0;
x_11 = l_Lean_MessageData_ofConstName(x_1, x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__3);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(x_14, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec_ref(x_4);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_14);
x_16 = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_18 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg(x_14, x_1, x_17, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_4 = x_15;
x_5 = x_19;
goto _start;
}
else
{
lean_dec(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_16, 0);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
x_22 = x_16;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__8(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__8(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 4);
lean_inc(x_10);
x_11 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__0));
lean_inc(x_10);
x_12 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__7___redArg(x_2, x_1, x_10, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_23; 
x_13 = lean_ctor_get(x_12, 0);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
x_14 = x_12;
x_15 = x_23;
goto block_22;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_23;
goto block_22;
}
block_22:
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_size(x_13);
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__8(x_16, x_17, x_13);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_18);
x_19 = x_14;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__3___redArg(x_1, x_4, x_5, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__5___redArg(x_1, x_4, x_5, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__7___redArg(x_1, x_2, x_3, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(x_1, x_2, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc_ref(x_3);
x_11 = l_Lean_Elab_Deriving_mkDiscrs(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc_ref(x_8);
x_13 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_44; 
x_14 = lean_ctor_get(x_13, 0);
x_44 = !lean_is_exclusive(x_13);
if (x_44 == 0)
{
x_15 = x_13;
x_16 = x_44;
goto block_43;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_17 = lean_ctor_get(x_8, 5);
lean_inc(x_17);
lean_dec_ref(x_8);
x_18 = 0;
x_19 = l_Lean_SourceInfo_fromRef(x_17, x_18);
lean_dec(x_17);
x_20 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__0));
x_21 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__1));
lean_inc(x_19);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
x_23 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_24 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
lean_inc(x_19);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_array_size(x_12);
x_27 = 0;
x_28 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__1(x_26, x_27, x_12);
x_29 = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__4);
x_30 = l_Lean_mkSepArray(x_28, x_29);
lean_dec_ref(x_28);
x_31 = l_Array_append___redArg(x_24, x_30);
lean_dec_ref(x_30);
lean_inc(x_19);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_31);
x_33 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__2));
lean_inc(x_19);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_33);
x_35 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__4));
x_36 = l_Array_append___redArg(x_24, x_14);
lean_dec(x_14);
lean_inc(x_19);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_19);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_36);
lean_inc(x_19);
x_38 = l_Lean_Syntax_node1(x_19, x_35, x_37);
lean_inc_ref(x_25);
x_39 = l_Lean_Syntax_node6(x_19, x_21, x_22, x_25, x_25, x_32, x_34, x_38);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_39);
x_40 = x_15;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_dec(x_12);
lean_dec_ref(x_8);
x_45 = lean_ctor_get(x_13, 0);
x_52 = !lean_is_exclusive(x_13);
if (x_52 == 0)
{
x_46 = x_13;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_13);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_53 = lean_ctor_get(x_11, 0);
x_60 = !lean_is_exclusive(x_11);
if (x_60 == 0)
{
x_54 = x_11;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_11);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_mkSameCtorRhs___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_1 == 0)
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_13 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_mkSameCtorRhs(x_2, x_3, x_4, x_5, x_6, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_10, 5);
x_16 = lean_ctor_get(x_10, 10);
x_17 = lean_ctor_get(x_10, 11);
x_18 = l_Lean_SourceInfo_fromRef(x_15, x_1);
x_19 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__1));
x_20 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__2));
lean_inc(x_18);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__4));
x_23 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6);
x_24 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__7));
lean_inc(x_17);
lean_inc(x_16);
x_25 = l_Lean_addMacroScope(x_16, x_24, x_17);
x_26 = lean_box(0);
lean_inc(x_18);
x_27 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
lean_inc_ref(x_27);
lean_inc(x_18);
x_28 = l_Lean_Syntax_node1(x_18, x_22, x_27);
x_29 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__8));
lean_inc(x_18);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
x_31 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__10));
x_32 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22));
x_33 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__23));
lean_inc(x_18);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_33);
lean_inc_ref(x_34);
lean_inc(x_18);
x_35 = l_Lean_Syntax_node2(x_18, x_32, x_34, x_7);
x_36 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__11));
lean_inc(x_18);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_18);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_18);
x_38 = l_Lean_Syntax_node2(x_18, x_32, x_34, x_8);
lean_inc(x_18);
x_39 = l_Lean_Syntax_node3(x_18, x_31, x_35, x_37, x_38);
x_40 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__12));
lean_inc(x_18);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_18);
lean_ctor_set(x_41, 1, x_40);
x_42 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__14));
x_43 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__15));
lean_inc(x_18);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_18);
lean_ctor_set(x_44, 1, x_43);
x_45 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__18));
x_46 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__20));
x_47 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_48 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__21));
x_49 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__22));
lean_inc(x_18);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_18);
lean_ctor_set(x_50, 1, x_48);
lean_inc_ref(x_27);
lean_inc(x_18);
x_51 = l_Lean_Syntax_node1(x_18, x_47, x_27);
lean_inc(x_18);
x_52 = l_Lean_Syntax_node2(x_18, x_49, x_50, x_51);
x_53 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__24));
lean_inc(x_18);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_18);
lean_ctor_set(x_54, 1, x_53);
x_55 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__23));
x_56 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__24));
lean_inc(x_18);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_18);
lean_ctor_set(x_57, 1, x_55);
lean_inc(x_18);
x_58 = l_Lean_Syntax_node2(x_18, x_56, x_57, x_14);
lean_inc_ref(x_54);
lean_inc(x_18);
x_59 = l_Lean_Syntax_node3(x_18, x_47, x_52, x_54, x_58);
lean_inc(x_18);
x_60 = l_Lean_Syntax_node1(x_18, x_46, x_59);
lean_inc(x_18);
x_61 = l_Lean_Syntax_node1(x_18, x_45, x_60);
lean_inc_ref(x_44);
lean_inc(x_18);
x_62 = l_Lean_Syntax_node2(x_18, x_42, x_44, x_61);
x_63 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__25));
lean_inc(x_18);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_18);
lean_ctor_set(x_64, 1, x_63);
x_65 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20));
x_66 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27);
x_67 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__28));
lean_inc(x_17);
lean_inc(x_16);
x_68 = l_Lean_addMacroScope(x_16, x_67, x_17);
x_69 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__31));
lean_inc(x_18);
x_70 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_70, 0, x_18);
lean_ctor_set(x_70, 1, x_66);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_69);
x_71 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__33));
x_72 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35));
x_73 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__36));
lean_inc(x_18);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_18);
lean_ctor_set(x_74, 1, x_73);
x_75 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__38));
x_76 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40);
x_77 = lean_box(0);
lean_inc(x_17);
lean_inc(x_16);
x_78 = l_Lean_addMacroScope(x_16, x_77, x_17);
x_79 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__50));
lean_inc(x_18);
x_80 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_80, 0, x_18);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_78);
lean_ctor_set(x_80, 3, x_79);
lean_inc(x_18);
x_81 = l_Lean_Syntax_node1(x_18, x_75, x_80);
lean_inc(x_18);
x_82 = l_Lean_Syntax_node2(x_18, x_72, x_74, x_81);
x_83 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__51));
x_84 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__52));
lean_inc(x_18);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_18);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__54, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__54_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__54);
x_87 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__55));
lean_inc(x_17);
lean_inc(x_16);
x_88 = l_Lean_addMacroScope(x_16, x_87, x_17);
lean_inc(x_18);
x_89 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_89, 0, x_18);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_26);
lean_inc_ref(x_89);
lean_inc(x_18);
x_90 = l_Lean_Syntax_node1(x_18, x_47, x_89);
lean_inc(x_18);
x_91 = l_Lean_Syntax_node2(x_18, x_84, x_85, x_90);
x_92 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__56));
x_93 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__57));
lean_inc(x_18);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_18);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
lean_inc(x_18);
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_18);
lean_ctor_set(x_96, 1, x_47);
lean_ctor_set(x_96, 2, x_95);
lean_inc(x_18);
x_97 = l_Lean_Syntax_node3(x_18, x_93, x_94, x_89, x_96);
x_98 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__58));
x_99 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__59));
lean_inc(x_18);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_18);
lean_ctor_set(x_100, 1, x_98);
x_101 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__61));
x_102 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__62));
lean_inc(x_18);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_18);
lean_ctor_set(x_103, 1, x_102);
lean_inc(x_18);
x_104 = l_Lean_Syntax_node1(x_18, x_101, x_103);
lean_inc(x_18);
x_105 = l_Lean_Syntax_node1(x_18, x_47, x_104);
lean_inc(x_18);
x_106 = l_Lean_Syntax_node2(x_18, x_65, x_27, x_105);
lean_inc(x_18);
x_107 = l_Lean_Syntax_node2(x_18, x_99, x_100, x_106);
x_108 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__63));
x_109 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__64));
lean_inc(x_18);
x_110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_110, 0, x_18);
lean_ctor_set(x_110, 1, x_108);
lean_inc(x_18);
x_111 = l_Lean_Syntax_node1(x_18, x_109, x_110);
lean_inc_ref_n(x_54, 2);
lean_inc(x_18);
x_112 = l_Lean_Syntax_node7(x_18, x_47, x_91, x_54, x_97, x_54, x_107, x_54, x_111);
lean_inc(x_18);
x_113 = l_Lean_Syntax_node1(x_18, x_46, x_112);
lean_inc(x_18);
x_114 = l_Lean_Syntax_node1(x_18, x_45, x_113);
lean_inc(x_18);
x_115 = l_Lean_Syntax_node2(x_18, x_42, x_44, x_114);
x_116 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__65));
lean_inc(x_18);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_18);
lean_ctor_set(x_117, 1, x_116);
lean_inc(x_18);
x_118 = l_Lean_Syntax_node3(x_18, x_71, x_82, x_115, x_117);
lean_inc(x_18);
x_119 = l_Lean_Syntax_node1(x_18, x_47, x_118);
lean_inc(x_18);
x_120 = l_Lean_Syntax_node2(x_18, x_65, x_70, x_119);
x_121 = l_Lean_Syntax_node8(x_18, x_19, x_21, x_28, x_30, x_39, x_41, x_62, x_64, x_120);
x_122 = lean_apply_8(x_9, x_121, x_3, x_4, x_5, x_6, x_10, x_11, lean_box(0));
return x_122;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_13;
}
}
else
{
lean_object* x_123; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_123 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_mkSameCtorRhs(x_2, x_3, x_4, x_5, x_6, x_10, x_11);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = lean_ctor_get(x_10, 5);
x_126 = lean_ctor_get(x_10, 10);
x_127 = lean_ctor_get(x_10, 11);
x_128 = 0;
x_129 = l_Lean_SourceInfo_fromRef(x_125, x_128);
x_130 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__66));
x_131 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__67));
lean_inc(x_129);
x_132 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
x_133 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__5));
x_134 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_135 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
lean_inc(x_129);
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_129);
lean_ctor_set(x_136, 1, x_134);
lean_ctor_set(x_136, 2, x_135);
lean_inc_ref(x_136);
lean_inc(x_129);
x_137 = l_Lean_Syntax_node1(x_129, x_133, x_136);
x_138 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__10));
x_139 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__12));
x_140 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__14));
x_141 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6);
x_142 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__7));
lean_inc(x_127);
lean_inc(x_126);
x_143 = l_Lean_addMacroScope(x_126, x_142, x_127);
x_144 = lean_box(0);
lean_inc(x_129);
x_145 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_145, 0, x_129);
lean_ctor_set(x_145, 1, x_141);
lean_ctor_set(x_145, 2, x_143);
lean_ctor_set(x_145, 3, x_144);
lean_inc_ref(x_145);
lean_inc(x_129);
x_146 = l_Lean_Syntax_node1(x_129, x_140, x_145);
x_147 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__69));
x_148 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__8));
lean_inc(x_129);
x_149 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_149, 0, x_129);
lean_ctor_set(x_149, 1, x_148);
x_150 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__10));
x_151 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22));
x_152 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__23));
lean_inc(x_129);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_129);
lean_ctor_set(x_153, 1, x_152);
lean_inc_ref(x_153);
lean_inc(x_129);
x_154 = l_Lean_Syntax_node2(x_129, x_151, x_153, x_7);
x_155 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__11));
lean_inc(x_129);
x_156 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_156, 0, x_129);
lean_ctor_set(x_156, 1, x_155);
lean_inc(x_129);
x_157 = l_Lean_Syntax_node2(x_129, x_151, x_153, x_8);
lean_inc(x_129);
x_158 = l_Lean_Syntax_node3(x_129, x_150, x_154, x_156, x_157);
lean_inc(x_129);
x_159 = l_Lean_Syntax_node2(x_129, x_147, x_149, x_158);
lean_inc(x_129);
x_160 = l_Lean_Syntax_node1(x_129, x_134, x_159);
x_161 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__18));
lean_inc(x_129);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_129);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8);
x_164 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__9));
lean_inc(x_127);
lean_inc(x_126);
x_165 = l_Lean_addMacroScope(x_126, x_164, x_127);
x_166 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__71));
lean_inc(x_129);
x_167 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_167, 0, x_129);
lean_ctor_set(x_167, 1, x_163);
lean_ctor_set(x_167, 2, x_165);
lean_ctor_set(x_167, 3, x_166);
lean_inc(x_129);
x_168 = l_Lean_Syntax_node5(x_129, x_139, x_146, x_136, x_160, x_162, x_167);
lean_inc(x_129);
x_169 = l_Lean_Syntax_node1(x_129, x_138, x_168);
x_170 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__24));
lean_inc(x_129);
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_129);
lean_ctor_set(x_171, 1, x_170);
x_172 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__14));
x_173 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__15));
lean_inc(x_129);
x_174 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_174, 0, x_129);
lean_ctor_set(x_174, 1, x_173);
x_175 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__18));
x_176 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__20));
x_177 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__21));
x_178 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__22));
lean_inc(x_129);
x_179 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_179, 0, x_129);
lean_ctor_set(x_179, 1, x_177);
lean_inc(x_129);
x_180 = l_Lean_Syntax_node1(x_129, x_134, x_145);
lean_inc(x_129);
x_181 = l_Lean_Syntax_node2(x_129, x_178, x_179, x_180);
x_182 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__23));
x_183 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__24));
lean_inc(x_129);
x_184 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_184, 0, x_129);
lean_ctor_set(x_184, 1, x_182);
lean_inc(x_129);
x_185 = l_Lean_Syntax_node2(x_129, x_183, x_184, x_124);
lean_inc_ref(x_171);
lean_inc(x_129);
x_186 = l_Lean_Syntax_node3(x_129, x_134, x_181, x_171, x_185);
lean_inc(x_129);
x_187 = l_Lean_Syntax_node1(x_129, x_176, x_186);
lean_inc(x_129);
x_188 = l_Lean_Syntax_node1(x_129, x_175, x_187);
lean_inc(x_129);
x_189 = l_Lean_Syntax_node2(x_129, x_172, x_174, x_188);
x_190 = l_Lean_Syntax_node5(x_129, x_131, x_132, x_137, x_169, x_171, x_189);
x_191 = lean_apply_8(x_9, x_190, x_3, x_4, x_5, x_6, x_10, x_11, lean_box(0));
return x_191;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_mkSameCtorRhs___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
x_14 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_mkSameCtorRhs___lam__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_mkSameCtorRhs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_6, 5);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 10);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 11);
lean_inc(x_11);
lean_dec_ref(x_6);
x_12 = 0;
x_13 = l_Lean_SourceInfo_fromRef(x_9, x_12);
lean_dec(x_9);
x_14 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20));
x_15 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__1, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__1_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__1);
x_16 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__2));
lean_inc(x_11);
lean_inc(x_10);
x_17 = l_Lean_addMacroScope(x_10, x_16, x_11);
x_18 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__6));
lean_inc(x_13);
x_19 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
x_20 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_21 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8);
x_22 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__9));
x_23 = l_Lean_addMacroScope(x_10, x_22, x_11);
x_24 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__11));
lean_inc(x_13);
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_24);
lean_inc(x_13);
x_26 = l_Lean_Syntax_node1(x_13, x_20, x_25);
x_27 = l_Lean_Syntax_node2(x_13, x_14, x_19, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_dec_ref(x_1);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
lean_inc(x_34);
lean_inc(x_33);
x_37 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___boxed), 11, 3);
lean_closure_set(x_37, 0, x_35);
lean_closure_set(x_37, 1, x_33);
lean_closure_set(x_37, 2, x_34);
x_38 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_mkSameCtorRhs___lam__1___boxed), 12, 9);
lean_closure_set(x_38, 0, x_36);
lean_closure_set(x_38, 1, x_32);
lean_closure_set(x_38, 2, x_2);
lean_closure_set(x_38, 3, x_3);
lean_closure_set(x_38, 4, x_4);
lean_closure_set(x_38, 5, x_5);
lean_closure_set(x_38, 6, x_33);
lean_closure_set(x_38, 7, x_34);
lean_closure_set(x_38, 8, x_37);
x_39 = l_Lean_Core_withFreshMacroScope___redArg(x_38, x_6, x_7);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_mkSameCtorRhs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_mkSameCtorRhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__0___closed__0);
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_panic___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_6, x_1);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_125; 
x_20 = lean_ctor_get(x_7, 1);
x_21 = lean_ctor_get(x_7, 0);
x_125 = !lean_is_exclusive(x_7);
if (x_125 == 0)
{
x_22 = x_7;
x_23 = x_125;
goto block_124;
}
else
{
lean_inc(x_20);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_box(0);
x_23 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_123; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
x_123 = !lean_is_exclusive(x_20);
if (x_123 == 0)
{
x_26 = x_20;
x_27 = x_123;
goto block_122;
}
else
{
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_2, 1);
x_29 = l_Lean_instInhabitedExpr;
x_30 = lean_nat_add(x_28, x_6);
x_31 = lean_array_get_borrowed(x_29, x_3, x_30);
lean_dec(x_30);
x_32 = l_Lean_Expr_fvarId_x21(x_31);
x_33 = l_Lean_Expr_containsFVar(x_4, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__1));
lean_inc(x_11);
lean_inc_ref(x_10);
x_35 = l_Lean_Core_mkFreshUserName(x_34, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___closed__3));
lean_inc(x_11);
lean_inc_ref(x_10);
x_38 = l_Lean_Core_mkFreshUserName(x_37, x_10, x_11);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_31);
x_40 = lean_infer_type(x_31, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_71; lean_object* x_72; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_ctor_get(x_5, 1);
x_43 = lean_ctor_get(x_5, 2);
lean_inc(x_41);
x_44 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_44, 0, x_41);
x_45 = lean_mk_syntax_ident(x_36);
x_46 = lean_mk_syntax_ident(x_39);
lean_inc(x_45);
x_47 = lean_array_push(x_21, x_45);
lean_inc(x_46);
x_48 = lean_array_push(x_24, x_46);
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Array_findIdx_x3f_loop___redArg(x_44, x_42, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_box(0);
x_49 = x_73;
goto block_70;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_83; 
x_74 = lean_ctor_get(x_72, 0);
x_83 = !lean_is_exclusive(x_72);
if (x_83 == 0)
{
x_75 = x_72;
x_76 = x_83;
goto block_82;
}
else
{
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_box(0);
x_76 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_box(0);
x_78 = lean_array_get_borrowed(x_77, x_43, x_74);
lean_dec(x_74);
lean_inc(x_78);
if (x_76 == 0)
{
lean_ctor_set(x_75, 0, x_78);
x_79 = x_75;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_78);
x_79 = x_81;
goto block_80;
}
block_80:
{
x_49 = x_79;
goto block_70;
}
}
}
block_70:
{
lean_object* x_50; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_50 = l_Lean_Meta_isProp(x_41, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_array_push(x_25, x_54);
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_55);
lean_ctor_set(x_26, 0, x_48);
x_56 = x_26;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_48);
lean_ctor_set(x_61, 1, x_55);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_56);
lean_ctor_set(x_22, 0, x_47);
x_57 = x_22;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
x_13 = x_57;
goto block_17;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_del_object(x_26);
lean_dec(x_25);
lean_del_object(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
x_62 = lean_ctor_get(x_50, 0);
x_69 = !lean_is_exclusive(x_50);
if (x_69 == 0)
{
x_63 = x_50;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_50);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
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
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
lean_dec(x_39);
lean_dec(x_36);
lean_del_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_del_object(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
x_84 = lean_ctor_get(x_40, 0);
x_91 = !lean_is_exclusive(x_40);
if (x_91 == 0)
{
x_85 = x_40;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_40);
x_85 = lean_box(0);
x_86 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_87; 
if (x_86 == 0)
{
x_87 = x_85;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_84);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_99; 
lean_dec(x_36);
lean_del_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_del_object(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
x_92 = lean_ctor_get(x_38, 0);
x_99 = !lean_is_exclusive(x_38);
if (x_99 == 0)
{
x_93 = x_38;
x_94 = x_99;
goto block_98;
}
else
{
lean_inc(x_92);
lean_dec(x_38);
x_93 = lean_box(0);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_94 == 0)
{
x_95 = x_93;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_92);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_107; 
lean_del_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_del_object(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
x_100 = lean_ctor_get(x_35, 0);
x_107 = !lean_is_exclusive(x_35);
if (x_107 == 0)
{
x_101 = x_35;
x_102 = x_107;
goto block_106;
}
else
{
lean_inc(x_100);
lean_dec(x_35);
x_101 = lean_box(0);
x_102 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_103; 
if (x_102 == 0)
{
x_103 = x_101;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_100);
x_103 = x_105;
goto block_104;
}
block_104:
{
return x_103;
}
}
}
}
else
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_108 = lean_ctor_get(x_10, 5);
x_109 = 0;
x_110 = l_Lean_SourceInfo_fromRef(x_108, x_109);
x_111 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__61));
x_112 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__62));
lean_inc(x_110);
x_113 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_Syntax_node1(x_110, x_111, x_113);
x_115 = lean_array_push(x_21, x_114);
if (x_27 == 0)
{
x_116 = x_26;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_24);
lean_ctor_set(x_121, 1, x_25);
x_116 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_117; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_116);
lean_ctor_set(x_22, 0, x_115);
x_117 = x_22;
goto block_118;
}
else
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_116);
x_117 = x_119;
goto block_118;
}
block_118:
{
x_13 = x_117;
goto block_17;
}
}
}
}
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_6 = x_15;
x_7 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
x_14 = l_Lean_Core_betaReduce(x_6, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_mk_empty_array_with_capacity(x_1);
lean_inc_ref_n(x_16, 2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_1);
x_19 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__1___redArg(x_2, x_3, x_5, x_15, x_4, x_1, x_18, x_9, x_10, x_11, x_12);
lean_dec(x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_101; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 1);
x_22 = lean_ctor_get(x_20, 0);
x_101 = !lean_is_exclusive(x_20);
if (x_101 == 0)
{
x_23 = x_20;
x_24 = x_101;
goto block_100;
}
else
{
lean_inc(x_21);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_99; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
x_99 = !lean_is_exclusive(x_21);
if (x_99 == 0)
{
x_27 = x_21;
x_28 = x_99;
goto block_98;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_box(0);
x_28 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_72; uint8_t x_73; 
x_72 = lean_array_get_size(x_22);
x_73 = lean_nat_dec_eq(x_72, x_1);
lean_dec(x_1);
if (x_73 == 0)
{
x_29 = x_22;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
x_33 = x_10;
x_34 = x_11;
x_35 = x_12;
goto block_71;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_74 = lean_ctor_get(x_11, 5);
x_75 = lean_ctor_get(x_11, 10);
x_76 = lean_ctor_get(x_11, 11);
x_77 = 0;
x_78 = l_Lean_SourceInfo_fromRef(x_74, x_77);
x_79 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__5));
x_80 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35));
x_81 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__36));
lean_inc(x_78);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_81);
x_83 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__38));
x_84 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40);
x_85 = lean_box(0);
lean_inc(x_76);
lean_inc(x_75);
x_86 = l_Lean_addMacroScope(x_75, x_85, x_76);
x_87 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__50));
lean_inc(x_78);
x_88 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_88, 0, x_78);
lean_ctor_set(x_88, 1, x_84);
lean_ctor_set(x_88, 2, x_86);
lean_ctor_set(x_88, 3, x_87);
lean_inc(x_78);
x_89 = l_Lean_Syntax_node1(x_78, x_83, x_88);
lean_inc(x_78);
x_90 = l_Lean_Syntax_node2(x_78, x_80, x_82, x_89);
x_91 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_92 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
lean_inc(x_78);
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_78);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_92);
x_94 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__65));
lean_inc(x_78);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_78);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Syntax_node3(x_78, x_79, x_90, x_93, x_95);
x_97 = lean_array_push(x_22, x_96);
x_29 = x_97;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
x_33 = x_10;
x_34 = x_11;
x_35 = x_12;
goto block_71;
}
block_71:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_array_to_list(x_26);
lean_inc_ref(x_34);
x_37 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_mkSameCtorRhs(x_36, x_30, x_31, x_32, x_33, x_34, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_70; 
x_38 = lean_ctor_get(x_37, 0);
x_70 = !lean_is_exclusive(x_37);
if (x_70 == 0)
{
x_39 = x_37;
x_40 = x_70;
goto block_69;
}
else
{
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_34, 5);
lean_inc(x_41);
lean_dec_ref(x_34);
x_42 = 0;
x_43 = l_Lean_SourceInfo_fromRef(x_41, x_42);
lean_dec(x_41);
x_44 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__22));
x_45 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__23));
lean_inc(x_43);
if (x_28 == 0)
{
lean_ctor_set_tag(x_27, 2);
lean_ctor_set(x_27, 1, x_45);
lean_ctor_set(x_27, 0, x_43);
x_46 = x_27;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_43);
lean_ctor_set(x_68, 1, x_45);
x_46 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__0));
x_48 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__1));
lean_inc(x_43);
if (x_24 == 0)
{
lean_ctor_set_tag(x_23, 2);
lean_ctor_set(x_23, 1, x_47);
lean_ctor_set(x_23, 0, x_43);
x_49 = x_23;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_43);
lean_ctor_set(x_66, 1, x_47);
x_49 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_50 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__3));
x_51 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_52 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
x_53 = l_Array_append___redArg(x_52, x_29);
lean_dec_ref(x_29);
x_54 = l_Array_append___redArg(x_53, x_25);
lean_dec(x_25);
lean_inc(x_43);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_55, 2, x_54);
lean_inc(x_43);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_43);
lean_ctor_set(x_56, 1, x_51);
lean_ctor_set(x_56, 2, x_52);
x_57 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__5));
lean_inc(x_43);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_43);
lean_ctor_set(x_58, 1, x_57);
lean_inc(x_43);
x_59 = l_Lean_Syntax_node4(x_43, x_50, x_55, x_56, x_58, x_38);
lean_inc(x_43);
x_60 = l_Lean_Syntax_node2(x_43, x_48, x_49, x_59);
x_61 = l_Lean_Syntax_node2(x_43, x_44, x_46, x_60);
if (x_40 == 0)
{
lean_ctor_set(x_39, 0, x_61);
x_62 = x_39;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_61);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
}
}
else
{
lean_dec_ref(x_34);
lean_dec_ref(x_29);
lean_del_object(x_27);
lean_dec(x_25);
lean_del_object(x_23);
return x_37;
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_109; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_102 = lean_ctor_get(x_19, 0);
x_109 = !lean_is_exclusive(x_19);
if (x_109 == 0)
{
x_103 = x_19;
x_104 = x_109;
goto block_108;
}
else
{
lean_inc(x_102);
lean_dec(x_19);
x_103 = lean_box(0);
x_104 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_105; 
if (x_104 == 0)
{
x_105 = x_103;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_102);
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
lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_117; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_110 = lean_ctor_get(x_14, 0);
x_117 = !lean_is_exclusive(x_14);
if (x_117 == 0)
{
x_111 = x_14;
x_112 = x_117;
goto block_116;
}
else
{
lean_inc(x_110);
lean_dec(x_14);
x_111 = lean_box(0);
x_112 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_113; 
if (x_112 == 0)
{
x_113 = x_111;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_110);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_List_get_x21Internal___redArg(x_1, x_2, x_6);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_15 = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0(x_14, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_16, 4);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 2);
lean_inc_ref(x_19);
lean_dec_ref(x_17);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___boxed), 13, 4);
lean_closure_set(x_20, 0, x_3);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_4);
lean_closure_set(x_20, 3, x_5);
x_21 = 0;
x_22 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__4___redArg(x_19, x_20, x_21, x_21, x_7, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_23 = lean_ctor_get(x_15, 0);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
x_24 = x_15;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_4, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
else
{
lean_object* x_14; 
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_14 = lean_apply_8(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_array_push(x_3, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_4, x_17);
lean_dec(x_4);
x_3 = x_16;
x_4 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_20 = lean_ctor_get(x_14, 0);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
x_21 = x_14;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_mk_empty_array_with_capacity(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2_spec__2___redArg(x_2, x_1, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__2));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(109u);
x_4 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Deriving_DecEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__15));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__18));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_216; 
x_11 = lean_ctor_get(x_2, 2);
x_216 = !lean_is_exclusive(x_2);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_2, 3);
lean_dec(x_217);
x_218 = lean_ctor_get(x_2, 1);
lean_dec(x_218);
x_219 = lean_ctor_get(x_2, 0);
lean_dec(x_219);
x_12 = x_2;
x_13 = x_216;
goto block_215;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_216;
goto block_215;
}
block_215:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_get_size(x_11);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_del_object(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_17 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__3, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__3_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__3);
x_18 = l_panic___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__0(x_17, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_212; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_3, 4);
x_21 = lean_ctor_get(x_19, 0);
x_212 = !lean_is_exclusive(x_19);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_19, 2);
lean_dec(x_213);
x_214 = lean_ctor_get(x_19, 1);
lean_dec(x_214);
x_22 = x_19;
x_23 = x_212;
goto block_211;
}
else
{
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_212;
goto block_211;
}
block_211:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc(x_21);
x_24 = l_mkCtorIdxName(x_21);
x_25 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__5));
lean_inc(x_21);
x_26 = l_Lean_Name_append(x_21, x_25);
lean_inc(x_9);
lean_inc_ref(x_8);
x_27 = l_Lean_Core_mkFreshUserName(x_26, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_28);
x_29 = l_Lean_mkCasesOnSameCtor(x_28, x_21, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_29);
x_30 = lean_box(0);
x_31 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_3);
lean_inc(x_20);
x_32 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__1___boxed), 13, 5);
lean_closure_set(x_32, 0, x_30);
lean_closure_set(x_32, 1, x_20);
lean_closure_set(x_32, 2, x_31);
lean_closure_set(x_32, 3, x_3);
lean_closure_set(x_32, 4, x_1);
x_33 = l_Lean_InductiveVal_numCtors(x_3);
lean_dec_ref(x_3);
lean_inc_ref(x_8);
x_34 = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2___redArg(x_33, x_32, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_186; 
x_35 = lean_ctor_get(x_34, 0);
x_186 = !lean_is_exclusive(x_34);
if (x_186 == 0)
{
x_36 = x_34;
x_37 = x_186;
goto block_185;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_186;
goto block_185;
}
block_185:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_array_get_borrowed(x_30, x_11, x_31);
lean_inc(x_38);
x_39 = lean_mk_syntax_ident(x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_array_get(x_30, x_11, x_40);
lean_dec_ref(x_11);
x_42 = lean_mk_syntax_ident(x_41);
x_43 = lean_nat_dec_eq(x_33, x_40);
lean_dec(x_33);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_8, 5);
lean_inc(x_44);
x_45 = lean_ctor_get(x_8, 10);
lean_inc(x_45);
x_46 = lean_ctor_get(x_8, 11);
lean_inc(x_46);
lean_dec_ref(x_8);
x_47 = l_Lean_SourceInfo_fromRef(x_44, x_43);
lean_dec(x_44);
x_48 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__0));
x_49 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__1));
lean_inc(x_47);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
x_51 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_52 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
lean_inc(x_47);
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 2, x_52);
lean_ctor_set(x_22, 1, x_51);
lean_ctor_set(x_22, 0, x_47);
x_53 = x_22;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_47);
lean_ctor_set(x_160, 1, x_51);
lean_ctor_set(x_160, 2, x_52);
x_53 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__7));
x_55 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20));
x_56 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__8);
x_57 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__9));
lean_inc(x_46);
lean_inc(x_45);
x_58 = l_Lean_addMacroScope(x_45, x_57, x_46);
x_59 = lean_box(0);
x_60 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__11));
lean_inc(x_47);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 3);
lean_ctor_set(x_12, 3, x_60);
lean_ctor_set(x_12, 2, x_58);
lean_ctor_set(x_12, 1, x_56);
lean_ctor_set(x_12, 0, x_47);
x_61 = x_12;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_158, 0, x_47);
lean_ctor_set(x_158, 1, x_56);
lean_ctor_set(x_158, 2, x_58);
lean_ctor_set(x_158, 3, x_60);
x_61 = x_158;
goto block_157;
}
block_157:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_62 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__33));
x_63 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35));
x_64 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__36));
lean_inc(x_47);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_47);
lean_ctor_set(x_65, 1, x_64);
x_66 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__38));
x_67 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40);
lean_inc(x_46);
lean_inc(x_45);
x_68 = l_Lean_addMacroScope(x_45, x_30, x_46);
x_69 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__5));
lean_inc(x_47);
x_70 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_70, 0, x_47);
lean_ctor_set(x_70, 1, x_67);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_69);
lean_inc(x_47);
x_71 = l_Lean_Syntax_node1(x_47, x_66, x_70);
lean_inc(x_47);
x_72 = l_Lean_Syntax_node2(x_47, x_63, x_65, x_71);
x_73 = l_Lean_mkCIdent(x_24);
lean_inc(x_39);
lean_inc(x_47);
x_74 = l_Lean_Syntax_node1(x_47, x_51, x_39);
lean_inc(x_73);
lean_inc(x_47);
x_75 = l_Lean_Syntax_node2(x_47, x_55, x_73, x_74);
x_76 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__65));
lean_inc(x_47);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_47);
lean_ctor_set(x_77, 1, x_76);
lean_inc_ref(x_77);
lean_inc(x_72);
lean_inc(x_47);
x_78 = l_Lean_Syntax_node3(x_47, x_62, x_72, x_75, x_77);
lean_inc(x_42);
lean_inc(x_47);
x_79 = l_Lean_Syntax_node1(x_47, x_51, x_42);
lean_inc(x_73);
lean_inc(x_47);
x_80 = l_Lean_Syntax_node2(x_47, x_55, x_73, x_79);
lean_inc_ref(x_77);
lean_inc(x_72);
lean_inc(x_47);
x_81 = l_Lean_Syntax_node3(x_47, x_62, x_72, x_80, x_77);
lean_inc(x_47);
x_82 = l_Lean_Syntax_node2(x_47, x_51, x_78, x_81);
lean_inc(x_47);
x_83 = l_Lean_Syntax_node2(x_47, x_55, x_61, x_82);
lean_inc_ref(x_53);
lean_inc(x_47);
x_84 = l_Lean_Syntax_node2(x_47, x_54, x_53, x_83);
lean_inc(x_47);
x_85 = l_Lean_Syntax_node1(x_47, x_51, x_84);
x_86 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__2));
lean_inc(x_47);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_47);
lean_ctor_set(x_87, 1, x_86);
x_88 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld___closed__4));
x_89 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__1));
x_90 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__2));
lean_inc(x_47);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_47);
lean_ctor_set(x_91, 1, x_90);
x_92 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__13));
x_93 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__14));
lean_inc(x_47);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_47);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__1, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__1_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__1);
x_96 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__2));
lean_inc(x_46);
lean_inc(x_45);
x_97 = l_Lean_addMacroScope(x_45, x_96, x_46);
x_98 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__6));
lean_inc(x_47);
x_99 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_99, 0, x_47);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set(x_99, 2, x_97);
lean_ctor_set(x_99, 3, x_98);
lean_inc_ref(x_94);
lean_inc(x_47);
x_100 = l_Lean_Syntax_node2(x_47, x_92, x_94, x_99);
x_101 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6);
x_102 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__7));
lean_inc(x_46);
lean_inc(x_45);
x_103 = l_Lean_addMacroScope(x_45, x_102, x_46);
lean_inc(x_47);
x_104 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_104, 0, x_47);
lean_ctor_set(x_104, 1, x_101);
lean_ctor_set(x_104, 2, x_103);
lean_ctor_set(x_104, 3, x_59);
lean_inc_ref(x_104);
lean_inc(x_47);
x_105 = l_Lean_Syntax_node1(x_47, x_51, x_104);
lean_inc(x_105);
lean_inc(x_47);
x_106 = l_Lean_Syntax_node2(x_47, x_55, x_100, x_105);
lean_inc(x_47);
x_107 = l_Lean_Syntax_node1(x_47, x_51, x_106);
lean_inc(x_47);
x_108 = l_Lean_Syntax_node1(x_47, x_51, x_107);
x_109 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__5));
lean_inc(x_47);
x_110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_110, 0, x_47);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_mkCIdent(x_28);
lean_inc_ref(x_104);
x_112 = l_Array_mkArray3___redArg(x_39, x_42, x_104);
x_113 = l_Array_append___redArg(x_112, x_35);
lean_dec(x_35);
lean_inc(x_47);
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_47);
lean_ctor_set(x_114, 1, x_51);
lean_ctor_set(x_114, 2, x_113);
lean_inc(x_47);
x_115 = l_Lean_Syntax_node2(x_47, x_55, x_111, x_114);
lean_inc_ref(x_110);
lean_inc_ref(x_91);
lean_inc(x_47);
x_116 = l_Lean_Syntax_node4(x_47, x_89, x_91, x_108, x_110, x_115);
x_117 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27);
x_118 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__28));
lean_inc(x_46);
lean_inc(x_45);
x_119 = l_Lean_addMacroScope(x_45, x_118, x_46);
x_120 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__2));
lean_inc(x_47);
x_121 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_121, 0, x_47);
lean_ctor_set(x_121, 1, x_117);
lean_ctor_set(x_121, 2, x_119);
lean_ctor_set(x_121, 3, x_120);
lean_inc_ref(x_121);
lean_inc(x_47);
x_122 = l_Lean_Syntax_node2(x_47, x_92, x_94, x_121);
lean_inc(x_47);
x_123 = l_Lean_Syntax_node2(x_47, x_55, x_122, x_105);
lean_inc(x_47);
x_124 = l_Lean_Syntax_node1(x_47, x_51, x_123);
lean_inc(x_47);
x_125 = l_Lean_Syntax_node1(x_47, x_51, x_124);
x_126 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__0));
x_127 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__1));
lean_inc(x_47);
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_47);
lean_ctor_set(x_128, 1, x_126);
x_129 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__3));
x_130 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__16, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__16_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__16);
x_131 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__17));
lean_inc(x_46);
lean_inc(x_45);
x_132 = l_Lean_addMacroScope(x_45, x_131, x_46);
lean_inc(x_47);
x_133 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_133, 0, x_47);
lean_ctor_set(x_133, 1, x_130);
lean_ctor_set(x_133, 2, x_132);
lean_ctor_set(x_133, 3, x_59);
lean_inc_ref(x_133);
lean_inc(x_47);
x_134 = l_Lean_Syntax_node1(x_47, x_51, x_133);
x_135 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__19, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__19_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__19);
x_136 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__20));
x_137 = l_Lean_addMacroScope(x_45, x_136, x_46);
x_138 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__22));
lean_inc(x_47);
x_139 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_139, 0, x_47);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_139, 3, x_138);
lean_inc(x_47);
x_140 = l_Lean_Syntax_node2(x_47, x_51, x_73, x_133);
lean_inc(x_47);
x_141 = l_Lean_Syntax_node2(x_47, x_55, x_139, x_140);
lean_inc_ref(x_77);
lean_inc(x_72);
lean_inc(x_47);
x_142 = l_Lean_Syntax_node3(x_47, x_62, x_72, x_141, x_77);
lean_inc(x_47);
x_143 = l_Lean_Syntax_node1(x_47, x_51, x_142);
lean_inc(x_47);
x_144 = l_Lean_Syntax_node2(x_47, x_55, x_104, x_143);
lean_inc_ref(x_110);
lean_inc_ref(x_53);
lean_inc(x_47);
x_145 = l_Lean_Syntax_node4(x_47, x_129, x_134, x_53, x_110, x_144);
lean_inc(x_47);
x_146 = l_Lean_Syntax_node2(x_47, x_127, x_128, x_145);
lean_inc(x_47);
x_147 = l_Lean_Syntax_node3(x_47, x_62, x_72, x_146, x_77);
lean_inc(x_47);
x_148 = l_Lean_Syntax_node1(x_47, x_51, x_147);
lean_inc(x_47);
x_149 = l_Lean_Syntax_node2(x_47, x_55, x_121, x_148);
lean_inc(x_47);
x_150 = l_Lean_Syntax_node4(x_47, x_89, x_91, x_125, x_110, x_149);
lean_inc(x_47);
x_151 = l_Lean_Syntax_node2(x_47, x_51, x_116, x_150);
lean_inc(x_47);
x_152 = l_Lean_Syntax_node1(x_47, x_88, x_151);
lean_inc_ref(x_53);
x_153 = l_Lean_Syntax_node6(x_47, x_49, x_50, x_53, x_53, x_85, x_87, x_152);
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_153);
x_154 = x_36;
goto block_155;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_153);
x_154 = x_156;
goto block_155;
}
block_155:
{
return x_154;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_24);
x_161 = lean_ctor_get(x_8, 5);
lean_inc(x_161);
x_162 = lean_ctor_get(x_8, 10);
lean_inc(x_162);
x_163 = lean_ctor_get(x_8, 11);
lean_inc(x_163);
lean_dec_ref(x_8);
x_164 = 0;
x_165 = l_Lean_SourceInfo_fromRef(x_161, x_164);
lean_dec(x_161);
x_166 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20));
x_167 = l_Lean_mkCIdent(x_28);
x_168 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_169 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__8);
x_170 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__9));
x_171 = l_Lean_addMacroScope(x_162, x_170, x_163);
x_172 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__11));
lean_inc(x_165);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 3);
lean_ctor_set(x_12, 3, x_172);
lean_ctor_set(x_12, 2, x_171);
lean_ctor_set(x_12, 1, x_169);
lean_ctor_set(x_12, 0, x_165);
x_173 = x_12;
goto block_183;
}
else
{
lean_object* x_184; 
x_184 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_184, 0, x_165);
lean_ctor_set(x_184, 1, x_169);
lean_ctor_set(x_184, 2, x_171);
lean_ctor_set(x_184, 3, x_172);
x_173 = x_184;
goto block_183;
}
block_183:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = l_Array_mkArray3___redArg(x_39, x_42, x_173);
x_175 = l_Array_append___redArg(x_174, x_35);
lean_dec(x_35);
lean_inc(x_165);
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 2, x_175);
lean_ctor_set(x_22, 1, x_168);
lean_ctor_set(x_22, 0, x_165);
x_176 = x_22;
goto block_181;
}
else
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_182, 0, x_165);
lean_ctor_set(x_182, 1, x_168);
lean_ctor_set(x_182, 2, x_175);
x_176 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_177; lean_object* x_178; 
x_177 = l_Lean_Syntax_node2(x_165, x_166, x_167, x_176);
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_177);
x_178 = x_36;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_177);
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
}
}
else
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_194; 
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_24);
lean_del_object(x_22);
lean_del_object(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_8);
x_187 = lean_ctor_get(x_34, 0);
x_194 = !lean_is_exclusive(x_34);
if (x_194 == 0)
{
x_188 = x_34;
x_189 = x_194;
goto block_193;
}
else
{
lean_inc(x_187);
lean_dec(x_34);
x_188 = lean_box(0);
x_189 = x_194;
goto block_193;
}
block_193:
{
lean_object* x_190; 
if (x_189 == 0)
{
x_190 = x_188;
goto block_191;
}
else
{
lean_object* x_192; 
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_187);
x_190 = x_192;
goto block_191;
}
block_191:
{
return x_190;
}
}
}
}
else
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; uint8_t x_202; 
lean_dec(x_28);
lean_dec(x_24);
lean_del_object(x_22);
lean_del_object(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_195 = lean_ctor_get(x_29, 0);
x_202 = !lean_is_exclusive(x_29);
if (x_202 == 0)
{
x_196 = x_29;
x_197 = x_202;
goto block_201;
}
else
{
lean_inc(x_195);
lean_dec(x_29);
x_196 = lean_box(0);
x_197 = x_202;
goto block_201;
}
block_201:
{
lean_object* x_198; 
if (x_197 == 0)
{
x_198 = x_196;
goto block_199;
}
else
{
lean_object* x_200; 
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_195);
x_198 = x_200;
goto block_199;
}
block_199:
{
return x_198;
}
}
}
}
else
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_210; 
lean_dec(x_24);
lean_del_object(x_22);
lean_dec(x_21);
lean_del_object(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_203 = lean_ctor_get(x_27, 0);
x_210 = !lean_is_exclusive(x_27);
if (x_210 == 0)
{
x_204 = x_27;
x_205 = x_210;
goto block_209;
}
else
{
lean_inc(x_203);
lean_dec(x_27);
x_204 = lean_box(0);
x_205 = x_210;
goto block_209;
}
block_209:
{
lean_object* x_206; 
if (x_205 == 0)
{
x_206 = x_204;
goto block_207;
}
else
{
lean_object* x_208; 
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_203);
x_206 = x_208;
goto block_207;
}
block_207:
{
return x_206;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatch_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_dec(x_7);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatch_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 2);
x_12 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_deriving_decEq_linear__construction__threshold;
x_13 = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatch_spec__0(x_11, x_12);
x_14 = l_Lean_InductiveVal_numCtors(x_3);
x_15 = lean_nat_dec_le(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatch(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__3));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_11 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc_ref(x_8);
lean_inc_ref(x_3);
lean_inc(x_12);
x_13 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatch(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_126; 
x_14 = lean_ctor_get(x_13, 0);
x_126 = !lean_is_exclusive(x_13);
if (x_126 == 0)
{
x_15 = x_13;
x_16 = x_126;
goto block_125;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_122; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 2);
x_122 = !lean_is_exclusive(x_12);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_12, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_12, 1);
lean_dec(x_124);
x_19 = x_12;
x_20 = x_122;
goto block_121;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_122;
goto block_121;
}
block_121:
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
lean_dec_ref(x_3);
x_22 = lean_box(0);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get_borrowed(x_22, x_18, x_23);
lean_inc(x_24);
x_25 = lean_mk_syntax_ident(x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_array_get(x_22, x_18, x_26);
lean_dec_ref(x_18);
x_28 = lean_mk_syntax_ident(x_27);
if (x_21 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_94 = lean_ctor_get(x_8, 5);
lean_inc(x_94);
x_95 = lean_ctor_get(x_8, 10);
lean_inc(x_95);
x_96 = lean_ctor_get(x_8, 11);
lean_inc(x_96);
lean_dec_ref(x_8);
x_97 = l_Lean_SourceInfo_fromRef(x_94, x_21);
x_98 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22));
x_99 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_100 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
lean_inc(x_97);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_99);
lean_ctor_set(x_101, 2, x_100);
lean_inc_ref(x_101);
x_102 = l_Lean_Syntax_node2(x_97, x_98, x_101, x_101);
x_29 = x_102;
x_30 = x_94;
x_31 = x_95;
x_32 = x_96;
goto block_93;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_103 = lean_ctor_get(x_8, 5);
lean_inc(x_103);
x_104 = lean_ctor_get(x_8, 10);
lean_inc(x_104);
x_105 = lean_ctor_get(x_8, 11);
lean_inc(x_105);
lean_dec_ref(x_8);
x_106 = 0;
x_107 = l_Lean_SourceInfo_fromRef(x_103, x_106);
x_108 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22));
x_109 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_110 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24));
x_111 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__25));
lean_inc(x_107);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_107);
lean_ctor_set(x_112, 1, x_111);
x_113 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__26));
lean_inc(x_107);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_107);
lean_ctor_set(x_114, 1, x_113);
lean_inc(x_107);
x_115 = l_Lean_Syntax_node1(x_107, x_109, x_114);
x_116 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
lean_inc(x_107);
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_107);
lean_ctor_set(x_117, 1, x_109);
lean_ctor_set(x_117, 2, x_116);
lean_inc(x_25);
lean_inc_ref(x_117);
lean_inc(x_107);
x_118 = l_Lean_Syntax_node4(x_107, x_110, x_112, x_115, x_117, x_25);
lean_inc(x_107);
x_119 = l_Lean_Syntax_node1(x_107, x_109, x_118);
x_120 = l_Lean_Syntax_node2(x_107, x_108, x_119, x_117);
x_29 = x_120;
x_30 = x_103;
x_31 = x_104;
x_32 = x_105;
goto block_93;
}
block_93:
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = 0;
x_34 = l_Lean_SourceInfo_fromRef(x_30, x_33);
lean_dec(x_30);
x_35 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20));
x_36 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__0, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__0_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__0);
x_37 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__1));
lean_inc(x_32);
lean_inc(x_31);
x_38 = l_Lean_addMacroScope(x_31, x_37, x_32);
x_39 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__5));
lean_inc(x_34);
if (x_20 == 0)
{
lean_ctor_set_tag(x_19, 3);
lean_ctor_set(x_19, 3, x_39);
lean_ctor_set(x_19, 2, x_38);
lean_ctor_set(x_19, 1, x_36);
lean_ctor_set(x_19, 0, x_34);
x_40 = x_19;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_92, 0, x_34);
lean_ctor_set(x_92, 1, x_36);
lean_ctor_set(x_92, 2, x_38);
lean_ctor_set(x_92, 3, x_39);
x_40 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_41 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_42 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__33));
x_43 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35));
x_44 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__36));
lean_inc(x_34);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_44);
x_46 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__38));
x_47 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40);
x_48 = l_Lean_addMacroScope(x_31, x_22, x_32);
x_49 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__5));
lean_inc(x_34);
x_50 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_50, 0, x_34);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set(x_50, 3, x_49);
lean_inc(x_34);
x_51 = l_Lean_Syntax_node1(x_34, x_46, x_50);
lean_inc(x_34);
x_52 = l_Lean_Syntax_node2(x_34, x_43, x_45, x_51);
x_53 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__10));
x_54 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__11));
lean_inc(x_34);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_34);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_34);
x_56 = l_Lean_Syntax_node3(x_34, x_53, x_25, x_55, x_28);
x_57 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__65));
lean_inc(x_34);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_34);
lean_ctor_set(x_58, 1, x_57);
lean_inc(x_34);
x_59 = l_Lean_Syntax_node3(x_34, x_42, x_52, x_56, x_58);
lean_inc(x_34);
x_60 = l_Lean_Syntax_node1(x_34, x_41, x_59);
lean_inc(x_34);
x_61 = l_Lean_Syntax_node2(x_34, x_35, x_40, x_60);
x_62 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8));
x_63 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10));
x_64 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
lean_inc(x_34);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_34);
lean_ctor_set(x_65, 1, x_41);
lean_ctor_set(x_65, 2, x_64);
lean_inc_ref_n(x_65, 7);
lean_inc(x_34);
x_66 = l_Lean_Syntax_node7(x_34, x_63, x_65, x_65, x_65, x_65, x_65, x_65, x_65);
x_67 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12));
x_68 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__13));
lean_inc(x_34);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_34);
lean_ctor_set(x_69, 1, x_68);
x_70 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15));
x_71 = lean_mk_syntax_ident(x_2);
lean_inc_ref(x_65);
lean_inc(x_34);
x_72 = l_Lean_Syntax_node2(x_34, x_70, x_71, x_65);
x_73 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17));
x_74 = l_Array_append___redArg(x_64, x_17);
lean_dec_ref(x_17);
lean_inc(x_34);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_34);
lean_ctor_set(x_75, 1, x_41);
lean_ctor_set(x_75, 2, x_74);
x_76 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__69));
x_77 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__8));
lean_inc(x_34);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_34);
lean_ctor_set(x_78, 1, x_77);
lean_inc(x_34);
x_79 = l_Lean_Syntax_node2(x_34, x_76, x_78, x_61);
lean_inc(x_34);
x_80 = l_Lean_Syntax_node1(x_34, x_41, x_79);
lean_inc(x_34);
x_81 = l_Lean_Syntax_node2(x_34, x_73, x_75, x_80);
x_82 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19));
x_83 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__18));
lean_inc(x_34);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_34);
lean_ctor_set(x_84, 1, x_83);
lean_inc_ref(x_65);
lean_inc(x_34);
x_85 = l_Lean_Syntax_node4(x_34, x_82, x_84, x_14, x_29, x_65);
lean_inc(x_34);
x_86 = l_Lean_Syntax_node5(x_34, x_67, x_69, x_72, x_81, x_85, x_65);
x_87 = l_Lean_Syntax_node2(x_34, x_62, x_66, x_86);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_87);
x_88 = x_15;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_87);
x_88 = x_90;
goto block_89;
}
block_89:
{
return x_88;
}
}
}
}
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_13;
}
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_134; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_127 = lean_ctor_get(x_11, 0);
x_134 = !lean_is_exclusive(x_11);
if (x_134 == 0)
{
x_128 = x_11;
x_129 = x_134;
goto block_133;
}
else
{
lean_inc(x_127);
lean_dec(x_11);
x_128 = lean_box(0);
x_129 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_130; 
if (x_129 == 0)
{
x_130 = x_128;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_127);
x_130 = x_132;
goto block_131;
}
block_131:
{
return x_130;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_4, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_box(0);
x_17 = l_Lean_instInhabitedInductiveVal_default;
x_18 = lean_array_get_borrowed(x_16, x_2, x_4);
x_19 = lean_array_get_borrowed(x_17, x_15, x_4);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_19);
lean_inc(x_18);
lean_inc_ref(x_3);
x_20 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction(x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_array_push(x_5, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
x_4 = x_24;
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_26 = lean_ctor_get(x_20, 0);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
x_27 = x_20;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_9);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__0));
lean_inc_ref(x_6);
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions_spec__0___redArg(x_10, x_9, x_1, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_37; 
x_14 = lean_ctor_get(x_13, 0);
x_37 = !lean_is_exclusive(x_13);
if (x_37 == 0)
{
x_15 = x_13;
x_16 = x_37;
goto block_36;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_17 = lean_ctor_get(x_6, 5);
lean_inc(x_17);
lean_dec_ref(x_6);
x_18 = 0;
x_19 = l_Lean_SourceInfo_fromRef(x_17, x_18);
lean_dec(x_17);
x_20 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__0));
x_21 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__1));
lean_inc(x_19);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
x_23 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_24 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
x_25 = lean_array_size(x_14);
x_26 = 0;
x_27 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__1(x_25, x_26, x_14);
x_28 = l_Array_append___redArg(x_24, x_27);
lean_dec_ref(x_27);
lean_inc(x_19);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_29, 2, x_28);
x_30 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___closed__2));
lean_inc(x_19);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Syntax_node3(x_19, x_21, x_22, x_29, x_31);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_32);
x_33 = x_15;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec_ref(x_6);
x_38 = lean_ctor_get(x_13, 0);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
x_39 = x_13;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_13);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg(x_1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_6 = x_1;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_MessageData_ofSyntax(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
x_9 = x_12;
goto block_11;
}
block_11:
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__39));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___closed__1));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1));
x_12 = ((lean_object*)(l_Lean_Elab_Deriving_DecEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_));
x_13 = 1;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_10);
x_14 = l_Lean_Elab_Deriving_mkContext(x_11, x_12, x_10, x_13, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_15);
x_16 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunctions(x_15, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
lean_inc_ref(x_19);
x_20 = lean_array_push(x_19, x_10);
x_21 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_22 = l_Lean_Elab_Deriving_mkInstanceCmds(x_15, x_11, x_20, x_21, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_59; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__0));
x_25 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg(x_24, x_6);
x_26 = lean_ctor_get(x_25, 0);
x_59 = !lean_is_exclusive(x_25);
if (x_59 == 0)
{
x_27 = x_25;
x_28 = x_59;
goto block_58;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_array_push(x_19, x_17);
x_30 = l_Array_append___redArg(x_29, x_23);
lean_dec(x_23);
x_31 = lean_unbox(x_26);
lean_dec(x_26);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_30);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_30);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_del_object(x_27);
x_35 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2);
lean_inc_ref(x_30);
x_36 = lean_array_to_list(x_30);
x_37 = lean_box(0);
x_38 = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__1(x_36, x_37);
x_39 = l_Lean_MessageData_ofList(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg(x_24, x_40, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; uint8_t x_48; 
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_41, 0);
lean_dec(x_49);
x_42 = x_41;
x_43 = x_48;
goto block_47;
}
else
{
lean_dec(x_41);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_30);
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_30);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec_ref(x_30);
x_50 = lean_ctor_get(x_41, 0);
x_57 = !lean_is_exclusive(x_41);
if (x_57 == 0)
{
x_51 = x_41;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_41);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
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
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_67; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_60 = lean_ctor_get(x_22, 0);
x_67 = !lean_is_exclusive(x_22);
if (x_67 == 0)
{
x_61 = x_22;
x_62 = x_67;
goto block_66;
}
else
{
lean_inc(x_60);
lean_dec(x_22);
x_61 = lean_box(0);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_62 == 0)
{
x_63 = x_61;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_60);
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
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_75; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_68 = lean_ctor_get(x_16, 0);
x_75 = !lean_is_exclusive(x_16);
if (x_75 == 0)
{
x_69 = x_16;
x_70 = x_75;
goto block_74;
}
else
{
lean_inc(x_68);
lean_dec(x_16);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_76 = lean_ctor_get(x_14, 0);
x_83 = !lean_is_exclusive(x_14);
if (x_83 == 0)
{
x_77 = x_14;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_14);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg(x_1, x_2, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_9);
x_10 = l_Lean_Elab_Command_elabCommand(x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
else
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec_ref(x_5);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__1(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_nat_dec_lt(x_1, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec_ref(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_2, x_2);
if (x_10 == 0)
{
if (x_8 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_7);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_2);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__1(x_3, x_12, x_13, x_7, x_4, x_5);
return x_14;
}
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_2);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__1(x_3, x_15, x_16, x_7, x_4, x_5);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2_spec__3___redArg(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_35; 
x_4 = lean_st_ref_take(x_2);
x_5 = lean_ctor_get(x_4, 8);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
x_9 = lean_ctor_get(x_4, 3);
x_10 = lean_ctor_get(x_4, 4);
x_11 = lean_ctor_get(x_4, 5);
x_12 = lean_ctor_get(x_4, 6);
x_13 = lean_ctor_get(x_4, 7);
x_14 = lean_ctor_get(x_4, 9);
x_15 = lean_ctor_get(x_4, 10);
x_35 = !lean_is_exclusive(x_4);
if (x_35 == 0)
{
x_16 = x_4;
x_17 = x_35;
goto block_34;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_33; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_5, 2);
x_33 = !lean_is_exclusive(x_5);
if (x_33 == 0)
{
x_21 = x_5;
x_22 = x_33;
goto block_32;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_21 = lean_box(0);
x_22 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_20);
x_23 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_24; 
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_1);
if (x_17 == 0)
{
lean_ctor_set(x_16, 8, x_23);
x_24 = x_16;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_7);
lean_ctor_set(x_29, 2, x_8);
lean_ctor_set(x_29, 3, x_9);
lean_ctor_set(x_29, 4, x_10);
lean_ctor_set(x_29, 5, x_11);
lean_ctor_set(x_29, 6, x_12);
lean_ctor_set(x_29, 7, x_13);
lean_ctor_set(x_29, 8, x_23);
lean_ctor_set(x_29, 9, x_14);
lean_ctor_set(x_29, 10, x_15);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_st_ref_set(x_2, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2_spec__3___redArg(x_4, x_2);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_20; lean_object* x_21; 
x_6 = lean_st_ref_get(x_4);
x_7 = lean_ctor_get(x_6, 8);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
lean_dec_ref(x_7);
x_20 = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2_spec__3___redArg(x_1, x_4);
lean_dec_ref(x_20);
lean_inc(x_4);
x_21 = lean_apply_3(x_2, x_3, x_4, lean_box(0));
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2_spec__3___redArg(x_8, x_4);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_23, 0);
lean_dec(x_31);
x_24 = x_23;
x_25 = x_30;
goto block_29;
}
else
{
lean_dec(x_23);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_22);
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_22);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec_ref(x_21);
x_9 = x_32;
goto block_19;
}
block_19:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
x_10 = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2_spec__3___redArg(x_8, x_4);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_11 = x_10;
x_12 = x_17;
goto block_16;
}
else
{
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_9);
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_9);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Command_instInhabitedScope_default;
x_8 = l_List_head_x21___redArg(x_7, x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_pp_macroStack;
x_11 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_30; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_14, 0);
lean_dec(x_31);
x_16 = x_14;
x_17 = x_30;
goto block_29;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13___closed__0);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_1);
x_19 = x_16;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_18);
x_19 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_MessageData_ofSyntax(x_15);
x_23 = l_Lean_indentD(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__13(x_24, x_2);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__4(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__3);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__4);
x_3 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_instInhabitedScope_default;
x_9 = l_List_head_x21___redArg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__2);
x_12 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__5);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg(x_1, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_7);
x_10 = l_Lean_Elab_getBetterRef(x_6, x_7);
lean_dec(x_6);
x_11 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__2___redArg(x_9, x_7, x_3);
x_12 = lean_ctor_get(x_11, 0);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
x_13 = x_11;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_12);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_5, 0);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
x_22 = x_5;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_5);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
lean_inc(x_1);
x_7 = l_Lean_isInductiveCore_x3f(x_6, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__1);
x_9 = 0;
x_10 = l_Lean_MessageData_ofConstName(x_1, x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0___closed__1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0___redArg(x_13, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_7, 0);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
x_16 = x_7;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 0);
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
lean_inc_ref(x_2);
x_5 = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_49; 
x_6 = lean_ctor_get(x_5, 0);
x_49 = !lean_is_exclusive(x_5);
if (x_49 == 0)
{
x_7 = x_5;
x_8 = x_49;
goto block_48;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_49;
goto block_48;
}
block_48:
{
uint8_t x_9; 
x_9 = l_Lean_InductiveVal_isNested(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_del_object(x_7);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___boxed), 8, 1);
lean_closure_set(x_10, 0, x_6);
lean_inc_ref(x_2);
x_11 = l_Lean_Elab_Command_liftTermElabM___redArg(x_10, x_2, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_12);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq___lam__0___boxed), 6, 3);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_12);
x_16 = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2___redArg(x_9, x_15, x_2, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_25; 
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_17 = x_16;
x_18 = x_25;
goto block_24;
}
else
{
lean_dec(x_16);
x_17 = lean_box(0);
x_18 = x_25;
goto block_24;
}
block_24:
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 1;
x_20 = lean_box(x_19);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_20);
x_21 = x_17;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
x_27 = lean_ctor_get(x_16, 0);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
x_28 = x_16;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_16);
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
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_35 = lean_ctor_get(x_11, 0);
x_42 = !lean_is_exclusive(x_11);
if (x_42 == 0)
{
x_36 = x_11;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_43 = 0;
x_44 = lean_box(x_43);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_44);
x_45 = x_7;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_50 = lean_ctor_get(x_5, 0);
x_57 = !lean_is_exclusive(x_5);
if (x_57 == 0)
{
x_51 = x_5;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_5);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2_spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2_spec__3___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2_spec__3(x_5, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__2(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__2___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_1);
lean_inc_ref(x_6);
x_12 = l_mkNatLookupTable(x_6, x_1, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_6);
x_17 = 0;
x_18 = 1;
x_19 = 1;
x_20 = l_Lean_Meta_mkLambdaFVars(x_16, x_13, x_17, x_18, x_17, x_18, x_19, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc(x_10);
lean_inc_ref(x_9);
x_22 = l_Lean_mkArrow(x_3, x_1, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___lam__0___closed__0));
x_25 = l_Lean_Name_str___override(x_4, x_24);
lean_inc(x_25);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
lean_ctor_set(x_26, 2, x_23);
x_27 = lean_box(1);
x_28 = 1;
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_21);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_28);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_addAndCompile(x_32, x_18, x_9, x_10);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_34 = lean_ctor_get(x_22, 0);
x_41 = !lean_is_exclusive(x_22);
if (x_41 == 0)
{
x_35 = x_22;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_42 = lean_ctor_get(x_20, 0);
x_49 = !lean_is_exclusive(x_20);
if (x_49 == 0)
{
x_43 = x_20;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_20);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_12, 0);
x_57 = !lean_is_exclusive(x_12);
if (x_57 == 0)
{
x_51 = x_12;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_12);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = l_Lean_mkConst(x_6, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__2(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_6 = x_1;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Level_param___override(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
x_9 = x_12;
goto block_11;
}
block_11:
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
lean_inc(x_1);
x_9 = l_Lean_isInductiveCore_x3f(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__1);
x_11 = 0;
x_12 = l_Lean_MessageData_ofConstName(x_1, x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0___closed__1);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0_spec__0___redArg(x_15, x_2, x_3, x_4, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_9, 0);
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
x_18 = x_9;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 0);
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
x_14 = x_12;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
x_21 = lean_ctor_get(x_12, 0);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
x_22 = x_12;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4___redArg(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = 0;
x_11 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4___redArg(x_1, x_9, x_2, x_3, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_8, 4);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_box(0);
lean_inc(x_11);
x_13 = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__1(x_11, x_12);
lean_inc(x_13);
lean_inc(x_1);
x_14 = l_Lean_mkConst(x_1, x_13);
x_15 = lean_array_mk(x_10);
x_16 = lean_array_size(x_15);
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__2(x_13, x_16, x_17, x_15);
x_19 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__55));
x_20 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__2, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__2_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__2);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___lam__0___boxed), 11, 5);
lean_closure_set(x_21, 0, x_14);
lean_closure_set(x_21, 1, x_18);
lean_closure_set(x_21, 2, x_20);
lean_closure_set(x_21, 3, x_1);
lean_closure_set(x_21, 4, x_11);
x_22 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3___redArg(x_19, x_20, x_21, x_2, x_3, x_4, x_5);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_23 = lean_ctor_get(x_7, 0);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
x_24 = x_7;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3_spec__4(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
lean_inc(x_1);
x_9 = l_Lean_mkConst(x_7, x_1);
lean_inc_ref(x_2);
x_10 = l_Lean_Expr_app___override(x_2, x_9);
x_11 = l_Lean_Expr_app___override(x_4, x_10);
x_3 = x_8;
x_4 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
lean_inc_ref(x_9);
x_15 = l_Lean_Expr_app___override(x_1, x_9);
x_16 = l_Lean_Expr_app___override(x_2, x_15);
lean_inc_ref(x_9);
x_17 = l_Lean_mkAppB(x_3, x_16, x_9);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
lean_inc_ref(x_9);
x_20 = lean_array_push(x_19, x_9);
x_21 = 0;
x_22 = 1;
x_23 = 1;
lean_inc_ref(x_17);
x_24 = l_Lean_Meta_mkLambdaFVars(x_20, x_17, x_21, x_22, x_21, x_22, x_23, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_66; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_4);
x_26 = l_Lean_mkCasesOnName(x_4);
x_27 = lean_box(0);
lean_inc(x_5);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
x_29 = l_Lean_mkConst(x_26, x_28);
x_30 = l_Lean_mkAppB(x_29, x_25, x_9);
x_31 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm_spec__0___redArg(x_5, x_6, x_7, x_30);
x_32 = lean_ctor_get(x_31, 0);
x_66 = !lean_is_exclusive(x_31);
if (x_66 == 0)
{
x_33 = x_31;
x_34 = x_66;
goto block_65;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_35; 
x_35 = l_Lean_Meta_mkLambdaFVars(x_20, x_32, x_21, x_22, x_21, x_22, x_23, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_Meta_mkForallFVars(x_20, x_17, x_21, x_22, x_22, x_23, x_10, x_11, x_12, x_13);
lean_dec_ref(x_20);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lam__0___closed__0));
x_40 = l_Lean_Name_str___override(x_4, x_39);
lean_inc(x_40);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_8);
lean_ctor_set(x_41, 2, x_38);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_43);
if (x_34 == 0)
{
lean_ctor_set_tag(x_33, 2);
lean_ctor_set(x_33, 0, x_44);
x_45 = x_33;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_44);
x_45 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_46; 
x_46 = l_Lean_addAndCompile(x_45, x_22, x_12, x_13);
return x_46;
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_36);
lean_del_object(x_33);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_8);
lean_dec(x_4);
x_49 = lean_ctor_get(x_37, 0);
x_56 = !lean_is_exclusive(x_37);
if (x_56 == 0)
{
x_50 = x_37;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_37);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_del_object(x_33);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_8);
lean_dec(x_4);
x_57 = lean_ctor_get(x_35, 0);
x_64 = !lean_is_exclusive(x_35);
if (x_64 == 0)
{
x_58 = x_35;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_dec(x_35);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_74; 
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_67 = lean_ctor_get(x_24, 0);
x_74 = !lean_is_exclusive(x_24);
if (x_74 == 0)
{
x_68 = x_24;
x_69 = x_74;
goto block_73;
}
else
{
lean_inc(x_67);
lean_dec(x_24);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__0(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_8, 4);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_box(0);
lean_inc(x_11);
x_13 = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__1(x_11, x_12);
lean_inc(x_1);
x_14 = l_mkCtorIdxName(x_1);
lean_inc(x_13);
x_15 = l_Lean_mkConst(x_14, x_13);
x_16 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___lam__0___closed__0));
lean_inc(x_1);
x_17 = l_Lean_Name_str___override(x_1, x_16);
lean_inc(x_13);
x_18 = l_Lean_mkConst(x_17, x_13);
lean_inc(x_13);
lean_inc(x_1);
x_19 = l_Lean_mkConst(x_1, x_13);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_19);
x_20 = l_Lean_Meta_getLevel(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__1));
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_12);
lean_inc_ref(x_23);
x_24 = l_Lean_mkConst(x_22, x_23);
lean_inc_ref(x_19);
x_25 = l_Lean_Expr_app___override(x_24, x_19);
x_26 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__3));
x_27 = l_Lean_mkConst(x_26, x_23);
lean_inc_ref(x_19);
x_28 = l_Lean_Expr_app___override(x_27, x_19);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lam__0___boxed), 14, 8);
lean_closure_set(x_29, 0, x_15);
lean_closure_set(x_29, 1, x_18);
lean_closure_set(x_29, 2, x_25);
lean_closure_set(x_29, 3, x_1);
lean_closure_set(x_29, 4, x_13);
lean_closure_set(x_29, 5, x_28);
lean_closure_set(x_29, 6, x_10);
lean_closure_set(x_29, 7, x_11);
x_30 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__5));
x_31 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat_spec__3___redArg(x_30, x_19, x_29, x_2, x_3, x_4, x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_32 = lean_ctor_get(x_20, 0);
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
x_33 = x_20;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_40 = lean_ctor_get(x_7, 0);
x_47 = !lean_is_exclusive(x_7);
if (x_47 == 0)
{
x_41 = x_7;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_7);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm_spec__0___redArg(x_1, x_2, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lean_inheritedTraceOptions;
x_5 = lean_st_ref_get(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_instInhabitedScope_default;
x_9 = l_List_head_x21___redArg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__0___redArg___closed__1));
x_15 = l_Lean_Name_append(x_14, x_1);
x_16 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_5, x_10, x_15);
lean_dec(x_15);
lean_dec_ref(x_10);
lean_dec(x_5);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__0___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__4));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__10));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__13));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__17));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__31(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__30));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_1);
x_9 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec_ref(x_9);
lean_inc_ref(x_6);
lean_inc(x_1);
x_10 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; uint8_t x_233; 
x_233 = !lean_is_exclusive(x_10);
if (x_233 == 0)
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_10, 0);
lean_dec(x_234);
x_11 = x_10;
x_12 = x_233;
goto block_232;
}
else
{
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = x_233;
goto block_232;
}
block_232:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_13 = lean_ctor_get(x_6, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 10);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 11);
lean_inc(x_15);
lean_dec_ref(x_6);
x_16 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNat___lam__0___closed__0));
lean_inc(x_1);
x_17 = l_Lean_Name_str___override(x_1, x_16);
x_18 = lean_mk_syntax_ident(x_17);
x_19 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lam__0___closed__0));
lean_inc(x_1);
x_20 = l_Lean_Name_str___override(x_1, x_19);
x_21 = lean_mk_syntax_ident(x_20);
x_22 = 0;
x_23 = l_Lean_SourceInfo_fromRef(x_13, x_22);
lean_dec(x_13);
x_24 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8));
x_25 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10));
x_26 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__7));
x_27 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__8);
lean_inc(x_23);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
lean_inc_ref_n(x_28, 7);
lean_inc(x_23);
x_29 = l_Lean_Syntax_node7(x_23, x_25, x_28, x_28, x_28, x_28, x_28, x_28, x_28);
x_30 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__0));
x_31 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__1));
x_32 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__3));
lean_inc_ref(x_28);
lean_inc(x_23);
x_33 = l_Lean_Syntax_node1(x_23, x_32, x_28);
lean_inc(x_23);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_30);
x_35 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__5));
x_36 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__69));
x_37 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__8));
lean_inc(x_23);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_37);
x_39 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__20));
x_40 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__6, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__6);
x_41 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1));
lean_inc(x_15);
lean_inc(x_14);
x_42 = l_Lean_addMacroScope(x_14, x_41, x_15);
x_43 = lean_box(0);
x_44 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__8));
lean_inc(x_23);
x_45 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_45, 0, x_23);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_44);
x_46 = l_Lean_mkCIdent(x_1);
lean_inc(x_23);
x_47 = l_Lean_Syntax_node1(x_23, x_26, x_46);
lean_inc(x_23);
x_48 = l_Lean_Syntax_node2(x_23, x_39, x_45, x_47);
lean_inc_ref(x_38);
lean_inc(x_23);
x_49 = l_Lean_Syntax_node2(x_23, x_36, x_38, x_48);
lean_inc_ref(x_28);
lean_inc(x_23);
x_50 = l_Lean_Syntax_node2(x_23, x_35, x_28, x_49);
x_51 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19));
x_52 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__18));
lean_inc(x_23);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_23);
lean_ctor_set(x_53, 1, x_52);
x_54 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__0));
x_55 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__1));
lean_inc(x_23);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_23);
lean_ctor_set(x_56, 1, x_54);
x_57 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___lam__0___closed__3));
x_58 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__9, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__9_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__9);
x_59 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__5));
lean_inc(x_15);
lean_inc(x_14);
x_60 = l_Lean_addMacroScope(x_14, x_59, x_15);
lean_inc(x_23);
x_61 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_61, 0, x_23);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_43);
x_62 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__11, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__11_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__11);
x_63 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__12));
lean_inc(x_15);
lean_inc(x_14);
x_64 = l_Lean_addMacroScope(x_14, x_63, x_15);
lean_inc(x_23);
x_65 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_65, 0, x_23);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set(x_65, 3, x_43);
lean_inc(x_23);
x_66 = l_Lean_Syntax_node2(x_23, x_26, x_61, x_65);
x_67 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__5));
lean_inc(x_23);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_23);
lean_ctor_set(x_68, 1, x_67);
x_69 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__1));
x_70 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__2));
lean_inc(x_23);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_23);
lean_ctor_set(x_71, 1, x_70);
x_72 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__4));
x_73 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__6);
x_74 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__7));
lean_inc(x_15);
lean_inc(x_14);
x_75 = l_Lean_addMacroScope(x_14, x_74, x_15);
lean_inc(x_23);
x_76 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_76, 0, x_23);
lean_ctor_set(x_76, 1, x_73);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set(x_76, 3, x_43);
lean_inc_ref(x_76);
lean_inc(x_23);
x_77 = l_Lean_Syntax_node1(x_23, x_72, x_76);
x_78 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__10));
x_79 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__14, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__14_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__14);
x_80 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__16));
lean_inc(x_15);
lean_inc(x_14);
x_81 = l_Lean_addMacroScope(x_14, x_80, x_15);
lean_inc(x_23);
x_82 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_82, 0, x_23);
lean_ctor_set(x_82, 1, x_79);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_43);
x_83 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__11));
lean_inc(x_23);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_23);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__18, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__18_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__18);
x_86 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__19));
lean_inc(x_15);
lean_inc(x_14);
x_87 = l_Lean_addMacroScope(x_14, x_86, x_15);
lean_inc(x_23);
x_88 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_88, 0, x_23);
lean_ctor_set(x_88, 1, x_85);
lean_ctor_set(x_88, 2, x_87);
lean_ctor_set(x_88, 3, x_43);
lean_inc(x_23);
x_89 = l_Lean_Syntax_node3(x_23, x_78, x_82, x_84, x_88);
x_90 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__12));
lean_inc(x_23);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_23);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__1, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__1_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__1);
x_93 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__2));
lean_inc(x_15);
lean_inc(x_14);
x_94 = l_Lean_addMacroScope(x_14, x_93, x_15);
x_95 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__6));
lean_inc(x_23);
x_96 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_96, 0, x_23);
lean_ctor_set(x_96, 1, x_92);
lean_ctor_set(x_96, 2, x_94);
lean_ctor_set(x_96, 3, x_95);
x_97 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__33));
x_98 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__35));
x_99 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__36));
lean_inc(x_23);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_23);
lean_ctor_set(x_100, 1, x_99);
x_101 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__38));
x_102 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__40);
x_103 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
x_104 = l_Lean_addMacroScope(x_14, x_103, x_15);
x_105 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__23));
lean_inc(x_23);
x_106 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_106, 0, x_23);
lean_ctor_set(x_106, 1, x_102);
lean_ctor_set(x_106, 2, x_104);
lean_ctor_set(x_106, 3, x_105);
lean_inc(x_23);
x_107 = l_Lean_Syntax_node1(x_23, x_101, x_106);
lean_inc(x_23);
x_108 = l_Lean_Syntax_node2(x_23, x_98, x_100, x_107);
x_109 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__14));
x_110 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__15));
lean_inc(x_23);
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_23);
lean_ctor_set(x_111, 1, x_110);
x_112 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__18));
x_113 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__20));
x_114 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__24));
x_115 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__25));
lean_inc(x_23);
x_116 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_116, 0, x_23);
lean_ctor_set(x_116, 1, x_114);
x_117 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__27));
x_118 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__2));
lean_inc(x_23);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_23);
lean_ctor_set(x_119, 1, x_118);
x_120 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__29));
x_121 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__66));
lean_inc(x_23);
x_122 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_122, 0, x_23);
lean_ctor_set(x_122, 1, x_121);
x_123 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__5));
lean_inc_ref(x_28);
lean_inc(x_23);
x_124 = l_Lean_Syntax_node1(x_23, x_123, x_28);
x_125 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__10));
x_126 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__12));
x_127 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__14));
x_128 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__31, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__31_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__31);
x_129 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__32));
lean_inc(x_15);
lean_inc(x_14);
x_130 = l_Lean_addMacroScope(x_14, x_129, x_15);
lean_inc(x_23);
x_131 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_131, 0, x_23);
lean_ctor_set(x_131, 1, x_128);
lean_ctor_set(x_131, 2, x_130);
lean_ctor_set(x_131, 3, x_43);
lean_inc_ref(x_131);
lean_inc(x_23);
x_132 = l_Lean_Syntax_node1(x_23, x_127, x_131);
x_133 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__19, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__19_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__19);
x_134 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__20));
lean_inc(x_15);
lean_inc(x_14);
x_135 = l_Lean_addMacroScope(x_14, x_134, x_15);
x_136 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchNew___closed__22));
lean_inc(x_23);
x_137 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_137, 0, x_23);
lean_ctor_set(x_137, 1, x_133);
lean_ctor_set(x_137, 2, x_135);
lean_ctor_set(x_137, 3, x_136);
lean_inc_ref(x_76);
lean_inc(x_23);
x_138 = l_Lean_Syntax_node2(x_23, x_26, x_18, x_76);
lean_inc(x_23);
x_139 = l_Lean_Syntax_node2(x_23, x_39, x_137, x_138);
lean_inc_ref(x_53);
lean_inc_ref_n(x_28, 2);
lean_inc(x_23);
x_140 = l_Lean_Syntax_node5(x_23, x_126, x_132, x_28, x_28, x_53, x_139);
lean_inc(x_23);
x_141 = l_Lean_Syntax_node1(x_23, x_125, x_140);
lean_inc(x_23);
x_142 = l_Lean_Syntax_node3(x_23, x_120, x_122, x_124, x_141);
x_143 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__0___closed__24));
lean_inc(x_23);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_23);
lean_ctor_set(x_144, 1, x_143);
x_145 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__34));
x_146 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__35));
lean_inc(x_23);
x_147 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_147, 0, x_23);
lean_ctor_set(x_147, 1, x_146);
x_148 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__37));
lean_inc_ref(x_28);
lean_inc(x_23);
x_149 = l_Lean_Syntax_node1(x_23, x_148, x_28);
x_150 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__39));
x_151 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__40));
lean_inc(x_23);
x_152 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_152, 0, x_23);
lean_ctor_set(x_152, 1, x_151);
x_153 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__42));
lean_inc_ref(x_28);
lean_inc(x_23);
x_154 = l_Lean_Syntax_node2(x_23, x_153, x_28, x_21);
x_155 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___lam__2___closed__3));
lean_inc(x_23);
x_156 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_156, 0, x_23);
lean_ctor_set(x_156, 1, x_155);
lean_inc(x_154);
lean_inc(x_23);
x_157 = l_Lean_Syntax_node3(x_23, x_26, x_154, x_156, x_154);
x_158 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__43));
lean_inc(x_23);
x_159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_159, 0, x_23);
lean_ctor_set(x_159, 1, x_158);
lean_inc(x_23);
x_160 = l_Lean_Syntax_node3(x_23, x_150, x_152, x_157, x_159);
x_161 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__45));
x_162 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__46));
lean_inc(x_23);
x_163 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_163, 0, x_23);
lean_ctor_set(x_163, 1, x_162);
x_164 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__48));
lean_inc(x_23);
x_165 = l_Lean_Syntax_node1(x_23, x_26, x_131);
lean_inc(x_23);
x_166 = l_Lean_Syntax_node1(x_23, x_164, x_165);
lean_inc(x_23);
x_167 = l_Lean_Syntax_node2(x_23, x_161, x_163, x_166);
lean_inc(x_23);
x_168 = l_Lean_Syntax_node1(x_23, x_26, x_167);
lean_inc(x_23);
x_169 = l_Lean_Syntax_node4(x_23, x_145, x_147, x_149, x_160, x_168);
x_170 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__63));
x_171 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__64));
lean_inc(x_23);
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_23);
lean_ctor_set(x_172, 1, x_170);
lean_inc(x_23);
x_173 = l_Lean_Syntax_node1(x_23, x_171, x_172);
lean_inc_ref_n(x_144, 2);
lean_inc(x_23);
x_174 = l_Lean_Syntax_node5(x_23, x_26, x_142, x_144, x_169, x_144, x_173);
lean_inc(x_23);
x_175 = l_Lean_Syntax_node1(x_23, x_113, x_174);
lean_inc(x_23);
x_176 = l_Lean_Syntax_node1(x_23, x_112, x_175);
lean_inc_ref(x_119);
lean_inc(x_23);
x_177 = l_Lean_Syntax_node2(x_23, x_117, x_119, x_176);
x_178 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__50));
x_179 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___closed__7));
lean_inc(x_23);
x_180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_180, 0, x_23);
lean_ctor_set(x_180, 1, x_179);
lean_inc(x_23);
x_181 = l_Lean_Syntax_node1(x_23, x_178, x_180);
lean_inc(x_23);
x_182 = l_Lean_Syntax_node1(x_23, x_26, x_181);
lean_inc(x_23);
x_183 = l_Lean_Syntax_node1(x_23, x_113, x_182);
lean_inc(x_23);
x_184 = l_Lean_Syntax_node1(x_23, x_112, x_183);
lean_inc(x_23);
x_185 = l_Lean_Syntax_node2(x_23, x_117, x_119, x_184);
lean_inc(x_23);
x_186 = l_Lean_Syntax_node2(x_23, x_26, x_177, x_185);
lean_inc(x_23);
x_187 = l_Lean_Syntax_node2(x_23, x_115, x_116, x_186);
lean_inc(x_23);
x_188 = l_Lean_Syntax_node1(x_23, x_26, x_187);
lean_inc(x_23);
x_189 = l_Lean_Syntax_node1(x_23, x_113, x_188);
lean_inc(x_23);
x_190 = l_Lean_Syntax_node1(x_23, x_112, x_189);
lean_inc_ref(x_111);
lean_inc(x_23);
x_191 = l_Lean_Syntax_node2(x_23, x_109, x_111, x_190);
x_192 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__65));
lean_inc(x_23);
x_193 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_193, 0, x_23);
lean_ctor_set(x_193, 1, x_192);
lean_inc(x_23);
x_194 = l_Lean_Syntax_node3(x_23, x_97, x_108, x_191, x_193);
lean_inc(x_23);
x_195 = l_Lean_Syntax_node1(x_23, x_26, x_194);
lean_inc(x_23);
x_196 = l_Lean_Syntax_node2(x_23, x_39, x_96, x_195);
x_197 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__25));
lean_inc(x_23);
x_198 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_198, 0, x_23);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__27);
x_200 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__28));
x_201 = l_Lean_addMacroScope(x_14, x_200, x_15);
x_202 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__6___redArg___closed__2));
lean_inc(x_23);
x_203 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_203, 0, x_23);
lean_ctor_set(x_203, 1, x_199);
lean_ctor_set(x_203, 2, x_201);
lean_ctor_set(x_203, 3, x_202);
lean_inc(x_23);
x_204 = l_Lean_Syntax_node1(x_23, x_26, x_76);
x_205 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__21));
x_206 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__22));
lean_inc(x_23);
x_207 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_207, 0, x_23);
lean_ctor_set(x_207, 1, x_205);
lean_inc(x_204);
lean_inc(x_23);
x_208 = l_Lean_Syntax_node2(x_23, x_206, x_207, x_204);
x_209 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__51));
x_210 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___closed__52));
lean_inc(x_23);
x_211 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_211, 0, x_23);
lean_ctor_set(x_211, 1, x_209);
lean_inc(x_23);
x_212 = l_Lean_Syntax_node1(x_23, x_210, x_211);
lean_inc(x_23);
x_213 = l_Lean_Syntax_node3(x_23, x_26, x_208, x_144, x_212);
lean_inc(x_23);
x_214 = l_Lean_Syntax_node1(x_23, x_113, x_213);
lean_inc(x_23);
x_215 = l_Lean_Syntax_node1(x_23, x_112, x_214);
lean_inc(x_23);
x_216 = l_Lean_Syntax_node2(x_23, x_109, x_111, x_215);
lean_inc_ref(x_68);
lean_inc_ref(x_28);
lean_inc(x_23);
x_217 = l_Lean_Syntax_node4(x_23, x_57, x_204, x_28, x_68, x_216);
lean_inc_ref(x_56);
lean_inc(x_23);
x_218 = l_Lean_Syntax_node2(x_23, x_55, x_56, x_217);
lean_inc(x_23);
x_219 = l_Lean_Syntax_node1(x_23, x_26, x_218);
lean_inc(x_23);
x_220 = l_Lean_Syntax_node2(x_23, x_39, x_203, x_219);
lean_inc(x_23);
x_221 = l_Lean_Syntax_node8(x_23, x_69, x_71, x_77, x_38, x_89, x_91, x_196, x_198, x_220);
lean_inc_ref(x_28);
lean_inc(x_23);
x_222 = l_Lean_Syntax_node4(x_23, x_57, x_66, x_28, x_68, x_221);
lean_inc(x_23);
x_223 = l_Lean_Syntax_node2(x_23, x_55, x_56, x_222);
x_224 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22));
lean_inc_ref_n(x_28, 2);
lean_inc(x_23);
x_225 = l_Lean_Syntax_node2(x_23, x_224, x_28, x_28);
lean_inc_ref(x_28);
lean_inc(x_23);
x_226 = l_Lean_Syntax_node4(x_23, x_51, x_53, x_223, x_225, x_28);
lean_inc_ref(x_28);
lean_inc(x_23);
x_227 = l_Lean_Syntax_node6(x_23, x_31, x_33, x_34, x_28, x_28, x_50, x_226);
x_228 = l_Lean_Syntax_node2(x_23, x_24, x_29, x_227);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_228);
x_229 = x_11;
goto block_230;
}
else
{
lean_object* x_231; 
x_231 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_231, 0, x_228);
x_229 = x_231;
goto block_230;
}
block_230:
{
return x_229;
}
}
}
else
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; uint8_t x_242; 
lean_dec_ref(x_6);
lean_dec(x_1);
x_235 = lean_ctor_get(x_10, 0);
x_242 = !lean_is_exclusive(x_10);
if (x_242 == 0)
{
x_236 = x_10;
x_237 = x_242;
goto block_241;
}
else
{
lean_inc(x_235);
lean_dec(x_10);
x_236 = lean_box(0);
x_237 = x_242;
goto block_241;
}
block_241:
{
lean_object* x_238; 
if (x_237 == 0)
{
x_238 = x_236;
goto block_239;
}
else
{
lean_object* x_240; 
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_235);
x_238 = x_240;
goto block_239;
}
block_239:
{
return x_238;
}
}
}
}
else
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; uint8_t x_250; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_243 = lean_ctor_get(x_9, 0);
x_250 = !lean_is_exclusive(x_9);
if (x_250 == 0)
{
x_244 = x_9;
x_245 = x_250;
goto block_249;
}
else
{
lean_inc(x_243);
lean_dec(x_9);
x_244 = lean_box(0);
x_245 = x_250;
goto block_249;
}
block_249:
{
lean_object* x_246; 
if (x_245 == 0)
{
x_246 = x_244;
goto block_247;
}
else
{
lean_object* x_248; 
x_248 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_248, 0, x_243);
x_246 = x_248;
goto block_247;
}
block_247:
{
return x_246;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_getRef___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_54; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg(x_2, x_4);
x_9 = lean_ctor_get(x_8, 0);
x_54 = !lean_is_exclusive(x_8);
if (x_54 == 0)
{
x_10 = x_8;
x_11 = x_54;
goto block_53;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_52; 
x_12 = lean_st_ref_take(x_4);
x_13 = lean_ctor_get(x_12, 9);
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_19 = lean_ctor_get(x_12, 5);
x_20 = lean_ctor_get(x_12, 6);
x_21 = lean_ctor_get(x_12, 7);
x_22 = lean_ctor_get(x_12, 8);
x_23 = lean_ctor_get(x_12, 10);
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
x_24 = x_12;
x_25 = x_52;
goto block_51;
}
else
{
lean_inc(x_23);
lean_inc(x_13);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_24 = lean_box(0);
x_25 = x_52;
goto block_51;
}
block_51:
{
uint64_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_50; 
x_26 = lean_ctor_get_uint64(x_13, sizeof(void*)*1);
x_27 = lean_ctor_get(x_13, 0);
x_50 = !lean_is_exclusive(x_13);
if (x_50 == 0)
{
x_28 = x_13;
x_29 = x_50;
goto block_49;
}
else
{
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_box(0);
x_29 = x_50;
goto block_49;
}
block_49:
{
double x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___closed__0);
x_31 = 0;
x_32 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkSameCtorRhs___lam__1___closed__39));
x_33 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_float(x_33, sizeof(void*)*2, x_30);
lean_ctor_set_float(x_33, sizeof(void*)*2 + 8, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*2 + 16, x_31);
x_34 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds_spec__2___redArg___closed__1));
x_35 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_9);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_PersistentArray_push___redArg(x_27, x_36);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_37);
x_38 = x_28;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set_uint64(x_48, sizeof(void*)*1, x_26);
x_38 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_39; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 9, x_38);
x_39 = x_24;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_46, 0, x_14);
lean_ctor_set(x_46, 1, x_15);
lean_ctor_set(x_46, 2, x_16);
lean_ctor_set(x_46, 3, x_17);
lean_ctor_set(x_46, 4, x_18);
lean_ctor_set(x_46, 5, x_19);
lean_ctor_set(x_46, 6, x_20);
lean_ctor_set(x_46, 7, x_21);
lean_ctor_set(x_46, 8, x_22);
lean_ctor_set(x_46, 9, x_38);
lean_ctor_set(x_46, 10, x_23);
x_39 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_st_ref_set(x_4, x_39);
x_41 = lean_box(0);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_41);
x_42 = x_10;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
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
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_6, 0);
x_62 = !lean_is_exclusive(x_6);
if (x_62 == 0)
{
x_56 = x_6;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_6);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
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
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___lam__0___boxed), 8, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc_ref(x_2);
x_6 = l_Lean_Elab_Command_liftTermElabM___redArg(x_5, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__0));
x_9 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__0___redArg(x_8, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabCommand(x_7, x_2, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2_once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2);
lean_inc(x_7);
x_14 = l_Lean_MessageData_ofSyntax(x_7);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum_spec__1(x_8, x_15, x_2, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_16);
x_17 = l_Lean_Elab_Command_elabCommand(x_7, x_2, x_3);
return x_17;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_16;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_18 = lean_ctor_get(x_6, 0);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
x_19 = x_6;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_getRef___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_26; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 3);
x_12 = lean_ctor_get(x_3, 4);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_3, 6);
x_15 = lean_ctor_get(x_3, 8);
x_16 = lean_ctor_get(x_3, 9);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_3, 7);
lean_dec(x_27);
x_18 = x_3;
x_19 = x_26;
goto block_25;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
if (x_19 == 0)
{
lean_ctor_set(x_18, 7, x_20);
x_21 = x_18;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_9);
lean_ctor_set(x_24, 2, x_10);
lean_ctor_set(x_24, 3, x_11);
lean_ctor_set(x_24, 4, x_12);
lean_ctor_set(x_24, 5, x_13);
lean_ctor_set(x_24, 6, x_14);
lean_ctor_set(x_24, 7, x_20);
lean_ctor_set(x_24, 8, x_15);
lean_ctor_set(x_24, 9, x_16);
lean_ctor_set_uint8(x_24, sizeof(void*)*10, x_17);
x_21 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_22; 
x_22 = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0___redArg(x_2, x_21, x_4);
return x_22;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_28 = lean_ctor_get(x_6, 0);
x_35 = !lean_is_exclusive(x_6);
if (x_35 == 0)
{
x_29 = x_6;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_6);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_Name_isAnonymous(x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_6);
x_10 = l_Lean_Environment_setExporting(x_6, x_7);
lean_inc(x_2);
lean_inc_ref(x_10);
x_11 = l_Lean_Environment_contains(x_10, x_2, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_10);
lean_dec_ref(x_6);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__2);
x_14 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq_spec__0_spec__0_spec__1___redArg___closed__5);
x_15 = l_Lean_Options_empty;
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
lean_inc(x_2);
x_17 = l_Lean_MessageData_ofConstName(x_2, x_7);
x_18 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Environment_getModuleIdxFor_x3f(x_6, x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_20 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_MessageData_note(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_62; 
x_27 = lean_ctor_get(x_19, 0);
x_62 = !lean_is_exclusive(x_19);
if (x_62 == 0)
{
x_28 = x_19;
x_29 = x_62;
goto block_61;
}
else
{
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_box(0);
x_29 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_box(0);
x_31 = l_Lean_Environment_header(x_6);
lean_dec_ref(x_6);
x_32 = l_Lean_EnvironmentHeader_moduleNames(x_31);
x_33 = lean_array_get(x_30, x_32, x_27);
lean_dec(x_27);
lean_dec_ref(x_32);
x_34 = l_Lean_isPrivateName(x_2);
lean_dec(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_18);
x_37 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_MessageData_ofName(x_33);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_MessageData_note(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_44);
x_45 = x_28;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_18);
x_50 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_MessageData_ofName(x_33);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_MessageData_note(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_57);
x_58 = x_28;
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
}
}
}
else
{
lean_object* x_63; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_1);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_16; 
x_6 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(x_1, x_2, x_4);
x_7 = lean_ctor_get(x_6, 0);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
x_8 = x_6;
x_9 = x_16;
goto block_15;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_unknownIdentifierMessageTag;
x_11 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_11);
x_12 = x_8;
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(x_1, x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
x_7 = 0;
lean_inc(x_2);
x_8 = l_Lean_MessageData_ofConstName(x_2, x_7);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkMatchOld_mkAlts_spec__0___closed__1);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(x_1, x_11, x_2, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg(x_6, x_1, x_2, x_3);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 0);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
x_9 = x_5;
x_10 = x_15;
goto block_14;
}
else
{
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; 
if (x_10 == 0)
{
x_11 = x_9;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = 0;
lean_inc(x_1);
x_8 = l_Lean_Environment_find_x3f(x_6, x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_11 = x_8;
x_12 = x_17;
goto block_16;
}
else
{
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
lean_ctor_set_tag(x_11, 0);
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_10);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_3);
x_6 = 1;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_11 = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0(x_9, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_32; 
x_12 = lean_ctor_get(x_11, 0);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
x_13 = x_11;
x_14 = x_32;
goto block_31;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_15; uint8_t x_16; 
if (lean_obj_tag(x_12) == 6)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_12);
x_20 = lean_ctor_get(x_19, 4);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_20);
x_23 = lean_box(x_22);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_23);
x_24 = x_13;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
x_15 = x_24;
x_16 = x_22;
goto block_18;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
x_27 = lean_box(x_1);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_27);
x_28 = x_13;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
x_15 = x_28;
x_16 = x_1;
goto block_18;
}
}
block_18:
{
if (x_16 == 0)
{
lean_dec(x_10);
lean_dec_ref(x_3);
return x_15;
}
else
{
lean_dec_ref(x_15);
x_2 = x_10;
goto _start;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_10);
lean_dec_ref(x_3);
x_33 = lean_ctor_get(x_11, 0);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
x_34 = x_11;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_11);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__1(x_6, x_2, x_3, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
lean_inc_ref(x_2);
x_5 = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_61; 
x_6 = lean_ctor_get(x_5, 0);
x_61 = !lean_is_exclusive(x_5);
if (x_61 == 0)
{
x_7 = x_5;
x_8 = x_61;
goto block_60;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_61;
goto block_60;
}
block_60:
{
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_6);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 4);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_9, sizeof(void*)*6);
x_15 = lean_ctor_get_uint8(x_9, sizeof(void*)*6 + 1);
x_16 = lean_ctor_get(x_10, 2);
x_17 = l_Lean_Expr_isProp(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_InductiveVal_numTypeFormers(x_9);
lean_dec_ref(x_9);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_2);
x_21 = lean_box(x_20);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_21);
x_22 = x_7;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_12, x_25);
lean_dec(x_12);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_2);
x_27 = lean_box(x_26);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_27);
x_28 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_eq(x_11, x_25);
lean_dec(x_11);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_13);
lean_dec_ref(x_2);
x_32 = lean_box(x_31);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_32);
x_33 = x_7;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
else
{
uint8_t x_36; 
x_36 = l_List_isEmpty___redArg(x_13);
if (x_36 == 0)
{
if (x_14 == 0)
{
if (x_15 == 0)
{
lean_object* x_37; 
lean_del_object(x_7);
x_37 = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__1(x_15, x_13, x_2, x_3);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_13);
lean_dec_ref(x_2);
x_38 = lean_box(x_14);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_38);
x_39 = x_7;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_13);
lean_dec_ref(x_2);
x_42 = lean_box(x_36);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_42);
x_43 = x_7;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_13);
lean_dec_ref(x_2);
x_46 = lean_box(x_17);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_46);
x_47 = x_7;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_46);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
}
else
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_50 = 0;
x_51 = lean_box(x_50);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_51);
x_52 = x_7;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_51);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
else
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_6);
lean_dec_ref(x_2);
x_55 = 0;
x_56 = lean_box(x_55);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_56);
x_57 = x_7;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec_ref(x_2);
x_62 = lean_ctor_get(x_5, 0);
x_69 = !lean_is_exclusive(x_5);
if (x_69 == 0)
{
x_63 = x_5;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_5);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
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
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
lean_inc_ref(x_2);
lean_inc(x_1);
x_5 = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEq(x_1, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqEnum(x_1, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
x_10 = x_9;
x_11 = x_16;
goto block_15;
}
else
{
lean_dec(x_9);
x_10 = lean_box(0);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_6);
x_12 = x_10;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_6);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec(x_6);
x_18 = lean_ctor_get(x_9, 0);
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
x_19 = x_9;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance___lam__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance___lam__0___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(x_1, x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler_spec__0(lean_object* x_1, size_t x_2, size_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
if (x_4 == 0)
{
x_8 = x_4;
goto block_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_14);
x_15 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstance(x_14, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
x_8 = x_17;
goto block_12;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
return x_15;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec_ref(x_5);
x_18 = lean_box(x_4);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler_spec__0(x_1, x_8, x_9, x_10, x_5, x_6);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = 1;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_9 = lean_box(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
if (x_8 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_12 = lean_box(x_5);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_7);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler_spec__0(x_1, x_14, x_15, x_5, x_2, x_3);
return x_16;
}
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_7);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler_spec__0(x_1, x_17, x_18, x_5, x_2, x_3);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2689463041u);
x_2 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_);
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1));
x_3 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_));
x_4 = l_Lean_Elab_registerDerivingHandler(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_4);
x_5 = ((lean_object*)(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__0));
x_6 = 0;
x_7 = lean_obj_once(&l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_);
x_8 = l_Lean_registerTraceClass(x_5, x_6, x_7);
return x_8;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Inductive(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatTable(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_OfFn(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_DecEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Options(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Inductive(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatTable(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SameCtorUtils(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_OfFn(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_1775403645____hygCtx___hyg_4_()
;
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_deriving_decEq_linear__construction__threshold = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_deriving_decEq_linear__construction__threshold);
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_DecEq_0__Lean_Elab_Deriving_DecEq_initFn_00___x40_Lean_Elab_Deriving_DecEq_2689463041____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_DecEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Options(uint8_t builtin);
lean_object* initialize_Lean_Meta_Inductive(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatTable(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin);
lean_object* initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* initialize_Init_Data_Array_OfFn(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_DecEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Options(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Inductive(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatTable(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SameCtorUtils(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_OfFn(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_DecEq(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_DecEq(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_DecEq(builtin);
}
#ifdef __cplusplus
}
#endif
