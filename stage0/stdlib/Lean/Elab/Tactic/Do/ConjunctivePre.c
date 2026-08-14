// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ConjunctivePre
// Imports: public import Lean.Meta.Basic public import Std.Internal.Do.Triple.Basic
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Expr_eta(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__3_value),LEAN_SCALAR_PTR_LITERAL(190, 57, 218, 157, 42, 52, 8, 129)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__5_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__3_value),LEAN_SCALAR_PTR_LITERAL(202, 119, 227, 254, 29, 206, 25, 24)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__6_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wp"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__5_value),LEAN_SCALAR_PTR_LITERAL(8, 127, 121, 224, 88, 246, 48, 72)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(114, 80, 184, 106, 225, 60, 114, 167)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__5_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__5_value),LEAN_SCALAR_PTR_LITERAL(124, 118, 39, 144, 78, 10, 170, 168)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 255, 127, 189, 81, 246, 28, 251)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__2_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__1_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__2_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "EPost"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Cons"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "head"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 220, 195, 28, 231, 198, 56, 30)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__1_value),LEAN_SCALAR_PTR_LITERAL(141, 182, 16, 6, 247, 146, 42, 70)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__3_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__2_value),LEAN_SCALAR_PTR_LITERAL(65, 41, 155, 61, 92, 197, 165, 144)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames___closed__5_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 91, 36, 233, 42, 127, 239, 103)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__1_value),LEAN_SCALAR_PTR_LITERAL(121, 138, 171, 54, 136, 21, 182, 106)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 123, 42, 193, 46, 33, 120, 28)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__4_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__4_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames___closed__5_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "himp"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(173, 29, 48, 122, 5, 158, 45, 140)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iInf"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 96, 105, 10, 16, 194, 128, 157)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__6_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f_spec__0_spec__0(lean_object* v_a_63_, lean_object* v_as_64_, size_t v_i_65_, size_t v_stop_66_){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = lean_usize_dec_eq(v_i_65_, v_stop_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = lean_array_uget_borrowed(v_as_64_, v_i_65_);
v___x_69_ = lean_name_eq(v_a_63_, v___x_68_);
if (v___x_69_ == 0)
{
size_t v___x_70_; size_t v___x_71_; 
v___x_70_ = ((size_t)1ULL);
v___x_71_ = lean_usize_add(v_i_65_, v___x_70_);
v_i_65_ = v___x_71_;
goto _start;
}
else
{
return v___x_69_;
}
}
else
{
uint8_t v___x_73_; 
v___x_73_ = 0;
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f_spec__0_spec__0___boxed(lean_object* v_a_74_, lean_object* v_as_75_, lean_object* v_i_76_, lean_object* v_stop_77_){
_start:
{
size_t v_i_boxed_78_; size_t v_stop_boxed_79_; uint8_t v_res_80_; lean_object* v_r_81_; 
v_i_boxed_78_ = lean_unbox_usize(v_i_76_);
lean_dec(v_i_76_);
v_stop_boxed_79_ = lean_unbox_usize(v_stop_77_);
lean_dec(v_stop_77_);
v_res_80_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f_spec__0_spec__0(v_a_74_, v_as_75_, v_i_boxed_78_, v_stop_boxed_79_);
lean_dec_ref(v_as_75_);
lean_dec(v_a_74_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f_spec__0(lean_object* v_as_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_array_get_size(v_as_82_);
v___x_86_ = lean_nat_dec_lt(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
return v___x_86_;
}
else
{
if (v___x_86_ == 0)
{
return v___x_86_;
}
else
{
size_t v___x_87_; size_t v___x_88_; uint8_t v___x_89_; 
v___x_87_ = ((size_t)0ULL);
v___x_88_ = lean_usize_of_nat(v___x_85_);
v___x_89_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f_spec__0_spec__0(v_a_83_, v_as_82_, v___x_87_, v___x_88_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f_spec__0___boxed(lean_object* v_as_90_, lean_object* v_a_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Array_contains___at___00Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f_spec__0(v_as_90_, v_a_91_);
lean_dec(v_a_91_);
lean_dec_ref(v_as_90_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f(lean_object* v_names_94_, lean_object* v_e_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Expr_getAppFn(v_e_95_);
if (lean_obj_tag(v___x_96_) == 4)
{
lean_object* v_declName_97_; uint8_t v___x_98_; 
v_declName_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_declName_97_);
lean_dec_ref_known(v___x_96_, 2);
v___x_98_ = l_Array_contains___at___00Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f_spec__0(v_names_94_, v_declName_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; 
lean_dec(v_declName_97_);
v___x_99_ = lean_box(0);
return v___x_99_;
}
else
{
lean_object* v___x_100_; 
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v_declName_97_);
return v___x_100_;
}
}
else
{
lean_object* v___x_101_; 
lean_dec_ref(v___x_96_);
v___x_101_ = lean_box(0);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f___boxed(lean_object* v_names_102_, lean_object* v_e_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f(v_names_102_, v_e_103_);
lean_dec_ref(v_e_103_);
lean_dec_ref(v_names_102_);
return v_res_104_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0(void){
_start:
{
lean_object* v___x_105_; lean_object* v_dummy_106_; 
v___x_105_ = lean_box(0);
v_dummy_106_ = l_Lean_Expr_sort___override(v___x_105_);
return v_dummy_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f(lean_object* v_concl_116_){
_start:
{
lean_object* v___x_150_; uint8_t v___x_151_; 
lean_inc_ref(v_concl_116_);
v___x_150_ = l_Lean_Expr_cleanupAnnotations(v_concl_116_);
v___x_151_ = l_Lean_Expr_isApp(v___x_150_);
if (v___x_151_ == 0)
{
lean_dec_ref(v___x_150_);
goto v___jp_117_;
}
else
{
lean_object* v_arg_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_arg_152_ = lean_ctor_get(v___x_150_, 1);
lean_inc_ref(v_arg_152_);
v___x_153_ = l_Lean_Expr_appFnCleanup___redArg(v___x_150_);
v___x_154_ = l_Lean_Expr_isApp(v___x_153_);
if (v___x_154_ == 0)
{
lean_dec_ref(v___x_153_);
lean_dec_ref(v_arg_152_);
goto v___jp_117_;
}
else
{
lean_object* v_arg_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v_arg_155_ = lean_ctor_get(v___x_153_, 1);
lean_inc_ref(v_arg_155_);
v___x_156_ = l_Lean_Expr_appFnCleanup___redArg(v___x_153_);
v___x_157_ = l_Lean_Expr_isApp(v___x_156_);
if (v___x_157_ == 0)
{
lean_dec_ref(v___x_156_);
lean_dec_ref(v_arg_155_);
lean_dec_ref(v_arg_152_);
goto v___jp_117_;
}
else
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = l_Lean_Expr_appFnCleanup___redArg(v___x_156_);
v___x_159_ = l_Lean_Expr_isApp(v___x_158_);
if (v___x_159_ == 0)
{
lean_dec_ref(v___x_158_);
lean_dec_ref(v_arg_155_);
lean_dec_ref(v_arg_152_);
goto v___jp_117_;
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_160_ = l_Lean_Expr_appFnCleanup___redArg(v___x_158_);
v___x_161_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5));
v___x_162_ = l_Lean_Expr_isConstOf(v___x_160_, v___x_161_);
lean_dec_ref(v___x_160_);
if (v___x_162_ == 0)
{
lean_dec_ref(v_arg_155_);
lean_dec_ref(v_arg_152_);
goto v___jp_117_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec_ref(v_concl_116_);
v___x_163_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames));
v___x_164_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f(v___x_163_, v_arg_152_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v___x_165_; 
lean_dec_ref(v_arg_155_);
lean_dec_ref(v_arg_152_);
v___x_165_ = lean_box(0);
return v___x_165_;
}
else
{
lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_192_; 
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; 
v_unused_193_ = lean_ctor_get(v___x_164_, 0);
lean_dec(v_unused_193_);
v___x_167_ = v___x_164_;
v_isShared_168_ = v_isSharedCheck_192_;
goto v_resetjp_166_;
}
else
{
lean_dec(v___x_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_192_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
if (v___x_162_ == 0)
{
lean_object* v___x_169_; 
lean_del_object(v___x_167_);
lean_dec_ref(v_arg_155_);
lean_dec_ref(v_arg_152_);
v___x_169_ = lean_box(0);
return v___x_169_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_170_ = l_Lean_Expr_getAppNumArgs(v_arg_152_);
v___x_171_ = lean_unsigned_to_nat(10u);
v___x_172_ = lean_nat_dec_eq(v___x_170_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
lean_dec(v___x_170_);
lean_del_object(v___x_167_);
lean_dec_ref(v_arg_155_);
lean_dec_ref(v_arg_152_);
v___x_173_ = lean_box(0);
return v___x_173_;
}
else
{
lean_object* v_dummy_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v_args_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v_dummy_174_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0);
lean_inc(v___x_170_);
v___x_175_ = lean_mk_array(v___x_170_, v_dummy_174_);
v___x_176_ = lean_unsigned_to_nat(1u);
v___x_177_ = lean_nat_sub(v___x_170_, v___x_176_);
lean_dec(v___x_170_);
v_args_178_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_arg_152_, v___x_175_, v___x_177_);
v___x_179_ = l_Lean_instInhabitedExpr;
v___x_180_ = lean_unsigned_to_nat(7u);
v___x_181_ = lean_array_get(v___x_179_, v_args_178_, v___x_180_);
v___x_182_ = lean_unsigned_to_nat(8u);
v___x_183_ = lean_array_get(v___x_179_, v_args_178_, v___x_182_);
v___x_184_ = lean_unsigned_to_nat(9u);
v___x_185_ = lean_array_get(v___x_179_, v_args_178_, v___x_184_);
lean_dec_ref(v_args_178_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_183_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_181_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v_arg_155_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_188_);
v___x_190_ = v___x_167_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
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
v___jp_117_:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_SpecAttr_tripleNames));
v___x_119_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f(v___x_118_, v_concl_116_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v___x_120_; 
lean_dec_ref(v_concl_116_);
v___x_120_ = lean_box(0);
return v___x_120_;
}
else
{
lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_148_; 
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; 
v_unused_149_ = lean_ctor_get(v___x_119_, 0);
lean_dec(v_unused_149_);
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_148_;
goto v_resetjp_121_;
}
else
{
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_148_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_124_ = l_Lean_Expr_getAppNumArgs(v_concl_116_);
v___x_125_ = lean_unsigned_to_nat(11u);
v___x_126_ = lean_nat_dec_eq(v___x_124_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
lean_dec(v___x_124_);
lean_del_object(v___x_122_);
lean_dec_ref(v_concl_116_);
v___x_127_ = lean_box(0);
return v___x_127_;
}
else
{
lean_object* v_dummy_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v_args_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v_dummy_128_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0);
lean_inc(v___x_124_);
v___x_129_ = lean_mk_array(v___x_124_, v_dummy_128_);
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_nat_sub(v___x_124_, v___x_130_);
lean_dec(v___x_124_);
v_args_132_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_concl_116_, v___x_129_, v___x_131_);
v___x_133_ = l_Lean_instInhabitedExpr;
v___x_134_ = lean_unsigned_to_nat(8u);
v___x_135_ = lean_array_get(v___x_133_, v_args_132_, v___x_134_);
v___x_136_ = lean_unsigned_to_nat(6u);
v___x_137_ = lean_array_get(v___x_133_, v_args_132_, v___x_136_);
v___x_138_ = lean_unsigned_to_nat(9u);
v___x_139_ = lean_array_get(v___x_133_, v_args_132_, v___x_138_);
v___x_140_ = lean_unsigned_to_nat(10u);
v___x_141_ = lean_array_get(v___x_133_, v_args_132_, v___x_140_);
lean_dec_ref(v_args_132_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_139_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_137_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_135_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v___x_144_);
v___x_146_ = v___x_122_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0(lean_object* v_a_194_, lean_object* v_as_195_, size_t v_i_196_, size_t v_stop_197_){
_start:
{
uint8_t v___x_198_; 
v___x_198_ = lean_usize_dec_eq(v_i_196_, v_stop_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_array_uget_borrowed(v_as_195_, v_i_196_);
v___x_200_ = l_Lean_instBEqMVarId_beq(v_a_194_, v___x_199_);
if (v___x_200_ == 0)
{
size_t v___x_201_; size_t v___x_202_; 
v___x_201_ = ((size_t)1ULL);
v___x_202_ = lean_usize_add(v_i_196_, v___x_201_);
v_i_196_ = v___x_202_;
goto _start;
}
else
{
return v___x_200_;
}
}
else
{
uint8_t v___x_204_; 
v___x_204_ = 0;
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0___boxed(lean_object* v_a_205_, lean_object* v_as_206_, lean_object* v_i_207_, lean_object* v_stop_208_){
_start:
{
size_t v_i_boxed_209_; size_t v_stop_boxed_210_; uint8_t v_res_211_; lean_object* v_r_212_; 
v_i_boxed_209_ = lean_unbox_usize(v_i_207_);
lean_dec(v_i_207_);
v_stop_boxed_210_ = lean_unbox_usize(v_stop_208_);
lean_dec(v_stop_208_);
v_res_211_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0(v_a_205_, v_as_206_, v_i_boxed_209_, v_stop_boxed_210_);
lean_dec_ref(v_as_206_);
lean_dec(v_a_205_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(lean_object* v_as_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = lean_array_get_size(v_as_213_);
v___x_217_ = lean_nat_dec_lt(v___x_215_, v___x_216_);
if (v___x_217_ == 0)
{
return v___x_217_;
}
else
{
if (v___x_217_ == 0)
{
return v___x_217_;
}
else
{
size_t v___x_218_; size_t v___x_219_; uint8_t v___x_220_; 
v___x_218_ = ((size_t)0ULL);
v___x_219_ = lean_usize_of_nat(v___x_216_);
v___x_220_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0(v_a_214_, v_as_213_, v___x_218_, v___x_219_);
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0___boxed(lean_object* v_as_221_, lean_object* v_a_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(v_as_221_, v_a_222_);
lean_dec(v_a_222_);
lean_dec_ref(v_as_221_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0(lean_object* v_mvarIds_225_, lean_object* v_s_226_){
_start:
{
if (lean_obj_tag(v_s_226_) == 2)
{
lean_object* v_mvarId_227_; uint8_t v___x_228_; 
v_mvarId_227_ = lean_ctor_get(v_s_226_, 0);
v___x_228_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(v_mvarIds_225_, v_mvarId_227_);
return v___x_228_;
}
else
{
uint8_t v___x_229_; 
v___x_229_ = 0;
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0___boxed(lean_object* v_mvarIds_230_, lean_object* v_s_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0(v_mvarIds_230_, v_s_231_);
lean_dec_ref(v_s_231_);
lean_dec_ref(v_mvarIds_230_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(lean_object* v_mvarIds_234_, lean_object* v_e_235_){
_start:
{
lean_object* v___f_236_; lean_object* v___x_237_; 
v___f_236_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0___boxed), 2, 1);
lean_closure_set(v___f_236_, 0, v_mvarIds_234_);
v___x_237_ = lean_find_expr(v___f_236_, v_e_235_);
lean_dec_ref(v___f_236_);
if (lean_obj_tag(v___x_237_) == 0)
{
uint8_t v___x_238_; 
v___x_238_ = 0;
return v___x_238_;
}
else
{
uint8_t v___x_239_; 
lean_dec_ref_known(v___x_237_, 1);
v___x_239_ = 1;
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___boxed(lean_object* v_mvarIds_240_, lean_object* v_e_241_){
_start:
{
uint8_t v_res_242_; lean_object* v_r_243_; 
v_res_242_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_mvarIds_240_, v_e_241_);
lean_dec_ref(v_e_241_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1(lean_object* v_args_244_, lean_object* v_qs_245_, uint8_t v___x_246_, uint8_t v___x_247_, lean_object* v_x_248_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
uint8_t v___x_249_; 
lean_dec_ref(v_qs_245_);
v___x_249_ = 1;
return v___x_249_;
}
else
{
lean_object* v_head_250_; lean_object* v_tail_251_; uint8_t v___y_253_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_head_250_ = lean_ctor_get(v_x_248_, 0);
v_tail_251_ = lean_ctor_get(v_x_248_, 1);
v___x_255_ = lean_unsigned_to_nat(2u);
v___x_256_ = lean_nat_dec_eq(v_head_250_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_257_ = l_Lean_instInhabitedExpr;
v___x_258_ = lean_array_get_borrowed(v___x_257_, v_args_244_, v_head_250_);
lean_inc_ref(v_qs_245_);
v___x_259_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_245_, v___x_258_);
if (v___x_259_ == 0)
{
v___y_253_ = v___x_246_;
goto v___jp_252_;
}
else
{
v___y_253_ = v___x_256_;
goto v___jp_252_;
}
}
else
{
v___y_253_ = v___x_247_;
goto v___jp_252_;
}
v___jp_252_:
{
if (v___y_253_ == 0)
{
lean_dec_ref(v_qs_245_);
return v___y_253_;
}
else
{
v_x_248_ = v_tail_251_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1___boxed(lean_object* v_args_260_, lean_object* v_qs_261_, lean_object* v___x_262_, lean_object* v___x_263_, lean_object* v_x_264_){
_start:
{
uint8_t v___x_3815__boxed_265_; uint8_t v___x_3816__boxed_266_; uint8_t v_res_267_; lean_object* v_r_268_; 
v___x_3815__boxed_265_ = lean_unbox(v___x_262_);
v___x_3816__boxed_266_ = lean_unbox(v___x_263_);
v_res_267_ = l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1(v_args_260_, v_qs_261_, v___x_3815__boxed_265_, v___x_3816__boxed_266_, v_x_264_);
lean_dec(v_x_264_);
lean_dec_ref(v_args_260_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0(lean_object* v_qs_269_, uint8_t v___x_270_, lean_object* v_as_271_, size_t v_i_272_, size_t v_stop_273_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = lean_usize_dec_eq(v_i_272_, v_stop_273_);
if (v___x_278_ == 0)
{
uint8_t v___x_279_; uint8_t v___y_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_279_ = 1;
v___x_282_ = lean_array_uget_borrowed(v_as_271_, v_i_272_);
lean_inc_ref(v_qs_269_);
v___x_283_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_269_, v___x_282_);
if (v___x_283_ == 0)
{
if (v___x_270_ == 0)
{
goto v___jp_274_;
}
else
{
v___y_281_ = v___x_283_;
goto v___jp_280_;
}
}
else
{
v___y_281_ = v___x_270_;
goto v___jp_280_;
}
v___jp_280_:
{
if (v___y_281_ == 0)
{
goto v___jp_274_;
}
else
{
lean_dec_ref(v_qs_269_);
return v___x_279_;
}
}
}
else
{
uint8_t v___x_284_; 
lean_dec_ref(v_qs_269_);
v___x_284_ = 0;
return v___x_284_;
}
v___jp_274_:
{
size_t v___x_275_; size_t v___x_276_; 
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_add(v_i_272_, v___x_275_);
v_i_272_ = v___x_276_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0___boxed(lean_object* v_qs_285_, lean_object* v___x_286_, lean_object* v_as_287_, lean_object* v_i_288_, lean_object* v_stop_289_){
_start:
{
uint8_t v___x_3846__boxed_290_; size_t v_i_boxed_291_; size_t v_stop_boxed_292_; uint8_t v_res_293_; lean_object* v_r_294_; 
v___x_3846__boxed_290_ = lean_unbox(v___x_286_);
v_i_boxed_291_ = lean_unbox_usize(v_i_288_);
lean_dec(v_i_288_);
v_stop_boxed_292_ = lean_unbox_usize(v_stop_289_);
lean_dec(v_stop_289_);
v_res_293_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0(v_qs_285_, v___x_3846__boxed_290_, v_as_287_, v_i_boxed_291_, v_stop_boxed_292_);
lean_dec_ref(v_as_287_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(lean_object* v_qs_313_, lean_object* v_e_314_){
_start:
{
lean_object* v_a_316_; lean_object* v_b_317_; uint8_t v___x_343_; 
lean_inc_ref(v_qs_313_);
v___x_343_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_313_, v_e_314_);
if (v___x_343_ == 0)
{
uint8_t v___x_344_; 
lean_dec_ref(v_e_314_);
lean_dec_ref(v_qs_313_);
v___x_344_ = 1;
return v___x_344_;
}
else
{
uint8_t v___x_345_; 
v___x_345_ = 0;
switch(lean_obj_tag(v_e_314_))
{
case 10:
{
lean_object* v_expr_346_; 
v_expr_346_ = lean_ctor_get(v_e_314_, 1);
lean_inc_ref(v_expr_346_);
lean_dec_ref_known(v_e_314_, 2);
v_e_314_ = v_expr_346_;
goto _start;
}
case 6:
{
lean_object* v_binderType_348_; lean_object* v_body_349_; uint8_t v___x_350_; 
v_binderType_348_ = lean_ctor_get(v_e_314_, 1);
lean_inc_ref(v_binderType_348_);
v_body_349_ = lean_ctor_get(v_e_314_, 2);
lean_inc_ref(v_body_349_);
lean_dec_ref_known(v_e_314_, 3);
lean_inc_ref(v_qs_313_);
v___x_350_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_313_, v_binderType_348_);
lean_dec_ref(v_binderType_348_);
if (v___x_350_ == 0)
{
v_e_314_ = v_body_349_;
goto _start;
}
else
{
lean_dec_ref(v_body_349_);
lean_dec_ref(v_qs_313_);
return v___x_345_;
}
}
default: 
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Expr_getAppFn(v_e_314_);
if (lean_obj_tag(v___x_352_) == 2)
{
lean_object* v_mvarId_353_; uint8_t v___x_354_; 
v_mvarId_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_mvarId_353_);
lean_dec_ref_known(v___x_352_, 1);
v___x_354_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(v_qs_313_, v_mvarId_353_);
lean_dec(v_mvarId_353_);
if (v___x_354_ == 0)
{
lean_dec_ref(v_e_314_);
lean_dec_ref(v_qs_313_);
return v___x_354_;
}
else
{
lean_object* v_dummy_355_; lean_object* v_nargs_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_dummy_355_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0);
v_nargs_356_ = l_Lean_Expr_getAppNumArgs(v_e_314_);
lean_inc(v_nargs_356_);
v___x_357_ = lean_mk_array(v_nargs_356_, v_dummy_355_);
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_nat_sub(v_nargs_356_, v___x_358_);
lean_dec(v_nargs_356_);
v___x_360_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_314_, v___x_357_, v___x_359_);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_array_get_size(v___x_360_);
v___x_363_ = lean_nat_dec_lt(v___x_361_, v___x_362_);
if (v___x_363_ == 0)
{
lean_dec_ref(v___x_360_);
lean_dec_ref(v_qs_313_);
return v___x_354_;
}
else
{
if (v___x_363_ == 0)
{
lean_dec_ref(v___x_360_);
lean_dec_ref(v_qs_313_);
return v___x_354_;
}
else
{
size_t v___x_364_; size_t v___x_365_; uint8_t v___x_366_; 
v___x_364_ = ((size_t)0ULL);
v___x_365_ = lean_usize_of_nat(v___x_362_);
v___x_366_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0(v_qs_313_, v___x_354_, v___x_360_, v___x_364_, v___x_365_);
lean_dec_ref(v___x_360_);
if (v___x_366_ == 0)
{
return v___x_354_;
}
else
{
return v___x_345_;
}
}
}
}
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; 
lean_dec_ref(v___x_352_);
v___x_367_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_SpecAttr_epostConsHeadNames));
v___x_368_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f(v___x_367_, v_e_314_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_SpecAttr_wpNames));
v___x_370_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_appName_x3f(v___x_369_, v_e_314_);
if (lean_obj_tag(v___x_370_) == 0)
{
goto v___jp_320_;
}
else
{
lean_dec_ref_known(v___x_370_, 1);
if (v___x_343_ == 0)
{
goto v___jp_320_;
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_371_ = l_Lean_Expr_getAppNumArgs(v_e_314_);
v___x_372_ = lean_unsigned_to_nat(10u);
v___x_373_ = lean_nat_dec_eq(v___x_371_, v___x_372_);
if (v___x_373_ == 0)
{
lean_dec(v___x_371_);
goto v___jp_320_;
}
else
{
lean_object* v_dummy_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v_args_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_dummy_374_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0);
lean_inc(v___x_371_);
v___x_375_ = lean_mk_array(v___x_371_, v_dummy_374_);
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_nat_sub(v___x_371_, v___x_376_);
lean_dec(v___x_371_);
v_args_378_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_314_, v___x_375_, v___x_377_);
v___x_379_ = l_Lean_instInhabitedExpr;
v___x_380_ = lean_unsigned_to_nat(7u);
v___x_381_ = lean_array_get(v___x_379_, v_args_378_, v___x_380_);
lean_inc_ref(v_qs_313_);
v___x_382_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_313_, v___x_381_);
lean_dec(v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_383_ = lean_unsigned_to_nat(8u);
v___x_384_ = lean_array_get(v___x_379_, v_args_378_, v___x_383_);
lean_inc_ref(v_qs_313_);
v___x_385_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_qs_313_, v___x_384_);
if (v___x_385_ == 0)
{
lean_dec_ref(v_args_378_);
lean_dec_ref(v_qs_313_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_unsigned_to_nat(9u);
v___x_387_ = lean_array_get(v___x_379_, v_args_378_, v___x_386_);
lean_dec_ref(v_args_378_);
v_e_314_ = v___x_387_;
goto _start;
}
}
else
{
lean_dec_ref(v_args_378_);
lean_dec_ref(v_qs_313_);
return v___x_345_;
}
}
}
}
}
else
{
lean_object* v_dummy_389_; lean_object* v_nargs_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v_args_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
lean_dec_ref_known(v___x_368_, 1);
v_dummy_389_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0);
v_nargs_390_ = l_Lean_Expr_getAppNumArgs(v_e_314_);
lean_inc(v_nargs_390_);
v___x_391_ = lean_mk_array(v_nargs_390_, v_dummy_389_);
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = lean_nat_sub(v_nargs_390_, v___x_392_);
lean_dec(v_nargs_390_);
v_args_394_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_314_, v___x_391_, v___x_393_);
v___x_395_ = lean_unsigned_to_nat(2u);
v___x_396_ = lean_array_get_size(v_args_394_);
v___x_397_ = lean_nat_dec_lt(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
lean_dec_ref(v_args_394_);
lean_dec_ref(v_qs_313_);
return v___x_345_;
}
else
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = lean_array_fget(v_args_394_, v___x_395_);
lean_inc_ref(v_qs_313_);
v___x_399_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_qs_313_, v___x_398_);
if (v___x_399_ == 0)
{
lean_dec_ref(v_args_394_);
lean_dec_ref(v_qs_313_);
return v___x_399_;
}
else
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = l_List_range(v___x_396_);
v___x_401_ = l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1(v_args_394_, v_qs_313_, v___x_399_, v___x_343_, v___x_400_);
lean_dec(v___x_400_);
lean_dec_ref(v_args_394_);
return v___x_401_;
}
}
}
}
}
}
}
v___jp_315_:
{
uint8_t v___x_318_; 
lean_inc_ref(v_qs_313_);
v___x_318_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_qs_313_, v_a_316_);
if (v___x_318_ == 0)
{
lean_dec_ref(v_b_317_);
lean_dec_ref(v_qs_313_);
return v___x_318_;
}
else
{
v_e_314_ = v_b_317_;
goto _start;
}
}
v___jp_320_:
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = l_Lean_Expr_cleanupAnnotations(v_e_314_);
v___x_322_ = l_Lean_Expr_isApp(v___x_321_);
if (v___x_322_ == 0)
{
lean_dec_ref(v___x_321_);
lean_dec_ref(v_qs_313_);
return v___x_322_;
}
else
{
lean_object* v_arg_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_arg_323_ = lean_ctor_get(v___x_321_, 1);
lean_inc_ref(v_arg_323_);
v___x_324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_321_);
v___x_325_ = l_Lean_Expr_isApp(v___x_324_);
if (v___x_325_ == 0)
{
lean_dec_ref(v___x_324_);
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_qs_313_);
return v___x_325_;
}
else
{
lean_object* v_arg_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_arg_326_ = lean_ctor_get(v___x_324_, 1);
lean_inc_ref(v_arg_326_);
v___x_327_ = l_Lean_Expr_appFnCleanup___redArg(v___x_324_);
v___x_328_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__1));
v___x_329_ = l_Lean_Expr_isConstOf(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
uint8_t v___x_330_; 
v___x_330_ = l_Lean_Expr_isApp(v___x_327_);
if (v___x_330_ == 0)
{
lean_dec_ref(v___x_327_);
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_qs_313_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_327_);
v___x_332_ = l_Lean_Expr_isApp(v___x_331_);
if (v___x_332_ == 0)
{
lean_dec_ref(v___x_331_);
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_qs_313_);
return v___x_332_;
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_333_ = l_Lean_Expr_appFnCleanup___redArg(v___x_331_);
v___x_334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3));
v___x_335_ = l_Lean_Expr_isConstOf(v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5));
v___x_337_ = l_Lean_Expr_isConstOf(v___x_333_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7));
v___x_339_ = l_Lean_Expr_isConstOf(v___x_333_, v___x_338_);
lean_dec_ref(v___x_333_);
if (v___x_339_ == 0)
{
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_qs_313_);
return v___x_339_;
}
else
{
v_a_316_ = v_arg_326_;
v_b_317_ = v_arg_323_;
goto v___jp_315_;
}
}
else
{
lean_dec_ref(v___x_333_);
lean_dec_ref(v_arg_326_);
v_e_314_ = v_arg_323_;
goto _start;
}
}
else
{
uint8_t v___x_341_; 
lean_dec_ref(v___x_333_);
lean_inc_ref(v_qs_313_);
v___x_341_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_313_, v_arg_326_);
lean_dec_ref(v_arg_326_);
if (v___x_341_ == 0)
{
v_e_314_ = v_arg_323_;
goto _start;
}
else
{
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_qs_313_);
return v___x_329_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_327_);
v_a_316_ = v_arg_326_;
v_b_317_ = v_arg_323_;
goto v___jp_315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___boxed(lean_object* v_qs_402_, lean_object* v_e_403_){
_start:
{
uint8_t v_res_404_; lean_object* v_r_405_; 
v_res_404_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_qs_402_, v_e_403_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1(lean_object* v_qs_409_, uint8_t v___x_410_, lean_object* v_as_411_, size_t v_sz_412_, size_t v_i_413_, lean_object* v_b_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
uint8_t v___x_420_; 
v___x_420_ = lean_usize_dec_lt(v_i_413_, v_sz_412_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_dec_ref(v_qs_409_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v_b_414_);
return v___x_421_;
}
else
{
lean_object* v_a_422_; lean_object* v___x_423_; 
lean_dec_ref(v_b_414_);
v_a_422_ = lean_array_uget_borrowed(v_as_411_, v_i_413_);
lean_inc(v___y_418_);
lean_inc_ref(v___y_417_);
lean_inc(v___y_416_);
lean_inc_ref(v___y_415_);
lean_inc(v_a_422_);
v___x_423_ = lean_infer_type(v_a_422_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_440_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_440_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_440_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_440_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = lean_box(0);
lean_inc_ref(v_qs_409_);
v___x_429_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_409_, v_a_424_);
lean_dec(v_a_424_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; size_t v___x_431_; size_t v___x_432_; 
lean_del_object(v___x_426_);
v___x_430_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___closed__0));
v___x_431_ = ((size_t)1ULL);
v___x_432_ = lean_usize_add(v_i_413_, v___x_431_);
v_i_413_ = v___x_432_;
v_b_414_ = v___x_430_;
goto _start;
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
lean_dec_ref(v_qs_409_);
v___x_434_ = lean_box(v___x_410_);
v___x_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v___x_428_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_436_);
v___x_438_ = v___x_426_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec_ref(v_qs_409_);
v_a_441_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_423_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_423_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___boxed(lean_object* v_qs_449_, lean_object* v___x_450_, lean_object* v_as_451_, lean_object* v_sz_452_, lean_object* v_i_453_, lean_object* v_b_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
uint8_t v___x_2412__boxed_460_; size_t v_sz_boxed_461_; size_t v_i_boxed_462_; lean_object* v_res_463_; 
v___x_2412__boxed_460_ = lean_unbox(v___x_450_);
v_sz_boxed_461_ = lean_unbox_usize(v_sz_452_);
lean_dec(v_sz_452_);
v_i_boxed_462_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_res_463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1(v_qs_449_, v___x_2412__boxed_460_, v_as_451_, v_sz_boxed_461_, v_i_boxed_462_, v_b_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec_ref(v_as_451_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(lean_object* v_as_464_, size_t v_i_465_, size_t v_stop_466_, lean_object* v_b_467_){
_start:
{
lean_object* v___y_469_; uint8_t v___x_473_; 
v___x_473_ = lean_usize_dec_eq(v_i_465_, v_stop_466_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_array_uget_borrowed(v_as_464_, v_i_465_);
lean_inc(v___x_474_);
v___x_475_ = l_Lean_Expr_eta(v___x_474_);
if (lean_obj_tag(v___x_475_) == 2)
{
lean_object* v_mvarId_476_; lean_object* v___x_477_; 
v_mvarId_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_mvarId_476_);
lean_dec_ref_known(v___x_475_, 1);
v___x_477_ = lean_array_push(v_b_467_, v_mvarId_476_);
v___y_469_ = v___x_477_;
goto v___jp_468_;
}
else
{
lean_dec_ref(v___x_475_);
v___y_469_ = v_b_467_;
goto v___jp_468_;
}
}
else
{
return v_b_467_;
}
v___jp_468_:
{
size_t v___x_470_; size_t v___x_471_; 
v___x_470_ = ((size_t)1ULL);
v___x_471_ = lean_usize_add(v_i_465_, v___x_470_);
v_i_465_ = v___x_471_;
v_b_467_ = v___y_469_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0___boxed(lean_object* v_as_478_, lean_object* v_i_479_, lean_object* v_stop_480_, lean_object* v_b_481_){
_start:
{
size_t v_i_boxed_482_; size_t v_stop_boxed_483_; lean_object* v_res_484_; 
v_i_boxed_482_ = lean_unbox_usize(v_i_479_);
lean_dec(v_i_479_);
v_stop_boxed_483_ = lean_unbox_usize(v_stop_480_);
lean_dec(v_stop_480_);
v_res_484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_478_, v_i_boxed_482_, v_stop_boxed_483_, v_b_481_);
lean_dec_ref(v_as_478_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0(lean_object* v_as_487_, lean_object* v_start_488_, lean_object* v_stop_489_){
_start:
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0___closed__0));
v___x_491_ = lean_nat_dec_lt(v_start_488_, v_stop_489_);
if (v___x_491_ == 0)
{
return v___x_490_;
}
else
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = lean_array_get_size(v_as_487_);
v___x_493_ = lean_nat_dec_le(v_stop_489_, v___x_492_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; 
v___x_494_ = lean_nat_dec_lt(v_start_488_, v___x_492_);
if (v___x_494_ == 0)
{
return v___x_490_;
}
else
{
size_t v___x_495_; size_t v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_usize_of_nat(v_start_488_);
v___x_496_ = lean_usize_of_nat(v___x_492_);
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_487_, v___x_495_, v___x_496_, v___x_490_);
return v___x_497_;
}
}
else
{
size_t v___x_498_; size_t v___x_499_; lean_object* v___x_500_; 
v___x_498_ = lean_usize_of_nat(v_start_488_);
v___x_499_ = lean_usize_of_nat(v_stop_489_);
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_487_, v___x_498_, v___x_499_, v___x_490_);
return v___x_500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0___boxed(lean_object* v_as_501_, lean_object* v_start_502_, lean_object* v_stop_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0(v_as_501_, v_start_502_, v_stop_503_);
lean_dec(v_stop_503_);
lean_dec(v_start_502_);
lean_dec_ref(v_as_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts(lean_object* v_concl_505_, lean_object* v_binders_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f(v_concl_505_);
if (lean_obj_tag(v___x_512_) == 1)
{
lean_object* v_val_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_569_; 
v_val_513_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_569_ == 0)
{
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_569_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_val_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_569_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v_snd_517_; lean_object* v_snd_518_; lean_object* v_fst_519_; lean_object* v_fst_520_; lean_object* v_fst_521_; lean_object* v_snd_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v_qs_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_snd_517_ = lean_ctor_get(v_val_513_, 1);
lean_inc(v_snd_517_);
v_snd_518_ = lean_ctor_get(v_snd_517_, 1);
lean_inc(v_snd_518_);
v_fst_519_ = lean_ctor_get(v_val_513_, 0);
lean_inc(v_fst_519_);
lean_dec(v_val_513_);
v_fst_520_ = lean_ctor_get(v_snd_517_, 0);
lean_inc(v_fst_520_);
lean_dec(v_snd_517_);
v_fst_521_ = lean_ctor_get(v_snd_518_, 0);
lean_inc(v_fst_521_);
v_snd_522_ = lean_ctor_get(v_snd_518_, 1);
lean_inc(v_snd_522_);
lean_dec(v_snd_518_);
v___x_523_ = lean_unsigned_to_nat(2u);
v___x_524_ = lean_mk_empty_array_with_capacity(v___x_523_);
v___x_525_ = lean_array_push(v___x_524_, v_fst_521_);
v___x_526_ = lean_array_push(v___x_525_, v_snd_522_);
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_array_get_size(v___x_526_);
v_qs_529_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0(v___x_526_, v___x_527_, v___x_528_);
lean_dec_ref(v___x_526_);
v___x_530_ = lean_array_get_size(v_qs_529_);
v___x_531_ = lean_nat_dec_eq(v___x_530_, v___x_527_);
if (v___x_531_ == 0)
{
uint8_t v___x_532_; 
lean_inc_ref(v_qs_529_);
v___x_532_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_529_, v_fst_520_);
lean_dec(v_fst_520_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; size_t v_sz_534_; size_t v___x_535_; lean_object* v___x_536_; 
lean_del_object(v___x_515_);
v___x_533_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___closed__0));
v_sz_534_ = lean_array_size(v_binders_506_);
v___x_535_ = ((size_t)0ULL);
lean_inc_ref(v_qs_529_);
v___x_536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1(v_qs_529_, v___x_532_, v_binders_506_, v_sz_534_, v___x_535_, v___x_533_, v_a_507_, v_a_508_, v_a_509_, v_a_510_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_551_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_551_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_551_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_551_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_fst_541_; 
v_fst_541_ = lean_ctor_get(v_a_537_, 0);
lean_inc(v_fst_541_);
lean_dec(v_a_537_);
if (lean_obj_tag(v_fst_541_) == 0)
{
uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_542_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_qs_529_, v_fst_519_);
v___x_543_ = lean_box(v___x_542_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_543_);
v___x_545_ = v___x_539_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
else
{
lean_object* v_val_547_; lean_object* v___x_549_; 
lean_dec_ref(v_qs_529_);
lean_dec(v_fst_519_);
v_val_547_ = lean_ctor_get(v_fst_541_, 0);
lean_inc(v_val_547_);
lean_dec_ref_known(v_fst_541_, 1);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v_val_547_);
v___x_549_ = v___x_539_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_val_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec_ref(v_qs_529_);
lean_dec(v_fst_519_);
v_a_552_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_536_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_536_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_562_; 
lean_dec_ref(v_qs_529_);
lean_dec(v_fst_519_);
v___x_560_ = lean_box(v___x_531_);
if (v_isShared_516_ == 0)
{
lean_ctor_set_tag(v___x_515_, 0);
lean_ctor_set(v___x_515_, 0, v___x_560_);
v___x_562_ = v___x_515_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
else
{
uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
lean_dec_ref(v_qs_529_);
lean_dec(v_fst_520_);
lean_dec(v_fst_519_);
v___x_564_ = 0;
v___x_565_ = lean_box(v___x_564_);
if (v_isShared_516_ == 0)
{
lean_ctor_set_tag(v___x_515_, 0);
lean_ctor_set(v___x_515_, 0, v___x_565_);
v___x_567_ = v___x_515_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
else
{
uint8_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v___x_512_);
v___x_570_ = 0;
v___x_571_ = lean_box(v___x_570_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts___boxed(lean_object* v_concl_573_, lean_object* v_binders_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts(v_concl_573_, v_binders_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec_ref(v_binders_574_);
return v_res_580_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ConjunctivePre(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ConjunctivePre(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ConjunctivePre(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ConjunctivePre(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ConjunctivePre(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ConjunctivePre(builtin);
}
#ifdef __cplusplus
}
#endif
