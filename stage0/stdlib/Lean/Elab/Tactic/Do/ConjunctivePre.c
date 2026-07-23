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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eta(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(190, 57, 218, 157, 42, 52, 8, 129)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wp"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(8, 127, 121, 224, 88, 246, 48, 72)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__12_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(114, 80, 184, 106, 225, 60, 114, 167)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "himp"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(173, 29, 48, 122, 5, 158, 45, 140)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iInf"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 96, 105, 10, 16, 194, 128, 157)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__6_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__8;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "EPost"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Cons"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "head"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__11_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f(lean_object* v_concl_27_){
_start:
{
lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_28_ = l_Lean_Expr_cleanupAnnotations(v_concl_27_);
v___x_29_ = l_Lean_Expr_isApp(v___x_28_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; 
lean_dec_ref(v___x_28_);
v___x_30_ = lean_box(0);
return v___x_30_;
}
else
{
lean_object* v_arg_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v_arg_31_ = lean_ctor_get(v___x_28_, 1);
lean_inc_ref(v_arg_31_);
v___x_32_ = l_Lean_Expr_appFnCleanup___redArg(v___x_28_);
v___x_33_ = l_Lean_Expr_isApp(v___x_32_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
lean_dec_ref(v___x_32_);
lean_dec_ref(v_arg_31_);
v___x_34_ = lean_box(0);
return v___x_34_;
}
else
{
lean_object* v_arg_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_arg_35_ = lean_ctor_get(v___x_32_, 1);
lean_inc_ref(v_arg_35_);
v___x_36_ = l_Lean_Expr_appFnCleanup___redArg(v___x_32_);
v___x_37_ = l_Lean_Expr_isApp(v___x_36_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; 
lean_dec_ref(v___x_36_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v_arg_31_);
v___x_38_ = lean_box(0);
return v___x_38_;
}
else
{
lean_object* v_arg_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v_arg_39_ = lean_ctor_get(v___x_36_, 1);
lean_inc_ref(v_arg_39_);
v___x_40_ = l_Lean_Expr_appFnCleanup___redArg(v___x_36_);
v___x_41_ = l_Lean_Expr_isApp(v___x_40_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; 
lean_dec_ref(v___x_40_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v_arg_31_);
v___x_42_ = lean_box(0);
return v___x_42_;
}
else
{
lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_43_ = l_Lean_Expr_appFnCleanup___redArg(v___x_40_);
v___x_44_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__4));
v___x_45_ = l_Lean_Expr_isConstOf(v___x_43_, v___x_44_);
if (v___x_45_ == 0)
{
uint8_t v___x_46_; 
v___x_46_ = l_Lean_Expr_isApp(v___x_43_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; 
lean_dec_ref(v___x_43_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v_arg_31_);
v___x_47_ = lean_box(0);
return v___x_47_;
}
else
{
lean_object* v_arg_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
v_arg_48_ = lean_ctor_get(v___x_43_, 1);
lean_inc_ref(v_arg_48_);
v___x_49_ = l_Lean_Expr_appFnCleanup___redArg(v___x_43_);
v___x_50_ = l_Lean_Expr_isApp(v___x_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; 
lean_dec_ref(v___x_49_);
lean_dec_ref(v_arg_48_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v_arg_31_);
v___x_51_ = lean_box(0);
return v___x_51_;
}
else
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = l_Lean_Expr_appFnCleanup___redArg(v___x_49_);
v___x_53_ = l_Lean_Expr_isApp(v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; 
lean_dec_ref(v___x_52_);
lean_dec_ref(v_arg_48_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v_arg_31_);
v___x_54_ = lean_box(0);
return v___x_54_;
}
else
{
lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_55_ = l_Lean_Expr_appFnCleanup___redArg(v___x_52_);
v___x_56_ = l_Lean_Expr_isApp(v___x_55_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; 
lean_dec_ref(v___x_55_);
lean_dec_ref(v_arg_48_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v_arg_31_);
v___x_57_ = lean_box(0);
return v___x_57_;
}
else
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = l_Lean_Expr_appFnCleanup___redArg(v___x_55_);
v___x_59_ = l_Lean_Expr_isApp(v___x_58_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
lean_dec_ref(v___x_58_);
lean_dec_ref(v_arg_48_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v_arg_31_);
v___x_60_ = lean_box(0);
return v___x_60_;
}
else
{
lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_61_ = l_Lean_Expr_appFnCleanup___redArg(v___x_58_);
v___x_62_ = l_Lean_Expr_isApp(v___x_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; 
lean_dec_ref(v___x_61_);
lean_dec_ref(v_arg_48_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v_arg_31_);
v___x_63_ = lean_box(0);
return v___x_63_;
}
else
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = l_Lean_Expr_appFnCleanup___redArg(v___x_61_);
v___x_65_ = l_Lean_Expr_isApp(v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; 
lean_dec_ref(v___x_64_);
lean_dec_ref(v_arg_48_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v_arg_31_);
v___x_66_ = lean_box(0);
return v___x_66_;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_67_ = l_Lean_Expr_appFnCleanup___redArg(v___x_64_);
v___x_68_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__9));
v___x_69_ = l_Lean_Expr_isConstOf(v___x_67_, v___x_68_);
lean_dec_ref(v___x_67_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; 
lean_dec_ref(v_arg_48_);
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v_arg_31_);
v___x_70_ = lean_box(0);
return v___x_70_;
}
else
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v_arg_35_);
lean_ctor_set(v___x_71_, 1, v_arg_31_);
v___x_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_72_, 0, v_arg_48_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v_arg_39_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
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
lean_object* v___x_75_; uint8_t v___x_76_; 
lean_dec_ref(v___x_43_);
lean_dec_ref(v_arg_39_);
v___x_75_ = l_Lean_Expr_cleanupAnnotations(v_arg_31_);
v___x_76_ = l_Lean_Expr_isApp(v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
lean_dec_ref(v___x_75_);
lean_dec_ref(v_arg_35_);
v___x_77_ = lean_box(0);
return v___x_77_;
}
else
{
lean_object* v_arg_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v_arg_78_ = lean_ctor_get(v___x_75_, 1);
lean_inc_ref(v_arg_78_);
v___x_79_ = l_Lean_Expr_appFnCleanup___redArg(v___x_75_);
v___x_80_ = l_Lean_Expr_isApp(v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
lean_dec_ref(v___x_79_);
lean_dec_ref(v_arg_78_);
lean_dec_ref(v_arg_35_);
v___x_81_ = lean_box(0);
return v___x_81_;
}
else
{
lean_object* v_arg_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v_arg_82_ = lean_ctor_get(v___x_79_, 1);
lean_inc_ref(v_arg_82_);
v___x_83_ = l_Lean_Expr_appFnCleanup___redArg(v___x_79_);
v___x_84_ = l_Lean_Expr_isApp(v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
lean_dec_ref(v___x_83_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_78_);
lean_dec_ref(v_arg_35_);
v___x_85_ = lean_box(0);
return v___x_85_;
}
else
{
lean_object* v_arg_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v_arg_86_ = lean_ctor_get(v___x_83_, 1);
lean_inc_ref(v_arg_86_);
v___x_87_ = l_Lean_Expr_appFnCleanup___redArg(v___x_83_);
v___x_88_ = l_Lean_Expr_isApp(v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; 
lean_dec_ref(v___x_87_);
lean_dec_ref(v_arg_86_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_78_);
lean_dec_ref(v_arg_35_);
v___x_89_ = lean_box(0);
return v___x_89_;
}
else
{
lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_90_ = l_Lean_Expr_appFnCleanup___redArg(v___x_87_);
v___x_91_ = l_Lean_Expr_isApp(v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; 
lean_dec_ref(v___x_90_);
lean_dec_ref(v_arg_86_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_78_);
lean_dec_ref(v_arg_35_);
v___x_92_ = lean_box(0);
return v___x_92_;
}
else
{
lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = l_Lean_Expr_appFnCleanup___redArg(v___x_90_);
v___x_94_ = l_Lean_Expr_isApp(v___x_93_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; 
lean_dec_ref(v___x_93_);
lean_dec_ref(v_arg_86_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_78_);
lean_dec_ref(v_arg_35_);
v___x_95_ = lean_box(0);
return v___x_95_;
}
else
{
lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_96_ = l_Lean_Expr_appFnCleanup___redArg(v___x_93_);
v___x_97_ = l_Lean_Expr_isApp(v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
lean_dec_ref(v___x_96_);
lean_dec_ref(v_arg_86_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_78_);
lean_dec_ref(v_arg_35_);
v___x_98_ = lean_box(0);
return v___x_98_;
}
else
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = l_Lean_Expr_appFnCleanup___redArg(v___x_96_);
v___x_100_ = l_Lean_Expr_isApp(v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
lean_dec_ref(v___x_99_);
lean_dec_ref(v_arg_86_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_78_);
lean_dec_ref(v_arg_35_);
v___x_101_ = lean_box(0);
return v___x_101_;
}
else
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = l_Lean_Expr_appFnCleanup___redArg(v___x_99_);
v___x_103_ = l_Lean_Expr_isApp(v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
lean_dec_ref(v___x_102_);
lean_dec_ref(v_arg_86_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_78_);
lean_dec_ref(v_arg_35_);
v___x_104_ = lean_box(0);
return v___x_104_;
}
else
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = l_Lean_Expr_appFnCleanup___redArg(v___x_102_);
v___x_106_ = l_Lean_Expr_isApp(v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
lean_dec_ref(v___x_105_);
lean_dec_ref(v_arg_86_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_78_);
lean_dec_ref(v_arg_35_);
v___x_107_ = lean_box(0);
return v___x_107_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_108_ = l_Lean_Expr_appFnCleanup___redArg(v___x_105_);
v___x_109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__12));
v___x_110_ = l_Lean_Expr_isConstOf(v___x_108_, v___x_109_);
lean_dec_ref(v___x_108_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
lean_dec_ref(v_arg_86_);
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_78_);
lean_dec_ref(v_arg_35_);
v___x_111_ = lean_box(0);
return v___x_111_;
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v_arg_82_);
lean_ctor_set(v___x_112_, 1, v_arg_78_);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_arg_86_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v_arg_35_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
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
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar_spec__0_spec__0(lean_object* v_a_116_, lean_object* v_as_117_, size_t v_i_118_, size_t v_stop_119_){
_start:
{
uint8_t v___x_120_; 
v___x_120_ = lean_usize_dec_eq(v_i_118_, v_stop_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_array_uget_borrowed(v_as_117_, v_i_118_);
v___x_122_ = l_Lean_instBEqMVarId_beq(v_a_116_, v___x_121_);
if (v___x_122_ == 0)
{
size_t v___x_123_; size_t v___x_124_; 
v___x_123_ = ((size_t)1ULL);
v___x_124_ = lean_usize_add(v_i_118_, v___x_123_);
v_i_118_ = v___x_124_;
goto _start;
}
else
{
return v___x_122_;
}
}
else
{
uint8_t v___x_126_; 
v___x_126_ = 0;
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar_spec__0_spec__0___boxed(lean_object* v_a_127_, lean_object* v_as_128_, lean_object* v_i_129_, lean_object* v_stop_130_){
_start:
{
size_t v_i_boxed_131_; size_t v_stop_boxed_132_; uint8_t v_res_133_; lean_object* v_r_134_; 
v_i_boxed_131_ = lean_unbox_usize(v_i_129_);
lean_dec(v_i_129_);
v_stop_boxed_132_ = lean_unbox_usize(v_stop_130_);
lean_dec(v_stop_130_);
v_res_133_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar_spec__0_spec__0(v_a_127_, v_as_128_, v_i_boxed_131_, v_stop_boxed_132_);
lean_dec_ref(v_as_128_);
lean_dec(v_a_127_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar_spec__0(lean_object* v_as_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_array_get_size(v_as_135_);
v___x_139_ = lean_nat_dec_lt(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
return v___x_139_;
}
else
{
if (v___x_139_ == 0)
{
return v___x_139_;
}
else
{
size_t v___x_140_; size_t v___x_141_; uint8_t v___x_142_; 
v___x_140_ = ((size_t)0ULL);
v___x_141_ = lean_usize_of_nat(v___x_138_);
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar_spec__0_spec__0(v_a_136_, v_as_135_, v___x_140_, v___x_141_);
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar_spec__0___boxed(lean_object* v_as_143_, lean_object* v_a_144_){
_start:
{
uint8_t v_res_145_; lean_object* v_r_146_; 
v_res_145_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar_spec__0(v_as_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_as_143_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar___lam__0(lean_object* v_mvarIds_147_, lean_object* v_s_148_){
_start:
{
if (lean_obj_tag(v_s_148_) == 2)
{
lean_object* v_mvarId_149_; uint8_t v___x_150_; 
v_mvarId_149_ = lean_ctor_get(v_s_148_, 0);
v___x_150_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar_spec__0(v_mvarIds_147_, v_mvarId_149_);
return v___x_150_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = 0;
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar___lam__0___boxed(lean_object* v_mvarIds_152_, lean_object* v_s_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar___lam__0(v_mvarIds_152_, v_s_153_);
lean_dec_ref(v_s_153_);
lean_dec_ref(v_mvarIds_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar(lean_object* v_mvarIds_156_, lean_object* v_e_157_){
_start:
{
lean_object* v___f_158_; lean_object* v___x_159_; 
v___f_158_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar___lam__0___boxed), 2, 1);
lean_closure_set(v___f_158_, 0, v_mvarIds_156_);
v___x_159_ = lean_find_expr(v___f_158_, v_e_157_);
lean_dec_ref(v___f_158_);
if (lean_obj_tag(v___x_159_) == 0)
{
uint8_t v___x_160_; 
v___x_160_ = 0;
return v___x_160_;
}
else
{
uint8_t v___x_161_; 
lean_dec_ref_known(v___x_159_, 1);
v___x_161_ = 1;
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar___boxed(lean_object* v_mvarIds_162_, lean_object* v_e_163_){
_start:
{
uint8_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar(v_mvarIds_162_, v_e_163_);
lean_dec_ref(v_e_163_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn_spec__0(lean_object* v_qs_166_, uint8_t v___x_167_, lean_object* v_as_168_, size_t v_i_169_, size_t v_stop_170_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = lean_usize_dec_eq(v_i_169_, v_stop_170_);
if (v___x_175_ == 0)
{
uint8_t v___x_176_; uint8_t v___y_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_176_ = 1;
v___x_179_ = lean_array_uget_borrowed(v_as_168_, v_i_169_);
lean_inc_ref(v_qs_166_);
v___x_180_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar(v_qs_166_, v___x_179_);
if (v___x_180_ == 0)
{
if (v___x_167_ == 0)
{
goto v___jp_171_;
}
else
{
v___y_178_ = v___x_180_;
goto v___jp_177_;
}
}
else
{
v___y_178_ = v___x_167_;
goto v___jp_177_;
}
v___jp_177_:
{
if (v___y_178_ == 0)
{
goto v___jp_171_;
}
else
{
lean_dec_ref(v_qs_166_);
return v___x_176_;
}
}
}
else
{
uint8_t v___x_181_; 
lean_dec_ref(v_qs_166_);
v___x_181_ = 0;
return v___x_181_;
}
v___jp_171_:
{
size_t v___x_172_; size_t v___x_173_; 
v___x_172_ = ((size_t)1ULL);
v___x_173_ = lean_usize_add(v_i_169_, v___x_172_);
v_i_169_ = v___x_173_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn_spec__0___boxed(lean_object* v_qs_182_, lean_object* v___x_183_, lean_object* v_as_184_, lean_object* v_i_185_, lean_object* v_stop_186_){
_start:
{
uint8_t v___x_5214__boxed_187_; size_t v_i_boxed_188_; size_t v_stop_boxed_189_; uint8_t v_res_190_; lean_object* v_r_191_; 
v___x_5214__boxed_187_ = lean_unbox(v___x_183_);
v_i_boxed_188_ = lean_unbox_usize(v_i_185_);
lean_dec(v_i_185_);
v_stop_boxed_189_ = lean_unbox_usize(v_stop_186_);
lean_dec(v_stop_186_);
v_res_190_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn_spec__0(v_qs_182_, v___x_5214__boxed_187_, v_as_184_, v_i_boxed_188_, v_stop_boxed_189_);
lean_dec_ref(v_as_184_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn_spec__1(lean_object* v_args_192_, lean_object* v_qs_193_, uint8_t v___x_194_, uint8_t v___x_195_, lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
uint8_t v___x_197_; 
lean_dec_ref(v_qs_193_);
v___x_197_ = 1;
return v___x_197_;
}
else
{
lean_object* v_head_198_; lean_object* v_tail_199_; uint8_t v___y_201_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_head_198_ = lean_ctor_get(v_x_196_, 0);
v_tail_199_ = lean_ctor_get(v_x_196_, 1);
v___x_203_ = lean_unsigned_to_nat(2u);
v___x_204_ = lean_nat_dec_eq(v_head_198_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_205_ = l_Lean_instInhabitedExpr;
v___x_206_ = lean_array_get_borrowed(v___x_205_, v_args_192_, v_head_198_);
lean_inc_ref(v_qs_193_);
v___x_207_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar(v_qs_193_, v___x_206_);
if (v___x_207_ == 0)
{
v___y_201_ = v___x_194_;
goto v___jp_200_;
}
else
{
v___y_201_ = v___x_204_;
goto v___jp_200_;
}
}
else
{
v___y_201_ = v___x_195_;
goto v___jp_200_;
}
v___jp_200_:
{
if (v___y_201_ == 0)
{
lean_dec_ref(v_qs_193_);
return v___y_201_;
}
else
{
v_x_196_ = v_tail_199_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn_spec__1___boxed(lean_object* v_args_208_, lean_object* v_qs_209_, lean_object* v___x_210_, lean_object* v___x_211_, lean_object* v_x_212_){
_start:
{
uint8_t v___x_5239__boxed_213_; uint8_t v___x_5240__boxed_214_; uint8_t v_res_215_; lean_object* v_r_216_; 
v___x_5239__boxed_213_ = lean_unbox(v___x_210_);
v___x_5240__boxed_214_ = lean_unbox(v___x_211_);
v_res_215_ = l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn_spec__1(v_args_208_, v_qs_209_, v___x_5239__boxed_213_, v___x_5240__boxed_214_, v_x_212_);
lean_dec(v_x_212_);
lean_dec_ref(v_args_208_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__8(void){
_start:
{
lean_object* v___x_235_; lean_object* v_dummy_236_; 
v___x_235_ = lean_box(0);
v_dummy_236_ = l_Lean_Expr_sort___override(v___x_235_);
return v_dummy_236_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn(lean_object* v_qs_240_, lean_object* v_e_241_){
_start:
{
lean_object* v_a_243_; lean_object* v_b_244_; uint8_t v___x_288_; 
lean_inc_ref(v_qs_240_);
v___x_288_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar(v_qs_240_, v_e_241_);
if (v___x_288_ == 0)
{
uint8_t v___x_289_; 
lean_dec_ref(v_e_241_);
lean_dec_ref(v_qs_240_);
v___x_289_ = 1;
return v___x_289_;
}
else
{
uint8_t v___x_290_; 
v___x_290_ = 0;
switch(lean_obj_tag(v_e_241_))
{
case 10:
{
lean_object* v_expr_291_; 
v_expr_291_ = lean_ctor_get(v_e_241_, 1);
lean_inc_ref(v_expr_291_);
lean_dec_ref_known(v_e_241_, 2);
v_e_241_ = v_expr_291_;
goto _start;
}
case 6:
{
lean_object* v_binderType_293_; lean_object* v_body_294_; uint8_t v___x_295_; 
v_binderType_293_ = lean_ctor_get(v_e_241_, 1);
lean_inc_ref(v_binderType_293_);
v_body_294_ = lean_ctor_get(v_e_241_, 2);
lean_inc_ref(v_body_294_);
lean_dec_ref_known(v_e_241_, 3);
lean_inc_ref(v_qs_240_);
v___x_295_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar(v_qs_240_, v_binderType_293_);
lean_dec_ref(v_binderType_293_);
if (v___x_295_ == 0)
{
v_e_241_ = v_body_294_;
goto _start;
}
else
{
lean_dec_ref(v_body_294_);
lean_dec_ref(v_qs_240_);
return v___x_290_;
}
}
default: 
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_Expr_getAppFn(v_e_241_);
switch(lean_obj_tag(v___x_297_))
{
case 2:
{
lean_object* v_mvarId_298_; uint8_t v___x_299_; 
v_mvarId_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_mvarId_298_);
lean_dec_ref_known(v___x_297_, 1);
v___x_299_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar_spec__0(v_qs_240_, v_mvarId_298_);
lean_dec(v_mvarId_298_);
if (v___x_299_ == 0)
{
lean_dec_ref(v_e_241_);
lean_dec_ref(v_qs_240_);
return v___x_299_;
}
else
{
lean_object* v_dummy_300_; lean_object* v_nargs_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_dummy_300_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__8, &l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__8);
v_nargs_301_ = l_Lean_Expr_getAppNumArgs(v_e_241_);
lean_inc(v_nargs_301_);
v___x_302_ = lean_mk_array(v_nargs_301_, v_dummy_300_);
v___x_303_ = lean_unsigned_to_nat(1u);
v___x_304_ = lean_nat_sub(v_nargs_301_, v___x_303_);
lean_dec(v_nargs_301_);
v___x_305_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_241_, v___x_302_, v___x_304_);
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_array_get_size(v___x_305_);
v___x_308_ = lean_nat_dec_lt(v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_dec_ref(v___x_305_);
lean_dec_ref(v_qs_240_);
return v___x_299_;
}
else
{
if (v___x_308_ == 0)
{
lean_dec_ref(v___x_305_);
lean_dec_ref(v_qs_240_);
return v___x_299_;
}
else
{
size_t v___x_309_; size_t v___x_310_; uint8_t v___x_311_; 
v___x_309_ = ((size_t)0ULL);
v___x_310_ = lean_usize_of_nat(v___x_307_);
v___x_311_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn_spec__0(v_qs_240_, v___x_299_, v___x_305_, v___x_309_, v___x_310_);
lean_dec_ref(v___x_305_);
if (v___x_311_ == 0)
{
return v___x_299_;
}
else
{
return v___x_290_;
}
}
}
}
}
case 4:
{
lean_object* v_declName_312_; 
v_declName_312_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_declName_312_);
lean_dec_ref_known(v___x_297_, 2);
if (lean_obj_tag(v_declName_312_) == 1)
{
lean_object* v_pre_313_; 
v_pre_313_ = lean_ctor_get(v_declName_312_, 0);
lean_inc(v_pre_313_);
if (lean_obj_tag(v_pre_313_) == 1)
{
lean_object* v_pre_314_; 
v_pre_314_ = lean_ctor_get(v_pre_313_, 0);
lean_inc(v_pre_314_);
if (lean_obj_tag(v_pre_314_) == 1)
{
lean_object* v_pre_315_; 
v_pre_315_ = lean_ctor_get(v_pre_314_, 0);
lean_inc(v_pre_315_);
if (lean_obj_tag(v_pre_315_) == 1)
{
lean_object* v_pre_316_; 
v_pre_316_ = lean_ctor_get(v_pre_315_, 0);
lean_inc(v_pre_316_);
if (lean_obj_tag(v_pre_316_) == 1)
{
lean_object* v_pre_317_; 
v_pre_317_ = lean_ctor_get(v_pre_316_, 0);
lean_inc(v_pre_317_);
if (lean_obj_tag(v_pre_317_) == 1)
{
lean_object* v_pre_318_; 
v_pre_318_ = lean_ctor_get(v_pre_317_, 0);
if (lean_obj_tag(v_pre_318_) == 0)
{
lean_object* v_str_319_; lean_object* v_str_320_; lean_object* v_str_321_; lean_object* v_str_322_; lean_object* v_str_323_; lean_object* v_str_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_str_319_ = lean_ctor_get(v_declName_312_, 1);
lean_inc_ref(v_str_319_);
lean_dec_ref_known(v_declName_312_, 2);
v_str_320_ = lean_ctor_get(v_pre_313_, 1);
lean_inc_ref(v_str_320_);
lean_dec_ref_known(v_pre_313_, 2);
v_str_321_ = lean_ctor_get(v_pre_314_, 1);
lean_inc_ref(v_str_321_);
lean_dec_ref_known(v_pre_314_, 2);
v_str_322_ = lean_ctor_get(v_pre_315_, 1);
lean_inc_ref(v_str_322_);
lean_dec_ref_known(v_pre_315_, 2);
v_str_323_ = lean_ctor_get(v_pre_316_, 1);
lean_inc_ref(v_str_323_);
lean_dec_ref_known(v_pre_316_, 2);
v_str_324_ = lean_ctor_get(v_pre_317_, 1);
lean_inc_ref(v_str_324_);
lean_dec_ref_known(v_pre_317_, 2);
v___x_325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__5));
v___x_326_ = lean_string_dec_eq(v_str_324_, v___x_325_);
lean_dec_ref(v_str_324_);
if (v___x_326_ == 0)
{
lean_dec_ref(v_str_323_);
lean_dec_ref(v_str_322_);
lean_dec_ref(v_str_321_);
lean_dec_ref(v_str_320_);
lean_dec_ref(v_str_319_);
goto v___jp_247_;
}
else
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__6));
v___x_328_ = lean_string_dec_eq(v_str_323_, v___x_327_);
lean_dec_ref(v_str_323_);
if (v___x_328_ == 0)
{
lean_dec_ref(v_str_322_);
lean_dec_ref(v_str_321_);
lean_dec_ref(v_str_320_);
lean_dec_ref(v_str_319_);
goto v___jp_247_;
}
else
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__7));
v___x_330_ = lean_string_dec_eq(v_str_322_, v___x_329_);
lean_dec_ref(v_str_322_);
if (v___x_330_ == 0)
{
lean_dec_ref(v_str_321_);
lean_dec_ref(v_str_320_);
lean_dec_ref(v_str_319_);
goto v___jp_247_;
}
else
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__9));
v___x_332_ = lean_string_dec_eq(v_str_321_, v___x_331_);
lean_dec_ref(v_str_321_);
if (v___x_332_ == 0)
{
lean_dec_ref(v_str_320_);
lean_dec_ref(v_str_319_);
goto v___jp_247_;
}
else
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__10));
v___x_334_ = lean_string_dec_eq(v_str_320_, v___x_333_);
lean_dec_ref(v_str_320_);
if (v___x_334_ == 0)
{
lean_dec_ref(v_str_319_);
goto v___jp_247_;
}
else
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__11));
v___x_336_ = lean_string_dec_eq(v_str_319_, v___x_335_);
lean_dec_ref(v_str_319_);
if (v___x_336_ == 0)
{
goto v___jp_247_;
}
else
{
lean_object* v_dummy_337_; lean_object* v_nargs_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v_args_342_; lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v_dummy_337_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__8, &l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__8);
v_nargs_338_ = l_Lean_Expr_getAppNumArgs(v_e_241_);
lean_inc(v_nargs_338_);
v___x_339_ = lean_mk_array(v_nargs_338_, v_dummy_337_);
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = lean_nat_sub(v_nargs_338_, v___x_340_);
lean_dec(v_nargs_338_);
v_args_342_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_241_, v___x_339_, v___x_341_);
v___x_343_ = lean_unsigned_to_nat(2u);
v___x_344_ = lean_array_get_size(v_args_342_);
v___x_345_ = lean_nat_dec_lt(v___x_343_, v___x_344_);
if (v___x_345_ == 0)
{
lean_dec_ref(v_args_342_);
lean_dec_ref(v_qs_240_);
return v___x_290_;
}
else
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = lean_array_fget(v_args_342_, v___x_343_);
lean_inc_ref(v_qs_240_);
v___x_347_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn(v_qs_240_, v___x_346_);
if (v___x_347_ == 0)
{
lean_dec_ref(v_args_342_);
lean_dec_ref(v_qs_240_);
return v___x_347_;
}
else
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = l_List_range(v___x_344_);
v___x_349_ = l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn_spec__1(v_args_342_, v_qs_240_, v___x_347_, v___x_288_, v___x_348_);
lean_dec(v___x_348_);
lean_dec_ref(v_args_342_);
return v___x_349_;
}
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
lean_dec_ref_known(v_pre_317_, 2);
lean_dec_ref_known(v_pre_316_, 2);
lean_dec_ref_known(v_pre_315_, 2);
lean_dec_ref_known(v_pre_314_, 2);
lean_dec_ref_known(v_pre_313_, 2);
lean_dec_ref_known(v_declName_312_, 2);
goto v___jp_247_;
}
}
else
{
lean_dec(v_pre_317_);
lean_dec_ref_known(v_pre_316_, 2);
lean_dec_ref_known(v_pre_315_, 2);
lean_dec_ref_known(v_pre_314_, 2);
lean_dec_ref_known(v_pre_313_, 2);
lean_dec_ref_known(v_declName_312_, 2);
goto v___jp_247_;
}
}
else
{
lean_dec(v_pre_316_);
lean_dec_ref_known(v_pre_315_, 2);
lean_dec_ref_known(v_pre_314_, 2);
lean_dec_ref_known(v_pre_313_, 2);
lean_dec_ref_known(v_declName_312_, 2);
goto v___jp_247_;
}
}
else
{
lean_dec_ref_known(v_pre_314_, 2);
lean_dec(v_pre_315_);
lean_dec_ref_known(v_pre_313_, 2);
lean_dec_ref_known(v_declName_312_, 2);
goto v___jp_247_;
}
}
else
{
lean_dec(v_pre_314_);
lean_dec_ref_known(v_pre_313_, 2);
lean_dec_ref_known(v_declName_312_, 2);
goto v___jp_247_;
}
}
else
{
lean_dec_ref_known(v_declName_312_, 2);
lean_dec(v_pre_313_);
goto v___jp_247_;
}
}
else
{
lean_dec(v_declName_312_);
goto v___jp_247_;
}
}
default: 
{
lean_dec_ref(v___x_297_);
goto v___jp_247_;
}
}
}
}
}
v___jp_242_:
{
uint8_t v___x_245_; 
lean_inc_ref(v_qs_240_);
v___x_245_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn(v_qs_240_, v_a_243_);
if (v___x_245_ == 0)
{
lean_dec_ref(v_b_244_);
lean_dec_ref(v_qs_240_);
return v___x_245_;
}
else
{
v_e_241_ = v_b_244_;
goto _start;
}
}
v___jp_247_:
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = l_Lean_Expr_cleanupAnnotations(v_e_241_);
v___x_249_ = l_Lean_Expr_isApp(v___x_248_);
if (v___x_249_ == 0)
{
lean_dec_ref(v___x_248_);
lean_dec_ref(v_qs_240_);
return v___x_249_;
}
else
{
lean_object* v_arg_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v_arg_250_ = lean_ctor_get(v___x_248_, 1);
lean_inc_ref(v_arg_250_);
v___x_251_ = l_Lean_Expr_appFnCleanup___redArg(v___x_248_);
v___x_252_ = l_Lean_Expr_isApp(v___x_251_);
if (v___x_252_ == 0)
{
lean_dec_ref(v___x_251_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_qs_240_);
return v___x_252_;
}
else
{
lean_object* v_arg_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_arg_253_ = lean_ctor_get(v___x_251_, 1);
lean_inc_ref(v_arg_253_);
v___x_254_ = l_Lean_Expr_appFnCleanup___redArg(v___x_251_);
v___x_255_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__1));
v___x_256_ = l_Lean_Expr_isConstOf(v___x_254_, v___x_255_);
if (v___x_256_ == 0)
{
uint8_t v___x_257_; 
v___x_257_ = l_Lean_Expr_isApp(v___x_254_);
if (v___x_257_ == 0)
{
lean_dec_ref(v___x_254_);
lean_dec_ref(v_arg_253_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_qs_240_);
return v___x_257_;
}
else
{
lean_object* v_arg_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v_arg_258_ = lean_ctor_get(v___x_254_, 1);
lean_inc_ref(v_arg_258_);
v___x_259_ = l_Lean_Expr_appFnCleanup___redArg(v___x_254_);
v___x_260_ = l_Lean_Expr_isApp(v___x_259_);
if (v___x_260_ == 0)
{
lean_dec_ref(v___x_259_);
lean_dec_ref(v_arg_258_);
lean_dec_ref(v_arg_253_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_qs_240_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_261_ = l_Lean_Expr_appFnCleanup___redArg(v___x_259_);
v___x_262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__3));
v___x_263_ = l_Lean_Expr_isConstOf(v___x_261_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__5));
v___x_265_ = l_Lean_Expr_isConstOf(v___x_261_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___closed__7));
v___x_267_ = l_Lean_Expr_isConstOf(v___x_261_, v___x_266_);
if (v___x_267_ == 0)
{
uint8_t v___x_268_; 
v___x_268_ = l_Lean_Expr_isApp(v___x_261_);
if (v___x_268_ == 0)
{
lean_dec_ref(v___x_261_);
lean_dec_ref(v_arg_258_);
lean_dec_ref(v_arg_253_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_qs_240_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = l_Lean_Expr_appFnCleanup___redArg(v___x_261_);
v___x_270_ = l_Lean_Expr_isApp(v___x_269_);
if (v___x_270_ == 0)
{
lean_dec_ref(v___x_269_);
lean_dec_ref(v_arg_258_);
lean_dec_ref(v_arg_253_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_qs_240_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = l_Lean_Expr_appFnCleanup___redArg(v___x_269_);
v___x_272_ = l_Lean_Expr_isApp(v___x_271_);
if (v___x_272_ == 0)
{
lean_dec_ref(v___x_271_);
lean_dec_ref(v_arg_258_);
lean_dec_ref(v_arg_253_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_qs_240_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = l_Lean_Expr_appFnCleanup___redArg(v___x_271_);
v___x_274_ = l_Lean_Expr_isApp(v___x_273_);
if (v___x_274_ == 0)
{
lean_dec_ref(v___x_273_);
lean_dec_ref(v_arg_258_);
lean_dec_ref(v_arg_253_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_qs_240_);
return v___x_274_;
}
else
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = l_Lean_Expr_appFnCleanup___redArg(v___x_273_);
v___x_276_ = l_Lean_Expr_isApp(v___x_275_);
if (v___x_276_ == 0)
{
lean_dec_ref(v___x_275_);
lean_dec_ref(v_arg_258_);
lean_dec_ref(v_arg_253_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_qs_240_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = l_Lean_Expr_appFnCleanup___redArg(v___x_275_);
v___x_278_ = l_Lean_Expr_isApp(v___x_277_);
if (v___x_278_ == 0)
{
lean_dec_ref(v___x_277_);
lean_dec_ref(v_arg_258_);
lean_dec_ref(v_arg_253_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_qs_240_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_279_ = l_Lean_Expr_appFnCleanup___redArg(v___x_277_);
v___x_280_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f___closed__12));
v___x_281_ = l_Lean_Expr_isConstOf(v___x_279_, v___x_280_);
lean_dec_ref(v___x_279_);
if (v___x_281_ == 0)
{
lean_dec_ref(v_arg_258_);
lean_dec_ref(v_arg_253_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_qs_240_);
return v___x_281_;
}
else
{
uint8_t v___x_282_; 
lean_inc_ref(v_qs_240_);
v___x_282_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar(v_qs_240_, v_arg_258_);
lean_dec_ref(v_arg_258_);
if (v___x_282_ == 0)
{
uint8_t v___x_283_; 
lean_inc_ref(v_qs_240_);
v___x_283_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn(v_qs_240_, v_arg_253_);
if (v___x_283_ == 0)
{
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_qs_240_);
return v___x_283_;
}
else
{
v_e_241_ = v_arg_250_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_253_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_qs_240_);
return v___x_267_;
}
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
lean_dec_ref(v___x_261_);
lean_dec_ref(v_arg_258_);
v_a_243_ = v_arg_253_;
v_b_244_ = v_arg_250_;
goto v___jp_242_;
}
}
else
{
lean_dec_ref(v___x_261_);
lean_dec_ref(v_arg_258_);
lean_dec_ref(v_arg_253_);
v_e_241_ = v_arg_250_;
goto _start;
}
}
else
{
uint8_t v___x_286_; 
lean_dec_ref(v___x_261_);
lean_dec_ref(v_arg_258_);
lean_inc_ref(v_qs_240_);
v___x_286_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar(v_qs_240_, v_arg_253_);
lean_dec_ref(v_arg_253_);
if (v___x_286_ == 0)
{
v_e_241_ = v_arg_250_;
goto _start;
}
else
{
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_qs_240_);
return v___x_256_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_254_);
v_a_243_ = v_arg_253_;
v_b_244_ = v_arg_250_;
goto v___jp_242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn___boxed(lean_object* v_qs_350_, lean_object* v_e_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn(v_qs_350_, v_e_351_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__1(lean_object* v_qs_357_, uint8_t v___x_358_, lean_object* v_as_359_, size_t v_sz_360_, size_t v_i_361_, lean_object* v_b_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
uint8_t v___x_368_; 
v___x_368_ = lean_usize_dec_lt(v_i_361_, v_sz_360_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
lean_dec_ref(v_qs_357_);
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v_b_362_);
return v___x_369_;
}
else
{
lean_object* v_a_370_; lean_object* v___x_371_; 
lean_dec_ref(v_b_362_);
v_a_370_ = lean_array_uget_borrowed(v_as_359_, v_i_361_);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
lean_inc(v___y_364_);
lean_inc_ref(v___y_363_);
lean_inc(v_a_370_);
v___x_371_ = lean_infer_type(v_a_370_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_388_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_388_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_388_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_388_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = lean_box(0);
lean_inc_ref(v_qs_357_);
v___x_377_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar(v_qs_357_, v_a_372_);
lean_dec(v_a_372_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; size_t v___x_379_; size_t v___x_380_; 
lean_del_object(v___x_374_);
v___x_378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__1___closed__0));
v___x_379_ = ((size_t)1ULL);
v___x_380_ = lean_usize_add(v_i_361_, v___x_379_);
v_i_361_ = v___x_380_;
v_b_362_ = v___x_378_;
goto _start;
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
lean_dec_ref(v_qs_357_);
v___x_382_ = lean_box(v___x_358_);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___x_376_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_384_);
v___x_386_ = v___x_374_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec_ref(v_qs_357_);
v_a_389_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_371_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_371_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__1___boxed(lean_object* v_qs_397_, lean_object* v___x_398_, lean_object* v_as_399_, lean_object* v_sz_400_, lean_object* v_i_401_, lean_object* v_b_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
uint8_t v___x_2412__boxed_408_; size_t v_sz_boxed_409_; size_t v_i_boxed_410_; lean_object* v_res_411_; 
v___x_2412__boxed_408_ = lean_unbox(v___x_398_);
v_sz_boxed_409_ = lean_unbox_usize(v_sz_400_);
lean_dec(v_sz_400_);
v_i_boxed_410_ = lean_unbox_usize(v_i_401_);
lean_dec(v_i_401_);
v_res_411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__1(v_qs_397_, v___x_2412__boxed_408_, v_as_399_, v_sz_boxed_409_, v_i_boxed_410_, v_b_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec_ref(v_as_399_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(lean_object* v_as_412_, size_t v_i_413_, size_t v_stop_414_, lean_object* v_b_415_){
_start:
{
lean_object* v___y_417_; uint8_t v___x_421_; 
v___x_421_ = lean_usize_dec_eq(v_i_413_, v_stop_414_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_array_uget_borrowed(v_as_412_, v_i_413_);
lean_inc(v___x_422_);
v___x_423_ = l_Lean_Expr_eta(v___x_422_);
if (lean_obj_tag(v___x_423_) == 2)
{
lean_object* v_mvarId_424_; lean_object* v___x_425_; 
v_mvarId_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_mvarId_424_);
lean_dec_ref_known(v___x_423_, 1);
v___x_425_ = lean_array_push(v_b_415_, v_mvarId_424_);
v___y_417_ = v___x_425_;
goto v___jp_416_;
}
else
{
lean_dec_ref(v___x_423_);
v___y_417_ = v_b_415_;
goto v___jp_416_;
}
}
else
{
return v_b_415_;
}
v___jp_416_:
{
size_t v___x_418_; size_t v___x_419_; 
v___x_418_ = ((size_t)1ULL);
v___x_419_ = lean_usize_add(v_i_413_, v___x_418_);
v_i_413_ = v___x_419_;
v_b_415_ = v___y_417_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0_spec__0___boxed(lean_object* v_as_426_, lean_object* v_i_427_, lean_object* v_stop_428_, lean_object* v_b_429_){
_start:
{
size_t v_i_boxed_430_; size_t v_stop_boxed_431_; lean_object* v_res_432_; 
v_i_boxed_430_ = lean_unbox_usize(v_i_427_);
lean_dec(v_i_427_);
v_stop_boxed_431_ = lean_unbox_usize(v_stop_428_);
lean_dec(v_stop_428_);
v_res_432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_426_, v_i_boxed_430_, v_stop_boxed_431_, v_b_429_);
lean_dec_ref(v_as_426_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0(lean_object* v_as_435_, lean_object* v_start_436_, lean_object* v_stop_437_){
_start:
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0___closed__0));
v___x_439_ = lean_nat_dec_lt(v_start_436_, v_stop_437_);
if (v___x_439_ == 0)
{
return v___x_438_;
}
else
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_array_get_size(v_as_435_);
v___x_441_ = lean_nat_dec_le(v_stop_437_, v___x_440_);
if (v___x_441_ == 0)
{
uint8_t v___x_442_; 
v___x_442_ = lean_nat_dec_lt(v_start_436_, v___x_440_);
if (v___x_442_ == 0)
{
return v___x_438_;
}
else
{
size_t v___x_443_; size_t v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_usize_of_nat(v_start_436_);
v___x_444_ = lean_usize_of_nat(v___x_440_);
v___x_445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_435_, v___x_443_, v___x_444_, v___x_438_);
return v___x_445_;
}
}
else
{
size_t v___x_446_; size_t v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_usize_of_nat(v_start_436_);
v___x_447_ = lean_usize_of_nat(v_stop_437_);
v___x_448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_435_, v___x_446_, v___x_447_, v___x_438_);
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0___boxed(lean_object* v_as_449_, lean_object* v_start_450_, lean_object* v_stop_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0(v_as_449_, v_start_450_, v_stop_451_);
lean_dec(v_stop_451_);
lean_dec(v_start_450_);
lean_dec_ref(v_as_449_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts(lean_object* v_concl_453_, lean_object* v_binders_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_specComponents_x3f(v_concl_453_);
if (lean_obj_tag(v___x_460_) == 1)
{
lean_object* v_val_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_517_; 
v_val_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_517_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_517_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_val_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_517_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v_snd_465_; lean_object* v_snd_466_; lean_object* v_fst_467_; lean_object* v_fst_468_; lean_object* v_fst_469_; lean_object* v_snd_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v_qs_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v_snd_465_ = lean_ctor_get(v_val_461_, 1);
lean_inc(v_snd_465_);
v_snd_466_ = lean_ctor_get(v_snd_465_, 1);
lean_inc(v_snd_466_);
v_fst_467_ = lean_ctor_get(v_val_461_, 0);
lean_inc(v_fst_467_);
lean_dec(v_val_461_);
v_fst_468_ = lean_ctor_get(v_snd_465_, 0);
lean_inc(v_fst_468_);
lean_dec(v_snd_465_);
v_fst_469_ = lean_ctor_get(v_snd_466_, 0);
lean_inc(v_fst_469_);
v_snd_470_ = lean_ctor_get(v_snd_466_, 1);
lean_inc(v_snd_470_);
lean_dec(v_snd_466_);
v___x_471_ = lean_unsigned_to_nat(2u);
v___x_472_ = lean_mk_empty_array_with_capacity(v___x_471_);
v___x_473_ = lean_array_push(v___x_472_, v_fst_469_);
v___x_474_ = lean_array_push(v___x_473_, v_snd_470_);
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_array_get_size(v___x_474_);
v_qs_477_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__0(v___x_474_, v___x_475_, v___x_476_);
lean_dec_ref(v___x_474_);
v___x_478_ = lean_array_get_size(v_qs_477_);
v___x_479_ = lean_nat_dec_eq(v___x_478_, v___x_475_);
if (v___x_479_ == 0)
{
uint8_t v___x_480_; 
lean_inc_ref(v_qs_477_);
v___x_480_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_occursMVar(v_qs_477_, v_fst_468_);
lean_dec(v_fst_468_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; size_t v_sz_482_; size_t v___x_483_; lean_object* v___x_484_; 
lean_del_object(v___x_463_);
v___x_481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__1___closed__0));
v_sz_482_ = lean_array_size(v_binders_454_);
v___x_483_ = ((size_t)0ULL);
lean_inc_ref(v_qs_477_);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts_spec__1(v_qs_477_, v___x_480_, v_binders_454_, v_sz_482_, v___x_483_, v___x_481_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_499_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_499_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_499_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_499_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v_fst_489_; 
v_fst_489_ = lean_ctor_get(v_a_485_, 0);
lean_inc(v_fst_489_);
lean_dec(v_a_485_);
if (lean_obj_tag(v_fst_489_) == 0)
{
uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_490_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveIn(v_qs_477_, v_fst_467_);
v___x_491_ = lean_box(v___x_490_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_491_);
v___x_493_ = v___x_487_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
else
{
lean_object* v_val_495_; lean_object* v___x_497_; 
lean_dec_ref(v_qs_477_);
lean_dec(v_fst_467_);
v_val_495_ = lean_ctor_get(v_fst_489_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v_fst_489_, 1);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v_val_495_);
v___x_497_ = v___x_487_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_val_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec_ref(v_qs_477_);
lean_dec(v_fst_467_);
v_a_500_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_484_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_484_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_510_; 
lean_dec_ref(v_qs_477_);
lean_dec(v_fst_467_);
v___x_508_ = lean_box(v___x_479_);
if (v_isShared_464_ == 0)
{
lean_ctor_set_tag(v___x_463_, 0);
lean_ctor_set(v___x_463_, 0, v___x_508_);
v___x_510_ = v___x_463_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
lean_dec_ref(v_qs_477_);
lean_dec(v_fst_468_);
lean_dec(v_fst_467_);
v___x_512_ = 0;
v___x_513_ = lean_box(v___x_512_);
if (v_isShared_464_ == 0)
{
lean_ctor_set_tag(v___x_463_, 0);
lean_ctor_set(v___x_463_, 0, v___x_513_);
v___x_515_ = v___x_463_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec(v___x_460_);
v___x_518_ = 0;
v___x_519_ = lean_box(v___x_518_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts___boxed(lean_object* v_concl_521_, lean_object* v_binders_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_isConjunctiveInPosts(v_concl_521_, v_binders_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec_ref(v_binders_522_);
return v_res_528_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ConjunctivePre(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
