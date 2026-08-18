// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ConjunctivePre
// Imports: import Init.BinderNameHint public import Lean.Meta.Basic public import Std.WP.Triple.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_eta(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(202, 119, 227, 254, 29, 206, 25, 24)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wp"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(124, 118, 39, 144, 78, 10, 170, 168)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(182, 255, 127, 189, 81, 246, 28, 251)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__10_value;
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(173, 29, 48, 122, 5, 158, 45, 140)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iInf"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 96, 105, 10, 16, 194, 128, 157)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__6_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__8;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "binderNameHint"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "EPost"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Cons"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "head"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__12_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f(lean_object* v_concl_22_){
_start:
{
lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_23_ = l_Lean_Expr_cleanupAnnotations(v_concl_22_);
v___x_24_ = l_Lean_Expr_isApp(v___x_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; 
lean_dec_ref(v___x_23_);
v___x_25_ = lean_box(0);
return v___x_25_;
}
else
{
lean_object* v_arg_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v_arg_26_ = lean_ctor_get(v___x_23_, 1);
lean_inc_ref(v_arg_26_);
v___x_27_ = l_Lean_Expr_appFnCleanup___redArg(v___x_23_);
v___x_28_ = l_Lean_Expr_isApp(v___x_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; 
lean_dec_ref(v___x_27_);
lean_dec_ref(v_arg_26_);
v___x_29_ = lean_box(0);
return v___x_29_;
}
else
{
lean_object* v_arg_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v_arg_30_ = lean_ctor_get(v___x_27_, 1);
lean_inc_ref(v_arg_30_);
v___x_31_ = l_Lean_Expr_appFnCleanup___redArg(v___x_27_);
v___x_32_ = l_Lean_Expr_isApp(v___x_31_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; 
lean_dec_ref(v___x_31_);
lean_dec_ref(v_arg_30_);
lean_dec_ref(v_arg_26_);
v___x_33_ = lean_box(0);
return v___x_33_;
}
else
{
lean_object* v_arg_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v_arg_34_ = lean_ctor_get(v___x_31_, 1);
lean_inc_ref(v_arg_34_);
v___x_35_ = l_Lean_Expr_appFnCleanup___redArg(v___x_31_);
v___x_36_ = l_Lean_Expr_isApp(v___x_35_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; 
lean_dec_ref(v___x_35_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_30_);
lean_dec_ref(v_arg_26_);
v___x_37_ = lean_box(0);
return v___x_37_;
}
else
{
lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_38_ = l_Lean_Expr_appFnCleanup___redArg(v___x_35_);
v___x_39_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__4));
v___x_40_ = l_Lean_Expr_isConstOf(v___x_38_, v___x_39_);
if (v___x_40_ == 0)
{
uint8_t v___x_41_; 
v___x_41_ = l_Lean_Expr_isApp(v___x_38_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; 
lean_dec_ref(v___x_38_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_30_);
lean_dec_ref(v_arg_26_);
v___x_42_ = lean_box(0);
return v___x_42_;
}
else
{
lean_object* v_arg_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v_arg_43_ = lean_ctor_get(v___x_38_, 1);
lean_inc_ref(v_arg_43_);
v___x_44_ = l_Lean_Expr_appFnCleanup___redArg(v___x_38_);
v___x_45_ = l_Lean_Expr_isApp(v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; 
lean_dec_ref(v___x_44_);
lean_dec_ref(v_arg_43_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_30_);
lean_dec_ref(v_arg_26_);
v___x_46_ = lean_box(0);
return v___x_46_;
}
else
{
lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_47_ = l_Lean_Expr_appFnCleanup___redArg(v___x_44_);
v___x_48_ = l_Lean_Expr_isApp(v___x_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; 
lean_dec_ref(v___x_47_);
lean_dec_ref(v_arg_43_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_30_);
lean_dec_ref(v_arg_26_);
v___x_49_ = lean_box(0);
return v___x_49_;
}
else
{
lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_50_ = l_Lean_Expr_appFnCleanup___redArg(v___x_47_);
v___x_51_ = l_Lean_Expr_isApp(v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; 
lean_dec_ref(v___x_50_);
lean_dec_ref(v_arg_43_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_30_);
lean_dec_ref(v_arg_26_);
v___x_52_ = lean_box(0);
return v___x_52_;
}
else
{
lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_53_ = l_Lean_Expr_appFnCleanup___redArg(v___x_50_);
v___x_54_ = l_Lean_Expr_isApp(v___x_53_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; 
lean_dec_ref(v___x_53_);
lean_dec_ref(v_arg_43_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_30_);
lean_dec_ref(v_arg_26_);
v___x_55_ = lean_box(0);
return v___x_55_;
}
else
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = l_Lean_Expr_appFnCleanup___redArg(v___x_53_);
v___x_57_ = l_Lean_Expr_isApp(v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; 
lean_dec_ref(v___x_56_);
lean_dec_ref(v_arg_43_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_30_);
lean_dec_ref(v_arg_26_);
v___x_58_ = lean_box(0);
return v___x_58_;
}
else
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = l_Lean_Expr_appFnCleanup___redArg(v___x_56_);
v___x_60_ = l_Lean_Expr_isApp(v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
lean_dec_ref(v___x_59_);
lean_dec_ref(v_arg_43_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_30_);
lean_dec_ref(v_arg_26_);
v___x_61_ = lean_box(0);
return v___x_61_;
}
else
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_62_ = l_Lean_Expr_appFnCleanup___redArg(v___x_59_);
v___x_63_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__8));
v___x_64_ = l_Lean_Expr_isConstOf(v___x_62_, v___x_63_);
lean_dec_ref(v___x_62_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; 
lean_dec_ref(v_arg_43_);
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_30_);
lean_dec_ref(v_arg_26_);
v___x_65_ = lean_box(0);
return v___x_65_;
}
else
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v_arg_30_);
lean_ctor_set(v___x_66_, 1, v_arg_26_);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v_arg_43_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_68_, 0, v_arg_34_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
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
lean_object* v___x_70_; uint8_t v___x_71_; 
lean_dec_ref(v___x_38_);
lean_dec_ref(v_arg_34_);
v___x_70_ = l_Lean_Expr_cleanupAnnotations(v_arg_26_);
v___x_71_ = l_Lean_Expr_isApp(v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; 
lean_dec_ref(v___x_70_);
lean_dec_ref(v_arg_30_);
v___x_72_ = lean_box(0);
return v___x_72_;
}
else
{
lean_object* v_arg_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v_arg_73_ = lean_ctor_get(v___x_70_, 1);
lean_inc_ref(v_arg_73_);
v___x_74_ = l_Lean_Expr_appFnCleanup___redArg(v___x_70_);
v___x_75_ = l_Lean_Expr_isApp(v___x_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; 
lean_dec_ref(v___x_74_);
lean_dec_ref(v_arg_73_);
lean_dec_ref(v_arg_30_);
v___x_76_ = lean_box(0);
return v___x_76_;
}
else
{
lean_object* v_arg_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v_arg_77_ = lean_ctor_get(v___x_74_, 1);
lean_inc_ref(v_arg_77_);
v___x_78_ = l_Lean_Expr_appFnCleanup___redArg(v___x_74_);
v___x_79_ = l_Lean_Expr_isApp(v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
lean_dec_ref(v___x_78_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_arg_73_);
lean_dec_ref(v_arg_30_);
v___x_80_ = lean_box(0);
return v___x_80_;
}
else
{
lean_object* v_arg_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v_arg_81_ = lean_ctor_get(v___x_78_, 1);
lean_inc_ref(v_arg_81_);
v___x_82_ = l_Lean_Expr_appFnCleanup___redArg(v___x_78_);
v___x_83_ = l_Lean_Expr_isApp(v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
lean_dec_ref(v___x_82_);
lean_dec_ref(v_arg_81_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_arg_73_);
lean_dec_ref(v_arg_30_);
v___x_84_ = lean_box(0);
return v___x_84_;
}
else
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = l_Lean_Expr_appFnCleanup___redArg(v___x_82_);
v___x_86_ = l_Lean_Expr_isApp(v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; 
lean_dec_ref(v___x_85_);
lean_dec_ref(v_arg_81_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_arg_73_);
lean_dec_ref(v_arg_30_);
v___x_87_ = lean_box(0);
return v___x_87_;
}
else
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = l_Lean_Expr_appFnCleanup___redArg(v___x_85_);
v___x_89_ = l_Lean_Expr_isApp(v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
lean_dec_ref(v___x_88_);
lean_dec_ref(v_arg_81_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_arg_73_);
lean_dec_ref(v_arg_30_);
v___x_90_ = lean_box(0);
return v___x_90_;
}
else
{
lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_91_ = l_Lean_Expr_appFnCleanup___redArg(v___x_88_);
v___x_92_ = l_Lean_Expr_isApp(v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
lean_dec_ref(v___x_91_);
lean_dec_ref(v_arg_81_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_arg_73_);
lean_dec_ref(v_arg_30_);
v___x_93_ = lean_box(0);
return v___x_93_;
}
else
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = l_Lean_Expr_appFnCleanup___redArg(v___x_91_);
v___x_95_ = l_Lean_Expr_isApp(v___x_94_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
lean_dec_ref(v___x_94_);
lean_dec_ref(v_arg_81_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_arg_73_);
lean_dec_ref(v_arg_30_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
else
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = l_Lean_Expr_appFnCleanup___redArg(v___x_94_);
v___x_98_ = l_Lean_Expr_isApp(v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; 
lean_dec_ref(v___x_97_);
lean_dec_ref(v_arg_81_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_arg_73_);
lean_dec_ref(v_arg_30_);
v___x_99_ = lean_box(0);
return v___x_99_;
}
else
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_97_);
v___x_101_ = l_Lean_Expr_isApp(v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
lean_dec_ref(v___x_100_);
lean_dec_ref(v_arg_81_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_arg_73_);
lean_dec_ref(v_arg_30_);
v___x_102_ = lean_box(0);
return v___x_102_;
}
else
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_103_ = l_Lean_Expr_appFnCleanup___redArg(v___x_100_);
v___x_104_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__10));
v___x_105_ = l_Lean_Expr_isConstOf(v___x_103_, v___x_104_);
lean_dec_ref(v___x_103_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
lean_dec_ref(v_arg_81_);
lean_dec_ref(v_arg_77_);
lean_dec_ref(v_arg_73_);
lean_dec_ref(v_arg_30_);
v___x_106_ = lean_box(0);
return v___x_106_;
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v_arg_77_);
lean_ctor_set(v___x_107_, 1, v_arg_73_);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v_arg_81_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v_arg_30_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0(lean_object* v_a_111_, lean_object* v_as_112_, size_t v_i_113_, size_t v_stop_114_){
_start:
{
uint8_t v___x_115_; 
v___x_115_ = lean_usize_dec_eq(v_i_113_, v_stop_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_array_uget_borrowed(v_as_112_, v_i_113_);
v___x_117_ = l_Lean_instBEqMVarId_beq(v_a_111_, v___x_116_);
if (v___x_117_ == 0)
{
size_t v___x_118_; size_t v___x_119_; 
v___x_118_ = ((size_t)1ULL);
v___x_119_ = lean_usize_add(v_i_113_, v___x_118_);
v_i_113_ = v___x_119_;
goto _start;
}
else
{
return v___x_117_;
}
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 0;
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0___boxed(lean_object* v_a_122_, lean_object* v_as_123_, lean_object* v_i_124_, lean_object* v_stop_125_){
_start:
{
size_t v_i_boxed_126_; size_t v_stop_boxed_127_; uint8_t v_res_128_; lean_object* v_r_129_; 
v_i_boxed_126_ = lean_unbox_usize(v_i_124_);
lean_dec(v_i_124_);
v_stop_boxed_127_ = lean_unbox_usize(v_stop_125_);
lean_dec(v_stop_125_);
v_res_128_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0(v_a_122_, v_as_123_, v_i_boxed_126_, v_stop_boxed_127_);
lean_dec_ref(v_as_123_);
lean_dec(v_a_122_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(lean_object* v_as_130_, lean_object* v_a_131_){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_array_get_size(v_as_130_);
v___x_134_ = lean_nat_dec_lt(v___x_132_, v___x_133_);
if (v___x_134_ == 0)
{
return v___x_134_;
}
else
{
if (v___x_134_ == 0)
{
return v___x_134_;
}
else
{
size_t v___x_135_; size_t v___x_136_; uint8_t v___x_137_; 
v___x_135_ = ((size_t)0ULL);
v___x_136_ = lean_usize_of_nat(v___x_133_);
v___x_137_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0(v_a_131_, v_as_130_, v___x_135_, v___x_136_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0___boxed(lean_object* v_as_138_, lean_object* v_a_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(v_as_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_as_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0(lean_object* v_mvarIds_142_, lean_object* v_s_143_){
_start:
{
if (lean_obj_tag(v_s_143_) == 2)
{
lean_object* v_mvarId_144_; uint8_t v___x_145_; 
v_mvarId_144_ = lean_ctor_get(v_s_143_, 0);
v___x_145_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(v_mvarIds_142_, v_mvarId_144_);
return v___x_145_;
}
else
{
uint8_t v___x_146_; 
v___x_146_ = 0;
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0___boxed(lean_object* v_mvarIds_147_, lean_object* v_s_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0(v_mvarIds_147_, v_s_148_);
lean_dec_ref(v_s_148_);
lean_dec_ref(v_mvarIds_147_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(lean_object* v_mvarIds_151_, lean_object* v_e_152_){
_start:
{
lean_object* v___f_153_; lean_object* v___x_154_; 
v___f_153_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0___boxed), 2, 1);
lean_closure_set(v___f_153_, 0, v_mvarIds_151_);
v___x_154_ = lean_find_expr(v___f_153_, v_e_152_);
lean_dec_ref(v___f_153_);
if (lean_obj_tag(v___x_154_) == 0)
{
uint8_t v___x_155_; 
v___x_155_ = 0;
return v___x_155_;
}
else
{
uint8_t v___x_156_; 
lean_dec_ref_known(v___x_154_, 1);
v___x_156_ = 1;
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___boxed(lean_object* v_mvarIds_157_, lean_object* v_e_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_mvarIds_157_, v_e_158_);
lean_dec_ref(v_e_158_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1(lean_object* v_args_161_, lean_object* v_qs_162_, uint8_t v___x_163_, uint8_t v___x_164_, lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
uint8_t v___x_166_; 
lean_dec_ref(v_qs_162_);
v___x_166_ = 1;
return v___x_166_;
}
else
{
lean_object* v_head_167_; lean_object* v_tail_168_; uint8_t v___y_170_; lean_object* v___x_172_; uint8_t v___x_173_; 
v_head_167_ = lean_ctor_get(v_x_165_, 0);
v_tail_168_ = lean_ctor_get(v_x_165_, 1);
v___x_172_ = lean_unsigned_to_nat(2u);
v___x_173_ = lean_nat_dec_eq(v_head_167_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_174_ = l_Lean_instInhabitedExpr;
v___x_175_ = lean_array_get_borrowed(v___x_174_, v_args_161_, v_head_167_);
lean_inc_ref(v_qs_162_);
v___x_176_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_162_, v___x_175_);
if (v___x_176_ == 0)
{
v___y_170_ = v___x_163_;
goto v___jp_169_;
}
else
{
v___y_170_ = v___x_173_;
goto v___jp_169_;
}
}
else
{
v___y_170_ = v___x_164_;
goto v___jp_169_;
}
v___jp_169_:
{
if (v___y_170_ == 0)
{
lean_dec_ref(v_qs_162_);
return v___y_170_;
}
else
{
v_x_165_ = v_tail_168_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1___boxed(lean_object* v_args_177_, lean_object* v_qs_178_, lean_object* v___x_179_, lean_object* v___x_180_, lean_object* v_x_181_){
_start:
{
uint8_t v___x_5043__boxed_182_; uint8_t v___x_5044__boxed_183_; uint8_t v_res_184_; lean_object* v_r_185_; 
v___x_5043__boxed_182_ = lean_unbox(v___x_179_);
v___x_5044__boxed_183_ = lean_unbox(v___x_180_);
v_res_184_ = l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1(v_args_177_, v_qs_178_, v___x_5043__boxed_182_, v___x_5044__boxed_183_, v_x_181_);
lean_dec(v_x_181_);
lean_dec_ref(v_args_177_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0(lean_object* v_qs_186_, uint8_t v___x_187_, lean_object* v_as_188_, size_t v_i_189_, size_t v_stop_190_){
_start:
{
uint8_t v___x_195_; 
v___x_195_ = lean_usize_dec_eq(v_i_189_, v_stop_190_);
if (v___x_195_ == 0)
{
uint8_t v___x_196_; uint8_t v___y_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_196_ = 1;
v___x_199_ = lean_array_uget_borrowed(v_as_188_, v_i_189_);
lean_inc_ref(v_qs_186_);
v___x_200_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_186_, v___x_199_);
if (v___x_200_ == 0)
{
if (v___x_187_ == 0)
{
goto v___jp_191_;
}
else
{
v___y_198_ = v___x_200_;
goto v___jp_197_;
}
}
else
{
v___y_198_ = v___x_187_;
goto v___jp_197_;
}
v___jp_197_:
{
if (v___y_198_ == 0)
{
goto v___jp_191_;
}
else
{
lean_dec_ref(v_qs_186_);
return v___x_196_;
}
}
}
else
{
uint8_t v___x_201_; 
lean_dec_ref(v_qs_186_);
v___x_201_ = 0;
return v___x_201_;
}
v___jp_191_:
{
size_t v___x_192_; size_t v___x_193_; 
v___x_192_ = ((size_t)1ULL);
v___x_193_ = lean_usize_add(v_i_189_, v___x_192_);
v_i_189_ = v___x_193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0___boxed(lean_object* v_qs_202_, lean_object* v___x_203_, lean_object* v_as_204_, lean_object* v_i_205_, lean_object* v_stop_206_){
_start:
{
uint8_t v___x_5074__boxed_207_; size_t v_i_boxed_208_; size_t v_stop_boxed_209_; uint8_t v_res_210_; lean_object* v_r_211_; 
v___x_5074__boxed_207_ = lean_unbox(v___x_203_);
v_i_boxed_208_ = lean_unbox_usize(v_i_205_);
lean_dec(v_i_205_);
v_stop_boxed_209_ = lean_unbox_usize(v_stop_206_);
lean_dec(v_stop_206_);
v_res_210_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0(v_qs_202_, v___x_5074__boxed_207_, v_as_204_, v_i_boxed_208_, v_stop_boxed_209_);
lean_dec_ref(v_as_204_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__8(void){
_start:
{
lean_object* v___x_230_; lean_object* v_dummy_231_; 
v___x_230_ = lean_box(0);
v_dummy_231_ = l_Lean_Expr_sort___override(v___x_230_);
return v_dummy_231_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(lean_object* v_qs_236_, lean_object* v_e_237_){
_start:
{
lean_object* v_a_239_; lean_object* v_b_240_; uint8_t v___x_284_; 
lean_inc_ref(v_qs_236_);
v___x_284_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_236_, v_e_237_);
if (v___x_284_ == 0)
{
uint8_t v___x_285_; 
lean_dec_ref(v_e_237_);
lean_dec_ref(v_qs_236_);
v___x_285_ = 1;
return v___x_285_;
}
else
{
uint8_t v___x_286_; 
v___x_286_ = 0;
switch(lean_obj_tag(v_e_237_))
{
case 10:
{
lean_object* v_expr_287_; 
v_expr_287_ = lean_ctor_get(v_e_237_, 1);
lean_inc_ref(v_expr_287_);
lean_dec_ref_known(v_e_237_, 2);
v_e_237_ = v_expr_287_;
goto _start;
}
case 6:
{
lean_object* v_binderType_289_; lean_object* v_body_290_; uint8_t v___x_291_; 
v_binderType_289_ = lean_ctor_get(v_e_237_, 1);
lean_inc_ref(v_binderType_289_);
v_body_290_ = lean_ctor_get(v_e_237_, 2);
lean_inc_ref(v_body_290_);
lean_dec_ref_known(v_e_237_, 3);
lean_inc_ref(v_qs_236_);
v___x_291_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_236_, v_binderType_289_);
lean_dec_ref(v_binderType_289_);
if (v___x_291_ == 0)
{
v_e_237_ = v_body_290_;
goto _start;
}
else
{
lean_dec_ref(v_body_290_);
lean_dec_ref(v_qs_236_);
return v___x_286_;
}
}
default: 
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Expr_getAppFn(v_e_237_);
switch(lean_obj_tag(v___x_293_))
{
case 2:
{
lean_object* v_mvarId_294_; uint8_t v___x_295_; 
v_mvarId_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_mvarId_294_);
lean_dec_ref_known(v___x_293_, 1);
v___x_295_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(v_qs_236_, v_mvarId_294_);
lean_dec(v_mvarId_294_);
if (v___x_295_ == 0)
{
lean_dec_ref(v_e_237_);
lean_dec_ref(v_qs_236_);
return v___x_295_;
}
else
{
lean_object* v_dummy_296_; lean_object* v_nargs_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_dummy_296_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__8, &l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__8);
v_nargs_297_ = l_Lean_Expr_getAppNumArgs(v_e_237_);
lean_inc(v_nargs_297_);
v___x_298_ = lean_mk_array(v_nargs_297_, v_dummy_296_);
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_nat_sub(v_nargs_297_, v___x_299_);
lean_dec(v_nargs_297_);
v___x_301_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_237_, v___x_298_, v___x_300_);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_array_get_size(v___x_301_);
v___x_304_ = lean_nat_dec_lt(v___x_302_, v___x_303_);
if (v___x_304_ == 0)
{
lean_dec_ref(v___x_301_);
lean_dec_ref(v_qs_236_);
return v___x_295_;
}
else
{
if (v___x_304_ == 0)
{
lean_dec_ref(v___x_301_);
lean_dec_ref(v_qs_236_);
return v___x_295_;
}
else
{
size_t v___x_305_; size_t v___x_306_; uint8_t v___x_307_; 
v___x_305_ = ((size_t)0ULL);
v___x_306_ = lean_usize_of_nat(v___x_303_);
v___x_307_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0(v_qs_236_, v___x_295_, v___x_301_, v___x_305_, v___x_306_);
lean_dec_ref(v___x_301_);
if (v___x_307_ == 0)
{
return v___x_295_;
}
else
{
return v___x_286_;
}
}
}
}
}
case 4:
{
lean_object* v_declName_308_; 
v_declName_308_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_declName_308_);
lean_dec_ref_known(v___x_293_, 2);
if (lean_obj_tag(v_declName_308_) == 1)
{
lean_object* v_pre_309_; 
v_pre_309_ = lean_ctor_get(v_declName_308_, 0);
switch(lean_obj_tag(v_pre_309_))
{
case 0:
{
lean_object* v_str_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_str_310_ = lean_ctor_get(v_declName_308_, 1);
lean_inc_ref(v_str_310_);
lean_dec_ref_known(v_declName_308_, 2);
v___x_311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__9));
v___x_312_ = lean_string_dec_eq(v_str_310_, v___x_311_);
lean_dec_ref(v_str_310_);
if (v___x_312_ == 0)
{
goto v___jp_243_;
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_313_ = lean_unsigned_to_nat(5u);
v___x_314_ = l_Lean_Expr_getAppNumArgs(v_e_237_);
v___x_315_ = lean_nat_sub(v___x_314_, v___x_313_);
lean_dec(v___x_314_);
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_nat_sub(v___x_315_, v___x_316_);
lean_dec(v___x_315_);
v___x_318_ = l_Lean_Expr_getRevArg_x21(v_e_237_, v___x_317_);
lean_dec_ref(v_e_237_);
v_e_237_ = v___x_318_;
goto _start;
}
}
case 1:
{
lean_object* v_pre_320_; 
lean_inc_ref(v_pre_309_);
v_pre_320_ = lean_ctor_get(v_pre_309_, 0);
lean_inc(v_pre_320_);
if (lean_obj_tag(v_pre_320_) == 1)
{
lean_object* v_pre_321_; 
v_pre_321_ = lean_ctor_get(v_pre_320_, 0);
lean_inc(v_pre_321_);
if (lean_obj_tag(v_pre_321_) == 1)
{
lean_object* v_pre_322_; 
v_pre_322_ = lean_ctor_get(v_pre_321_, 0);
lean_inc(v_pre_322_);
if (lean_obj_tag(v_pre_322_) == 1)
{
lean_object* v_pre_323_; 
v_pre_323_ = lean_ctor_get(v_pre_322_, 0);
if (lean_obj_tag(v_pre_323_) == 0)
{
lean_object* v_str_324_; lean_object* v_str_325_; lean_object* v_str_326_; lean_object* v_str_327_; lean_object* v_str_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v_str_324_ = lean_ctor_get(v_declName_308_, 1);
lean_inc_ref(v_str_324_);
lean_dec_ref_known(v_declName_308_, 2);
v_str_325_ = lean_ctor_get(v_pre_309_, 1);
lean_inc_ref(v_str_325_);
lean_dec_ref_known(v_pre_309_, 2);
v_str_326_ = lean_ctor_get(v_pre_320_, 1);
lean_inc_ref(v_str_326_);
lean_dec_ref_known(v_pre_320_, 2);
v_str_327_ = lean_ctor_get(v_pre_321_, 1);
lean_inc_ref(v_str_327_);
lean_dec_ref_known(v_pre_321_, 2);
v_str_328_ = lean_ctor_get(v_pre_322_, 1);
lean_inc_ref(v_str_328_);
lean_dec_ref_known(v_pre_322_, 2);
v___x_329_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5));
v___x_330_ = lean_string_dec_eq(v_str_328_, v___x_329_);
lean_dec_ref(v_str_328_);
if (v___x_330_ == 0)
{
lean_dec_ref(v_str_327_);
lean_dec_ref(v_str_326_);
lean_dec_ref(v_str_325_);
lean_dec_ref(v_str_324_);
goto v___jp_243_;
}
else
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__6));
v___x_332_ = lean_string_dec_eq(v_str_327_, v___x_331_);
lean_dec_ref(v_str_327_);
if (v___x_332_ == 0)
{
lean_dec_ref(v_str_326_);
lean_dec_ref(v_str_325_);
lean_dec_ref(v_str_324_);
goto v___jp_243_;
}
else
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__10));
v___x_334_ = lean_string_dec_eq(v_str_326_, v___x_333_);
lean_dec_ref(v_str_326_);
if (v___x_334_ == 0)
{
lean_dec_ref(v_str_325_);
lean_dec_ref(v_str_324_);
goto v___jp_243_;
}
else
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__11));
v___x_336_ = lean_string_dec_eq(v_str_325_, v___x_335_);
lean_dec_ref(v_str_325_);
if (v___x_336_ == 0)
{
lean_dec_ref(v_str_324_);
goto v___jp_243_;
}
else
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__12));
v___x_338_ = lean_string_dec_eq(v_str_324_, v___x_337_);
lean_dec_ref(v_str_324_);
if (v___x_338_ == 0)
{
goto v___jp_243_;
}
else
{
lean_object* v_dummy_339_; lean_object* v_nargs_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_args_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_dummy_339_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__8, &l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__8);
v_nargs_340_ = l_Lean_Expr_getAppNumArgs(v_e_237_);
lean_inc(v_nargs_340_);
v___x_341_ = lean_mk_array(v_nargs_340_, v_dummy_339_);
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_sub(v_nargs_340_, v___x_342_);
lean_dec(v_nargs_340_);
v_args_344_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_237_, v___x_341_, v___x_343_);
v___x_345_ = lean_unsigned_to_nat(2u);
v___x_346_ = lean_array_get_size(v_args_344_);
v___x_347_ = lean_nat_dec_lt(v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
lean_dec_ref(v_args_344_);
lean_dec_ref(v_qs_236_);
return v___x_286_;
}
else
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_array_fget(v_args_344_, v___x_345_);
lean_inc_ref(v_qs_236_);
v___x_349_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_qs_236_, v___x_348_);
if (v___x_349_ == 0)
{
lean_dec_ref(v_args_344_);
lean_dec_ref(v_qs_236_);
return v___x_349_;
}
else
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = l_List_range(v___x_346_);
v___x_351_ = l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1(v_args_344_, v_qs_236_, v___x_349_, v___x_284_, v___x_350_);
lean_dec(v___x_350_);
lean_dec_ref(v_args_344_);
return v___x_351_;
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
lean_dec_ref_known(v_pre_322_, 2);
lean_dec_ref_known(v_pre_321_, 2);
lean_dec_ref_known(v_pre_320_, 2);
lean_dec_ref_known(v_pre_309_, 2);
lean_dec_ref_known(v_declName_308_, 2);
goto v___jp_243_;
}
}
else
{
lean_dec(v_pre_322_);
lean_dec_ref_known(v_pre_321_, 2);
lean_dec_ref_known(v_pre_320_, 2);
lean_dec_ref_known(v_pre_309_, 2);
lean_dec_ref_known(v_declName_308_, 2);
goto v___jp_243_;
}
}
else
{
lean_dec_ref_known(v_pre_320_, 2);
lean_dec(v_pre_321_);
lean_dec_ref_known(v_pre_309_, 2);
lean_dec_ref_known(v_declName_308_, 2);
goto v___jp_243_;
}
}
else
{
lean_dec(v_pre_320_);
lean_dec_ref_known(v_pre_309_, 2);
lean_dec_ref_known(v_declName_308_, 2);
goto v___jp_243_;
}
}
default: 
{
lean_dec_ref_known(v_declName_308_, 2);
goto v___jp_243_;
}
}
}
else
{
lean_dec(v_declName_308_);
goto v___jp_243_;
}
}
default: 
{
lean_dec_ref(v___x_293_);
goto v___jp_243_;
}
}
}
}
}
v___jp_238_:
{
uint8_t v___x_241_; 
lean_inc_ref(v_qs_236_);
v___x_241_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_qs_236_, v_a_239_);
if (v___x_241_ == 0)
{
lean_dec_ref(v_b_240_);
lean_dec_ref(v_qs_236_);
return v___x_241_;
}
else
{
v_e_237_ = v_b_240_;
goto _start;
}
}
v___jp_243_:
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = l_Lean_Expr_cleanupAnnotations(v_e_237_);
v___x_245_ = l_Lean_Expr_isApp(v___x_244_);
if (v___x_245_ == 0)
{
lean_dec_ref(v___x_244_);
lean_dec_ref(v_qs_236_);
return v___x_245_;
}
else
{
lean_object* v_arg_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_arg_246_ = lean_ctor_get(v___x_244_, 1);
lean_inc_ref(v_arg_246_);
v___x_247_ = l_Lean_Expr_appFnCleanup___redArg(v___x_244_);
v___x_248_ = l_Lean_Expr_isApp(v___x_247_);
if (v___x_248_ == 0)
{
lean_dec_ref(v___x_247_);
lean_dec_ref(v_arg_246_);
lean_dec_ref(v_qs_236_);
return v___x_248_;
}
else
{
lean_object* v_arg_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v_arg_249_ = lean_ctor_get(v___x_247_, 1);
lean_inc_ref(v_arg_249_);
v___x_250_ = l_Lean_Expr_appFnCleanup___redArg(v___x_247_);
v___x_251_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__1));
v___x_252_ = l_Lean_Expr_isConstOf(v___x_250_, v___x_251_);
if (v___x_252_ == 0)
{
uint8_t v___x_253_; 
v___x_253_ = l_Lean_Expr_isApp(v___x_250_);
if (v___x_253_ == 0)
{
lean_dec_ref(v___x_250_);
lean_dec_ref(v_arg_249_);
lean_dec_ref(v_arg_246_);
lean_dec_ref(v_qs_236_);
return v___x_253_;
}
else
{
lean_object* v_arg_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_arg_254_ = lean_ctor_get(v___x_250_, 1);
lean_inc_ref(v_arg_254_);
v___x_255_ = l_Lean_Expr_appFnCleanup___redArg(v___x_250_);
v___x_256_ = l_Lean_Expr_isApp(v___x_255_);
if (v___x_256_ == 0)
{
lean_dec_ref(v___x_255_);
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_arg_249_);
lean_dec_ref(v_arg_246_);
lean_dec_ref(v_qs_236_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_257_ = l_Lean_Expr_appFnCleanup___redArg(v___x_255_);
v___x_258_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__3));
v___x_259_ = l_Lean_Expr_isConstOf(v___x_257_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__5));
v___x_261_ = l_Lean_Expr_isConstOf(v___x_257_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__7));
v___x_263_ = l_Lean_Expr_isConstOf(v___x_257_, v___x_262_);
if (v___x_263_ == 0)
{
uint8_t v___x_264_; 
v___x_264_ = l_Lean_Expr_isApp(v___x_257_);
if (v___x_264_ == 0)
{
lean_dec_ref(v___x_257_);
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_arg_249_);
lean_dec_ref(v_arg_246_);
lean_dec_ref(v_qs_236_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = l_Lean_Expr_appFnCleanup___redArg(v___x_257_);
v___x_266_ = l_Lean_Expr_isApp(v___x_265_);
if (v___x_266_ == 0)
{
lean_dec_ref(v___x_265_);
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_arg_249_);
lean_dec_ref(v_arg_246_);
lean_dec_ref(v_qs_236_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = l_Lean_Expr_appFnCleanup___redArg(v___x_265_);
v___x_268_ = l_Lean_Expr_isApp(v___x_267_);
if (v___x_268_ == 0)
{
lean_dec_ref(v___x_267_);
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_arg_249_);
lean_dec_ref(v_arg_246_);
lean_dec_ref(v_qs_236_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = l_Lean_Expr_appFnCleanup___redArg(v___x_267_);
v___x_270_ = l_Lean_Expr_isApp(v___x_269_);
if (v___x_270_ == 0)
{
lean_dec_ref(v___x_269_);
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_arg_249_);
lean_dec_ref(v_arg_246_);
lean_dec_ref(v_qs_236_);
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
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_arg_249_);
lean_dec_ref(v_arg_246_);
lean_dec_ref(v_qs_236_);
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
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_arg_249_);
lean_dec_ref(v_arg_246_);
lean_dec_ref(v_qs_236_);
return v___x_274_;
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_275_ = l_Lean_Expr_appFnCleanup___redArg(v___x_273_);
v___x_276_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__10));
v___x_277_ = l_Lean_Expr_isConstOf(v___x_275_, v___x_276_);
lean_dec_ref(v___x_275_);
if (v___x_277_ == 0)
{
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_arg_249_);
lean_dec_ref(v_arg_246_);
lean_dec_ref(v_qs_236_);
return v___x_277_;
}
else
{
uint8_t v___x_278_; 
lean_inc_ref(v_qs_236_);
v___x_278_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_236_, v_arg_254_);
lean_dec_ref(v_arg_254_);
if (v___x_278_ == 0)
{
uint8_t v___x_279_; 
lean_inc_ref(v_qs_236_);
v___x_279_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_qs_236_, v_arg_249_);
if (v___x_279_ == 0)
{
lean_dec_ref(v_arg_246_);
lean_dec_ref(v_qs_236_);
return v___x_279_;
}
else
{
v_e_237_ = v_arg_246_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_249_);
lean_dec_ref(v_arg_246_);
lean_dec_ref(v_qs_236_);
return v___x_263_;
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
lean_dec_ref(v___x_257_);
lean_dec_ref(v_arg_254_);
v_a_239_ = v_arg_249_;
v_b_240_ = v_arg_246_;
goto v___jp_238_;
}
}
else
{
lean_dec_ref(v___x_257_);
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_arg_249_);
v_e_237_ = v_arg_246_;
goto _start;
}
}
else
{
uint8_t v___x_282_; 
lean_dec_ref(v___x_257_);
lean_dec_ref(v_arg_254_);
lean_inc_ref(v_qs_236_);
v___x_282_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_236_, v_arg_249_);
lean_dec_ref(v_arg_249_);
if (v___x_282_ == 0)
{
v_e_237_ = v_arg_246_;
goto _start;
}
else
{
lean_dec_ref(v_arg_246_);
lean_dec_ref(v_qs_236_);
return v___x_252_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_250_);
v_a_239_ = v_arg_249_;
v_b_240_ = v_arg_246_;
goto v___jp_238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___boxed(lean_object* v_qs_352_, lean_object* v_e_353_){
_start:
{
uint8_t v_res_354_; lean_object* v_r_355_; 
v_res_354_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_qs_352_, v_e_353_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1(lean_object* v_qs_359_, uint8_t v___x_360_, lean_object* v_as_361_, size_t v_sz_362_, size_t v_i_363_, lean_object* v_b_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
uint8_t v___x_370_; 
v___x_370_ = lean_usize_dec_lt(v_i_363_, v_sz_362_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec_ref(v_qs_359_);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v_b_364_);
return v___x_371_;
}
else
{
lean_object* v_a_372_; lean_object* v___x_373_; 
lean_dec_ref(v_b_364_);
v_a_372_ = lean_array_uget_borrowed(v_as_361_, v_i_363_);
lean_inc(v___y_368_);
lean_inc_ref(v___y_367_);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
lean_inc(v_a_372_);
v___x_373_ = lean_infer_type(v_a_372_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_390_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_390_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_390_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_390_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_box(0);
lean_inc_ref(v_qs_359_);
v___x_379_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_359_, v_a_374_);
lean_dec(v_a_374_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; size_t v___x_381_; size_t v___x_382_; 
lean_del_object(v___x_376_);
v___x_380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___closed__0));
v___x_381_ = ((size_t)1ULL);
v___x_382_ = lean_usize_add(v_i_363_, v___x_381_);
v_i_363_ = v___x_382_;
v_b_364_ = v___x_380_;
goto _start;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
lean_dec_ref(v_qs_359_);
v___x_384_ = lean_box(v___x_360_);
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___x_378_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_386_);
v___x_388_ = v___x_376_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec_ref(v_qs_359_);
v_a_391_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_373_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_373_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___boxed(lean_object* v_qs_399_, lean_object* v___x_400_, lean_object* v_as_401_, lean_object* v_sz_402_, lean_object* v_i_403_, lean_object* v_b_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
uint8_t v___x_2401__boxed_410_; size_t v_sz_boxed_411_; size_t v_i_boxed_412_; lean_object* v_res_413_; 
v___x_2401__boxed_410_ = lean_unbox(v___x_400_);
v_sz_boxed_411_ = lean_unbox_usize(v_sz_402_);
lean_dec(v_sz_402_);
v_i_boxed_412_ = lean_unbox_usize(v_i_403_);
lean_dec(v_i_403_);
v_res_413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1(v_qs_399_, v___x_2401__boxed_410_, v_as_401_, v_sz_boxed_411_, v_i_boxed_412_, v_b_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec_ref(v_as_401_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(lean_object* v_as_414_, size_t v_i_415_, size_t v_stop_416_, lean_object* v_b_417_){
_start:
{
lean_object* v___y_419_; uint8_t v___x_423_; 
v___x_423_ = lean_usize_dec_eq(v_i_415_, v_stop_416_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_array_uget_borrowed(v_as_414_, v_i_415_);
lean_inc(v___x_424_);
v___x_425_ = l_Lean_Expr_eta(v___x_424_);
if (lean_obj_tag(v___x_425_) == 2)
{
lean_object* v_mvarId_426_; lean_object* v___x_427_; 
v_mvarId_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_mvarId_426_);
lean_dec_ref_known(v___x_425_, 1);
v___x_427_ = lean_array_push(v_b_417_, v_mvarId_426_);
v___y_419_ = v___x_427_;
goto v___jp_418_;
}
else
{
lean_dec_ref(v___x_425_);
v___y_419_ = v_b_417_;
goto v___jp_418_;
}
}
else
{
return v_b_417_;
}
v___jp_418_:
{
size_t v___x_420_; size_t v___x_421_; 
v___x_420_ = ((size_t)1ULL);
v___x_421_ = lean_usize_add(v_i_415_, v___x_420_);
v_i_415_ = v___x_421_;
v_b_417_ = v___y_419_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0___boxed(lean_object* v_as_428_, lean_object* v_i_429_, lean_object* v_stop_430_, lean_object* v_b_431_){
_start:
{
size_t v_i_boxed_432_; size_t v_stop_boxed_433_; lean_object* v_res_434_; 
v_i_boxed_432_ = lean_unbox_usize(v_i_429_);
lean_dec(v_i_429_);
v_stop_boxed_433_ = lean_unbox_usize(v_stop_430_);
lean_dec(v_stop_430_);
v_res_434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_428_, v_i_boxed_432_, v_stop_boxed_433_, v_b_431_);
lean_dec_ref(v_as_428_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0(lean_object* v_as_437_, lean_object* v_start_438_, lean_object* v_stop_439_){
_start:
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0___closed__0));
v___x_441_ = lean_nat_dec_lt(v_start_438_, v_stop_439_);
if (v___x_441_ == 0)
{
return v___x_440_;
}
else
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_array_get_size(v_as_437_);
v___x_443_ = lean_nat_dec_le(v_stop_439_, v___x_442_);
if (v___x_443_ == 0)
{
uint8_t v___x_444_; 
v___x_444_ = lean_nat_dec_lt(v_start_438_, v___x_442_);
if (v___x_444_ == 0)
{
return v___x_440_;
}
else
{
size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_usize_of_nat(v_start_438_);
v___x_446_ = lean_usize_of_nat(v___x_442_);
v___x_447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_437_, v___x_445_, v___x_446_, v___x_440_);
return v___x_447_;
}
}
else
{
size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v___x_448_ = lean_usize_of_nat(v_start_438_);
v___x_449_ = lean_usize_of_nat(v_stop_439_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_437_, v___x_448_, v___x_449_, v___x_440_);
return v___x_450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0___boxed(lean_object* v_as_451_, lean_object* v_start_452_, lean_object* v_stop_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0(v_as_451_, v_start_452_, v_stop_453_);
lean_dec(v_stop_453_);
lean_dec(v_start_452_);
lean_dec_ref(v_as_451_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts(lean_object* v_concl_455_, lean_object* v_binders_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f(v_concl_455_);
if (lean_obj_tag(v___x_462_) == 1)
{
lean_object* v_val_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_519_; 
v_val_463_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_519_ == 0)
{
v___x_465_ = v___x_462_;
v_isShared_466_ = v_isSharedCheck_519_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_val_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_519_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v_snd_467_; lean_object* v_snd_468_; lean_object* v_fst_469_; lean_object* v_fst_470_; lean_object* v_fst_471_; lean_object* v_snd_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v_qs_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v_snd_467_ = lean_ctor_get(v_val_463_, 1);
lean_inc(v_snd_467_);
v_snd_468_ = lean_ctor_get(v_snd_467_, 1);
lean_inc(v_snd_468_);
v_fst_469_ = lean_ctor_get(v_val_463_, 0);
lean_inc(v_fst_469_);
lean_dec(v_val_463_);
v_fst_470_ = lean_ctor_get(v_snd_467_, 0);
lean_inc(v_fst_470_);
lean_dec(v_snd_467_);
v_fst_471_ = lean_ctor_get(v_snd_468_, 0);
lean_inc(v_fst_471_);
v_snd_472_ = lean_ctor_get(v_snd_468_, 1);
lean_inc(v_snd_472_);
lean_dec(v_snd_468_);
v___x_473_ = lean_unsigned_to_nat(2u);
v___x_474_ = lean_mk_empty_array_with_capacity(v___x_473_);
v___x_475_ = lean_array_push(v___x_474_, v_fst_471_);
v___x_476_ = lean_array_push(v___x_475_, v_snd_472_);
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = lean_array_get_size(v___x_476_);
v_qs_479_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0(v___x_476_, v___x_477_, v___x_478_);
lean_dec_ref(v___x_476_);
v___x_480_ = lean_array_get_size(v_qs_479_);
v___x_481_ = lean_nat_dec_eq(v___x_480_, v___x_477_);
if (v___x_481_ == 0)
{
uint8_t v___x_482_; 
lean_inc_ref(v_qs_479_);
v___x_482_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_479_, v_fst_470_);
lean_dec(v_fst_470_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; size_t v_sz_484_; size_t v___x_485_; lean_object* v___x_486_; 
lean_del_object(v___x_465_);
v___x_483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___closed__0));
v_sz_484_ = lean_array_size(v_binders_456_);
v___x_485_ = ((size_t)0ULL);
lean_inc_ref(v_qs_479_);
v___x_486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1(v_qs_479_, v___x_482_, v_binders_456_, v_sz_484_, v___x_485_, v___x_483_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_501_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_501_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_501_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_501_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v_fst_491_; 
v_fst_491_ = lean_ctor_get(v_a_487_, 0);
lean_inc(v_fst_491_);
lean_dec(v_a_487_);
if (lean_obj_tag(v_fst_491_) == 0)
{
uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_492_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_qs_479_, v_fst_469_);
v___x_493_ = lean_box(v___x_492_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_493_);
v___x_495_ = v___x_489_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
lean_object* v_val_497_; lean_object* v___x_499_; 
lean_dec_ref(v_qs_479_);
lean_dec(v_fst_469_);
v_val_497_ = lean_ctor_get(v_fst_491_, 0);
lean_inc(v_val_497_);
lean_dec_ref_known(v_fst_491_, 1);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v_val_497_);
v___x_499_ = v___x_489_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_val_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec_ref(v_qs_479_);
lean_dec(v_fst_469_);
v_a_502_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_486_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_486_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
lean_object* v___x_510_; lean_object* v___x_512_; 
lean_dec_ref(v_qs_479_);
lean_dec(v_fst_469_);
v___x_510_ = lean_box(v___x_481_);
if (v_isShared_466_ == 0)
{
lean_ctor_set_tag(v___x_465_, 0);
lean_ctor_set(v___x_465_, 0, v___x_510_);
v___x_512_ = v___x_465_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
lean_dec_ref(v_qs_479_);
lean_dec(v_fst_470_);
lean_dec(v_fst_469_);
v___x_514_ = 0;
v___x_515_ = lean_box(v___x_514_);
if (v_isShared_466_ == 0)
{
lean_ctor_set_tag(v___x_465_, 0);
lean_ctor_set(v___x_465_, 0, v___x_515_);
v___x_517_ = v___x_465_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
else
{
uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v___x_462_);
v___x_520_ = 0;
v___x_521_ = lean_box(v___x_520_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts___boxed(lean_object* v_concl_523_, lean_object* v_binders_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts(v_concl_523_, v_binders_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec_ref(v_binders_524_);
return v_res_530_;
}
}
lean_object* runtime_initialize_Init_BinderNameHint(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_WP_Triple_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ConjunctivePre(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_Triple_Basic(builtin);
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
lean_object* initialize_Init_BinderNameHint(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Std_WP_Triple_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ConjunctivePre(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP_Triple_Basic(builtin);
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
