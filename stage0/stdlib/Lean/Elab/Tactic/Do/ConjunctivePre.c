// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ConjunctivePre
// Imports: import Init.BinderNameHint public import Lean.Meta.Basic import Lean.Meta.Match.MatcherInfo public import Std.WP.Triple.Basic
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_getMatcherInfoCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_range_x27TR_go(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_Lean_Expr_eta(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__1_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__6_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__7_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__9_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__10_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__11_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iInf"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "himp"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__16_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__17_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__18_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fst"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "snd"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__24 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__24_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__25 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__26 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__26_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__27 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__27_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "binderNameHint"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__28 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__28_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__29 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__29_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__29_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__30 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__30_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__31 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__31_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__32 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__32_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__32_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__33 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__33_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__33_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__34 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__34_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__34_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__35 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__35_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__0;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___boxed(lean_object*, lean_object*, lean_object*);
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
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0(lean_object* v_a_111_, lean_object* v_as_112_, size_t v_i_113_, size_t v_stop_114_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_111_ = stack[0].m_obj;
lean_object* v_as_112_ = stack[1].m_obj;
size_t v_i_113_ = stack[2].m_num;
size_t v_stop_114_ = stack[3].m_num;
uint8_t v_res_122_;
v_res_122_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0(v_a_111_, v_as_112_, v_i_113_, v_stop_114_);
stack->m_num = v_res_122_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0___boxed(lean_object* v_a_123_, lean_object* v_as_124_, lean_object* v_i_125_, lean_object* v_stop_126_){
_start:
{
size_t v_i_boxed_127_; size_t v_stop_boxed_128_; uint8_t v_res_129_; lean_object* v_r_130_; 
v_i_boxed_127_ = lean_unbox_usize(v_i_125_);
lean_dec(v_i_125_);
v_stop_boxed_128_ = lean_unbox_usize(v_stop_126_);
lean_dec(v_stop_126_);
v_res_129_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0(v_a_123_, v_as_124_, v_i_boxed_127_, v_stop_boxed_128_);
lean_dec_ref(v_as_124_);
lean_dec(v_a_123_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(lean_object* v_as_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_array_get_size(v_as_131_);
v___x_135_ = lean_nat_dec_lt(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
return v___x_135_;
}
else
{
if (v___x_135_ == 0)
{
return v___x_135_;
}
else
{
size_t v___x_136_; size_t v___x_137_; uint8_t v___x_138_; 
v___x_136_ = ((size_t)0ULL);
v___x_137_ = lean_usize_of_nat(v___x_134_);
v___x_138_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0(v_a_132_, v_as_131_, v___x_136_, v___x_137_);
return v___x_138_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_131_ = stack[0].m_obj;
lean_object* v_a_132_ = stack[1].m_obj;
uint8_t v_res_139_;
v_res_139_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(v_as_131_, v_a_132_);
stack->m_num = v_res_139_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0___boxed(lean_object* v_as_140_, lean_object* v_a_141_){
_start:
{
uint8_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(v_as_140_, v_a_141_);
lean_dec(v_a_141_);
lean_dec_ref(v_as_140_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0(lean_object* v_mvarIds_144_, lean_object* v_s_145_){
_start:
{
if (lean_obj_tag(v_s_145_) == 2)
{
lean_object* v_mvarId_146_; uint8_t v___x_147_; 
v_mvarId_146_ = lean_ctor_get(v_s_145_, 0);
v___x_147_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(v_mvarIds_144_, v_mvarId_146_);
return v___x_147_;
}
else
{
uint8_t v___x_148_; 
v___x_148_ = 0;
return v___x_148_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarIds_144_ = stack[0].m_obj;
lean_object* v_s_145_ = stack[1].m_obj;
uint8_t v_res_149_;
v_res_149_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0(v_mvarIds_144_, v_s_145_);
stack->m_num = v_res_149_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0___boxed(lean_object* v_mvarIds_150_, lean_object* v_s_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0(v_mvarIds_150_, v_s_151_);
lean_dec_ref(v_s_151_);
lean_dec_ref(v_mvarIds_150_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(lean_object* v_mvarIds_154_, lean_object* v_e_155_){
_start:
{
lean_object* v___f_156_; lean_object* v___x_157_; 
v___f_156_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0___boxed), 2, 1);
lean_closure_set(v___f_156_, 0, v_mvarIds_154_);
v___x_157_ = lean_find_expr(v___f_156_, v_e_155_);
lean_dec_ref(v___f_156_);
if (lean_obj_tag(v___x_157_) == 0)
{
uint8_t v___x_158_; 
v___x_158_ = 0;
return v___x_158_;
}
else
{
uint8_t v___x_159_; 
lean_dec_ref_known(v___x_157_, 1);
v___x_159_ = 1;
return v___x_159_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarIds_154_ = stack[0].m_obj;
lean_object* v_e_155_ = stack[1].m_obj;
uint8_t v_res_160_;
v_res_160_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_mvarIds_154_, v_e_155_);
stack->m_num = v_res_160_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___boxed(lean_object* v_mvarIds_161_, lean_object* v_e_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_mvarIds_161_, v_e_162_);
lean_dec_ref(v_e_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f(lean_object* v_env_242_, lean_object* v_x_243_){
_start:
{
lean_object* v_c_245_; 
if (lean_obj_tag(v_x_243_) == 1)
{
lean_object* v_pre_272_; 
v_pre_272_ = lean_ctor_get(v_x_243_, 0);
switch(lean_obj_tag(v_pre_272_))
{
case 1:
{
lean_object* v_pre_273_; 
v_pre_273_ = lean_ctor_get(v_pre_272_, 0);
switch(lean_obj_tag(v_pre_273_))
{
case 1:
{
lean_object* v_pre_274_; 
v_pre_274_ = lean_ctor_get(v_pre_273_, 0);
switch(lean_obj_tag(v_pre_274_))
{
case 0:
{
lean_object* v_str_275_; lean_object* v_str_276_; lean_object* v_str_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v_str_275_ = lean_ctor_get(v_x_243_, 1);
v_str_276_ = lean_ctor_get(v_pre_272_, 1);
v_str_277_ = lean_ctor_get(v_pre_273_, 1);
v___x_278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0));
v___x_279_ = lean_string_dec_eq(v_str_277_, v___x_278_);
if (v___x_279_ == 0)
{
v_c_245_ = v_x_243_;
goto v___jp_244_;
}
else
{
lean_object* v___x_280_; uint8_t v___x_281_; 
lean_inc_ref(v_str_276_);
lean_inc(v_pre_274_);
lean_inc_ref(v_str_275_);
lean_dec_ref_known(v_x_243_, 2);
v___x_280_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1));
v___x_281_ = lean_string_dec_eq(v_str_276_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = l_Lean_Name_str___override(v_pre_274_, v___x_278_);
v___x_283_ = l_Lean_Name_str___override(v___x_282_, v_str_276_);
v___x_284_ = l_Lean_Name_str___override(v___x_283_, v_str_275_);
v_c_245_ = v___x_284_;
goto v___jp_244_;
}
else
{
lean_object* v___x_285_; uint8_t v___x_286_; 
lean_dec_ref(v_str_276_);
v___x_285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__13));
v___x_286_ = lean_string_dec_eq(v_str_275_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__14));
v___x_288_ = lean_string_dec_eq(v_str_275_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__15));
v___x_290_ = lean_string_dec_eq(v_str_275_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = l_Lean_Name_str___override(v_pre_274_, v___x_278_);
v___x_292_ = l_Lean_Name_str___override(v___x_291_, v___x_280_);
v___x_293_ = l_Lean_Name_str___override(v___x_292_, v_str_275_);
v_c_245_ = v___x_293_;
goto v___jp_244_;
}
else
{
lean_dec_ref(v_str_275_);
lean_dec_ref(v_env_242_);
goto v___jp_266_;
}
}
else
{
lean_dec_ref(v_str_275_);
lean_dec_ref(v_env_242_);
goto v___jp_266_;
}
}
else
{
lean_dec_ref(v_str_275_);
lean_dec_ref(v_env_242_);
goto v___jp_264_;
}
}
}
}
case 1:
{
lean_object* v_pre_294_; 
v_pre_294_ = lean_ctor_get(v_pre_274_, 0);
if (lean_obj_tag(v_pre_294_) == 0)
{
lean_object* v_str_295_; lean_object* v_str_296_; lean_object* v_str_297_; lean_object* v_str_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_str_295_ = lean_ctor_get(v_x_243_, 1);
v_str_296_ = lean_ctor_get(v_pre_272_, 1);
v_str_297_ = lean_ctor_get(v_pre_273_, 1);
v_str_298_ = lean_ctor_get(v_pre_274_, 1);
v___x_299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5));
v___x_300_ = lean_string_dec_eq(v_str_298_, v___x_299_);
if (v___x_300_ == 0)
{
v_c_245_ = v_x_243_;
goto v___jp_244_;
}
else
{
lean_object* v___x_301_; uint8_t v___x_302_; 
lean_inc_ref(v_str_297_);
lean_inc_ref(v_str_296_);
lean_inc_ref(v_str_295_);
lean_inc(v_pre_294_);
lean_dec_ref_known(v_x_243_, 2);
v___x_301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__6));
v___x_302_ = lean_string_dec_eq(v_str_297_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_303_ = l_Lean_Name_str___override(v_pre_294_, v___x_299_);
v___x_304_ = l_Lean_Name_str___override(v___x_303_, v_str_297_);
v___x_305_ = l_Lean_Name_str___override(v___x_304_, v_str_296_);
v___x_306_ = l_Lean_Name_str___override(v___x_305_, v_str_295_);
v_c_245_ = v___x_306_;
goto v___jp_244_;
}
else
{
uint8_t v___x_307_; 
lean_dec_ref(v_str_297_);
v___x_307_ = lean_string_dec_eq(v_str_296_, v___x_301_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_308_ = l_Lean_Name_str___override(v_pre_294_, v___x_299_);
v___x_309_ = l_Lean_Name_str___override(v___x_308_, v___x_301_);
v___x_310_ = l_Lean_Name_str___override(v___x_309_, v_str_296_);
v___x_311_ = l_Lean_Name_str___override(v___x_310_, v_str_295_);
v_c_245_ = v___x_311_;
goto v___jp_244_;
}
else
{
lean_object* v___x_312_; uint8_t v___x_313_; 
lean_dec_ref(v_str_296_);
v___x_312_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__9));
v___x_313_ = lean_string_dec_eq(v_str_295_, v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_314_ = l_Lean_Name_str___override(v_pre_294_, v___x_299_);
v___x_315_ = l_Lean_Name_str___override(v___x_314_, v___x_301_);
v___x_316_ = l_Lean_Name_str___override(v___x_315_, v___x_301_);
v___x_317_ = l_Lean_Name_str___override(v___x_316_, v_str_295_);
v_c_245_ = v___x_317_;
goto v___jp_244_;
}
else
{
lean_object* v___x_318_; 
lean_dec_ref(v_str_295_);
lean_dec_ref(v_env_242_);
v___x_318_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__19));
return v___x_318_;
}
}
}
}
}
else
{
v_c_245_ = v_x_243_;
goto v___jp_244_;
}
}
default: 
{
v_c_245_ = v_x_243_;
goto v___jp_244_;
}
}
}
case 0:
{
lean_object* v_str_319_; lean_object* v_str_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_str_319_ = lean_ctor_get(v_x_243_, 1);
v_str_320_ = lean_ctor_get(v_pre_272_, 1);
v___x_321_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__20));
v___x_322_ = lean_string_dec_eq(v_str_320_, v___x_321_);
if (v___x_322_ == 0)
{
v_c_245_ = v_x_243_;
goto v___jp_244_;
}
else
{
lean_object* v___x_323_; uint8_t v___x_324_; 
lean_inc_ref(v_str_319_);
lean_inc(v_pre_273_);
lean_dec_ref_known(v_x_243_, 2);
v___x_323_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__21));
v___x_324_ = lean_string_dec_eq(v_str_319_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__22));
v___x_326_ = lean_string_dec_eq(v_str_319_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__23));
v___x_328_ = lean_string_dec_eq(v_str_319_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = l_Lean_Name_str___override(v_pre_273_, v___x_321_);
v___x_330_ = l_Lean_Name_str___override(v___x_329_, v_str_319_);
v_c_245_ = v___x_330_;
goto v___jp_244_;
}
else
{
lean_dec_ref(v_str_319_);
lean_dec_ref(v_env_242_);
goto v___jp_264_;
}
}
else
{
lean_dec_ref(v_str_319_);
lean_dec_ref(v_env_242_);
goto v___jp_268_;
}
}
else
{
lean_dec_ref(v_str_319_);
lean_dec_ref(v_env_242_);
goto v___jp_268_;
}
}
}
default: 
{
v_c_245_ = v_x_243_;
goto v___jp_244_;
}
}
}
case 0:
{
lean_object* v_str_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_str_331_ = lean_ctor_get(v_x_243_, 1);
v___x_332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__24));
v___x_333_ = lean_string_dec_eq(v_str_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__25));
v___x_335_ = lean_string_dec_eq(v_str_331_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__26));
v___x_337_ = lean_string_dec_eq(v_str_331_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__27));
v___x_339_ = lean_string_dec_eq(v_str_331_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__28));
v___x_341_ = lean_string_dec_eq(v_str_331_, v___x_340_);
if (v___x_341_ == 0)
{
v_c_245_ = v_x_243_;
goto v___jp_244_;
}
else
{
lean_object* v___x_342_; 
lean_dec_ref_known(v_x_243_, 2);
lean_dec_ref(v_env_242_);
v___x_342_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__31));
return v___x_342_;
}
}
else
{
lean_dec_ref_known(v_x_243_, 2);
lean_dec_ref(v_env_242_);
goto v___jp_264_;
}
}
else
{
lean_dec_ref_known(v_x_243_, 2);
lean_dec_ref(v_env_242_);
goto v___jp_270_;
}
}
else
{
lean_dec_ref_known(v_x_243_, 2);
lean_dec_ref(v_env_242_);
goto v___jp_270_;
}
}
else
{
lean_object* v___x_343_; 
lean_dec_ref_known(v_x_243_, 2);
lean_dec_ref(v_env_242_);
v___x_343_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__35));
return v___x_343_;
}
}
default: 
{
v_c_245_ = v_x_243_;
goto v___jp_244_;
}
}
}
else
{
v_c_245_ = v_x_243_;
goto v___jp_244_;
}
v___jp_244_:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Meta_getMatcherInfoCore_x3f(v_env_242_, v_c_245_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v___x_247_; 
v___x_247_ = lean_box(0);
return v___x_247_;
}
else
{
lean_object* v_val_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_263_; 
v_val_248_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_263_ == 0)
{
v___x_250_ = v___x_246_;
v_isShared_251_ = v_isSharedCheck_263_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_val_248_);
lean_dec(v___x_246_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_263_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_252_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_248_);
v___x_253_ = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(v_val_248_);
v___x_254_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_248_);
lean_dec(v_val_248_);
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_add(v___x_253_, v___x_254_);
lean_dec(v___x_253_);
v___x_257_ = lean_box(0);
v___x_258_ = l_List_range_x27TR_go(v___x_255_, v___x_254_, v___x_256_, v___x_257_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_252_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_259_);
v___x_261_ = v___x_250_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
v___jp_264_:
{
lean_object* v___x_265_; 
v___x_265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__3));
return v___x_265_;
}
v___jp_266_:
{
lean_object* v___x_267_; 
v___x_267_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__5));
return v___x_267_;
}
v___jp_268_:
{
lean_object* v___x_269_; 
v___x_269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__8));
return v___x_269_;
}
v___jp_270_:
{
lean_object* v___x_271_; 
v___x_271_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__12));
return v___x_271_;
}
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0(lean_object* v_qs_344_, uint8_t v___x_345_, lean_object* v_as_346_, size_t v_i_347_, size_t v_stop_348_){
_start:
{
uint8_t v___x_353_; 
v___x_353_ = lean_usize_dec_eq(v_i_347_, v_stop_348_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_array_uget_borrowed(v_as_346_, v_i_347_);
lean_inc_ref(v_qs_344_);
v___x_355_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_344_, v___x_354_);
if (v___x_355_ == 0)
{
goto v___jp_349_;
}
else
{
if (v___x_345_ == 0)
{
goto v___jp_349_;
}
else
{
lean_dec_ref(v_qs_344_);
return v___x_345_;
}
}
}
else
{
uint8_t v___x_356_; 
lean_dec_ref(v_qs_344_);
v___x_356_ = 0;
return v___x_356_;
}
v___jp_349_:
{
size_t v___x_350_; size_t v___x_351_; 
v___x_350_ = ((size_t)1ULL);
v___x_351_ = lean_usize_add(v_i_347_, v___x_350_);
v_i_347_ = v___x_351_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_qs_344_ = stack[0].m_obj;
uint8_t v___x_345_ = stack[1].m_num;
lean_object* v_as_346_ = stack[2].m_obj;
size_t v_i_347_ = stack[3].m_num;
size_t v_stop_348_ = stack[4].m_num;
uint8_t v_res_357_;
v_res_357_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0(v_qs_344_, v___x_345_, v_as_346_, v_i_347_, v_stop_348_);
stack->m_num = v_res_357_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0___boxed(lean_object* v_qs_358_, lean_object* v___x_359_, lean_object* v_as_360_, lean_object* v_i_361_, lean_object* v_stop_362_){
_start:
{
uint8_t v___x_792__boxed_363_; size_t v_i_boxed_364_; size_t v_stop_boxed_365_; uint8_t v_res_366_; lean_object* v_r_367_; 
v___x_792__boxed_363_ = lean_unbox(v___x_359_);
v_i_boxed_364_ = lean_unbox_usize(v_i_361_);
lean_dec(v_i_361_);
v_stop_boxed_365_ = lean_unbox_usize(v_stop_362_);
lean_dec(v_stop_362_);
v_res_366_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0(v_qs_358_, v___x_792__boxed_363_, v_as_360_, v_i_boxed_364_, v_stop_boxed_365_);
lean_dec_ref(v_as_360_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
uint8_t l_List_elem___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1(lean_object* v_a_368_, lean_object* v_x_369_){
_start:
{
if (lean_obj_tag(v_x_369_) == 0)
{
uint8_t v___x_370_; 
v___x_370_ = 0;
return v___x_370_;
}
else
{
lean_object* v_head_371_; lean_object* v_tail_372_; uint8_t v___x_373_; 
v_head_371_ = lean_ctor_get(v_x_369_, 0);
v_tail_372_ = lean_ctor_get(v_x_369_, 1);
v___x_373_ = lean_nat_dec_eq(v_a_368_, v_head_371_);
if (v___x_373_ == 0)
{
v_x_369_ = v_tail_372_;
goto _start;
}
else
{
return v___x_373_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_368_ = stack[0].m_obj;
lean_object* v_x_369_ = stack[1].m_obj;
uint8_t v_res_375_;
v_res_375_ = l_List_elem___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1(v_a_368_, v_x_369_);
stack->m_num = v_res_375_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1___boxed(lean_object* v_a_376_, lean_object* v_x_377_){
_start:
{
uint8_t v_res_378_; lean_object* v_r_379_; 
v_res_378_ = l_List_elem___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1(v_a_376_, v_x_377_);
lean_dec(v_x_377_);
lean_dec(v_a_376_);
v_r_379_ = lean_box(v_res_378_);
return v_r_379_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__0(void){
_start:
{
lean_object* v___x_380_; lean_object* v_dummy_381_; 
v___x_380_ = lean_box(0);
v_dummy_381_ = l_Lean_Expr_sort___override(v___x_380_);
return v_dummy_381_;
}
}
uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(lean_object* v_env_382_, lean_object* v_qs_383_, lean_object* v_e_384_){
_start:
{
uint8_t v___x_385_; 
lean_inc_ref(v_qs_383_);
v___x_385_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_383_, v_e_384_);
if (v___x_385_ == 0)
{
uint8_t v___x_386_; 
lean_dec_ref(v_e_384_);
lean_dec_ref(v_qs_383_);
lean_dec_ref(v_env_382_);
v___x_386_ = 1;
return v___x_386_;
}
else
{
uint8_t v___x_387_; lean_object* v_dom_389_; lean_object* v_body_390_; 
v___x_387_ = 0;
switch(lean_obj_tag(v_e_384_))
{
case 10:
{
lean_object* v_expr_393_; 
v_expr_393_ = lean_ctor_get(v_e_384_, 1);
lean_inc_ref(v_expr_393_);
lean_dec_ref_known(v_e_384_, 2);
v_e_384_ = v_expr_393_;
goto _start;
}
case 6:
{
lean_object* v_binderType_395_; lean_object* v_body_396_; 
v_binderType_395_ = lean_ctor_get(v_e_384_, 1);
lean_inc_ref(v_binderType_395_);
v_body_396_ = lean_ctor_get(v_e_384_, 2);
lean_inc_ref(v_body_396_);
lean_dec_ref_known(v_e_384_, 3);
v_dom_389_ = v_binderType_395_;
v_body_390_ = v_body_396_;
goto v___jp_388_;
}
case 7:
{
lean_object* v_binderType_397_; lean_object* v_body_398_; 
v_binderType_397_ = lean_ctor_get(v_e_384_, 1);
lean_inc_ref(v_binderType_397_);
v_body_398_ = lean_ctor_get(v_e_384_, 2);
lean_inc_ref(v_body_398_);
lean_dec_ref_known(v_e_384_, 3);
v_dom_389_ = v_binderType_397_;
v_body_390_ = v_body_398_;
goto v___jp_388_;
}
default: 
{
lean_object* v_dummy_399_; lean_object* v_nargs_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v_args_404_; lean_object* v___x_405_; 
v_dummy_399_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__0, &l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__0);
v_nargs_400_ = l_Lean_Expr_getAppNumArgs(v_e_384_);
lean_inc(v_nargs_400_);
v___x_401_ = lean_mk_array(v_nargs_400_, v_dummy_399_);
v___x_402_ = lean_unsigned_to_nat(1u);
v___x_403_ = lean_nat_sub(v_nargs_400_, v___x_402_);
lean_dec(v_nargs_400_);
lean_inc_ref(v_e_384_);
v_args_404_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_384_, v___x_401_, v___x_403_);
v___x_405_ = l_Lean_Expr_getAppFn(v_e_384_);
lean_dec_ref(v_e_384_);
switch(lean_obj_tag(v___x_405_))
{
case 2:
{
lean_object* v_mvarId_406_; uint8_t v___x_407_; 
lean_dec_ref(v_env_382_);
v_mvarId_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_mvarId_406_);
lean_dec_ref_known(v___x_405_, 1);
v___x_407_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(v_qs_383_, v_mvarId_406_);
lean_dec(v_mvarId_406_);
if (v___x_407_ == 0)
{
lean_dec_ref(v_args_404_);
lean_dec_ref(v_qs_383_);
return v___x_387_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = lean_array_get_size(v_args_404_);
v___x_410_ = lean_nat_dec_lt(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_dec_ref(v_args_404_);
lean_dec_ref(v_qs_383_);
return v___x_407_;
}
else
{
if (v___x_410_ == 0)
{
lean_dec_ref(v_args_404_);
lean_dec_ref(v_qs_383_);
return v___x_407_;
}
else
{
size_t v___x_411_; size_t v___x_412_; uint8_t v___x_413_; 
v___x_411_ = ((size_t)0ULL);
v___x_412_ = lean_usize_of_nat(v___x_409_);
v___x_413_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0(v_qs_383_, v___x_407_, v_args_404_, v___x_411_, v___x_412_);
lean_dec_ref(v_args_404_);
if (v___x_413_ == 0)
{
return v___x_410_;
}
else
{
return v___x_387_;
}
}
}
}
}
case 4:
{
lean_object* v_declName_414_; lean_object* v___x_415_; 
v_declName_414_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_declName_414_);
lean_dec_ref_known(v___x_405_, 2);
lean_inc_ref(v_env_382_);
v___x_415_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f(v_env_382_, v_declName_414_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_dec_ref(v_args_404_);
lean_dec_ref(v_qs_383_);
lean_dec_ref(v_env_382_);
return v___x_387_;
}
else
{
lean_object* v_val_416_; lean_object* v_fst_417_; lean_object* v_snd_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_val_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_val_416_);
lean_dec_ref_known(v___x_415_, 1);
v_fst_417_ = lean_ctor_get(v_val_416_, 0);
lean_inc(v_fst_417_);
v_snd_418_ = lean_ctor_get(v_val_416_, 1);
lean_inc(v_snd_418_);
lean_dec(v_val_416_);
v___x_419_ = lean_array_get_size(v_args_404_);
v___x_420_ = lean_nat_dec_le(v_fst_417_, v___x_419_);
if (v___x_420_ == 0)
{
lean_dec(v_snd_418_);
lean_dec(v_fst_417_);
lean_dec_ref(v_args_404_);
lean_dec_ref(v_qs_383_);
lean_dec_ref(v_env_382_);
return v___x_387_;
}
else
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = l_List_range(v___x_419_);
v___x_422_ = l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__2(v_snd_418_, v_args_404_, v_qs_383_, v_fst_417_, v___x_419_, v_env_382_, v___x_421_);
lean_dec(v___x_421_);
lean_dec(v_fst_417_);
lean_dec_ref(v_args_404_);
lean_dec(v_snd_418_);
return v___x_422_;
}
}
}
default: 
{
lean_dec_ref(v___x_405_);
lean_dec_ref(v_args_404_);
lean_dec_ref(v_qs_383_);
lean_dec_ref(v_env_382_);
return v___x_387_;
}
}
}
}
v___jp_388_:
{
uint8_t v___x_391_; 
lean_inc_ref(v_qs_383_);
v___x_391_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_383_, v_dom_389_);
lean_dec_ref(v_dom_389_);
if (v___x_391_ == 0)
{
v_e_384_ = v_body_390_;
goto _start;
}
else
{
lean_dec_ref(v_body_390_);
lean_dec_ref(v_qs_383_);
lean_dec_ref(v_env_382_);
return v___x_387_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_382_ = stack[0].m_obj;
lean_object* v_qs_383_ = stack[1].m_obj;
lean_object* v_e_384_ = stack[2].m_obj;
uint8_t v_res_423_;
v_res_423_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_env_382_, v_qs_383_, v_e_384_);
stack->m_num = v_res_423_;
}
uint8_t l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__2(lean_object* v_snd_424_, lean_object* v_args_425_, lean_object* v_qs_426_, lean_object* v_fst_427_, lean_object* v___x_428_, lean_object* v_env_429_, lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
uint8_t v___x_431_; 
lean_dec_ref(v_env_429_);
lean_dec_ref(v_qs_426_);
v___x_431_ = 1;
return v___x_431_;
}
else
{
lean_object* v_head_432_; lean_object* v_tail_433_; uint8_t v___y_435_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_head_432_ = lean_ctor_get(v_x_430_, 0);
v_tail_433_ = lean_ctor_get(v_x_430_, 1);
v___x_437_ = l_Lean_instInhabitedExpr;
v___x_438_ = l_List_elem___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1(v_head_432_, v_snd_424_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = lean_array_get_borrowed(v___x_437_, v_args_425_, v_head_432_);
lean_inc_ref(v_qs_426_);
v___x_440_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_426_, v___x_439_);
if (v___x_440_ == 0)
{
uint8_t v___x_441_; 
v___x_441_ = lean_nat_dec_le(v_fst_427_, v___x_428_);
v___y_435_ = v___x_441_;
goto v___jp_434_;
}
else
{
v___y_435_ = v___x_438_;
goto v___jp_434_;
}
}
else
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_array_get_borrowed(v___x_437_, v_args_425_, v_head_432_);
lean_inc(v___x_442_);
lean_inc_ref(v_qs_426_);
lean_inc_ref(v_env_429_);
v___x_443_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_env_429_, v_qs_426_, v___x_442_);
v___y_435_ = v___x_443_;
goto v___jp_434_;
}
v___jp_434_:
{
if (v___y_435_ == 0)
{
lean_dec_ref(v_env_429_);
lean_dec_ref(v_qs_426_);
return v___y_435_;
}
else
{
v_x_430_ = v_tail_433_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_424_ = stack[0].m_obj;
lean_object* v_args_425_ = stack[1].m_obj;
lean_object* v_qs_426_ = stack[2].m_obj;
lean_object* v_fst_427_ = stack[3].m_obj;
lean_object* v___x_428_ = stack[4].m_obj;
lean_object* v_env_429_ = stack[5].m_obj;
lean_object* v_x_430_ = stack[6].m_obj;
uint8_t v_res_444_;
v_res_444_ = l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__2(v_snd_424_, v_args_425_, v_qs_426_, v_fst_427_, v___x_428_, v_env_429_, v_x_430_);
stack->m_num = v_res_444_;
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__2___boxed(lean_object* v_snd_445_, lean_object* v_args_446_, lean_object* v_qs_447_, lean_object* v_fst_448_, lean_object* v___x_449_, lean_object* v_env_450_, lean_object* v_x_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__2(v_snd_445_, v_args_446_, v_qs_447_, v_fst_448_, v___x_449_, v_env_450_, v_x_451_);
lean_dec(v_x_451_);
lean_dec(v___x_449_);
lean_dec(v_fst_448_);
lean_dec_ref(v_args_446_);
lean_dec(v_snd_445_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___boxed(lean_object* v_env_454_, lean_object* v_qs_455_, lean_object* v_e_456_){
_start:
{
uint8_t v_res_457_; lean_object* v_r_458_; 
v_res_457_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_env_454_, v_qs_455_, v_e_456_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1(lean_object* v_qs_462_, uint8_t v___x_463_, lean_object* v_as_464_, size_t v_sz_465_, size_t v_i_466_, lean_object* v_b_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v___x_473_; 
v___x_473_ = lean_usize_dec_lt(v_i_466_, v_sz_465_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
lean_dec_ref(v_qs_462_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v_b_467_);
return v___x_474_;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v_a_477_; lean_object* v___x_478_; 
lean_dec_ref(v_b_467_);
v___x_475_ = lean_box(0);
v___x_476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___closed__0));
v_a_477_ = lean_array_uget_borrowed(v_as_464_, v_i_466_);
lean_inc(v___y_471_);
lean_inc_ref(v___y_470_);
lean_inc(v___y_469_);
lean_inc_ref(v___y_468_);
lean_inc(v_a_477_);
v___x_478_ = lean_infer_type(v_a_477_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_493_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_493_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_493_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_493_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
uint8_t v___x_483_; 
lean_inc_ref(v_qs_462_);
v___x_483_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_462_, v_a_479_);
lean_dec(v_a_479_);
if (v___x_483_ == 0)
{
size_t v___x_484_; size_t v___x_485_; 
lean_del_object(v___x_481_);
v___x_484_ = ((size_t)1ULL);
v___x_485_ = lean_usize_add(v_i_466_, v___x_484_);
v_i_466_ = v___x_485_;
v_b_467_ = v___x_476_;
goto _start;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
lean_dec_ref(v_qs_462_);
v___x_487_ = lean_box(v___x_463_);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_475_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_489_);
v___x_491_ = v___x_481_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec_ref(v_qs_462_);
v_a_494_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_478_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_478_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_qs_462_ = stack[0].m_obj;
uint8_t v___x_463_ = stack[1].m_num;
lean_object* v_as_464_ = stack[2].m_obj;
size_t v_sz_465_ = stack[3].m_num;
size_t v_i_466_ = stack[4].m_num;
lean_object* v_b_467_ = stack[5].m_obj;
lean_object* v___y_468_ = stack[6].m_obj;
lean_object* v___y_469_ = stack[7].m_obj;
lean_object* v___y_470_ = stack[8].m_obj;
lean_object* v___y_471_ = stack[9].m_obj;
lean_object* v_res_502_;
v_res_502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1(v_qs_462_, v___x_463_, v_as_464_, v_sz_465_, v_i_466_, v_b_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
stack->m_obj
 = v_res_502_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___boxed(lean_object* v_qs_503_, lean_object* v___x_504_, lean_object* v_as_505_, lean_object* v_sz_506_, lean_object* v_i_507_, lean_object* v_b_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
uint8_t v___x_2134__boxed_514_; size_t v_sz_boxed_515_; size_t v_i_boxed_516_; lean_object* v_res_517_; 
v___x_2134__boxed_514_ = lean_unbox(v___x_504_);
v_sz_boxed_515_ = lean_unbox_usize(v_sz_506_);
lean_dec(v_sz_506_);
v_i_boxed_516_ = lean_unbox_usize(v_i_507_);
lean_dec(v_i_507_);
v_res_517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1(v_qs_503_, v___x_2134__boxed_514_, v_as_505_, v_sz_boxed_515_, v_i_boxed_516_, v_b_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec_ref(v_as_505_);
return v_res_517_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(lean_object* v_as_518_, size_t v_i_519_, size_t v_stop_520_, lean_object* v_b_521_){
_start:
{
lean_object* v___y_523_; uint8_t v___x_527_; 
v___x_527_ = lean_usize_dec_eq(v_i_519_, v_stop_520_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_array_uget_borrowed(v_as_518_, v_i_519_);
lean_inc(v___x_528_);
v___x_529_ = l_Lean_Expr_eta(v___x_528_);
if (lean_obj_tag(v___x_529_) == 2)
{
lean_object* v_mvarId_530_; lean_object* v___x_531_; 
v_mvarId_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_mvarId_530_);
lean_dec_ref_known(v___x_529_, 1);
v___x_531_ = lean_array_push(v_b_521_, v_mvarId_530_);
v___y_523_ = v___x_531_;
goto v___jp_522_;
}
else
{
lean_dec_ref(v___x_529_);
v___y_523_ = v_b_521_;
goto v___jp_522_;
}
}
else
{
return v_b_521_;
}
v___jp_522_:
{
size_t v___x_524_; size_t v___x_525_; 
v___x_524_ = ((size_t)1ULL);
v___x_525_ = lean_usize_add(v_i_519_, v___x_524_);
v_i_519_ = v___x_525_;
v_b_521_ = v___y_523_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_518_ = stack[0].m_obj;
size_t v_i_519_ = stack[1].m_num;
size_t v_stop_520_ = stack[2].m_num;
lean_object* v_b_521_ = stack[3].m_obj;
lean_object* v_res_532_;
v_res_532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_518_, v_i_519_, v_stop_520_, v_b_521_);
stack->m_obj
 = v_res_532_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0___boxed(lean_object* v_as_533_, lean_object* v_i_534_, lean_object* v_stop_535_, lean_object* v_b_536_){
_start:
{
size_t v_i_boxed_537_; size_t v_stop_boxed_538_; lean_object* v_res_539_; 
v_i_boxed_537_ = lean_unbox_usize(v_i_534_);
lean_dec(v_i_534_);
v_stop_boxed_538_ = lean_unbox_usize(v_stop_535_);
lean_dec(v_stop_535_);
v_res_539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_533_, v_i_boxed_537_, v_stop_boxed_538_, v_b_536_);
lean_dec_ref(v_as_533_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0(lean_object* v_as_542_, lean_object* v_start_543_, lean_object* v_stop_544_){
_start:
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0___closed__0));
v___x_546_ = lean_nat_dec_lt(v_start_543_, v_stop_544_);
if (v___x_546_ == 0)
{
return v___x_545_;
}
else
{
lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_547_ = lean_array_get_size(v_as_542_);
v___x_548_ = lean_nat_dec_le(v_stop_544_, v___x_547_);
if (v___x_548_ == 0)
{
uint8_t v___x_549_; 
v___x_549_ = lean_nat_dec_lt(v_start_543_, v___x_547_);
if (v___x_549_ == 0)
{
return v___x_545_;
}
else
{
size_t v___x_550_; size_t v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_usize_of_nat(v_start_543_);
v___x_551_ = lean_usize_of_nat(v___x_547_);
v___x_552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_542_, v___x_550_, v___x_551_, v___x_545_);
return v___x_552_;
}
}
else
{
size_t v___x_553_; size_t v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_usize_of_nat(v_start_543_);
v___x_554_ = lean_usize_of_nat(v_stop_544_);
v___x_555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_542_, v___x_553_, v___x_554_, v___x_545_);
return v___x_555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0___boxed(lean_object* v_as_556_, lean_object* v_start_557_, lean_object* v_stop_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0(v_as_556_, v_start_557_, v_stop_558_);
lean_dec(v_stop_558_);
lean_dec(v_start_557_);
lean_dec_ref(v_as_556_);
return v_res_559_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts(lean_object* v_concl_560_, lean_object* v_binders_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f(v_concl_560_);
if (lean_obj_tag(v___x_567_) == 1)
{
lean_object* v_val_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_626_; 
v_val_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_626_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_626_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_val_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_626_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_snd_572_; lean_object* v_snd_573_; lean_object* v_fst_574_; lean_object* v_fst_575_; lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v_qs_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_snd_572_ = lean_ctor_get(v_val_568_, 1);
lean_inc(v_snd_572_);
v_snd_573_ = lean_ctor_get(v_snd_572_, 1);
lean_inc(v_snd_573_);
v_fst_574_ = lean_ctor_get(v_val_568_, 0);
lean_inc(v_fst_574_);
lean_dec(v_val_568_);
v_fst_575_ = lean_ctor_get(v_snd_572_, 0);
lean_inc(v_fst_575_);
lean_dec(v_snd_572_);
v_fst_576_ = lean_ctor_get(v_snd_573_, 0);
lean_inc(v_fst_576_);
v_snd_577_ = lean_ctor_get(v_snd_573_, 1);
lean_inc(v_snd_577_);
lean_dec(v_snd_573_);
v___x_578_ = lean_unsigned_to_nat(2u);
v___x_579_ = lean_mk_empty_array_with_capacity(v___x_578_);
v___x_580_ = lean_array_push(v___x_579_, v_fst_576_);
v___x_581_ = lean_array_push(v___x_580_, v_snd_577_);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_array_get_size(v___x_581_);
v_qs_584_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0(v___x_581_, v___x_582_, v___x_583_);
lean_dec_ref(v___x_581_);
v___x_585_ = lean_array_get_size(v_qs_584_);
v___x_586_ = lean_nat_dec_eq(v___x_585_, v___x_582_);
if (v___x_586_ == 0)
{
uint8_t v___x_587_; 
lean_inc_ref(v_qs_584_);
v___x_587_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_584_, v_fst_575_);
lean_dec(v_fst_575_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; size_t v_sz_589_; size_t v___x_590_; lean_object* v___x_591_; 
lean_del_object(v___x_570_);
v___x_588_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___closed__0));
v_sz_589_ = lean_array_size(v_binders_561_);
v___x_590_ = ((size_t)0ULL);
lean_inc_ref(v_qs_584_);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1(v_qs_584_, v___x_587_, v_binders_561_, v_sz_589_, v___x_590_, v___x_588_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_608_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_608_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_608_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_608_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v_fst_596_; 
v_fst_596_ = lean_ctor_get(v_a_592_, 0);
lean_inc(v_fst_596_);
lean_dec(v_a_592_);
if (lean_obj_tag(v_fst_596_) == 0)
{
lean_object* v___x_597_; lean_object* v_env_598_; uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_597_ = lean_st_ref_get(v_a_565_);
v_env_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc_ref(v_env_598_);
lean_dec(v___x_597_);
v___x_599_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_env_598_, v_qs_584_, v_fst_574_);
v___x_600_ = lean_box(v___x_599_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_600_);
v___x_602_ = v___x_594_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
else
{
lean_object* v_val_604_; lean_object* v___x_606_; 
lean_dec_ref(v_qs_584_);
lean_dec(v_fst_574_);
v_val_604_ = lean_ctor_get(v_fst_596_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v_fst_596_, 1);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v_val_604_);
v___x_606_ = v___x_594_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_val_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v_qs_584_);
lean_dec(v_fst_574_);
v_a_609_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_591_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_591_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
else
{
lean_object* v___x_617_; lean_object* v___x_619_; 
lean_dec_ref(v_qs_584_);
lean_dec(v_fst_574_);
v___x_617_ = lean_box(v___x_586_);
if (v_isShared_571_ == 0)
{
lean_ctor_set_tag(v___x_570_, 0);
lean_ctor_set(v___x_570_, 0, v___x_617_);
v___x_619_ = v___x_570_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
else
{
uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
lean_dec_ref(v_qs_584_);
lean_dec(v_fst_575_);
lean_dec(v_fst_574_);
v___x_621_ = 0;
v___x_622_ = lean_box(v___x_621_);
if (v_isShared_571_ == 0)
{
lean_ctor_set_tag(v___x_570_, 0);
lean_ctor_set(v___x_570_, 0, v___x_622_);
v___x_624_ = v___x_570_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
else
{
uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec(v___x_567_);
v___x_627_ = 0;
v___x_628_ = lean_box(v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_0interp(lean_interpreter_value* stack)
{
lean_object* v_concl_560_ = stack[0].m_obj;
lean_object* v_binders_561_ = stack[1].m_obj;
lean_object* v_a_562_ = stack[2].m_obj;
lean_object* v_a_563_ = stack[3].m_obj;
lean_object* v_a_564_ = stack[4].m_obj;
lean_object* v_a_565_ = stack[5].m_obj;
lean_object* v_res_630_;
v_res_630_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts(v_concl_560_, v_binders_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
stack->m_obj
 = v_res_630_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts___boxed(lean_object* v_concl_631_, lean_object* v_binders_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts(v_concl_631_, v_binders_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec_ref(v_binders_632_);
return v_res_638_;
}
}
lean_object* runtime_initialize_Init_BinderNameHint(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
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
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
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
res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
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
