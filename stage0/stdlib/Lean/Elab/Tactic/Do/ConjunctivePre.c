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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___boxed(lean_object*);
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
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = l_Lean_Expr_appFnCleanup___redArg(v___x_23_);
v___x_27_ = l_Lean_Expr_isApp(v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; 
lean_dec_ref(v___x_26_);
lean_dec_ref(v___x_23_);
v___x_28_ = lean_box(0);
return v___x_28_;
}
else
{
lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = l_Lean_Expr_appFnCleanup___redArg(v___x_26_);
v___x_30_ = l_Lean_Expr_isApp(v___x_29_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; 
lean_dec_ref(v___x_29_);
lean_dec_ref(v___x_26_);
lean_dec_ref(v___x_23_);
v___x_31_ = lean_box(0);
return v___x_31_;
}
else
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = l_Lean_Expr_appFnCleanup___redArg(v___x_29_);
v___x_33_ = l_Lean_Expr_isApp(v___x_32_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
lean_dec_ref(v___x_32_);
lean_dec_ref(v___x_29_);
lean_dec_ref(v___x_26_);
lean_dec_ref(v___x_23_);
v___x_34_ = lean_box(0);
return v___x_34_;
}
else
{
lean_object* v_arg_35_; lean_object* v_arg_36_; lean_object* v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v_arg_35_ = lean_ctor_get(v___x_23_, 1);
lean_inc_ref(v_arg_35_);
lean_dec_ref(v___x_23_);
v_arg_36_ = lean_ctor_get(v___x_26_, 1);
lean_inc_ref(v_arg_36_);
lean_dec_ref(v___x_26_);
v___x_37_ = l_Lean_Expr_appFnCleanup___redArg(v___x_32_);
lean_dec_ref(v___x_32_);
v___x_38_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__4));
v___x_39_ = l_Lean_Expr_isConstOf(v___x_37_, v___x_38_);
if (v___x_39_ == 0)
{
uint8_t v___x_40_; 
v___x_40_ = l_Lean_Expr_isApp(v___x_37_);
if (v___x_40_ == 0)
{
lean_object* v___x_41_; 
lean_dec_ref(v___x_37_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v___x_29_);
v___x_41_ = lean_box(0);
return v___x_41_;
}
else
{
lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_42_ = l_Lean_Expr_appFnCleanup___redArg(v___x_37_);
v___x_43_ = l_Lean_Expr_isApp(v___x_42_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; 
lean_dec_ref(v___x_42_);
lean_dec_ref(v___x_37_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v___x_29_);
v___x_44_ = lean_box(0);
return v___x_44_;
}
else
{
lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_45_ = l_Lean_Expr_appFnCleanup___redArg(v___x_42_);
lean_dec_ref(v___x_42_);
v___x_46_ = l_Lean_Expr_isApp(v___x_45_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; 
lean_dec_ref(v___x_45_);
lean_dec_ref(v___x_37_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v___x_29_);
v___x_47_ = lean_box(0);
return v___x_47_;
}
else
{
lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = l_Lean_Expr_appFnCleanup___redArg(v___x_45_);
lean_dec_ref(v___x_45_);
v___x_49_ = l_Lean_Expr_isApp(v___x_48_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; 
lean_dec_ref(v___x_48_);
lean_dec_ref(v___x_37_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v___x_29_);
v___x_50_ = lean_box(0);
return v___x_50_;
}
else
{
lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_51_ = l_Lean_Expr_appFnCleanup___redArg(v___x_48_);
lean_dec_ref(v___x_48_);
v___x_52_ = l_Lean_Expr_isApp(v___x_51_);
if (v___x_52_ == 0)
{
lean_object* v___x_53_; 
lean_dec_ref(v___x_51_);
lean_dec_ref(v___x_37_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v___x_29_);
v___x_53_ = lean_box(0);
return v___x_53_;
}
else
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = l_Lean_Expr_appFnCleanup___redArg(v___x_51_);
lean_dec_ref(v___x_51_);
v___x_55_ = l_Lean_Expr_isApp(v___x_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; 
lean_dec_ref(v___x_54_);
lean_dec_ref(v___x_37_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v___x_29_);
v___x_56_ = lean_box(0);
return v___x_56_;
}
else
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = l_Lean_Expr_appFnCleanup___redArg(v___x_54_);
lean_dec_ref(v___x_54_);
v___x_58_ = l_Lean_Expr_isApp(v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; 
lean_dec_ref(v___x_57_);
lean_dec_ref(v___x_37_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v___x_29_);
v___x_59_ = lean_box(0);
return v___x_59_;
}
else
{
lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_60_ = l_Lean_Expr_appFnCleanup___redArg(v___x_57_);
lean_dec_ref(v___x_57_);
v___x_61_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__8));
v___x_62_ = l_Lean_Expr_isConstOf(v___x_60_, v___x_61_);
lean_dec_ref(v___x_60_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; 
lean_dec_ref(v___x_37_);
lean_dec_ref(v_arg_36_);
lean_dec_ref(v_arg_35_);
lean_dec_ref(v___x_29_);
v___x_63_ = lean_box(0);
return v___x_63_;
}
else
{
lean_object* v_arg_64_; lean_object* v_arg_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_arg_64_ = lean_ctor_get(v___x_29_, 1);
lean_inc_ref(v_arg_64_);
lean_dec_ref(v___x_29_);
v_arg_65_ = lean_ctor_get(v___x_37_, 1);
lean_inc_ref(v_arg_65_);
lean_dec_ref(v___x_37_);
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v_arg_36_);
lean_ctor_set(v___x_66_, 1, v_arg_35_);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v_arg_65_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_68_, 0, v_arg_64_);
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
lean_dec_ref(v___x_37_);
lean_dec_ref(v___x_29_);
v___x_70_ = l_Lean_Expr_cleanupAnnotations(v_arg_35_);
lean_dec_ref(v_arg_35_);
v___x_71_ = l_Lean_Expr_isApp(v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; 
lean_dec_ref(v___x_70_);
lean_dec_ref(v_arg_36_);
v___x_72_ = lean_box(0);
return v___x_72_;
}
else
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = l_Lean_Expr_appFnCleanup___redArg(v___x_70_);
v___x_74_ = l_Lean_Expr_isApp(v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
lean_dec_ref(v___x_73_);
lean_dec_ref(v___x_70_);
lean_dec_ref(v_arg_36_);
v___x_75_ = lean_box(0);
return v___x_75_;
}
else
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = l_Lean_Expr_appFnCleanup___redArg(v___x_73_);
v___x_77_ = l_Lean_Expr_isApp(v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; 
lean_dec_ref(v___x_76_);
lean_dec_ref(v___x_73_);
lean_dec_ref(v___x_70_);
lean_dec_ref(v_arg_36_);
v___x_78_ = lean_box(0);
return v___x_78_;
}
else
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = l_Lean_Expr_appFnCleanup___redArg(v___x_76_);
v___x_80_ = l_Lean_Expr_isApp(v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
lean_dec_ref(v___x_79_);
lean_dec_ref(v___x_76_);
lean_dec_ref(v___x_73_);
lean_dec_ref(v___x_70_);
lean_dec_ref(v_arg_36_);
v___x_81_ = lean_box(0);
return v___x_81_;
}
else
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = l_Lean_Expr_appFnCleanup___redArg(v___x_79_);
lean_dec_ref(v___x_79_);
v___x_83_ = l_Lean_Expr_isApp(v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
lean_dec_ref(v___x_82_);
lean_dec_ref(v___x_76_);
lean_dec_ref(v___x_73_);
lean_dec_ref(v___x_70_);
lean_dec_ref(v_arg_36_);
v___x_84_ = lean_box(0);
return v___x_84_;
}
else
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = l_Lean_Expr_appFnCleanup___redArg(v___x_82_);
lean_dec_ref(v___x_82_);
v___x_86_ = l_Lean_Expr_isApp(v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; 
lean_dec_ref(v___x_85_);
lean_dec_ref(v___x_76_);
lean_dec_ref(v___x_73_);
lean_dec_ref(v___x_70_);
lean_dec_ref(v_arg_36_);
v___x_87_ = lean_box(0);
return v___x_87_;
}
else
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = l_Lean_Expr_appFnCleanup___redArg(v___x_85_);
lean_dec_ref(v___x_85_);
v___x_89_ = l_Lean_Expr_isApp(v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
lean_dec_ref(v___x_88_);
lean_dec_ref(v___x_76_);
lean_dec_ref(v___x_73_);
lean_dec_ref(v___x_70_);
lean_dec_ref(v_arg_36_);
v___x_90_ = lean_box(0);
return v___x_90_;
}
else
{
lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_91_ = l_Lean_Expr_appFnCleanup___redArg(v___x_88_);
lean_dec_ref(v___x_88_);
v___x_92_ = l_Lean_Expr_isApp(v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
lean_dec_ref(v___x_91_);
lean_dec_ref(v___x_76_);
lean_dec_ref(v___x_73_);
lean_dec_ref(v___x_70_);
lean_dec_ref(v_arg_36_);
v___x_93_ = lean_box(0);
return v___x_93_;
}
else
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = l_Lean_Expr_appFnCleanup___redArg(v___x_91_);
lean_dec_ref(v___x_91_);
v___x_95_ = l_Lean_Expr_isApp(v___x_94_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
lean_dec_ref(v___x_94_);
lean_dec_ref(v___x_76_);
lean_dec_ref(v___x_73_);
lean_dec_ref(v___x_70_);
lean_dec_ref(v_arg_36_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
else
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = l_Lean_Expr_appFnCleanup___redArg(v___x_94_);
lean_dec_ref(v___x_94_);
v___x_98_ = l_Lean_Expr_isApp(v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; 
lean_dec_ref(v___x_97_);
lean_dec_ref(v___x_76_);
lean_dec_ref(v___x_73_);
lean_dec_ref(v___x_70_);
lean_dec_ref(v_arg_36_);
v___x_99_ = lean_box(0);
return v___x_99_;
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_97_);
lean_dec_ref(v___x_97_);
v___x_101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__10));
v___x_102_ = l_Lean_Expr_isConstOf(v___x_100_, v___x_101_);
lean_dec_ref(v___x_100_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
lean_dec_ref(v___x_76_);
lean_dec_ref(v___x_73_);
lean_dec_ref(v___x_70_);
lean_dec_ref(v_arg_36_);
v___x_103_ = lean_box(0);
return v___x_103_;
}
else
{
lean_object* v_arg_104_; lean_object* v_arg_105_; lean_object* v_arg_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_arg_104_ = lean_ctor_get(v___x_70_, 1);
lean_inc_ref(v_arg_104_);
lean_dec_ref(v___x_70_);
v_arg_105_ = lean_ctor_get(v___x_73_, 1);
lean_inc_ref(v_arg_105_);
lean_dec_ref(v___x_73_);
v_arg_106_ = lean_ctor_get(v___x_76_, 1);
lean_inc_ref(v_arg_106_);
lean_dec_ref(v___x_76_);
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v_arg_105_);
lean_ctor_set(v___x_107_, 1, v_arg_104_);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v_arg_106_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v_arg_36_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___boxed(lean_object* v_concl_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f(v_concl_111_);
lean_dec_ref(v_concl_111_);
return v_res_112_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0(lean_object* v_a_113_, lean_object* v_as_114_, size_t v_i_115_, size_t v_stop_116_){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = lean_usize_dec_eq(v_i_115_, v_stop_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_array_uget_borrowed(v_as_114_, v_i_115_);
v___x_119_ = l_Lean_instBEqMVarId_beq(v_a_113_, v___x_118_);
if (v___x_119_ == 0)
{
size_t v___x_120_; size_t v___x_121_; 
v___x_120_ = ((size_t)1ULL);
v___x_121_ = lean_usize_add(v_i_115_, v___x_120_);
v_i_115_ = v___x_121_;
goto _start;
}
else
{
return v___x_119_;
}
}
else
{
uint8_t v___x_123_; 
v___x_123_ = 0;
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0___boxed(lean_object* v_a_124_, lean_object* v_as_125_, lean_object* v_i_126_, lean_object* v_stop_127_){
_start:
{
size_t v_i_boxed_128_; size_t v_stop_boxed_129_; uint8_t v_res_130_; lean_object* v_r_131_; 
v_i_boxed_128_ = lean_unbox_usize(v_i_126_);
lean_dec(v_i_126_);
v_stop_boxed_129_ = lean_unbox_usize(v_stop_127_);
lean_dec(v_stop_127_);
v_res_130_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0(v_a_124_, v_as_125_, v_i_boxed_128_, v_stop_boxed_129_);
lean_dec_ref(v_as_125_);
lean_dec(v_a_124_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(lean_object* v_as_132_, lean_object* v_a_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_array_get_size(v_as_132_);
v___x_136_ = lean_nat_dec_lt(v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
return v___x_136_;
}
else
{
size_t v___x_137_; size_t v___x_138_; uint8_t v___x_139_; 
v___x_137_ = ((size_t)0ULL);
v___x_138_ = lean_usize_of_nat(v___x_135_);
v___x_139_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0_spec__0(v_a_133_, v_as_132_, v___x_137_, v___x_138_);
return v___x_139_;
}
}
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
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0(lean_object* v_mvarIds_144_, lean_object* v_s_145_){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0___boxed(lean_object* v_mvarIds_149_, lean_object* v_s_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0(v_mvarIds_149_, v_s_150_);
lean_dec_ref(v_s_150_);
lean_dec_ref(v_mvarIds_149_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(lean_object* v_mvarIds_153_, lean_object* v_e_154_){
_start:
{
lean_object* v___f_155_; lean_object* v___x_156_; 
v___f_155_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___lam__0___boxed), 2, 1);
lean_closure_set(v___f_155_, 0, v_mvarIds_153_);
v___x_156_ = lean_find_expr(v___f_155_, v_e_154_);
lean_dec_ref(v___f_155_);
if (lean_obj_tag(v___x_156_) == 0)
{
uint8_t v___x_157_; 
v___x_157_ = 0;
return v___x_157_;
}
else
{
uint8_t v___x_158_; 
lean_dec_ref_known(v___x_156_, 1);
v___x_158_ = 1;
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar___boxed(lean_object* v_mvarIds_159_, lean_object* v_e_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_mvarIds_159_, v_e_160_);
lean_dec_ref(v_e_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f(lean_object* v_env_240_, lean_object* v_x_241_){
_start:
{
lean_object* v_c_243_; 
if (lean_obj_tag(v_x_241_) == 1)
{
lean_object* v_pre_270_; 
v_pre_270_ = lean_ctor_get(v_x_241_, 0);
switch(lean_obj_tag(v_pre_270_))
{
case 1:
{
lean_object* v_pre_271_; 
v_pre_271_ = lean_ctor_get(v_pre_270_, 0);
switch(lean_obj_tag(v_pre_271_))
{
case 1:
{
lean_object* v_pre_272_; 
v_pre_272_ = lean_ctor_get(v_pre_271_, 0);
switch(lean_obj_tag(v_pre_272_))
{
case 0:
{
lean_object* v_str_273_; lean_object* v_str_274_; lean_object* v_str_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v_str_273_ = lean_ctor_get(v_x_241_, 1);
v_str_274_ = lean_ctor_get(v_pre_270_, 1);
v_str_275_ = lean_ctor_get(v_pre_271_, 1);
v___x_276_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__0));
v___x_277_ = lean_string_dec_eq(v_str_275_, v___x_276_);
if (v___x_277_ == 0)
{
v_c_243_ = v_x_241_;
goto v___jp_242_;
}
else
{
lean_object* v___x_278_; uint8_t v___x_279_; 
lean_inc_ref(v_str_274_);
lean_inc(v_pre_272_);
lean_inc_ref(v_str_273_);
lean_dec_ref_known(v_x_241_, 2);
v___x_278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__1));
v___x_279_ = lean_string_dec_eq(v_str_274_, v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = l_Lean_Name_str___override(v_pre_272_, v___x_276_);
v___x_281_ = l_Lean_Name_str___override(v___x_280_, v_str_274_);
v___x_282_ = l_Lean_Name_str___override(v___x_281_, v_str_273_);
v_c_243_ = v___x_282_;
goto v___jp_242_;
}
else
{
lean_object* v___x_283_; uint8_t v___x_284_; 
lean_dec_ref(v_str_274_);
v___x_283_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__13));
v___x_284_ = lean_string_dec_eq(v_str_273_, v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__14));
v___x_286_ = lean_string_dec_eq(v_str_273_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__15));
v___x_288_ = lean_string_dec_eq(v_str_273_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = l_Lean_Name_str___override(v_pre_272_, v___x_276_);
v___x_290_ = l_Lean_Name_str___override(v___x_289_, v___x_278_);
v___x_291_ = l_Lean_Name_str___override(v___x_290_, v_str_273_);
v_c_243_ = v___x_291_;
goto v___jp_242_;
}
else
{
lean_dec_ref(v_str_273_);
lean_dec_ref(v_env_240_);
goto v___jp_264_;
}
}
else
{
lean_dec_ref(v_str_273_);
lean_dec_ref(v_env_240_);
goto v___jp_264_;
}
}
else
{
lean_dec_ref(v_str_273_);
lean_dec_ref(v_env_240_);
goto v___jp_262_;
}
}
}
}
case 1:
{
lean_object* v_pre_292_; 
v_pre_292_ = lean_ctor_get(v_pre_272_, 0);
if (lean_obj_tag(v_pre_292_) == 0)
{
lean_object* v_str_293_; lean_object* v_str_294_; lean_object* v_str_295_; lean_object* v_str_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v_str_293_ = lean_ctor_get(v_x_241_, 1);
v_str_294_ = lean_ctor_get(v_pre_270_, 1);
v_str_295_ = lean_ctor_get(v_pre_271_, 1);
v_str_296_ = lean_ctor_get(v_pre_272_, 1);
v___x_297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__5));
v___x_298_ = lean_string_dec_eq(v_str_296_, v___x_297_);
if (v___x_298_ == 0)
{
v_c_243_ = v_x_241_;
goto v___jp_242_;
}
else
{
lean_object* v___x_299_; uint8_t v___x_300_; 
lean_inc_ref(v_str_295_);
lean_inc_ref(v_str_294_);
lean_inc(v_pre_292_);
lean_inc_ref(v_str_293_);
lean_dec_ref_known(v_x_241_, 2);
v___x_299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__6));
v___x_300_ = lean_string_dec_eq(v_str_295_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_301_ = l_Lean_Name_str___override(v_pre_292_, v___x_297_);
v___x_302_ = l_Lean_Name_str___override(v___x_301_, v_str_295_);
v___x_303_ = l_Lean_Name_str___override(v___x_302_, v_str_294_);
v___x_304_ = l_Lean_Name_str___override(v___x_303_, v_str_293_);
v_c_243_ = v___x_304_;
goto v___jp_242_;
}
else
{
uint8_t v___x_305_; 
lean_dec_ref(v_str_295_);
v___x_305_ = lean_string_dec_eq(v_str_294_, v___x_299_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_306_ = l_Lean_Name_str___override(v_pre_292_, v___x_297_);
v___x_307_ = l_Lean_Name_str___override(v___x_306_, v___x_299_);
v___x_308_ = l_Lean_Name_str___override(v___x_307_, v_str_294_);
v___x_309_ = l_Lean_Name_str___override(v___x_308_, v_str_293_);
v_c_243_ = v___x_309_;
goto v___jp_242_;
}
else
{
lean_object* v___x_310_; uint8_t v___x_311_; 
lean_dec_ref(v_str_294_);
v___x_310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f___closed__9));
v___x_311_ = lean_string_dec_eq(v_str_293_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_312_ = l_Lean_Name_str___override(v_pre_292_, v___x_297_);
v___x_313_ = l_Lean_Name_str___override(v___x_312_, v___x_299_);
v___x_314_ = l_Lean_Name_str___override(v___x_313_, v___x_299_);
v___x_315_ = l_Lean_Name_str___override(v___x_314_, v_str_293_);
v_c_243_ = v___x_315_;
goto v___jp_242_;
}
else
{
lean_object* v___x_316_; 
lean_dec_ref(v_str_293_);
lean_dec_ref(v_env_240_);
v___x_316_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__19));
return v___x_316_;
}
}
}
}
}
else
{
v_c_243_ = v_x_241_;
goto v___jp_242_;
}
}
default: 
{
v_c_243_ = v_x_241_;
goto v___jp_242_;
}
}
}
case 0:
{
lean_object* v_str_317_; lean_object* v_str_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_str_317_ = lean_ctor_get(v_x_241_, 1);
v_str_318_ = lean_ctor_get(v_pre_270_, 1);
v___x_319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__20));
v___x_320_ = lean_string_dec_eq(v_str_318_, v___x_319_);
if (v___x_320_ == 0)
{
v_c_243_ = v_x_241_;
goto v___jp_242_;
}
else
{
lean_object* v___x_321_; uint8_t v___x_322_; 
lean_inc_ref(v_str_317_);
lean_inc(v_pre_271_);
lean_dec_ref_known(v_x_241_, 2);
v___x_321_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__21));
v___x_322_ = lean_string_dec_eq(v_str_317_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__22));
v___x_324_ = lean_string_dec_eq(v_str_317_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__23));
v___x_326_ = lean_string_dec_eq(v_str_317_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = l_Lean_Name_str___override(v_pre_271_, v___x_319_);
v___x_328_ = l_Lean_Name_str___override(v___x_327_, v_str_317_);
v_c_243_ = v___x_328_;
goto v___jp_242_;
}
else
{
lean_dec_ref(v_str_317_);
lean_dec_ref(v_env_240_);
goto v___jp_262_;
}
}
else
{
lean_dec_ref(v_str_317_);
lean_dec_ref(v_env_240_);
goto v___jp_266_;
}
}
else
{
lean_dec_ref(v_str_317_);
lean_dec_ref(v_env_240_);
goto v___jp_266_;
}
}
}
default: 
{
v_c_243_ = v_x_241_;
goto v___jp_242_;
}
}
}
case 0:
{
lean_object* v_str_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_str_329_ = lean_ctor_get(v_x_241_, 1);
v___x_330_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__24));
v___x_331_ = lean_string_dec_eq(v_str_329_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__25));
v___x_333_ = lean_string_dec_eq(v_str_329_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__26));
v___x_335_ = lean_string_dec_eq(v_str_329_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__27));
v___x_337_ = lean_string_dec_eq(v_str_329_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__28));
v___x_339_ = lean_string_dec_eq(v_str_329_, v___x_338_);
if (v___x_339_ == 0)
{
v_c_243_ = v_x_241_;
goto v___jp_242_;
}
else
{
lean_object* v___x_340_; 
lean_dec_ref_known(v_x_241_, 2);
lean_dec_ref(v_env_240_);
v___x_340_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__31));
return v___x_340_;
}
}
else
{
lean_dec_ref_known(v_x_241_, 2);
lean_dec_ref(v_env_240_);
goto v___jp_262_;
}
}
else
{
lean_dec_ref_known(v_x_241_, 2);
lean_dec_ref(v_env_240_);
goto v___jp_268_;
}
}
else
{
lean_dec_ref_known(v_x_241_, 2);
lean_dec_ref(v_env_240_);
goto v___jp_268_;
}
}
else
{
lean_object* v___x_341_; 
lean_dec_ref_known(v_x_241_, 2);
lean_dec_ref(v_env_240_);
v___x_341_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__35));
return v___x_341_;
}
}
default: 
{
v_c_243_ = v_x_241_;
goto v___jp_242_;
}
}
}
else
{
v_c_243_ = v_x_241_;
goto v___jp_242_;
}
v___jp_242_:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Meta_getMatcherInfoCore_x3f(v_env_240_, v_c_243_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v___x_245_; 
v___x_245_ = lean_box(0);
return v___x_245_;
}
else
{
lean_object* v_val_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_261_; 
v_val_246_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_261_ == 0)
{
v___x_248_ = v___x_244_;
v_isShared_249_ = v_isSharedCheck_261_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_val_246_);
lean_dec(v___x_244_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_261_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_250_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_246_);
v___x_251_ = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(v_val_246_);
v___x_252_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_246_);
lean_dec(v_val_246_);
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_nat_add(v___x_251_, v___x_252_);
lean_dec(v___x_251_);
v___x_255_ = lean_box(0);
v___x_256_ = l_List_range_x27TR_go(v___x_253_, v___x_252_, v___x_254_, v___x_255_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_250_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_257_);
v___x_259_ = v___x_248_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
v___jp_262_:
{
lean_object* v___x_263_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__3));
return v___x_263_;
}
v___jp_264_:
{
lean_object* v___x_265_; 
v___x_265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__5));
return v___x_265_;
}
v___jp_266_:
{
lean_object* v___x_267_; 
v___x_267_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__8));
return v___x_267_;
}
v___jp_268_:
{
lean_object* v___x_269_; 
v___x_269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f___closed__12));
return v___x_269_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0(lean_object* v_qs_342_, uint8_t v___x_343_, lean_object* v_as_344_, size_t v_i_345_, size_t v_stop_346_){
_start:
{
uint8_t v___x_351_; 
v___x_351_ = lean_usize_dec_eq(v_i_345_, v_stop_346_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_array_uget_borrowed(v_as_344_, v_i_345_);
lean_inc_ref(v_qs_342_);
v___x_353_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_342_, v___x_352_);
if (v___x_353_ == 0)
{
goto v___jp_347_;
}
else
{
if (v___x_343_ == 0)
{
goto v___jp_347_;
}
else
{
lean_dec_ref(v_qs_342_);
return v___x_343_;
}
}
}
else
{
uint8_t v___x_354_; 
lean_dec_ref(v_qs_342_);
v___x_354_ = 0;
return v___x_354_;
}
v___jp_347_:
{
size_t v___x_348_; size_t v___x_349_; 
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_add(v_i_345_, v___x_348_);
v_i_345_ = v___x_349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0___boxed(lean_object* v_qs_355_, lean_object* v___x_356_, lean_object* v_as_357_, lean_object* v_i_358_, lean_object* v_stop_359_){
_start:
{
uint8_t v___x_796__boxed_360_; size_t v_i_boxed_361_; size_t v_stop_boxed_362_; uint8_t v_res_363_; lean_object* v_r_364_; 
v___x_796__boxed_360_ = lean_unbox(v___x_356_);
v_i_boxed_361_ = lean_unbox_usize(v_i_358_);
lean_dec(v_i_358_);
v_stop_boxed_362_ = lean_unbox_usize(v_stop_359_);
lean_dec(v_stop_359_);
v_res_363_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0(v_qs_355_, v___x_796__boxed_360_, v_as_357_, v_i_boxed_361_, v_stop_boxed_362_);
lean_dec_ref(v_as_357_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1(lean_object* v_a_365_, lean_object* v_x_366_){
_start:
{
if (lean_obj_tag(v_x_366_) == 0)
{
uint8_t v___x_367_; 
v___x_367_ = 0;
return v___x_367_;
}
else
{
lean_object* v_head_368_; lean_object* v_tail_369_; uint8_t v___x_370_; 
v_head_368_ = lean_ctor_get(v_x_366_, 0);
v_tail_369_ = lean_ctor_get(v_x_366_, 1);
v___x_370_ = lean_nat_dec_eq(v_a_365_, v_head_368_);
if (v___x_370_ == 0)
{
v_x_366_ = v_tail_369_;
goto _start;
}
else
{
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1___boxed(lean_object* v_a_372_, lean_object* v_x_373_){
_start:
{
uint8_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = l_List_elem___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1(v_a_372_, v_x_373_);
lean_dec(v_x_373_);
lean_dec(v_a_372_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__0(void){
_start:
{
lean_object* v___x_376_; lean_object* v_dummy_377_; 
v___x_376_ = lean_box(0);
v_dummy_377_ = l_Lean_Expr_sort___override(v___x_376_);
return v_dummy_377_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(lean_object* v_env_378_, lean_object* v_qs_379_, lean_object* v_e_380_){
_start:
{
uint8_t v___x_381_; 
lean_inc_ref(v_qs_379_);
v___x_381_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_379_, v_e_380_);
if (v___x_381_ == 0)
{
uint8_t v___x_382_; 
lean_dec_ref(v_e_380_);
lean_dec_ref(v_qs_379_);
lean_dec_ref(v_env_378_);
v___x_382_ = 1;
return v___x_382_;
}
else
{
uint8_t v___x_383_; lean_object* v_dom_385_; lean_object* v_body_386_; 
v___x_383_ = 0;
switch(lean_obj_tag(v_e_380_))
{
case 10:
{
lean_object* v_expr_389_; 
v_expr_389_ = lean_ctor_get(v_e_380_, 1);
lean_inc_ref(v_expr_389_);
lean_dec_ref_known(v_e_380_, 2);
v_e_380_ = v_expr_389_;
goto _start;
}
case 6:
{
lean_object* v_binderType_391_; lean_object* v_body_392_; 
v_binderType_391_ = lean_ctor_get(v_e_380_, 1);
lean_inc_ref(v_binderType_391_);
v_body_392_ = lean_ctor_get(v_e_380_, 2);
lean_inc_ref(v_body_392_);
lean_dec_ref_known(v_e_380_, 3);
v_dom_385_ = v_binderType_391_;
v_body_386_ = v_body_392_;
goto v___jp_384_;
}
case 7:
{
lean_object* v_binderType_393_; lean_object* v_body_394_; 
v_binderType_393_ = lean_ctor_get(v_e_380_, 1);
lean_inc_ref(v_binderType_393_);
v_body_394_ = lean_ctor_get(v_e_380_, 2);
lean_inc_ref(v_body_394_);
lean_dec_ref_known(v_e_380_, 3);
v_dom_385_ = v_binderType_393_;
v_body_386_ = v_body_394_;
goto v___jp_384_;
}
default: 
{
lean_object* v_dummy_395_; lean_object* v_nargs_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v_args_400_; lean_object* v___x_401_; 
v_dummy_395_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__0, &l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___closed__0);
v_nargs_396_ = l_Lean_Expr_getAppNumArgs(v_e_380_);
lean_inc(v_nargs_396_);
v___x_397_ = lean_mk_array(v_nargs_396_, v_dummy_395_);
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_nat_sub(v_nargs_396_, v___x_398_);
lean_dec(v_nargs_396_);
lean_inc_ref(v_e_380_);
v_args_400_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_380_, v___x_397_, v___x_399_);
v___x_401_ = l_Lean_Expr_getAppFn(v_e_380_);
lean_dec_ref(v_e_380_);
switch(lean_obj_tag(v___x_401_))
{
case 2:
{
lean_object* v_mvarId_402_; uint8_t v___x_403_; 
lean_dec_ref(v_env_378_);
v_mvarId_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_mvarId_402_);
lean_dec_ref_known(v___x_401_, 1);
v___x_403_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar_spec__0(v_qs_379_, v_mvarId_402_);
lean_dec(v_mvarId_402_);
if (v___x_403_ == 0)
{
lean_dec_ref(v_args_400_);
lean_dec_ref(v_qs_379_);
return v___x_383_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_array_get_size(v_args_400_);
v___x_406_ = lean_nat_dec_lt(v___x_404_, v___x_405_);
if (v___x_406_ == 0)
{
lean_dec_ref(v_args_400_);
lean_dec_ref(v_qs_379_);
return v___x_403_;
}
else
{
if (v___x_406_ == 0)
{
lean_dec_ref(v_args_400_);
lean_dec_ref(v_qs_379_);
return v___x_403_;
}
else
{
size_t v___x_407_; size_t v___x_408_; uint8_t v___x_409_; 
v___x_407_ = ((size_t)0ULL);
v___x_408_ = lean_usize_of_nat(v___x_405_);
v___x_409_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__0(v_qs_379_, v___x_403_, v_args_400_, v___x_407_, v___x_408_);
lean_dec_ref(v_args_400_);
if (v___x_409_ == 0)
{
return v___x_406_;
}
else
{
return v___x_383_;
}
}
}
}
}
case 4:
{
lean_object* v_declName_410_; lean_object* v___x_411_; 
v_declName_410_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_declName_410_);
lean_dec_ref_known(v___x_401_, 2);
lean_inc_ref(v_env_378_);
v___x_411_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_conjunctiveArgs_x3f(v_env_378_, v_declName_410_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_dec_ref(v_args_400_);
lean_dec_ref(v_qs_379_);
lean_dec_ref(v_env_378_);
return v___x_383_;
}
else
{
lean_object* v_val_412_; lean_object* v_fst_413_; lean_object* v_snd_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v_val_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_val_412_);
lean_dec_ref_known(v___x_411_, 1);
v_fst_413_ = lean_ctor_get(v_val_412_, 0);
lean_inc(v_fst_413_);
v_snd_414_ = lean_ctor_get(v_val_412_, 1);
lean_inc(v_snd_414_);
lean_dec(v_val_412_);
v___x_415_ = lean_array_get_size(v_args_400_);
v___x_416_ = lean_nat_dec_le(v_fst_413_, v___x_415_);
if (v___x_416_ == 0)
{
lean_dec(v_snd_414_);
lean_dec(v_fst_413_);
lean_dec_ref(v_args_400_);
lean_dec_ref(v_qs_379_);
lean_dec_ref(v_env_378_);
return v___x_383_;
}
else
{
lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_417_ = l_List_range(v___x_415_);
v___x_418_ = l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__2(v_snd_414_, v_args_400_, v_qs_379_, v_fst_413_, v___x_415_, v_env_378_, v___x_417_);
lean_dec(v___x_417_);
lean_dec(v_fst_413_);
lean_dec_ref(v_args_400_);
lean_dec(v_snd_414_);
return v___x_418_;
}
}
}
default: 
{
lean_dec_ref(v___x_401_);
lean_dec_ref(v_args_400_);
lean_dec_ref(v_qs_379_);
lean_dec_ref(v_env_378_);
return v___x_383_;
}
}
}
}
v___jp_384_:
{
uint8_t v___x_387_; 
lean_inc_ref(v_qs_379_);
v___x_387_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_379_, v_dom_385_);
lean_dec_ref(v_dom_385_);
if (v___x_387_ == 0)
{
v_e_380_ = v_body_386_;
goto _start;
}
else
{
lean_dec_ref(v_body_386_);
lean_dec_ref(v_qs_379_);
lean_dec_ref(v_env_378_);
return v___x_383_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__2(lean_object* v_snd_419_, lean_object* v_args_420_, lean_object* v_qs_421_, lean_object* v_fst_422_, lean_object* v___x_423_, lean_object* v_env_424_, lean_object* v_x_425_){
_start:
{
if (lean_obj_tag(v_x_425_) == 0)
{
uint8_t v___x_426_; 
lean_dec_ref(v_env_424_);
lean_dec_ref(v_qs_421_);
v___x_426_ = 1;
return v___x_426_;
}
else
{
lean_object* v_head_427_; lean_object* v_tail_428_; uint8_t v___y_430_; lean_object* v___x_432_; uint8_t v___x_433_; 
v_head_427_ = lean_ctor_get(v_x_425_, 0);
v_tail_428_ = lean_ctor_get(v_x_425_, 1);
v___x_432_ = l_Lean_instInhabitedExpr;
v___x_433_ = l_List_elem___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__1(v_head_427_, v_snd_419_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_array_get_borrowed(v___x_432_, v_args_420_, v_head_427_);
lean_inc_ref(v_qs_421_);
v___x_435_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_421_, v___x_434_);
if (v___x_435_ == 0)
{
uint8_t v___x_436_; 
v___x_436_ = lean_nat_dec_le(v_fst_422_, v___x_423_);
v___y_430_ = v___x_436_;
goto v___jp_429_;
}
else
{
lean_dec_ref(v_env_424_);
lean_dec_ref(v_qs_421_);
return v___x_433_;
}
}
else
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_array_get_borrowed(v___x_432_, v_args_420_, v_head_427_);
lean_inc(v___x_437_);
lean_inc_ref(v_qs_421_);
lean_inc_ref(v_env_424_);
v___x_438_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_env_424_, v_qs_421_, v___x_437_);
v___y_430_ = v___x_438_;
goto v___jp_429_;
}
v___jp_429_:
{
if (v___y_430_ == 0)
{
lean_dec_ref(v_env_424_);
lean_dec_ref(v_qs_421_);
return v___y_430_;
}
else
{
v_x_425_ = v_tail_428_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__2___boxed(lean_object* v_snd_439_, lean_object* v_args_440_, lean_object* v_qs_441_, lean_object* v_fst_442_, lean_object* v___x_443_, lean_object* v_env_444_, lean_object* v_x_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_List_all___at___00__private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn_spec__2(v_snd_439_, v_args_440_, v_qs_441_, v_fst_442_, v___x_443_, v_env_444_, v_x_445_);
lean_dec(v_x_445_);
lean_dec(v___x_443_);
lean_dec(v_fst_442_);
lean_dec_ref(v_args_440_);
lean_dec(v_snd_439_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn___boxed(lean_object* v_env_448_, lean_object* v_qs_449_, lean_object* v_e_450_){
_start:
{
uint8_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_env_448_, v_qs_449_, v_e_450_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1(lean_object* v_qs_456_, uint8_t v___x_457_, lean_object* v_as_458_, size_t v_sz_459_, size_t v_i_460_, lean_object* v_b_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
uint8_t v___x_467_; 
v___x_467_ = lean_usize_dec_lt(v_i_460_, v_sz_459_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
lean_dec_ref(v_qs_456_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v_b_461_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v_a_471_; lean_object* v___x_472_; 
lean_dec_ref(v_b_461_);
v___x_469_ = lean_box(0);
v___x_470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___closed__0));
v_a_471_ = lean_array_uget_borrowed(v_as_458_, v_i_460_);
lean_inc(v___y_465_);
lean_inc_ref(v___y_464_);
lean_inc(v___y_463_);
lean_inc_ref(v___y_462_);
lean_inc(v_a_471_);
v___x_472_ = lean_infer_type(v_a_471_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_487_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_487_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_487_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_487_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
uint8_t v___x_477_; 
lean_inc_ref(v_qs_456_);
v___x_477_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_456_, v_a_473_);
lean_dec(v_a_473_);
if (v___x_477_ == 0)
{
size_t v___x_478_; size_t v___x_479_; 
lean_del_object(v___x_475_);
v___x_478_ = ((size_t)1ULL);
v___x_479_ = lean_usize_add(v_i_460_, v___x_478_);
v_i_460_ = v___x_479_;
v_b_461_ = v___x_470_;
goto _start;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec_ref(v_qs_456_);
v___x_481_ = lean_box(v___x_457_);
v___x_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___x_469_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_483_);
v___x_485_ = v___x_475_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v_qs_456_);
v_a_488_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_472_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_472_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___boxed(lean_object* v_qs_496_, lean_object* v___x_497_, lean_object* v_as_498_, lean_object* v_sz_499_, lean_object* v_i_500_, lean_object* v_b_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
uint8_t v___x_2138__boxed_507_; size_t v_sz_boxed_508_; size_t v_i_boxed_509_; lean_object* v_res_510_; 
v___x_2138__boxed_507_ = lean_unbox(v___x_497_);
v_sz_boxed_508_ = lean_unbox_usize(v_sz_499_);
lean_dec(v_sz_499_);
v_i_boxed_509_ = lean_unbox_usize(v_i_500_);
lean_dec(v_i_500_);
v_res_510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1(v_qs_496_, v___x_2138__boxed_507_, v_as_498_, v_sz_boxed_508_, v_i_boxed_509_, v_b_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec_ref(v_as_498_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(lean_object* v_as_511_, size_t v_i_512_, size_t v_stop_513_, lean_object* v_b_514_){
_start:
{
lean_object* v___y_516_; uint8_t v___x_520_; 
v___x_520_ = lean_usize_dec_eq(v_i_512_, v_stop_513_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_array_uget_borrowed(v_as_511_, v_i_512_);
lean_inc(v___x_521_);
v___x_522_ = l_Lean_Expr_eta(v___x_521_);
if (lean_obj_tag(v___x_522_) == 2)
{
lean_object* v_mvarId_523_; lean_object* v___x_524_; 
v_mvarId_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_mvarId_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = lean_array_push(v_b_514_, v_mvarId_523_);
v___y_516_ = v___x_524_;
goto v___jp_515_;
}
else
{
lean_dec_ref(v___x_522_);
v___y_516_ = v_b_514_;
goto v___jp_515_;
}
}
else
{
return v_b_514_;
}
v___jp_515_:
{
size_t v___x_517_; size_t v___x_518_; 
v___x_517_ = ((size_t)1ULL);
v___x_518_ = lean_usize_add(v_i_512_, v___x_517_);
v_i_512_ = v___x_518_;
v_b_514_ = v___y_516_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0___boxed(lean_object* v_as_525_, lean_object* v_i_526_, lean_object* v_stop_527_, lean_object* v_b_528_){
_start:
{
size_t v_i_boxed_529_; size_t v_stop_boxed_530_; lean_object* v_res_531_; 
v_i_boxed_529_ = lean_unbox_usize(v_i_526_);
lean_dec(v_i_526_);
v_stop_boxed_530_ = lean_unbox_usize(v_stop_527_);
lean_dec(v_stop_527_);
v_res_531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_525_, v_i_boxed_529_, v_stop_boxed_530_, v_b_528_);
lean_dec_ref(v_as_525_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0(lean_object* v_as_534_, lean_object* v_start_535_, lean_object* v_stop_536_){
_start:
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0___closed__0));
v___x_538_ = lean_nat_dec_lt(v_start_535_, v_stop_536_);
if (v___x_538_ == 0)
{
return v___x_537_;
}
else
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = lean_array_get_size(v_as_534_);
v___x_540_ = lean_nat_dec_le(v_stop_536_, v___x_539_);
if (v___x_540_ == 0)
{
uint8_t v___x_541_; 
v___x_541_ = lean_nat_dec_lt(v_start_535_, v___x_539_);
if (v___x_541_ == 0)
{
return v___x_537_;
}
else
{
size_t v___x_542_; size_t v___x_543_; lean_object* v___x_544_; 
v___x_542_ = lean_usize_of_nat(v_start_535_);
v___x_543_ = lean_usize_of_nat(v___x_539_);
v___x_544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_534_, v___x_542_, v___x_543_, v___x_537_);
return v___x_544_;
}
}
else
{
size_t v___x_545_; size_t v___x_546_; lean_object* v___x_547_; 
v___x_545_ = lean_usize_of_nat(v_start_535_);
v___x_546_ = lean_usize_of_nat(v_stop_536_);
v___x_547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0_spec__0(v_as_534_, v___x_545_, v___x_546_, v___x_537_);
return v___x_547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0___boxed(lean_object* v_as_548_, lean_object* v_start_549_, lean_object* v_stop_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0(v_as_548_, v_start_549_, v_stop_550_);
lean_dec(v_stop_550_);
lean_dec(v_start_549_);
lean_dec_ref(v_as_548_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts(lean_object* v_concl_552_, lean_object* v_binders_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_specComponents_x3f(v_concl_552_);
if (lean_obj_tag(v___x_559_) == 1)
{
lean_object* v_val_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_618_; 
v_val_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_618_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_618_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_val_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_618_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_snd_564_; lean_object* v_snd_565_; lean_object* v_fst_566_; lean_object* v_fst_567_; lean_object* v_fst_568_; lean_object* v_snd_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_qs_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v_snd_564_ = lean_ctor_get(v_val_560_, 1);
lean_inc(v_snd_564_);
v_snd_565_ = lean_ctor_get(v_snd_564_, 1);
lean_inc(v_snd_565_);
v_fst_566_ = lean_ctor_get(v_val_560_, 0);
lean_inc(v_fst_566_);
lean_dec(v_val_560_);
v_fst_567_ = lean_ctor_get(v_snd_564_, 0);
lean_inc(v_fst_567_);
lean_dec(v_snd_564_);
v_fst_568_ = lean_ctor_get(v_snd_565_, 0);
lean_inc(v_fst_568_);
v_snd_569_ = lean_ctor_get(v_snd_565_, 1);
lean_inc(v_snd_569_);
lean_dec(v_snd_565_);
v___x_570_ = lean_unsigned_to_nat(2u);
v___x_571_ = lean_mk_empty_array_with_capacity(v___x_570_);
v___x_572_ = lean_array_push(v___x_571_, v_fst_568_);
v___x_573_ = lean_array_push(v___x_572_, v_snd_569_);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_array_get_size(v___x_573_);
v_qs_576_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__0(v___x_573_, v___x_574_, v___x_575_);
lean_dec_ref(v___x_573_);
v___x_577_ = lean_array_get_size(v_qs_576_);
v___x_578_ = lean_nat_dec_eq(v___x_577_, v___x_574_);
if (v___x_578_ == 0)
{
uint8_t v___x_579_; 
lean_inc_ref(v_qs_576_);
v___x_579_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_occursMVar(v_qs_576_, v_fst_567_);
lean_dec(v_fst_567_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; size_t v_sz_581_; size_t v___x_582_; lean_object* v___x_583_; 
lean_del_object(v___x_562_);
v___x_580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1___closed__0));
v_sz_581_ = lean_array_size(v_binders_553_);
v___x_582_ = ((size_t)0ULL);
lean_inc_ref(v_qs_576_);
v___x_583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts_spec__1(v_qs_576_, v___x_579_, v_binders_553_, v_sz_581_, v___x_582_, v___x_580_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_600_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_600_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_600_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_600_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v_fst_588_; 
v_fst_588_ = lean_ctor_get(v_a_584_, 0);
lean_inc(v_fst_588_);
lean_dec(v_a_584_);
if (lean_obj_tag(v_fst_588_) == 0)
{
lean_object* v___x_589_; lean_object* v_env_590_; uint8_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_589_ = lean_st_ref_get(v_a_557_);
v_env_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc_ref(v_env_590_);
lean_dec(v___x_589_);
v___x_591_ = l___private_Lean_Elab_Tactic_Do_ConjunctivePre_0__Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveIn(v_env_590_, v_qs_576_, v_fst_566_);
v___x_592_ = lean_box(v___x_591_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_592_);
v___x_594_ = v___x_586_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
else
{
lean_object* v_val_596_; lean_object* v___x_598_; 
lean_dec_ref(v_qs_576_);
lean_dec(v_fst_566_);
v_val_596_ = lean_ctor_get(v_fst_588_, 0);
lean_inc(v_val_596_);
lean_dec_ref_known(v_fst_588_, 1);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v_val_596_);
v___x_598_ = v___x_586_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_val_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v_qs_576_);
lean_dec(v_fst_566_);
v_a_601_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_583_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_583_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
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
lean_object* v___x_609_; lean_object* v___x_611_; 
lean_dec_ref(v_qs_576_);
lean_dec(v_fst_566_);
v___x_609_ = lean_box(v___x_578_);
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 0);
lean_ctor_set(v___x_562_, 0, v___x_609_);
v___x_611_ = v___x_562_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
else
{
uint8_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
lean_dec_ref(v_qs_576_);
lean_dec(v_fst_567_);
lean_dec(v_fst_566_);
v___x_613_ = 0;
v___x_614_ = lean_box(v___x_613_);
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 0);
lean_ctor_set(v___x_562_, 0, v___x_614_);
v___x_616_ = v___x_562_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
else
{
uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v___x_559_);
v___x_619_ = 0;
v___x_620_ = lean_box(v___x_619_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts___boxed(lean_object* v_concl_622_, lean_object* v_binders_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_isConjunctiveInPosts(v_concl_622_, v_binders_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec_ref(v_binders_623_);
lean_dec_ref(v_concl_622_);
return v_res_629_;
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
