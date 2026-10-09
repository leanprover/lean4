// Lean compiler output
// Module: Lean.Util.Recognizers
// Imports: public import Lean.Environment
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21_x27(lean_object*);
lean_object* l_Lean_Expr_appFn_x21_x27(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object*);
lean_object* l_Lean_Expr_nat_x3f(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_const_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_const_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app1_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app1_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app2_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app2_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app3_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app3_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app4_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app4_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_eq_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Expr_eq_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_eq_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Expr_eq_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_eq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Expr_eq_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_eq_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_eq_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_eq_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_ne_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Lean_Expr_ne_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_ne_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Expr_ne_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_ne_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Lean_Expr_ne_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_ne_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_ne_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ne_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_iff_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l_Lean_Expr_iff_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_iff_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Expr_iff_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_iff_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l_Lean_Expr_iff_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_iff_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_iff_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_iff_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_eqOrIff_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_eqOrIff_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_not_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Expr_not_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_not_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Expr_not_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_not_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Expr_not_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_not_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_not_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_not_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_notNot_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_notNot_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_and_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Expr_and_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_and_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Expr_and_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_and_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Expr_and_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_and_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_and_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_and_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_heq_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_Expr_heq_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_heq_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Expr_heq_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_heq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_Expr_heq_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_heq_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_heq_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_heq_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_natAdd_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Expr_natAdd_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_natAdd_x3f___closed__0_value;
static const lean_string_object l_Lean_Expr_natAdd_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lean_Expr_natAdd_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_natAdd_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Expr_natAdd_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_natAdd_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Expr_natAdd_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_natAdd_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_natAdd_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 189, 86, 121, 130, 22, 242, 236)}};
static const lean_object* l_Lean_Expr_natAdd_x3f___closed__2 = (const lean_object*)&l_Lean_Expr_natAdd_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Expr_natAdd_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_natAdd_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_arrow_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_arrow_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isEq___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isHEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isHEq___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Expr_isIte___closed__0 = (const lean_object*)&l_Lean_Expr_isIte___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isIte___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Expr_isIte___closed__1 = (const lean_object*)&l_Lean_Expr_isIte___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isIte(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isIte___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isDIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_Expr_isDIte___closed__0 = (const lean_object*)&l_Lean_Expr_isDIte___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isDIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isDIte___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_Expr_isDIte___closed__1 = (const lean_object*)&l_Lean_Expr_isDIte___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isDIte(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isDIte___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0 = (const lean_object*)&l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0_value;
static const lean_string_object l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__1 = (const lean_object*)&l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__1_value;
static const lean_ctor_object l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2 = (const lean_object*)&l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2_value;
static const lean_string_object l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__3 = (const lean_object*)&l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__3_value;
static const lean_ctor_object l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__3_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4 = (const lean_object*)&l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_listLit_x3f(lean_object*);
static const lean_string_object l_Lean_Expr_arrayLit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l_Lean_Expr_arrayLit_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_arrayLit_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Expr_arrayLit_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Expr_arrayLit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_arrayLit_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_arrayLit_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l_Lean_Expr_arrayLit_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_arrayLit_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_arrayLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_arrayLit_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_prod_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_Expr_prod_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_prod_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Expr_prod_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_prod_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l_Lean_Expr_prod_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_prod_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_prod_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_prod_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_name_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Expr_name_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_name_x3f___closed__0_value;
static const lean_string_object l_Lean_Expr_name_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l_Lean_Expr_name_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_name_x3f___closed__1_value;
static const lean_string_object l_Lean_Expr_name_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "anonymous"};
static const lean_object* l_Lean_Expr_name_x3f___closed__2 = (const lean_object*)&l_Lean_Expr_name_x3f___closed__2_value;
static const lean_string_object l_Lean_Expr_name_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Expr_name_x3f___closed__3 = (const lean_object*)&l_Lean_Expr_name_x3f___closed__3_value;
static const lean_string_object l_Lean_Expr_name_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Expr_name_x3f___closed__4 = (const lean_object*)&l_Lean_Expr_name_x3f___closed__4_value;
static const lean_string_object l_Lean_Expr_name_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mkStr2"};
static const lean_object* l_Lean_Expr_name_x3f___closed__5 = (const lean_object*)&l_Lean_Expr_name_x3f___closed__5_value;
static const lean_string_object l_Lean_Expr_name_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mkStr3"};
static const lean_object* l_Lean_Expr_name_x3f___closed__6 = (const lean_object*)&l_Lean_Expr_name_x3f___closed__6_value;
static const lean_string_object l_Lean_Expr_name_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mkStr4"};
static const lean_object* l_Lean_Expr_name_x3f___closed__7 = (const lean_object*)&l_Lean_Expr_name_x3f___closed__7_value;
static const lean_string_object l_Lean_Expr_name_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mkStr5"};
static const lean_object* l_Lean_Expr_name_x3f___closed__8 = (const lean_object*)&l_Lean_Expr_name_x3f___closed__8_value;
static const lean_string_object l_Lean_Expr_name_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mkStr6"};
static const lean_object* l_Lean_Expr_name_x3f___closed__9 = (const lean_object*)&l_Lean_Expr_name_x3f___closed__9_value;
static const lean_string_object l_Lean_Expr_name_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mkStr7"};
static const lean_object* l_Lean_Expr_name_x3f___closed__10 = (const lean_object*)&l_Lean_Expr_name_x3f___closed__10_value;
static const lean_string_object l_Lean_Expr_name_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mkStr8"};
static const lean_object* l_Lean_Expr_name_x3f___closed__11 = (const lean_object*)&l_Lean_Expr_name_x3f___closed__11_value;
static const lean_string_object l_Lean_Expr_name_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mkStr1"};
static const lean_object* l_Lean_Expr_name_x3f___closed__12 = (const lean_object*)&l_Lean_Expr_name_x3f___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Expr_name_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_const_x3f(lean_object* v_e_1_){
_start:
{
if (lean_obj_tag(v_e_1_) == 4)
{
lean_object* v_declName_2_; lean_object* v_us_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v_declName_2_ = lean_ctor_get(v_e_1_, 0);
v_us_3_ = lean_ctor_get(v_e_1_, 1);
lean_inc(v_us_3_);
lean_inc(v_declName_2_);
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_declName_2_);
lean_ctor_set(v___x_4_, 1, v_us_3_);
v___x_5_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_x3f___boxed(lean_object* v_e_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Expr_const_x3f(v_e_7_);
lean_dec_ref(v_e_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app1_x3f(lean_object* v_e_9_, lean_object* v_fName_10_){
_start:
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = l_Lean_Expr_isAppOfArity(v_e_9_, v_fName_10_, v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
v___x_13_ = lean_box(0);
return v___x_13_;
}
else
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = l_Lean_Expr_appArg_x21(v_e_9_);
v___x_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app1_x3f___boxed(lean_object* v_e_16_, lean_object* v_fName_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Expr_app1_x3f(v_e_16_, v_fName_17_);
lean_dec(v_fName_17_);
lean_dec_ref(v_e_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app2_x3f(lean_object* v_e_19_, lean_object* v_fName_20_){
_start:
{
lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_21_ = lean_unsigned_to_nat(2u);
v___x_22_ = l_Lean_Expr_isAppOfArity(v_e_19_, v_fName_20_, v___x_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; 
v___x_23_ = lean_box(0);
return v___x_23_;
}
else
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_24_ = l_Lean_Expr_appFn_x21(v_e_19_);
v___x_25_ = l_Lean_Expr_appArg_x21(v___x_24_);
lean_dec_ref(v___x_24_);
v___x_26_ = l_Lean_Expr_appArg_x21(v_e_19_);
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_25_);
lean_ctor_set(v___x_27_, 1, v___x_26_);
v___x_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app2_x3f___boxed(lean_object* v_e_29_, lean_object* v_fName_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Expr_app2_x3f(v_e_29_, v_fName_30_);
lean_dec(v_fName_30_);
lean_dec_ref(v_e_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app3_x3f(lean_object* v_e_32_, lean_object* v_fName_33_){
_start:
{
lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_34_ = lean_unsigned_to_nat(3u);
v___x_35_ = l_Lean_Expr_isAppOfArity(v_e_32_, v_fName_33_, v___x_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; 
v___x_36_ = lean_box(0);
return v___x_36_;
}
else
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_37_ = l_Lean_Expr_appFn_x21(v_e_32_);
v___x_38_ = l_Lean_Expr_appFn_x21(v___x_37_);
v___x_39_ = l_Lean_Expr_appArg_x21(v___x_38_);
lean_dec_ref(v___x_38_);
v___x_40_ = l_Lean_Expr_appArg_x21(v___x_37_);
lean_dec_ref(v___x_37_);
v___x_41_ = l_Lean_Expr_appArg_x21(v_e_32_);
v___x_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_40_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_39_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
v___x_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app3_x3f___boxed(lean_object* v_e_45_, lean_object* v_fName_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Expr_app3_x3f(v_e_45_, v_fName_46_);
lean_dec(v_fName_46_);
lean_dec_ref(v_e_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app4_x3f(lean_object* v_e_48_, lean_object* v_fName_49_){
_start:
{
lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_50_ = lean_unsigned_to_nat(4u);
v___x_51_ = l_Lean_Expr_isAppOfArity(v_e_48_, v_fName_49_, v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; 
v___x_52_ = lean_box(0);
return v___x_52_;
}
else
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_53_ = l_Lean_Expr_appFn_x21(v_e_48_);
v___x_54_ = l_Lean_Expr_appFn_x21(v___x_53_);
v___x_55_ = l_Lean_Expr_appFn_x21(v___x_54_);
v___x_56_ = l_Lean_Expr_appArg_x21(v___x_55_);
lean_dec_ref(v___x_55_);
v___x_57_ = l_Lean_Expr_appArg_x21(v___x_54_);
lean_dec_ref(v___x_54_);
v___x_58_ = l_Lean_Expr_appArg_x21(v___x_53_);
lean_dec_ref(v___x_53_);
v___x_59_ = l_Lean_Expr_appArg_x21(v_e_48_);
v___x_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_57_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_56_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
v___x_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app4_x3f___boxed(lean_object* v_e_64_, lean_object* v_fName_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Expr_app4_x3f(v_e_64_, v_fName_65_);
lean_dec(v_fName_65_);
lean_dec_ref(v_e_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eq_x3f(lean_object* v_p_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_71_ = ((lean_object*)(l_Lean_Expr_eq_x3f___closed__1));
v___x_72_ = lean_unsigned_to_nat(3u);
v___x_73_ = l_Lean_Expr_isAppOfArity(v_p_70_, v___x_71_, v___x_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_75_ = l_Lean_Expr_appFn_x21(v_p_70_);
v___x_76_ = l_Lean_Expr_appFn_x21(v___x_75_);
v___x_77_ = l_Lean_Expr_appArg_x21(v___x_76_);
lean_dec_ref(v___x_76_);
v___x_78_ = l_Lean_Expr_appArg_x21(v___x_75_);
lean_dec_ref(v___x_75_);
v___x_79_ = l_Lean_Expr_appArg_x21(v_p_70_);
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_77_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eq_x3f___boxed(lean_object* v_p_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Expr_eq_x3f(v_p_83_);
lean_dec_ref(v_p_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ne_x3f(lean_object* v_p_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_89_ = ((lean_object*)(l_Lean_Expr_ne_x3f___closed__1));
v___x_90_ = lean_unsigned_to_nat(3u);
v___x_91_ = l_Lean_Expr_isAppOfArity(v_p_88_, v___x_89_, v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; 
v___x_92_ = lean_box(0);
return v___x_92_;
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_93_ = l_Lean_Expr_appFn_x21(v_p_88_);
v___x_94_ = l_Lean_Expr_appFn_x21(v___x_93_);
v___x_95_ = l_Lean_Expr_appArg_x21(v___x_94_);
lean_dec_ref(v___x_94_);
v___x_96_ = l_Lean_Expr_appArg_x21(v___x_93_);
lean_dec_ref(v___x_93_);
v___x_97_ = l_Lean_Expr_appArg_x21(v_p_88_);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_95_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ne_x3f___boxed(lean_object* v_p_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Expr_ne_x3f(v_p_101_);
lean_dec_ref(v_p_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_iff_x3f(lean_object* v_p_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_107_ = ((lean_object*)(l_Lean_Expr_iff_x3f___closed__1));
v___x_108_ = lean_unsigned_to_nat(2u);
v___x_109_ = l_Lean_Expr_isAppOfArity(v_p_106_, v___x_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(0);
return v___x_110_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_111_ = l_Lean_Expr_appFn_x21(v_p_106_);
v___x_112_ = l_Lean_Expr_appArg_x21(v___x_111_);
lean_dec_ref(v___x_111_);
v___x_113_ = l_Lean_Expr_appArg_x21(v_p_106_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_iff_x3f___boxed(lean_object* v_p_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Expr_iff_x3f(v_p_116_);
lean_dec_ref(v_p_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqOrIff_x3f(lean_object* v_p_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_119_ = ((lean_object*)(l_Lean_Expr_eq_x3f___closed__1));
v___x_120_ = lean_unsigned_to_nat(3u);
v___x_121_ = l_Lean_Expr_isAppOfArity(v_p_118_, v___x_119_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_122_ = ((lean_object*)(l_Lean_Expr_iff_x3f___closed__1));
v___x_123_ = lean_unsigned_to_nat(2u);
v___x_124_ = l_Lean_Expr_isAppOfArity(v_p_118_, v___x_122_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
v___x_125_ = lean_box(0);
return v___x_125_;
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_126_ = l_Lean_Expr_appFn_x21(v_p_118_);
v___x_127_ = l_Lean_Expr_appArg_x21(v___x_126_);
lean_dec_ref(v___x_126_);
v___x_128_ = l_Lean_Expr_appArg_x21(v_p_118_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_131_ = l_Lean_Expr_appFn_x21(v_p_118_);
v___x_132_ = l_Lean_Expr_appArg_x21(v___x_131_);
lean_dec_ref(v___x_131_);
v___x_133_ = l_Lean_Expr_appArg_x21(v_p_118_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_132_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqOrIff_x3f___boxed(lean_object* v_p_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_Expr_eqOrIff_x3f(v_p_136_);
lean_dec_ref(v_p_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_not_x3f(lean_object* v_p_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_142_ = ((lean_object*)(l_Lean_Expr_not_x3f___closed__1));
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = l_Lean_Expr_isAppOfArity(v_p_141_, v___x_142_, v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; 
v___x_145_ = lean_box(0);
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = l_Lean_Expr_appArg_x21(v_p_141_);
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_not_x3f___boxed(lean_object* v_p_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Expr_not_x3f(v_p_148_);
lean_dec_ref(v_p_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_notNot_x3f(lean_object* v_p_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_151_ = ((lean_object*)(l_Lean_Expr_not_x3f___closed__1));
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = l_Lean_Expr_isAppOfArity(v_p_150_, v___x_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; 
v___x_154_ = lean_box(0);
return v___x_154_;
}
else
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = l_Lean_Expr_appArg_x21(v_p_150_);
v___x_156_ = l_Lean_Expr_isAppOfArity(v___x_155_, v___x_151_, v___x_152_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; 
lean_dec_ref(v___x_155_);
v___x_157_ = lean_box(0);
return v___x_157_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = l_Lean_Expr_appArg_x21(v___x_155_);
lean_dec_ref(v___x_155_);
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_notNot_x3f___boxed(lean_object* v_p_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Expr_notNot_x3f(v_p_160_);
lean_dec_ref(v_p_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_and_x3f(lean_object* v_p_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_166_ = ((lean_object*)(l_Lean_Expr_and_x3f___closed__1));
v___x_167_ = lean_unsigned_to_nat(2u);
v___x_168_ = l_Lean_Expr_isAppOfArity(v_p_165_, v___x_166_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
v___x_169_ = lean_box(0);
return v___x_169_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_170_ = l_Lean_Expr_appFn_x21(v_p_165_);
v___x_171_ = l_Lean_Expr_appArg_x21(v___x_170_);
lean_dec_ref(v___x_170_);
v___x_172_ = l_Lean_Expr_appArg_x21(v_p_165_);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_and_x3f___boxed(lean_object* v_p_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Expr_and_x3f(v_p_175_);
lean_dec_ref(v_p_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_heq_x3f(lean_object* v_p_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_181_ = ((lean_object*)(l_Lean_Expr_heq_x3f___closed__1));
v___x_182_ = lean_unsigned_to_nat(4u);
v___x_183_ = l_Lean_Expr_isAppOfArity(v_p_180_, v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
v___x_184_ = lean_box(0);
return v___x_184_;
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_185_ = l_Lean_Expr_appFn_x21(v_p_180_);
v___x_186_ = l_Lean_Expr_appFn_x21(v___x_185_);
v___x_187_ = l_Lean_Expr_appFn_x21(v___x_186_);
v___x_188_ = l_Lean_Expr_appArg_x21(v___x_187_);
lean_dec_ref(v___x_187_);
v___x_189_ = l_Lean_Expr_appArg_x21(v___x_186_);
lean_dec_ref(v___x_186_);
v___x_190_ = l_Lean_Expr_appArg_x21(v___x_185_);
lean_dec_ref(v___x_185_);
v___x_191_ = l_Lean_Expr_appArg_x21(v_p_180_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_189_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_188_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_heq_x3f___boxed(lean_object* v_p_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Expr_heq_x3f(v_p_196_);
lean_dec_ref(v_p_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_natAdd_x3f(lean_object* v_e_203_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_204_ = ((lean_object*)(l_Lean_Expr_natAdd_x3f___closed__2));
v___x_205_ = lean_unsigned_to_nat(2u);
v___x_206_ = l_Lean_Expr_isAppOfArity(v_e_203_, v___x_204_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; 
v___x_207_ = lean_box(0);
return v___x_207_;
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_208_ = l_Lean_Expr_appFn_x21(v_e_203_);
v___x_209_ = l_Lean_Expr_appArg_x21(v___x_208_);
lean_dec_ref(v___x_208_);
v___x_210_ = l_Lean_Expr_appArg_x21(v_e_203_);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_natAdd_x3f___boxed(lean_object* v_e_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Expr_natAdd_x3f(v_e_213_);
lean_dec_ref(v_e_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_arrow_x3f(lean_object* v_x_215_){
_start:
{
if (lean_obj_tag(v_x_215_) == 7)
{
lean_object* v_binderType_216_; lean_object* v_body_217_; uint8_t v___x_218_; 
v_binderType_216_ = lean_ctor_get(v_x_215_, 1);
v_body_217_ = lean_ctor_get(v_x_215_, 2);
v___x_218_ = l_Lean_Expr_hasLooseBVars(v_body_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_inc_ref(v_body_217_);
lean_inc_ref(v_binderType_216_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v_binderType_216_);
lean_ctor_set(v___x_219_, 1, v_body_217_);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
else
{
lean_object* v___x_221_; 
v___x_221_ = lean_box(0);
return v___x_221_;
}
}
else
{
lean_object* v___x_222_; 
v___x_222_ = lean_box(0);
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_arrow_x3f___boxed(lean_object* v_x_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Expr_arrow_x3f(v_x_223_);
lean_dec_ref(v_x_223_);
return v_res_224_;
}
}
uint8_t l_Lean_Expr_isEq(lean_object* v_e_225_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_226_ = ((lean_object*)(l_Lean_Expr_eq_x3f___closed__1));
v___x_227_ = lean_unsigned_to_nat(3u);
v___x_228_ = l_Lean_Expr_isAppOfArity(v_e_225_, v___x_226_, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT void l_Lean_Expr_isEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_225_ = stack[0].m_obj;
uint8_t v_res_229_;
v_res_229_ = l_Lean_Expr_isEq(v_e_225_);
stack->m_num = v_res_229_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isEq___boxed(lean_object* v_e_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Lean_Expr_isEq(v_e_230_);
lean_dec_ref(v_e_230_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
uint8_t l_Lean_Expr_isHEq(lean_object* v_e_233_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_234_ = ((lean_object*)(l_Lean_Expr_heq_x3f___closed__1));
v___x_235_ = lean_unsigned_to_nat(4u);
v___x_236_ = l_Lean_Expr_isAppOfArity(v_e_233_, v___x_234_, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT void l_Lean_Expr_isHEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_233_ = stack[0].m_obj;
uint8_t v_res_237_;
v_res_237_ = l_Lean_Expr_isHEq(v_e_233_);
stack->m_num = v_res_237_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHEq___boxed(lean_object* v_e_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Lean_Expr_isHEq(v_e_238_);
lean_dec_ref(v_e_238_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
uint8_t l_Lean_Expr_isIte(lean_object* v_e_244_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_245_ = ((lean_object*)(l_Lean_Expr_isIte___closed__1));
v___x_246_ = lean_unsigned_to_nat(5u);
v___x_247_ = l_Lean_Expr_isAppOfArity(v_e_244_, v___x_245_, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT void l_Lean_Expr_isIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_244_ = stack[0].m_obj;
uint8_t v_res_248_;
v_res_248_ = l_Lean_Expr_isIte(v_e_244_);
stack->m_num = v_res_248_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isIte___boxed(lean_object* v_e_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Lean_Expr_isIte(v_e_249_);
lean_dec_ref(v_e_249_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
uint8_t l_Lean_Expr_isDIte(lean_object* v_e_255_){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_256_ = ((lean_object*)(l_Lean_Expr_isDIte___closed__1));
v___x_257_ = lean_unsigned_to_nat(5u);
v___x_258_ = l_Lean_Expr_isAppOfArity(v_e_255_, v___x_256_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT void l_Lean_Expr_isDIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_255_ = stack[0].m_obj;
uint8_t v_res_259_;
v_res_259_ = l_Lean_Expr_isDIte(v_e_255_);
stack->m_num = v_res_259_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isDIte___boxed(lean_object* v_e_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Lean_Expr_isDIte(v_e_260_);
lean_dec_ref(v_e_260_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop(lean_object* v_e_272_, lean_object* v_acc_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_274_ = ((lean_object*)(l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2));
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = l_Lean_Expr_isAppOfArity_x27(v_e_272_, v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4));
v___x_278_ = lean_unsigned_to_nat(3u);
v___x_279_ = l_Lean_Expr_isAppOfArity_x27(v_e_272_, v___x_277_, v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
lean_dec(v_acc_273_);
lean_dec_ref(v_e_272_);
v___x_280_ = lean_box(0);
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_281_ = l_Lean_Expr_appArg_x21_x27(v_e_272_);
v___x_282_ = l_Lean_Expr_appFn_x21_x27(v_e_272_);
lean_dec_ref(v_e_272_);
v___x_283_ = l_Lean_Expr_appArg_x21_x27(v___x_282_);
lean_dec_ref(v___x_282_);
v___x_284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v_acc_273_);
v_e_272_ = v___x_281_;
v_acc_273_ = v___x_284_;
goto _start;
}
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_286_ = l_Lean_Expr_appArg_x21_x27(v_e_272_);
lean_dec_ref(v_e_272_);
v___x_287_ = l_List_reverse___redArg(v_acc_273_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_listLit_x3f(lean_object* v_e_290_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_box(0);
v___x_292_ = l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop(v_e_290_, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_arrayLit_x3f(lean_object* v_e_297_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_298_ = ((lean_object*)(l_Lean_Expr_arrayLit_x3f___closed__1));
v___x_299_ = lean_unsigned_to_nat(2u);
v___x_300_ = l_Lean_Expr_isAppOfArity_x27(v_e_297_, v___x_298_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_box(0);
return v___x_301_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = l_Lean_Expr_appArg_x21_x27(v_e_297_);
v___x_303_ = l_Lean_Expr_listLit_x3f(v___x_302_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_arrayLit_x3f___boxed(lean_object* v_e_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Expr_arrayLit_x3f(v_e_304_);
lean_dec_ref(v_e_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_prod_x3f(lean_object* v_e_309_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_310_ = ((lean_object*)(l_Lean_Expr_prod_x3f___closed__1));
v___x_311_ = lean_unsigned_to_nat(2u);
v___x_312_ = l_Lean_Expr_isAppOfArity(v_e_309_, v___x_310_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
v___x_313_ = lean_box(0);
return v___x_313_;
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_314_ = l_Lean_Expr_appFn_x21(v_e_309_);
v___x_315_ = l_Lean_Expr_appArg_x21(v___x_314_);
lean_dec_ref(v___x_314_);
v___x_316_ = l_Lean_Expr_appArg_x21(v_e_309_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_prod_x3f___boxed(lean_object* v_e_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Expr_prod_x3f(v_e_319_);
lean_dec_ref(v_e_319_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_name_x3f(lean_object* v_x_334_){
_start:
{
switch(lean_obj_tag(v_x_334_))
{
case 4:
{
lean_object* v_declName_335_; 
v_declName_335_ = lean_ctor_get(v_x_334_, 0);
lean_inc(v_declName_335_);
lean_dec_ref_known(v_x_334_, 2);
if (lean_obj_tag(v_declName_335_) == 1)
{
lean_object* v_pre_336_; 
v_pre_336_ = lean_ctor_get(v_declName_335_, 0);
lean_inc(v_pre_336_);
if (lean_obj_tag(v_pre_336_) == 1)
{
lean_object* v_pre_337_; 
v_pre_337_ = lean_ctor_get(v_pre_336_, 0);
lean_inc(v_pre_337_);
if (lean_obj_tag(v_pre_337_) == 1)
{
lean_object* v_pre_338_; 
v_pre_338_ = lean_ctor_get(v_pre_337_, 0);
lean_inc(v_pre_338_);
if (lean_obj_tag(v_pre_338_) == 0)
{
lean_object* v_str_339_; lean_object* v_str_340_; lean_object* v_str_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_str_339_ = lean_ctor_get(v_declName_335_, 1);
lean_inc_ref(v_str_339_);
lean_dec_ref_known(v_declName_335_, 2);
v_str_340_ = lean_ctor_get(v_pre_336_, 1);
lean_inc_ref(v_str_340_);
lean_dec_ref_known(v_pre_336_, 2);
v_str_341_ = lean_ctor_get(v_pre_337_, 1);
lean_inc_ref(v_str_341_);
lean_dec_ref_known(v_pre_337_, 2);
v___x_342_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_343_ = lean_string_dec_eq(v_str_341_, v___x_342_);
lean_dec_ref(v_str_341_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
lean_dec_ref(v_str_340_);
lean_dec_ref(v_str_339_);
v___x_344_ = lean_box(0);
return v___x_344_;
}
else
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_346_ = lean_string_dec_eq(v_str_340_, v___x_345_);
lean_dec_ref(v_str_340_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_dec_ref(v_str_339_);
v___x_347_ = lean_box(0);
return v___x_347_;
}
else
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__2));
v___x_349_ = lean_string_dec_eq(v_str_339_, v___x_348_);
lean_dec_ref(v_str_339_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
v___x_350_ = lean_box(0);
return v___x_350_;
}
else
{
lean_object* v___x_351_; 
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v_pre_338_);
return v___x_351_;
}
}
}
}
else
{
lean_object* v___x_352_; 
lean_dec(v_pre_338_);
lean_dec_ref_known(v_pre_337_, 2);
lean_dec_ref_known(v_pre_336_, 2);
lean_dec_ref_known(v_declName_335_, 2);
v___x_352_ = lean_box(0);
return v___x_352_;
}
}
else
{
lean_object* v___x_353_; 
lean_dec(v_pre_337_);
lean_dec_ref_known(v_pre_336_, 2);
lean_dec_ref_known(v_declName_335_, 2);
v___x_353_ = lean_box(0);
return v___x_353_;
}
}
else
{
lean_object* v___x_354_; 
lean_dec_ref_known(v_declName_335_, 2);
lean_dec(v_pre_336_);
v___x_354_ = lean_box(0);
return v___x_354_;
}
}
else
{
lean_object* v___x_355_; 
lean_dec(v_declName_335_);
v___x_355_ = lean_box(0);
return v___x_355_;
}
}
case 5:
{
lean_object* v_fn_356_; 
v_fn_356_ = lean_ctor_get(v_x_334_, 0);
switch(lean_obj_tag(v_fn_356_))
{
case 5:
{
lean_object* v_arg_357_; lean_object* v_fn_358_; lean_object* v_arg_359_; lean_object* v___y_361_; 
lean_inc_ref(v_fn_356_);
v_arg_357_ = lean_ctor_get(v_x_334_, 1);
lean_inc_ref(v_arg_357_);
lean_dec_ref_known(v_x_334_, 2);
v_fn_358_ = lean_ctor_get(v_fn_356_, 0);
lean_inc_ref(v_fn_358_);
v_arg_359_ = lean_ctor_get(v_fn_356_, 1);
lean_inc_ref(v_arg_359_);
lean_dec_ref_known(v_fn_356_, 2);
switch(lean_obj_tag(v_fn_358_))
{
case 4:
{
lean_object* v_declName_374_; 
v_declName_374_ = lean_ctor_get(v_fn_358_, 0);
lean_inc(v_declName_374_);
lean_dec_ref_known(v_fn_358_, 2);
if (lean_obj_tag(v_declName_374_) == 1)
{
lean_object* v_pre_375_; 
v_pre_375_ = lean_ctor_get(v_declName_374_, 0);
lean_inc(v_pre_375_);
if (lean_obj_tag(v_pre_375_) == 1)
{
lean_object* v_pre_376_; 
v_pre_376_ = lean_ctor_get(v_pre_375_, 0);
lean_inc(v_pre_376_);
if (lean_obj_tag(v_pre_376_) == 1)
{
lean_object* v_pre_377_; 
v_pre_377_ = lean_ctor_get(v_pre_376_, 0);
if (lean_obj_tag(v_pre_377_) == 0)
{
lean_object* v_str_378_; lean_object* v_str_379_; lean_object* v_str_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_str_378_ = lean_ctor_get(v_declName_374_, 1);
lean_inc_ref(v_str_378_);
lean_dec_ref_known(v_declName_374_, 2);
v_str_379_ = lean_ctor_get(v_pre_375_, 1);
lean_inc_ref(v_str_379_);
lean_dec_ref_known(v_pre_375_, 2);
v_str_380_ = lean_ctor_get(v_pre_376_, 1);
lean_inc_ref(v_str_380_);
lean_dec_ref_known(v_pre_376_, 2);
v___x_381_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_382_ = lean_string_dec_eq(v_str_380_, v___x_381_);
lean_dec_ref(v_str_380_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec_ref(v_str_379_);
lean_dec_ref(v_str_378_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_383_ = lean_box(0);
return v___x_383_;
}
else
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_385_ = lean_string_dec_eq(v_str_379_, v___x_384_);
lean_dec_ref(v_str_379_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec_ref(v_str_378_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_386_ = lean_box(0);
return v___x_386_;
}
else
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__3));
v___x_388_ = lean_string_dec_eq(v_str_378_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__4));
v___x_390_ = lean_string_dec_eq(v_str_378_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__5));
v___x_392_ = lean_string_dec_eq(v_str_378_, v___x_391_);
lean_dec_ref(v_str_378_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_393_ = lean_box(0);
return v___x_393_;
}
else
{
if (lean_obj_tag(v_arg_359_) == 9)
{
lean_object* v_a_394_; 
v_a_394_ = lean_ctor_get(v_arg_359_, 0);
lean_inc_ref(v_a_394_);
lean_dec_ref_known(v_arg_359_, 1);
if (lean_obj_tag(v_a_394_) == 1)
{
if (lean_obj_tag(v_arg_357_) == 9)
{
lean_object* v_a_395_; 
v_a_395_ = lean_ctor_get(v_arg_357_, 0);
lean_inc_ref(v_a_395_);
lean_dec_ref_known(v_arg_357_, 1);
if (lean_obj_tag(v_a_395_) == 1)
{
lean_object* v_val_396_; lean_object* v_val_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_405_; 
v_val_396_ = lean_ctor_get(v_a_394_, 0);
lean_inc_ref(v_val_396_);
lean_dec_ref_known(v_a_394_, 1);
v_val_397_ = lean_ctor_get(v_a_395_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v_a_395_);
if (v_isSharedCheck_405_ == 0)
{
v___x_399_ = v_a_395_;
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_val_397_);
lean_dec(v_a_395_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = l_Lean_Name_mkStr2(v_val_396_, v_val_397_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_401_);
v___x_403_ = v___x_399_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
else
{
lean_object* v___x_406_; 
lean_dec_ref(v_a_395_);
lean_dec_ref_known(v_a_394_, 1);
v___x_406_ = lean_box(0);
return v___x_406_;
}
}
else
{
lean_object* v___x_407_; 
lean_dec_ref_known(v_a_394_, 1);
lean_dec_ref(v_arg_357_);
v___x_407_ = lean_box(0);
return v___x_407_;
}
}
else
{
lean_object* v___x_408_; 
lean_dec_ref(v_a_394_);
lean_dec_ref(v_arg_357_);
v___x_408_ = lean_box(0);
return v___x_408_;
}
}
else
{
lean_object* v___x_409_; 
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_409_ = lean_box(0);
return v___x_409_;
}
}
}
else
{
lean_object* v___x_410_; 
lean_dec_ref(v_str_378_);
lean_inc_ref(v_arg_357_);
v___x_410_ = l_Lean_Expr_rawNatLit_x3f(v_arg_357_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Expr_nat_x3f(v_arg_357_);
v___y_361_ = v___x_411_;
goto v___jp_360_;
}
else
{
lean_dec_ref(v_arg_357_);
v___y_361_ = v___x_410_;
goto v___jp_360_;
}
}
}
else
{
lean_dec_ref(v_str_378_);
if (lean_obj_tag(v_arg_357_) == 9)
{
lean_object* v_a_412_; 
v_a_412_ = lean_ctor_get(v_arg_357_, 0);
lean_inc_ref(v_a_412_);
lean_dec_ref_known(v_arg_357_, 1);
if (lean_obj_tag(v_a_412_) == 1)
{
lean_object* v_val_413_; lean_object* v___x_414_; 
v_val_413_ = lean_ctor_get(v_a_412_, 0);
lean_inc_ref(v_val_413_);
lean_dec_ref_known(v_a_412_, 1);
v___x_414_ = l_Lean_Expr_name_x3f(v_arg_359_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_dec_ref(v_val_413_);
return v___x_414_;
}
else
{
lean_object* v_val_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_423_; 
v_val_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_423_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_val_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = l_Lean_Name_str___override(v_val_415_, v_val_413_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_419_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
else
{
lean_object* v___x_424_; 
lean_dec_ref(v_a_412_);
lean_dec_ref(v_arg_359_);
v___x_424_ = lean_box(0);
return v___x_424_;
}
}
else
{
lean_object* v___x_425_; 
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_425_ = lean_box(0);
return v___x_425_;
}
}
}
}
}
else
{
lean_object* v___x_426_; 
lean_dec_ref_known(v_pre_376_, 2);
lean_dec_ref_known(v_pre_375_, 2);
lean_dec_ref_known(v_declName_374_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_426_ = lean_box(0);
return v___x_426_;
}
}
else
{
lean_object* v___x_427_; 
lean_dec(v_pre_376_);
lean_dec_ref_known(v_pre_375_, 2);
lean_dec_ref_known(v_declName_374_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_427_ = lean_box(0);
return v___x_427_;
}
}
else
{
lean_object* v___x_428_; 
lean_dec(v_pre_375_);
lean_dec_ref_known(v_declName_374_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_428_ = lean_box(0);
return v___x_428_;
}
}
else
{
lean_object* v___x_429_; 
lean_dec(v_declName_374_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_429_ = lean_box(0);
return v___x_429_;
}
}
case 5:
{
lean_object* v_fn_430_; 
v_fn_430_ = lean_ctor_get(v_fn_358_, 0);
switch(lean_obj_tag(v_fn_430_))
{
case 4:
{
lean_object* v_declName_431_; 
v_declName_431_ = lean_ctor_get(v_fn_430_, 0);
lean_inc(v_declName_431_);
if (lean_obj_tag(v_declName_431_) == 1)
{
lean_object* v_pre_432_; 
v_pre_432_ = lean_ctor_get(v_declName_431_, 0);
lean_inc(v_pre_432_);
if (lean_obj_tag(v_pre_432_) == 1)
{
lean_object* v_pre_433_; 
v_pre_433_ = lean_ctor_get(v_pre_432_, 0);
lean_inc(v_pre_433_);
if (lean_obj_tag(v_pre_433_) == 1)
{
lean_object* v_pre_434_; 
v_pre_434_ = lean_ctor_get(v_pre_433_, 0);
if (lean_obj_tag(v_pre_434_) == 0)
{
lean_object* v_arg_435_; lean_object* v_str_436_; lean_object* v_str_437_; lean_object* v_str_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v_arg_435_ = lean_ctor_get(v_fn_358_, 1);
lean_inc_ref(v_arg_435_);
lean_dec_ref_known(v_fn_358_, 2);
v_str_436_ = lean_ctor_get(v_declName_431_, 1);
lean_inc_ref(v_str_436_);
lean_dec_ref_known(v_declName_431_, 2);
v_str_437_ = lean_ctor_get(v_pre_432_, 1);
lean_inc_ref(v_str_437_);
lean_dec_ref_known(v_pre_432_, 2);
v_str_438_ = lean_ctor_get(v_pre_433_, 1);
lean_inc_ref(v_str_438_);
lean_dec_ref_known(v_pre_433_, 2);
v___x_439_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_440_ = lean_string_dec_eq(v_str_438_, v___x_439_);
lean_dec_ref(v_str_438_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
lean_dec_ref(v_str_437_);
lean_dec_ref(v_str_436_);
lean_dec_ref(v_arg_435_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_441_ = lean_box(0);
return v___x_441_;
}
else
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_443_ = lean_string_dec_eq(v_str_437_, v___x_442_);
lean_dec_ref(v_str_437_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
lean_dec_ref(v_str_436_);
lean_dec_ref(v_arg_435_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_444_ = lean_box(0);
return v___x_444_;
}
else
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__6));
v___x_446_ = lean_string_dec_eq(v_str_436_, v___x_445_);
lean_dec_ref(v_str_436_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
lean_dec_ref(v_arg_435_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_447_ = lean_box(0);
return v___x_447_;
}
else
{
if (lean_obj_tag(v_arg_435_) == 9)
{
lean_object* v_a_448_; 
v_a_448_ = lean_ctor_get(v_arg_435_, 0);
lean_inc_ref(v_a_448_);
lean_dec_ref_known(v_arg_435_, 1);
if (lean_obj_tag(v_a_448_) == 1)
{
if (lean_obj_tag(v_arg_359_) == 9)
{
lean_object* v_a_449_; 
v_a_449_ = lean_ctor_get(v_arg_359_, 0);
lean_inc_ref(v_a_449_);
lean_dec_ref_known(v_arg_359_, 1);
if (lean_obj_tag(v_a_449_) == 1)
{
if (lean_obj_tag(v_arg_357_) == 9)
{
lean_object* v_a_450_; 
v_a_450_ = lean_ctor_get(v_arg_357_, 0);
lean_inc_ref(v_a_450_);
lean_dec_ref_known(v_arg_357_, 1);
if (lean_obj_tag(v_a_450_) == 1)
{
lean_object* v_val_451_; lean_object* v_val_452_; lean_object* v_val_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_461_; 
v_val_451_ = lean_ctor_get(v_a_448_, 0);
lean_inc_ref(v_val_451_);
lean_dec_ref_known(v_a_448_, 1);
v_val_452_ = lean_ctor_get(v_a_449_, 0);
lean_inc_ref(v_val_452_);
lean_dec_ref_known(v_a_449_, 1);
v_val_453_ = lean_ctor_get(v_a_450_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v_a_450_);
if (v_isSharedCheck_461_ == 0)
{
v___x_455_ = v_a_450_;
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_val_453_);
lean_dec(v_a_450_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_457_ = l_Lean_Name_mkStr3(v_val_451_, v_val_452_, v_val_453_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_457_);
v___x_459_ = v___x_455_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
else
{
lean_object* v___x_462_; 
lean_dec_ref(v_a_450_);
lean_dec_ref_known(v_a_449_, 1);
lean_dec_ref_known(v_a_448_, 1);
v___x_462_ = lean_box(0);
return v___x_462_;
}
}
else
{
lean_object* v___x_463_; 
lean_dec_ref_known(v_a_449_, 1);
lean_dec_ref_known(v_a_448_, 1);
lean_dec_ref(v_arg_357_);
v___x_463_ = lean_box(0);
return v___x_463_;
}
}
else
{
lean_object* v___x_464_; 
lean_dec_ref(v_a_449_);
lean_dec_ref_known(v_a_448_, 1);
lean_dec_ref(v_arg_357_);
v___x_464_ = lean_box(0);
return v___x_464_;
}
}
else
{
lean_object* v___x_465_; 
lean_dec_ref_known(v_a_448_, 1);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_465_ = lean_box(0);
return v___x_465_;
}
}
else
{
lean_object* v___x_466_; 
lean_dec_ref(v_a_448_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_466_ = lean_box(0);
return v___x_466_;
}
}
else
{
lean_object* v___x_467_; 
lean_dec_ref(v_arg_435_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_467_ = lean_box(0);
return v___x_467_;
}
}
}
}
}
else
{
lean_object* v___x_468_; 
lean_dec_ref_known(v_pre_433_, 2);
lean_dec_ref_known(v_pre_432_, 2);
lean_dec_ref_known(v_declName_431_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_468_ = lean_box(0);
return v___x_468_;
}
}
else
{
lean_object* v___x_469_; 
lean_dec_ref_known(v_pre_432_, 2);
lean_dec(v_pre_433_);
lean_dec_ref_known(v_declName_431_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_469_ = lean_box(0);
return v___x_469_;
}
}
else
{
lean_object* v___x_470_; 
lean_dec_ref_known(v_declName_431_, 2);
lean_dec(v_pre_432_);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_470_ = lean_box(0);
return v___x_470_;
}
}
else
{
lean_object* v___x_471_; 
lean_dec(v_declName_431_);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_471_ = lean_box(0);
return v___x_471_;
}
}
case 5:
{
lean_object* v_fn_472_; 
lean_inc_ref(v_fn_430_);
v_fn_472_ = lean_ctor_get(v_fn_430_, 0);
switch(lean_obj_tag(v_fn_472_))
{
case 4:
{
lean_object* v_declName_473_; 
v_declName_473_ = lean_ctor_get(v_fn_472_, 0);
lean_inc(v_declName_473_);
if (lean_obj_tag(v_declName_473_) == 1)
{
lean_object* v_pre_474_; 
v_pre_474_ = lean_ctor_get(v_declName_473_, 0);
lean_inc(v_pre_474_);
if (lean_obj_tag(v_pre_474_) == 1)
{
lean_object* v_pre_475_; 
v_pre_475_ = lean_ctor_get(v_pre_474_, 0);
lean_inc(v_pre_475_);
if (lean_obj_tag(v_pre_475_) == 1)
{
lean_object* v_pre_476_; 
v_pre_476_ = lean_ctor_get(v_pre_475_, 0);
if (lean_obj_tag(v_pre_476_) == 0)
{
lean_object* v_arg_477_; lean_object* v_arg_478_; lean_object* v_str_479_; lean_object* v_str_480_; lean_object* v_str_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_arg_477_ = lean_ctor_get(v_fn_358_, 1);
lean_inc_ref(v_arg_477_);
lean_dec_ref_known(v_fn_358_, 2);
v_arg_478_ = lean_ctor_get(v_fn_430_, 1);
lean_inc_ref(v_arg_478_);
lean_dec_ref_known(v_fn_430_, 2);
v_str_479_ = lean_ctor_get(v_declName_473_, 1);
lean_inc_ref(v_str_479_);
lean_dec_ref_known(v_declName_473_, 2);
v_str_480_ = lean_ctor_get(v_pre_474_, 1);
lean_inc_ref(v_str_480_);
lean_dec_ref_known(v_pre_474_, 2);
v_str_481_ = lean_ctor_get(v_pre_475_, 1);
lean_inc_ref(v_str_481_);
lean_dec_ref_known(v_pre_475_, 2);
v___x_482_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_483_ = lean_string_dec_eq(v_str_481_, v___x_482_);
lean_dec_ref(v_str_481_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
lean_dec_ref(v_str_480_);
lean_dec_ref(v_str_479_);
lean_dec_ref(v_arg_478_);
lean_dec_ref(v_arg_477_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_484_ = lean_box(0);
return v___x_484_;
}
else
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_486_ = lean_string_dec_eq(v_str_480_, v___x_485_);
lean_dec_ref(v_str_480_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec_ref(v_str_479_);
lean_dec_ref(v_arg_478_);
lean_dec_ref(v_arg_477_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_487_ = lean_box(0);
return v___x_487_;
}
else
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__7));
v___x_489_ = lean_string_dec_eq(v_str_479_, v___x_488_);
lean_dec_ref(v_str_479_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; 
lean_dec_ref(v_arg_478_);
lean_dec_ref(v_arg_477_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_490_ = lean_box(0);
return v___x_490_;
}
else
{
if (lean_obj_tag(v_arg_478_) == 9)
{
lean_object* v_a_491_; 
v_a_491_ = lean_ctor_get(v_arg_478_, 0);
lean_inc_ref(v_a_491_);
lean_dec_ref_known(v_arg_478_, 1);
if (lean_obj_tag(v_a_491_) == 1)
{
if (lean_obj_tag(v_arg_477_) == 9)
{
lean_object* v_a_492_; 
v_a_492_ = lean_ctor_get(v_arg_477_, 0);
lean_inc_ref(v_a_492_);
lean_dec_ref_known(v_arg_477_, 1);
if (lean_obj_tag(v_a_492_) == 1)
{
if (lean_obj_tag(v_arg_359_) == 9)
{
lean_object* v_a_493_; 
v_a_493_ = lean_ctor_get(v_arg_359_, 0);
lean_inc_ref(v_a_493_);
lean_dec_ref_known(v_arg_359_, 1);
if (lean_obj_tag(v_a_493_) == 1)
{
if (lean_obj_tag(v_arg_357_) == 9)
{
lean_object* v_a_494_; 
v_a_494_ = lean_ctor_get(v_arg_357_, 0);
lean_inc_ref(v_a_494_);
lean_dec_ref_known(v_arg_357_, 1);
if (lean_obj_tag(v_a_494_) == 1)
{
lean_object* v_val_495_; lean_object* v_val_496_; lean_object* v_val_497_; lean_object* v_val_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_506_; 
v_val_495_ = lean_ctor_get(v_a_491_, 0);
lean_inc_ref(v_val_495_);
lean_dec_ref_known(v_a_491_, 1);
v_val_496_ = lean_ctor_get(v_a_492_, 0);
lean_inc_ref(v_val_496_);
lean_dec_ref_known(v_a_492_, 1);
v_val_497_ = lean_ctor_get(v_a_493_, 0);
lean_inc_ref(v_val_497_);
lean_dec_ref_known(v_a_493_, 1);
v_val_498_ = lean_ctor_get(v_a_494_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v_a_494_);
if (v_isSharedCheck_506_ == 0)
{
v___x_500_ = v_a_494_;
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_val_498_);
lean_dec(v_a_494_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = l_Lean_Name_mkStr4(v_val_495_, v_val_496_, v_val_497_, v_val_498_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_502_);
v___x_504_ = v___x_500_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
else
{
lean_object* v___x_507_; 
lean_dec_ref(v_a_494_);
lean_dec_ref_known(v_a_493_, 1);
lean_dec_ref_known(v_a_492_, 1);
lean_dec_ref_known(v_a_491_, 1);
v___x_507_ = lean_box(0);
return v___x_507_;
}
}
else
{
lean_object* v___x_508_; 
lean_dec_ref_known(v_a_493_, 1);
lean_dec_ref_known(v_a_492_, 1);
lean_dec_ref_known(v_a_491_, 1);
lean_dec_ref(v_arg_357_);
v___x_508_ = lean_box(0);
return v___x_508_;
}
}
else
{
lean_object* v___x_509_; 
lean_dec_ref(v_a_493_);
lean_dec_ref_known(v_a_492_, 1);
lean_dec_ref_known(v_a_491_, 1);
lean_dec_ref(v_arg_357_);
v___x_509_ = lean_box(0);
return v___x_509_;
}
}
else
{
lean_object* v___x_510_; 
lean_dec_ref_known(v_a_492_, 1);
lean_dec_ref_known(v_a_491_, 1);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_510_ = lean_box(0);
return v___x_510_;
}
}
else
{
lean_object* v___x_511_; 
lean_dec_ref(v_a_492_);
lean_dec_ref_known(v_a_491_, 1);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_511_ = lean_box(0);
return v___x_511_;
}
}
else
{
lean_object* v___x_512_; 
lean_dec_ref_known(v_a_491_, 1);
lean_dec_ref(v_arg_477_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_512_ = lean_box(0);
return v___x_512_;
}
}
else
{
lean_object* v___x_513_; 
lean_dec_ref(v_a_491_);
lean_dec_ref(v_arg_477_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_513_ = lean_box(0);
return v___x_513_;
}
}
else
{
lean_object* v___x_514_; 
lean_dec_ref(v_arg_478_);
lean_dec_ref(v_arg_477_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_514_ = lean_box(0);
return v___x_514_;
}
}
}
}
}
else
{
lean_object* v___x_515_; 
lean_dec_ref_known(v_pre_475_, 2);
lean_dec_ref_known(v_pre_474_, 2);
lean_dec_ref_known(v_declName_473_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_515_ = lean_box(0);
return v___x_515_;
}
}
else
{
lean_object* v___x_516_; 
lean_dec(v_pre_475_);
lean_dec_ref_known(v_pre_474_, 2);
lean_dec_ref_known(v_declName_473_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_516_ = lean_box(0);
return v___x_516_;
}
}
else
{
lean_object* v___x_517_; 
lean_dec_ref_known(v_declName_473_, 2);
lean_dec(v_pre_474_);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_517_ = lean_box(0);
return v___x_517_;
}
}
else
{
lean_object* v___x_518_; 
lean_dec(v_declName_473_);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_518_ = lean_box(0);
return v___x_518_;
}
}
case 5:
{
lean_object* v_fn_519_; 
lean_inc_ref(v_fn_472_);
v_fn_519_ = lean_ctor_get(v_fn_472_, 0);
switch(lean_obj_tag(v_fn_519_))
{
case 4:
{
lean_object* v_declName_520_; 
v_declName_520_ = lean_ctor_get(v_fn_519_, 0);
lean_inc(v_declName_520_);
if (lean_obj_tag(v_declName_520_) == 1)
{
lean_object* v_pre_521_; 
v_pre_521_ = lean_ctor_get(v_declName_520_, 0);
lean_inc(v_pre_521_);
if (lean_obj_tag(v_pre_521_) == 1)
{
lean_object* v_pre_522_; 
v_pre_522_ = lean_ctor_get(v_pre_521_, 0);
lean_inc(v_pre_522_);
if (lean_obj_tag(v_pre_522_) == 1)
{
lean_object* v_pre_523_; 
v_pre_523_ = lean_ctor_get(v_pre_522_, 0);
if (lean_obj_tag(v_pre_523_) == 0)
{
lean_object* v_arg_524_; lean_object* v_arg_525_; lean_object* v_arg_526_; lean_object* v_str_527_; lean_object* v_str_528_; lean_object* v_str_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_arg_524_ = lean_ctor_get(v_fn_358_, 1);
lean_inc_ref(v_arg_524_);
lean_dec_ref_known(v_fn_358_, 2);
v_arg_525_ = lean_ctor_get(v_fn_430_, 1);
lean_inc_ref(v_arg_525_);
lean_dec_ref_known(v_fn_430_, 2);
v_arg_526_ = lean_ctor_get(v_fn_472_, 1);
lean_inc_ref(v_arg_526_);
lean_dec_ref_known(v_fn_472_, 2);
v_str_527_ = lean_ctor_get(v_declName_520_, 1);
lean_inc_ref(v_str_527_);
lean_dec_ref_known(v_declName_520_, 2);
v_str_528_ = lean_ctor_get(v_pre_521_, 1);
lean_inc_ref(v_str_528_);
lean_dec_ref_known(v_pre_521_, 2);
v_str_529_ = lean_ctor_get(v_pre_522_, 1);
lean_inc_ref(v_str_529_);
lean_dec_ref_known(v_pre_522_, 2);
v___x_530_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_531_ = lean_string_dec_eq(v_str_529_, v___x_530_);
lean_dec_ref(v_str_529_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
lean_dec_ref(v_str_528_);
lean_dec_ref(v_str_527_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_525_);
lean_dec_ref(v_arg_524_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_532_ = lean_box(0);
return v___x_532_;
}
else
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_534_ = lean_string_dec_eq(v_str_528_, v___x_533_);
lean_dec_ref(v_str_528_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
lean_dec_ref(v_str_527_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_525_);
lean_dec_ref(v_arg_524_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_535_ = lean_box(0);
return v___x_535_;
}
else
{
lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_536_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__8));
v___x_537_ = lean_string_dec_eq(v_str_527_, v___x_536_);
lean_dec_ref(v_str_527_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_525_);
lean_dec_ref(v_arg_524_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_538_ = lean_box(0);
return v___x_538_;
}
else
{
if (lean_obj_tag(v_arg_526_) == 9)
{
lean_object* v_a_539_; 
v_a_539_ = lean_ctor_get(v_arg_526_, 0);
lean_inc_ref(v_a_539_);
lean_dec_ref_known(v_arg_526_, 1);
if (lean_obj_tag(v_a_539_) == 1)
{
if (lean_obj_tag(v_arg_525_) == 9)
{
lean_object* v_a_540_; 
v_a_540_ = lean_ctor_get(v_arg_525_, 0);
lean_inc_ref(v_a_540_);
lean_dec_ref_known(v_arg_525_, 1);
if (lean_obj_tag(v_a_540_) == 1)
{
if (lean_obj_tag(v_arg_524_) == 9)
{
lean_object* v_a_541_; 
v_a_541_ = lean_ctor_get(v_arg_524_, 0);
lean_inc_ref(v_a_541_);
lean_dec_ref_known(v_arg_524_, 1);
if (lean_obj_tag(v_a_541_) == 1)
{
if (lean_obj_tag(v_arg_359_) == 9)
{
lean_object* v_a_542_; 
v_a_542_ = lean_ctor_get(v_arg_359_, 0);
lean_inc_ref(v_a_542_);
lean_dec_ref_known(v_arg_359_, 1);
if (lean_obj_tag(v_a_542_) == 1)
{
if (lean_obj_tag(v_arg_357_) == 9)
{
lean_object* v_a_543_; 
v_a_543_ = lean_ctor_get(v_arg_357_, 0);
lean_inc_ref(v_a_543_);
lean_dec_ref_known(v_arg_357_, 1);
if (lean_obj_tag(v_a_543_) == 1)
{
lean_object* v_val_544_; lean_object* v_val_545_; lean_object* v_val_546_; lean_object* v_val_547_; lean_object* v_val_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_556_; 
v_val_544_ = lean_ctor_get(v_a_539_, 0);
lean_inc_ref(v_val_544_);
lean_dec_ref_known(v_a_539_, 1);
v_val_545_ = lean_ctor_get(v_a_540_, 0);
lean_inc_ref(v_val_545_);
lean_dec_ref_known(v_a_540_, 1);
v_val_546_ = lean_ctor_get(v_a_541_, 0);
lean_inc_ref(v_val_546_);
lean_dec_ref_known(v_a_541_, 1);
v_val_547_ = lean_ctor_get(v_a_542_, 0);
lean_inc_ref(v_val_547_);
lean_dec_ref_known(v_a_542_, 1);
v_val_548_ = lean_ctor_get(v_a_543_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v_a_543_);
if (v_isSharedCheck_556_ == 0)
{
v___x_550_ = v_a_543_;
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_val_548_);
lean_dec(v_a_543_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = l_Lean_Name_mkStr5(v_val_544_, v_val_545_, v_val_546_, v_val_547_, v_val_548_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_552_);
v___x_554_ = v___x_550_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
else
{
lean_object* v___x_557_; 
lean_dec_ref(v_a_543_);
lean_dec_ref_known(v_a_542_, 1);
lean_dec_ref_known(v_a_541_, 1);
lean_dec_ref_known(v_a_540_, 1);
lean_dec_ref_known(v_a_539_, 1);
v___x_557_ = lean_box(0);
return v___x_557_;
}
}
else
{
lean_object* v___x_558_; 
lean_dec_ref_known(v_a_542_, 1);
lean_dec_ref_known(v_a_541_, 1);
lean_dec_ref_known(v_a_540_, 1);
lean_dec_ref_known(v_a_539_, 1);
lean_dec_ref(v_arg_357_);
v___x_558_ = lean_box(0);
return v___x_558_;
}
}
else
{
lean_object* v___x_559_; 
lean_dec_ref(v_a_542_);
lean_dec_ref_known(v_a_541_, 1);
lean_dec_ref_known(v_a_540_, 1);
lean_dec_ref_known(v_a_539_, 1);
lean_dec_ref(v_arg_357_);
v___x_559_ = lean_box(0);
return v___x_559_;
}
}
else
{
lean_object* v___x_560_; 
lean_dec_ref_known(v_a_541_, 1);
lean_dec_ref_known(v_a_540_, 1);
lean_dec_ref_known(v_a_539_, 1);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_560_ = lean_box(0);
return v___x_560_;
}
}
else
{
lean_object* v___x_561_; 
lean_dec_ref(v_a_541_);
lean_dec_ref_known(v_a_540_, 1);
lean_dec_ref_known(v_a_539_, 1);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_561_ = lean_box(0);
return v___x_561_;
}
}
else
{
lean_object* v___x_562_; 
lean_dec_ref_known(v_a_540_, 1);
lean_dec_ref_known(v_a_539_, 1);
lean_dec_ref(v_arg_524_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_562_ = lean_box(0);
return v___x_562_;
}
}
else
{
lean_object* v___x_563_; 
lean_dec_ref(v_a_540_);
lean_dec_ref_known(v_a_539_, 1);
lean_dec_ref(v_arg_524_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_563_ = lean_box(0);
return v___x_563_;
}
}
else
{
lean_object* v___x_564_; 
lean_dec_ref_known(v_a_539_, 1);
lean_dec_ref(v_arg_525_);
lean_dec_ref(v_arg_524_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_564_ = lean_box(0);
return v___x_564_;
}
}
else
{
lean_object* v___x_565_; 
lean_dec_ref(v_a_539_);
lean_dec_ref(v_arg_525_);
lean_dec_ref(v_arg_524_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_565_ = lean_box(0);
return v___x_565_;
}
}
else
{
lean_object* v___x_566_; 
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_525_);
lean_dec_ref(v_arg_524_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_566_ = lean_box(0);
return v___x_566_;
}
}
}
}
}
else
{
lean_object* v___x_567_; 
lean_dec_ref_known(v_pre_522_, 2);
lean_dec_ref_known(v_pre_521_, 2);
lean_dec_ref_known(v_declName_520_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_567_ = lean_box(0);
return v___x_567_;
}
}
else
{
lean_object* v___x_568_; 
lean_dec_ref_known(v_pre_521_, 2);
lean_dec(v_pre_522_);
lean_dec_ref_known(v_declName_520_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_568_ = lean_box(0);
return v___x_568_;
}
}
else
{
lean_object* v___x_569_; 
lean_dec(v_pre_521_);
lean_dec_ref_known(v_declName_520_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_569_ = lean_box(0);
return v___x_569_;
}
}
else
{
lean_object* v___x_570_; 
lean_dec(v_declName_520_);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_570_ = lean_box(0);
return v___x_570_;
}
}
case 5:
{
lean_object* v_fn_571_; 
lean_inc_ref(v_fn_519_);
v_fn_571_ = lean_ctor_get(v_fn_519_, 0);
switch(lean_obj_tag(v_fn_571_))
{
case 4:
{
lean_object* v_declName_572_; 
v_declName_572_ = lean_ctor_get(v_fn_571_, 0);
lean_inc(v_declName_572_);
if (lean_obj_tag(v_declName_572_) == 1)
{
lean_object* v_pre_573_; 
v_pre_573_ = lean_ctor_get(v_declName_572_, 0);
lean_inc(v_pre_573_);
if (lean_obj_tag(v_pre_573_) == 1)
{
lean_object* v_pre_574_; 
v_pre_574_ = lean_ctor_get(v_pre_573_, 0);
lean_inc(v_pre_574_);
if (lean_obj_tag(v_pre_574_) == 1)
{
lean_object* v_pre_575_; 
v_pre_575_ = lean_ctor_get(v_pre_574_, 0);
if (lean_obj_tag(v_pre_575_) == 0)
{
lean_object* v_arg_576_; lean_object* v_arg_577_; lean_object* v_arg_578_; lean_object* v_arg_579_; lean_object* v_str_580_; lean_object* v_str_581_; lean_object* v_str_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v_arg_576_ = lean_ctor_get(v_fn_358_, 1);
lean_inc_ref(v_arg_576_);
lean_dec_ref_known(v_fn_358_, 2);
v_arg_577_ = lean_ctor_get(v_fn_430_, 1);
lean_inc_ref(v_arg_577_);
lean_dec_ref_known(v_fn_430_, 2);
v_arg_578_ = lean_ctor_get(v_fn_472_, 1);
lean_inc_ref(v_arg_578_);
lean_dec_ref_known(v_fn_472_, 2);
v_arg_579_ = lean_ctor_get(v_fn_519_, 1);
lean_inc_ref(v_arg_579_);
lean_dec_ref_known(v_fn_519_, 2);
v_str_580_ = lean_ctor_get(v_declName_572_, 1);
lean_inc_ref(v_str_580_);
lean_dec_ref_known(v_declName_572_, 2);
v_str_581_ = lean_ctor_get(v_pre_573_, 1);
lean_inc_ref(v_str_581_);
lean_dec_ref_known(v_pre_573_, 2);
v_str_582_ = lean_ctor_get(v_pre_574_, 1);
lean_inc_ref(v_str_582_);
lean_dec_ref_known(v_pre_574_, 2);
v___x_583_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_584_ = lean_string_dec_eq(v_str_582_, v___x_583_);
lean_dec_ref(v_str_582_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
lean_dec_ref(v_str_581_);
lean_dec_ref(v_str_580_);
lean_dec_ref(v_arg_579_);
lean_dec_ref(v_arg_578_);
lean_dec_ref(v_arg_577_);
lean_dec_ref(v_arg_576_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_585_ = lean_box(0);
return v___x_585_;
}
else
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_587_ = lean_string_dec_eq(v_str_581_, v___x_586_);
lean_dec_ref(v_str_581_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
lean_dec_ref(v_str_580_);
lean_dec_ref(v_arg_579_);
lean_dec_ref(v_arg_578_);
lean_dec_ref(v_arg_577_);
lean_dec_ref(v_arg_576_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_588_ = lean_box(0);
return v___x_588_;
}
else
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__9));
v___x_590_ = lean_string_dec_eq(v_str_580_, v___x_589_);
lean_dec_ref(v_str_580_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
lean_dec_ref(v_arg_579_);
lean_dec_ref(v_arg_578_);
lean_dec_ref(v_arg_577_);
lean_dec_ref(v_arg_576_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_591_ = lean_box(0);
return v___x_591_;
}
else
{
if (lean_obj_tag(v_arg_579_) == 9)
{
lean_object* v_a_592_; 
v_a_592_ = lean_ctor_get(v_arg_579_, 0);
lean_inc_ref(v_a_592_);
lean_dec_ref_known(v_arg_579_, 1);
if (lean_obj_tag(v_a_592_) == 1)
{
if (lean_obj_tag(v_arg_578_) == 9)
{
lean_object* v_a_593_; 
v_a_593_ = lean_ctor_get(v_arg_578_, 0);
lean_inc_ref(v_a_593_);
lean_dec_ref_known(v_arg_578_, 1);
if (lean_obj_tag(v_a_593_) == 1)
{
if (lean_obj_tag(v_arg_577_) == 9)
{
lean_object* v_a_594_; 
v_a_594_ = lean_ctor_get(v_arg_577_, 0);
lean_inc_ref(v_a_594_);
lean_dec_ref_known(v_arg_577_, 1);
if (lean_obj_tag(v_a_594_) == 1)
{
if (lean_obj_tag(v_arg_576_) == 9)
{
lean_object* v_a_595_; 
v_a_595_ = lean_ctor_get(v_arg_576_, 0);
lean_inc_ref(v_a_595_);
lean_dec_ref_known(v_arg_576_, 1);
if (lean_obj_tag(v_a_595_) == 1)
{
if (lean_obj_tag(v_arg_359_) == 9)
{
lean_object* v_a_596_; 
v_a_596_ = lean_ctor_get(v_arg_359_, 0);
lean_inc_ref(v_a_596_);
lean_dec_ref_known(v_arg_359_, 1);
if (lean_obj_tag(v_a_596_) == 1)
{
if (lean_obj_tag(v_arg_357_) == 9)
{
lean_object* v_a_597_; 
v_a_597_ = lean_ctor_get(v_arg_357_, 0);
lean_inc_ref(v_a_597_);
lean_dec_ref_known(v_arg_357_, 1);
if (lean_obj_tag(v_a_597_) == 1)
{
lean_object* v_val_598_; lean_object* v_val_599_; lean_object* v_val_600_; lean_object* v_val_601_; lean_object* v_val_602_; lean_object* v_val_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_611_; 
v_val_598_ = lean_ctor_get(v_a_592_, 0);
lean_inc_ref(v_val_598_);
lean_dec_ref_known(v_a_592_, 1);
v_val_599_ = lean_ctor_get(v_a_593_, 0);
lean_inc_ref(v_val_599_);
lean_dec_ref_known(v_a_593_, 1);
v_val_600_ = lean_ctor_get(v_a_594_, 0);
lean_inc_ref(v_val_600_);
lean_dec_ref_known(v_a_594_, 1);
v_val_601_ = lean_ctor_get(v_a_595_, 0);
lean_inc_ref(v_val_601_);
lean_dec_ref_known(v_a_595_, 1);
v_val_602_ = lean_ctor_get(v_a_596_, 0);
lean_inc_ref(v_val_602_);
lean_dec_ref_known(v_a_596_, 1);
v_val_603_ = lean_ctor_get(v_a_597_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_a_597_);
if (v_isSharedCheck_611_ == 0)
{
v___x_605_ = v_a_597_;
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_val_603_);
lean_dec(v_a_597_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_607_ = l_Lean_Name_mkStr6(v_val_598_, v_val_599_, v_val_600_, v_val_601_, v_val_602_, v_val_603_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_607_);
v___x_609_ = v___x_605_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
else
{
lean_object* v___x_612_; 
lean_dec_ref(v_a_597_);
lean_dec_ref_known(v_a_596_, 1);
lean_dec_ref_known(v_a_595_, 1);
lean_dec_ref_known(v_a_594_, 1);
lean_dec_ref_known(v_a_593_, 1);
lean_dec_ref_known(v_a_592_, 1);
v___x_612_ = lean_box(0);
return v___x_612_;
}
}
else
{
lean_object* v___x_613_; 
lean_dec_ref_known(v_a_596_, 1);
lean_dec_ref_known(v_a_595_, 1);
lean_dec_ref_known(v_a_594_, 1);
lean_dec_ref_known(v_a_593_, 1);
lean_dec_ref_known(v_a_592_, 1);
lean_dec_ref(v_arg_357_);
v___x_613_ = lean_box(0);
return v___x_613_;
}
}
else
{
lean_object* v___x_614_; 
lean_dec_ref(v_a_596_);
lean_dec_ref_known(v_a_595_, 1);
lean_dec_ref_known(v_a_594_, 1);
lean_dec_ref_known(v_a_593_, 1);
lean_dec_ref_known(v_a_592_, 1);
lean_dec_ref(v_arg_357_);
v___x_614_ = lean_box(0);
return v___x_614_;
}
}
else
{
lean_object* v___x_615_; 
lean_dec_ref_known(v_a_595_, 1);
lean_dec_ref_known(v_a_594_, 1);
lean_dec_ref_known(v_a_593_, 1);
lean_dec_ref_known(v_a_592_, 1);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_615_ = lean_box(0);
return v___x_615_;
}
}
else
{
lean_object* v___x_616_; 
lean_dec_ref(v_a_595_);
lean_dec_ref_known(v_a_594_, 1);
lean_dec_ref_known(v_a_593_, 1);
lean_dec_ref_known(v_a_592_, 1);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_616_ = lean_box(0);
return v___x_616_;
}
}
else
{
lean_object* v___x_617_; 
lean_dec_ref_known(v_a_594_, 1);
lean_dec_ref_known(v_a_593_, 1);
lean_dec_ref_known(v_a_592_, 1);
lean_dec_ref(v_arg_576_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_617_ = lean_box(0);
return v___x_617_;
}
}
else
{
lean_object* v___x_618_; 
lean_dec_ref(v_a_594_);
lean_dec_ref_known(v_a_593_, 1);
lean_dec_ref_known(v_a_592_, 1);
lean_dec_ref(v_arg_576_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_618_ = lean_box(0);
return v___x_618_;
}
}
else
{
lean_object* v___x_619_; 
lean_dec_ref_known(v_a_593_, 1);
lean_dec_ref_known(v_a_592_, 1);
lean_dec_ref(v_arg_577_);
lean_dec_ref(v_arg_576_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_619_ = lean_box(0);
return v___x_619_;
}
}
else
{
lean_object* v___x_620_; 
lean_dec_ref(v_a_593_);
lean_dec_ref_known(v_a_592_, 1);
lean_dec_ref(v_arg_577_);
lean_dec_ref(v_arg_576_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_620_ = lean_box(0);
return v___x_620_;
}
}
else
{
lean_object* v___x_621_; 
lean_dec_ref_known(v_a_592_, 1);
lean_dec_ref(v_arg_578_);
lean_dec_ref(v_arg_577_);
lean_dec_ref(v_arg_576_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_621_ = lean_box(0);
return v___x_621_;
}
}
else
{
lean_object* v___x_622_; 
lean_dec_ref(v_a_592_);
lean_dec_ref(v_arg_578_);
lean_dec_ref(v_arg_577_);
lean_dec_ref(v_arg_576_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_622_ = lean_box(0);
return v___x_622_;
}
}
else
{
lean_object* v___x_623_; 
lean_dec_ref(v_arg_579_);
lean_dec_ref(v_arg_578_);
lean_dec_ref(v_arg_577_);
lean_dec_ref(v_arg_576_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_623_ = lean_box(0);
return v___x_623_;
}
}
}
}
}
else
{
lean_object* v___x_624_; 
lean_dec_ref_known(v_pre_574_, 2);
lean_dec_ref_known(v_pre_573_, 2);
lean_dec_ref_known(v_declName_572_, 2);
lean_dec_ref_known(v_fn_519_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_624_ = lean_box(0);
return v___x_624_;
}
}
else
{
lean_object* v___x_625_; 
lean_dec_ref_known(v_pre_573_, 2);
lean_dec(v_pre_574_);
lean_dec_ref_known(v_declName_572_, 2);
lean_dec_ref_known(v_fn_519_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_625_ = lean_box(0);
return v___x_625_;
}
}
else
{
lean_object* v___x_626_; 
lean_dec_ref_known(v_declName_572_, 2);
lean_dec(v_pre_573_);
lean_dec_ref_known(v_fn_519_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_626_ = lean_box(0);
return v___x_626_;
}
}
else
{
lean_object* v___x_627_; 
lean_dec(v_declName_572_);
lean_dec_ref_known(v_fn_519_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_627_ = lean_box(0);
return v___x_627_;
}
}
case 5:
{
lean_object* v_fn_628_; 
lean_inc_ref(v_fn_571_);
v_fn_628_ = lean_ctor_get(v_fn_571_, 0);
switch(lean_obj_tag(v_fn_628_))
{
case 4:
{
lean_object* v_declName_629_; 
v_declName_629_ = lean_ctor_get(v_fn_628_, 0);
lean_inc(v_declName_629_);
if (lean_obj_tag(v_declName_629_) == 1)
{
lean_object* v_pre_630_; 
v_pre_630_ = lean_ctor_get(v_declName_629_, 0);
lean_inc(v_pre_630_);
if (lean_obj_tag(v_pre_630_) == 1)
{
lean_object* v_pre_631_; 
v_pre_631_ = lean_ctor_get(v_pre_630_, 0);
lean_inc(v_pre_631_);
if (lean_obj_tag(v_pre_631_) == 1)
{
lean_object* v_pre_632_; 
v_pre_632_ = lean_ctor_get(v_pre_631_, 0);
if (lean_obj_tag(v_pre_632_) == 0)
{
lean_object* v_arg_633_; lean_object* v_arg_634_; lean_object* v_arg_635_; lean_object* v_arg_636_; lean_object* v_arg_637_; lean_object* v_str_638_; lean_object* v_str_639_; lean_object* v_str_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_arg_633_ = lean_ctor_get(v_fn_358_, 1);
lean_inc_ref(v_arg_633_);
lean_dec_ref_known(v_fn_358_, 2);
v_arg_634_ = lean_ctor_get(v_fn_430_, 1);
lean_inc_ref(v_arg_634_);
lean_dec_ref_known(v_fn_430_, 2);
v_arg_635_ = lean_ctor_get(v_fn_472_, 1);
lean_inc_ref(v_arg_635_);
lean_dec_ref_known(v_fn_472_, 2);
v_arg_636_ = lean_ctor_get(v_fn_519_, 1);
lean_inc_ref(v_arg_636_);
lean_dec_ref_known(v_fn_519_, 2);
v_arg_637_ = lean_ctor_get(v_fn_571_, 1);
lean_inc_ref(v_arg_637_);
lean_dec_ref_known(v_fn_571_, 2);
v_str_638_ = lean_ctor_get(v_declName_629_, 1);
lean_inc_ref(v_str_638_);
lean_dec_ref_known(v_declName_629_, 2);
v_str_639_ = lean_ctor_get(v_pre_630_, 1);
lean_inc_ref(v_str_639_);
lean_dec_ref_known(v_pre_630_, 2);
v_str_640_ = lean_ctor_get(v_pre_631_, 1);
lean_inc_ref(v_str_640_);
lean_dec_ref_known(v_pre_631_, 2);
v___x_641_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_642_ = lean_string_dec_eq(v_str_640_, v___x_641_);
lean_dec_ref(v_str_640_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
lean_dec_ref(v_str_639_);
lean_dec_ref(v_str_638_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_arg_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_643_ = lean_box(0);
return v___x_643_;
}
else
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_645_ = lean_string_dec_eq(v_str_639_, v___x_644_);
lean_dec_ref(v_str_639_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
lean_dec_ref(v_str_638_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_arg_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_646_ = lean_box(0);
return v___x_646_;
}
else
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__10));
v___x_648_ = lean_string_dec_eq(v_str_638_, v___x_647_);
lean_dec_ref(v_str_638_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; 
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_arg_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_649_ = lean_box(0);
return v___x_649_;
}
else
{
if (lean_obj_tag(v_arg_637_) == 9)
{
lean_object* v_a_650_; 
v_a_650_ = lean_ctor_get(v_arg_637_, 0);
lean_inc_ref(v_a_650_);
lean_dec_ref_known(v_arg_637_, 1);
if (lean_obj_tag(v_a_650_) == 1)
{
if (lean_obj_tag(v_arg_636_) == 9)
{
lean_object* v_a_651_; 
v_a_651_ = lean_ctor_get(v_arg_636_, 0);
lean_inc_ref(v_a_651_);
lean_dec_ref_known(v_arg_636_, 1);
if (lean_obj_tag(v_a_651_) == 1)
{
if (lean_obj_tag(v_arg_635_) == 9)
{
lean_object* v_a_652_; 
v_a_652_ = lean_ctor_get(v_arg_635_, 0);
lean_inc_ref(v_a_652_);
lean_dec_ref_known(v_arg_635_, 1);
if (lean_obj_tag(v_a_652_) == 1)
{
if (lean_obj_tag(v_arg_634_) == 9)
{
lean_object* v_a_653_; 
v_a_653_ = lean_ctor_get(v_arg_634_, 0);
lean_inc_ref(v_a_653_);
lean_dec_ref_known(v_arg_634_, 1);
if (lean_obj_tag(v_a_653_) == 1)
{
if (lean_obj_tag(v_arg_633_) == 9)
{
lean_object* v_a_654_; 
v_a_654_ = lean_ctor_get(v_arg_633_, 0);
lean_inc_ref(v_a_654_);
lean_dec_ref_known(v_arg_633_, 1);
if (lean_obj_tag(v_a_654_) == 1)
{
if (lean_obj_tag(v_arg_359_) == 9)
{
lean_object* v_a_655_; 
v_a_655_ = lean_ctor_get(v_arg_359_, 0);
lean_inc_ref(v_a_655_);
lean_dec_ref_known(v_arg_359_, 1);
if (lean_obj_tag(v_a_655_) == 1)
{
if (lean_obj_tag(v_arg_357_) == 9)
{
lean_object* v_a_656_; 
v_a_656_ = lean_ctor_get(v_arg_357_, 0);
lean_inc_ref(v_a_656_);
lean_dec_ref_known(v_arg_357_, 1);
if (lean_obj_tag(v_a_656_) == 1)
{
lean_object* v_val_657_; lean_object* v_val_658_; lean_object* v_val_659_; lean_object* v_val_660_; lean_object* v_val_661_; lean_object* v_val_662_; lean_object* v_val_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_671_; 
v_val_657_ = lean_ctor_get(v_a_650_, 0);
lean_inc_ref(v_val_657_);
lean_dec_ref_known(v_a_650_, 1);
v_val_658_ = lean_ctor_get(v_a_651_, 0);
lean_inc_ref(v_val_658_);
lean_dec_ref_known(v_a_651_, 1);
v_val_659_ = lean_ctor_get(v_a_652_, 0);
lean_inc_ref(v_val_659_);
lean_dec_ref_known(v_a_652_, 1);
v_val_660_ = lean_ctor_get(v_a_653_, 0);
lean_inc_ref(v_val_660_);
lean_dec_ref_known(v_a_653_, 1);
v_val_661_ = lean_ctor_get(v_a_654_, 0);
lean_inc_ref(v_val_661_);
lean_dec_ref_known(v_a_654_, 1);
v_val_662_ = lean_ctor_get(v_a_655_, 0);
lean_inc_ref(v_val_662_);
lean_dec_ref_known(v_a_655_, 1);
v_val_663_ = lean_ctor_get(v_a_656_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v_a_656_);
if (v_isSharedCheck_671_ == 0)
{
v___x_665_ = v_a_656_;
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_val_663_);
lean_dec(v_a_656_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = l_Lean_Name_mkStr7(v_val_657_, v_val_658_, v_val_659_, v_val_660_, v_val_661_, v_val_662_, v_val_663_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v___x_672_; 
lean_dec_ref(v_a_656_);
lean_dec_ref_known(v_a_655_, 1);
lean_dec_ref_known(v_a_654_, 1);
lean_dec_ref_known(v_a_653_, 1);
lean_dec_ref_known(v_a_652_, 1);
lean_dec_ref_known(v_a_651_, 1);
lean_dec_ref_known(v_a_650_, 1);
v___x_672_ = lean_box(0);
return v___x_672_;
}
}
else
{
lean_object* v___x_673_; 
lean_dec_ref_known(v_a_655_, 1);
lean_dec_ref_known(v_a_654_, 1);
lean_dec_ref_known(v_a_653_, 1);
lean_dec_ref_known(v_a_652_, 1);
lean_dec_ref_known(v_a_651_, 1);
lean_dec_ref_known(v_a_650_, 1);
lean_dec_ref(v_arg_357_);
v___x_673_ = lean_box(0);
return v___x_673_;
}
}
else
{
lean_object* v___x_674_; 
lean_dec_ref(v_a_655_);
lean_dec_ref_known(v_a_654_, 1);
lean_dec_ref_known(v_a_653_, 1);
lean_dec_ref_known(v_a_652_, 1);
lean_dec_ref_known(v_a_651_, 1);
lean_dec_ref_known(v_a_650_, 1);
lean_dec_ref(v_arg_357_);
v___x_674_ = lean_box(0);
return v___x_674_;
}
}
else
{
lean_object* v___x_675_; 
lean_dec_ref_known(v_a_654_, 1);
lean_dec_ref_known(v_a_653_, 1);
lean_dec_ref_known(v_a_652_, 1);
lean_dec_ref_known(v_a_651_, 1);
lean_dec_ref_known(v_a_650_, 1);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_675_ = lean_box(0);
return v___x_675_;
}
}
else
{
lean_object* v___x_676_; 
lean_dec_ref(v_a_654_);
lean_dec_ref_known(v_a_653_, 1);
lean_dec_ref_known(v_a_652_, 1);
lean_dec_ref_known(v_a_651_, 1);
lean_dec_ref_known(v_a_650_, 1);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_676_ = lean_box(0);
return v___x_676_;
}
}
else
{
lean_object* v___x_677_; 
lean_dec_ref_known(v_a_653_, 1);
lean_dec_ref_known(v_a_652_, 1);
lean_dec_ref_known(v_a_651_, 1);
lean_dec_ref_known(v_a_650_, 1);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_677_ = lean_box(0);
return v___x_677_;
}
}
else
{
lean_object* v___x_678_; 
lean_dec_ref(v_a_653_);
lean_dec_ref_known(v_a_652_, 1);
lean_dec_ref_known(v_a_651_, 1);
lean_dec_ref_known(v_a_650_, 1);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_678_ = lean_box(0);
return v___x_678_;
}
}
else
{
lean_object* v___x_679_; 
lean_dec_ref_known(v_a_652_, 1);
lean_dec_ref_known(v_a_651_, 1);
lean_dec_ref_known(v_a_650_, 1);
lean_dec_ref(v_arg_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_679_ = lean_box(0);
return v___x_679_;
}
}
else
{
lean_object* v___x_680_; 
lean_dec_ref(v_a_652_);
lean_dec_ref_known(v_a_651_, 1);
lean_dec_ref_known(v_a_650_, 1);
lean_dec_ref(v_arg_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_680_ = lean_box(0);
return v___x_680_;
}
}
else
{
lean_object* v___x_681_; 
lean_dec_ref_known(v_a_651_, 1);
lean_dec_ref_known(v_a_650_, 1);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_arg_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_681_ = lean_box(0);
return v___x_681_;
}
}
else
{
lean_object* v___x_682_; 
lean_dec_ref(v_a_651_);
lean_dec_ref_known(v_a_650_, 1);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_arg_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_682_ = lean_box(0);
return v___x_682_;
}
}
else
{
lean_object* v___x_683_; 
lean_dec_ref_known(v_a_650_, 1);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_arg_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_683_ = lean_box(0);
return v___x_683_;
}
}
else
{
lean_object* v___x_684_; 
lean_dec_ref(v_a_650_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_arg_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_684_ = lean_box(0);
return v___x_684_;
}
}
else
{
lean_object* v___x_685_; 
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_arg_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_685_ = lean_box(0);
return v___x_685_;
}
}
}
}
}
else
{
lean_object* v___x_686_; 
lean_dec_ref_known(v_pre_631_, 2);
lean_dec_ref_known(v_pre_630_, 2);
lean_dec_ref_known(v_declName_629_, 2);
lean_dec_ref_known(v_fn_571_, 2);
lean_dec_ref_known(v_fn_519_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_686_ = lean_box(0);
return v___x_686_;
}
}
else
{
lean_object* v___x_687_; 
lean_dec(v_pre_631_);
lean_dec_ref_known(v_pre_630_, 2);
lean_dec_ref_known(v_declName_629_, 2);
lean_dec_ref_known(v_fn_571_, 2);
lean_dec_ref_known(v_fn_519_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_687_ = lean_box(0);
return v___x_687_;
}
}
else
{
lean_object* v___x_688_; 
lean_dec_ref_known(v_declName_629_, 2);
lean_dec(v_pre_630_);
lean_dec_ref_known(v_fn_571_, 2);
lean_dec_ref_known(v_fn_519_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_688_ = lean_box(0);
return v___x_688_;
}
}
else
{
lean_object* v___x_689_; 
lean_dec(v_declName_629_);
lean_dec_ref_known(v_fn_571_, 2);
lean_dec_ref_known(v_fn_519_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_689_ = lean_box(0);
return v___x_689_;
}
}
case 5:
{
lean_object* v_fn_690_; 
lean_inc_ref(v_fn_628_);
v_fn_690_ = lean_ctor_get(v_fn_628_, 0);
if (lean_obj_tag(v_fn_690_) == 4)
{
lean_object* v_declName_691_; 
v_declName_691_ = lean_ctor_get(v_fn_690_, 0);
lean_inc(v_declName_691_);
if (lean_obj_tag(v_declName_691_) == 1)
{
lean_object* v_pre_692_; 
v_pre_692_ = lean_ctor_get(v_declName_691_, 0);
lean_inc(v_pre_692_);
if (lean_obj_tag(v_pre_692_) == 1)
{
lean_object* v_pre_693_; 
v_pre_693_ = lean_ctor_get(v_pre_692_, 0);
lean_inc(v_pre_693_);
if (lean_obj_tag(v_pre_693_) == 1)
{
lean_object* v_pre_694_; 
v_pre_694_ = lean_ctor_get(v_pre_693_, 0);
if (lean_obj_tag(v_pre_694_) == 0)
{
lean_object* v_arg_695_; lean_object* v_arg_696_; lean_object* v_arg_697_; lean_object* v_arg_698_; lean_object* v_arg_699_; lean_object* v_arg_700_; lean_object* v_str_701_; lean_object* v_str_702_; lean_object* v_str_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_arg_695_ = lean_ctor_get(v_fn_358_, 1);
lean_inc_ref(v_arg_695_);
lean_dec_ref_known(v_fn_358_, 2);
v_arg_696_ = lean_ctor_get(v_fn_430_, 1);
lean_inc_ref(v_arg_696_);
lean_dec_ref_known(v_fn_430_, 2);
v_arg_697_ = lean_ctor_get(v_fn_472_, 1);
lean_inc_ref(v_arg_697_);
lean_dec_ref_known(v_fn_472_, 2);
v_arg_698_ = lean_ctor_get(v_fn_519_, 1);
lean_inc_ref(v_arg_698_);
lean_dec_ref_known(v_fn_519_, 2);
v_arg_699_ = lean_ctor_get(v_fn_571_, 1);
lean_inc_ref(v_arg_699_);
lean_dec_ref_known(v_fn_571_, 2);
v_arg_700_ = lean_ctor_get(v_fn_628_, 1);
lean_inc_ref(v_arg_700_);
lean_dec_ref_known(v_fn_628_, 2);
v_str_701_ = lean_ctor_get(v_declName_691_, 1);
lean_inc_ref(v_str_701_);
lean_dec_ref_known(v_declName_691_, 2);
v_str_702_ = lean_ctor_get(v_pre_692_, 1);
lean_inc_ref(v_str_702_);
lean_dec_ref_known(v_pre_692_, 2);
v_str_703_ = lean_ctor_get(v_pre_693_, 1);
lean_inc_ref(v_str_703_);
lean_dec_ref_known(v_pre_693_, 2);
v___x_704_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_705_ = lean_string_dec_eq(v_str_703_, v___x_704_);
lean_dec_ref(v_str_703_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; 
lean_dec_ref(v_str_702_);
lean_dec_ref(v_str_701_);
lean_dec_ref(v_arg_700_);
lean_dec_ref(v_arg_699_);
lean_dec_ref(v_arg_698_);
lean_dec_ref(v_arg_697_);
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_706_ = lean_box(0);
return v___x_706_;
}
else
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_708_ = lean_string_dec_eq(v_str_702_, v___x_707_);
lean_dec_ref(v_str_702_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
lean_dec_ref(v_str_701_);
lean_dec_ref(v_arg_700_);
lean_dec_ref(v_arg_699_);
lean_dec_ref(v_arg_698_);
lean_dec_ref(v_arg_697_);
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_709_ = lean_box(0);
return v___x_709_;
}
else
{
lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_710_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__11));
v___x_711_ = lean_string_dec_eq(v_str_701_, v___x_710_);
lean_dec_ref(v_str_701_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
lean_dec_ref(v_arg_700_);
lean_dec_ref(v_arg_699_);
lean_dec_ref(v_arg_698_);
lean_dec_ref(v_arg_697_);
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_712_ = lean_box(0);
return v___x_712_;
}
else
{
if (lean_obj_tag(v_arg_700_) == 9)
{
lean_object* v_a_713_; 
v_a_713_ = lean_ctor_get(v_arg_700_, 0);
lean_inc_ref(v_a_713_);
lean_dec_ref_known(v_arg_700_, 1);
if (lean_obj_tag(v_a_713_) == 1)
{
if (lean_obj_tag(v_arg_699_) == 9)
{
lean_object* v_a_714_; 
v_a_714_ = lean_ctor_get(v_arg_699_, 0);
lean_inc_ref(v_a_714_);
lean_dec_ref_known(v_arg_699_, 1);
if (lean_obj_tag(v_a_714_) == 1)
{
if (lean_obj_tag(v_arg_698_) == 9)
{
lean_object* v_a_715_; 
v_a_715_ = lean_ctor_get(v_arg_698_, 0);
lean_inc_ref(v_a_715_);
lean_dec_ref_known(v_arg_698_, 1);
if (lean_obj_tag(v_a_715_) == 1)
{
if (lean_obj_tag(v_arg_697_) == 9)
{
lean_object* v_a_716_; 
v_a_716_ = lean_ctor_get(v_arg_697_, 0);
lean_inc_ref(v_a_716_);
lean_dec_ref_known(v_arg_697_, 1);
if (lean_obj_tag(v_a_716_) == 1)
{
if (lean_obj_tag(v_arg_696_) == 9)
{
lean_object* v_a_717_; 
v_a_717_ = lean_ctor_get(v_arg_696_, 0);
lean_inc_ref(v_a_717_);
lean_dec_ref_known(v_arg_696_, 1);
if (lean_obj_tag(v_a_717_) == 1)
{
if (lean_obj_tag(v_arg_695_) == 9)
{
lean_object* v_a_718_; 
v_a_718_ = lean_ctor_get(v_arg_695_, 0);
lean_inc_ref(v_a_718_);
lean_dec_ref_known(v_arg_695_, 1);
if (lean_obj_tag(v_a_718_) == 1)
{
if (lean_obj_tag(v_arg_359_) == 9)
{
lean_object* v_a_719_; 
v_a_719_ = lean_ctor_get(v_arg_359_, 0);
lean_inc_ref(v_a_719_);
lean_dec_ref_known(v_arg_359_, 1);
if (lean_obj_tag(v_a_719_) == 1)
{
if (lean_obj_tag(v_arg_357_) == 9)
{
lean_object* v_a_720_; 
v_a_720_ = lean_ctor_get(v_arg_357_, 0);
lean_inc_ref(v_a_720_);
lean_dec_ref_known(v_arg_357_, 1);
if (lean_obj_tag(v_a_720_) == 1)
{
lean_object* v_val_721_; lean_object* v_val_722_; lean_object* v_val_723_; lean_object* v_val_724_; lean_object* v_val_725_; lean_object* v_val_726_; lean_object* v_val_727_; lean_object* v_val_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_736_; 
v_val_721_ = lean_ctor_get(v_a_713_, 0);
lean_inc_ref(v_val_721_);
lean_dec_ref_known(v_a_713_, 1);
v_val_722_ = lean_ctor_get(v_a_714_, 0);
lean_inc_ref(v_val_722_);
lean_dec_ref_known(v_a_714_, 1);
v_val_723_ = lean_ctor_get(v_a_715_, 0);
lean_inc_ref(v_val_723_);
lean_dec_ref_known(v_a_715_, 1);
v_val_724_ = lean_ctor_get(v_a_716_, 0);
lean_inc_ref(v_val_724_);
lean_dec_ref_known(v_a_716_, 1);
v_val_725_ = lean_ctor_get(v_a_717_, 0);
lean_inc_ref(v_val_725_);
lean_dec_ref_known(v_a_717_, 1);
v_val_726_ = lean_ctor_get(v_a_718_, 0);
lean_inc_ref(v_val_726_);
lean_dec_ref_known(v_a_718_, 1);
v_val_727_ = lean_ctor_get(v_a_719_, 0);
lean_inc_ref(v_val_727_);
lean_dec_ref_known(v_a_719_, 1);
v_val_728_ = lean_ctor_get(v_a_720_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v_a_720_);
if (v_isSharedCheck_736_ == 0)
{
v___x_730_ = v_a_720_;
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_val_728_);
lean_dec(v_a_720_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = l_Lean_Name_mkStr8(v_val_721_, v_val_722_, v_val_723_, v_val_724_, v_val_725_, v_val_726_, v_val_727_, v_val_728_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_732_);
v___x_734_ = v___x_730_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
else
{
lean_object* v___x_737_; 
lean_dec_ref(v_a_720_);
lean_dec_ref_known(v_a_719_, 1);
lean_dec_ref_known(v_a_718_, 1);
lean_dec_ref_known(v_a_717_, 1);
lean_dec_ref_known(v_a_716_, 1);
lean_dec_ref_known(v_a_715_, 1);
lean_dec_ref_known(v_a_714_, 1);
lean_dec_ref_known(v_a_713_, 1);
v___x_737_ = lean_box(0);
return v___x_737_;
}
}
else
{
lean_object* v___x_738_; 
lean_dec_ref_known(v_a_719_, 1);
lean_dec_ref_known(v_a_718_, 1);
lean_dec_ref_known(v_a_717_, 1);
lean_dec_ref_known(v_a_716_, 1);
lean_dec_ref_known(v_a_715_, 1);
lean_dec_ref_known(v_a_714_, 1);
lean_dec_ref_known(v_a_713_, 1);
lean_dec_ref(v_arg_357_);
v___x_738_ = lean_box(0);
return v___x_738_;
}
}
else
{
lean_object* v___x_739_; 
lean_dec_ref(v_a_719_);
lean_dec_ref_known(v_a_718_, 1);
lean_dec_ref_known(v_a_717_, 1);
lean_dec_ref_known(v_a_716_, 1);
lean_dec_ref_known(v_a_715_, 1);
lean_dec_ref_known(v_a_714_, 1);
lean_dec_ref_known(v_a_713_, 1);
lean_dec_ref(v_arg_357_);
v___x_739_ = lean_box(0);
return v___x_739_;
}
}
else
{
lean_object* v___x_740_; 
lean_dec_ref_known(v_a_718_, 1);
lean_dec_ref_known(v_a_717_, 1);
lean_dec_ref_known(v_a_716_, 1);
lean_dec_ref_known(v_a_715_, 1);
lean_dec_ref_known(v_a_714_, 1);
lean_dec_ref_known(v_a_713_, 1);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_740_ = lean_box(0);
return v___x_740_;
}
}
else
{
lean_object* v___x_741_; 
lean_dec_ref(v_a_718_);
lean_dec_ref_known(v_a_717_, 1);
lean_dec_ref_known(v_a_716_, 1);
lean_dec_ref_known(v_a_715_, 1);
lean_dec_ref_known(v_a_714_, 1);
lean_dec_ref_known(v_a_713_, 1);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_741_ = lean_box(0);
return v___x_741_;
}
}
else
{
lean_object* v___x_742_; 
lean_dec_ref_known(v_a_717_, 1);
lean_dec_ref_known(v_a_716_, 1);
lean_dec_ref_known(v_a_715_, 1);
lean_dec_ref_known(v_a_714_, 1);
lean_dec_ref_known(v_a_713_, 1);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_742_ = lean_box(0);
return v___x_742_;
}
}
else
{
lean_object* v___x_743_; 
lean_dec_ref(v_a_717_);
lean_dec_ref_known(v_a_716_, 1);
lean_dec_ref_known(v_a_715_, 1);
lean_dec_ref_known(v_a_714_, 1);
lean_dec_ref_known(v_a_713_, 1);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_743_ = lean_box(0);
return v___x_743_;
}
}
else
{
lean_object* v___x_744_; 
lean_dec_ref_known(v_a_716_, 1);
lean_dec_ref_known(v_a_715_, 1);
lean_dec_ref_known(v_a_714_, 1);
lean_dec_ref_known(v_a_713_, 1);
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_744_ = lean_box(0);
return v___x_744_;
}
}
else
{
lean_object* v___x_745_; 
lean_dec_ref(v_a_716_);
lean_dec_ref_known(v_a_715_, 1);
lean_dec_ref_known(v_a_714_, 1);
lean_dec_ref_known(v_a_713_, 1);
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_745_ = lean_box(0);
return v___x_745_;
}
}
else
{
lean_object* v___x_746_; 
lean_dec_ref_known(v_a_715_, 1);
lean_dec_ref_known(v_a_714_, 1);
lean_dec_ref_known(v_a_713_, 1);
lean_dec_ref(v_arg_697_);
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_746_ = lean_box(0);
return v___x_746_;
}
}
else
{
lean_object* v___x_747_; 
lean_dec_ref(v_a_715_);
lean_dec_ref_known(v_a_714_, 1);
lean_dec_ref_known(v_a_713_, 1);
lean_dec_ref(v_arg_697_);
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_747_ = lean_box(0);
return v___x_747_;
}
}
else
{
lean_object* v___x_748_; 
lean_dec_ref_known(v_a_714_, 1);
lean_dec_ref_known(v_a_713_, 1);
lean_dec_ref(v_arg_698_);
lean_dec_ref(v_arg_697_);
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_748_ = lean_box(0);
return v___x_748_;
}
}
else
{
lean_object* v___x_749_; 
lean_dec_ref(v_a_714_);
lean_dec_ref_known(v_a_713_, 1);
lean_dec_ref(v_arg_698_);
lean_dec_ref(v_arg_697_);
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_749_ = lean_box(0);
return v___x_749_;
}
}
else
{
lean_object* v___x_750_; 
lean_dec_ref_known(v_a_713_, 1);
lean_dec_ref(v_arg_699_);
lean_dec_ref(v_arg_698_);
lean_dec_ref(v_arg_697_);
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_750_ = lean_box(0);
return v___x_750_;
}
}
else
{
lean_object* v___x_751_; 
lean_dec_ref(v_a_713_);
lean_dec_ref(v_arg_699_);
lean_dec_ref(v_arg_698_);
lean_dec_ref(v_arg_697_);
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_751_ = lean_box(0);
return v___x_751_;
}
}
else
{
lean_object* v___x_752_; 
lean_dec_ref(v_arg_700_);
lean_dec_ref(v_arg_699_);
lean_dec_ref(v_arg_698_);
lean_dec_ref(v_arg_697_);
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_752_ = lean_box(0);
return v___x_752_;
}
}
}
}
}
else
{
lean_object* v___x_753_; 
lean_dec_ref_known(v_pre_693_, 2);
lean_dec_ref_known(v_pre_692_, 2);
lean_dec_ref_known(v_declName_691_, 2);
lean_dec_ref_known(v_fn_628_, 2);
lean_dec_ref_known(v_fn_571_, 2);
lean_dec_ref_known(v_fn_519_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_753_ = lean_box(0);
return v___x_753_;
}
}
else
{
lean_object* v___x_754_; 
lean_dec(v_pre_693_);
lean_dec_ref_known(v_pre_692_, 2);
lean_dec_ref_known(v_declName_691_, 2);
lean_dec_ref_known(v_fn_628_, 2);
lean_dec_ref_known(v_fn_571_, 2);
lean_dec_ref_known(v_fn_519_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_754_ = lean_box(0);
return v___x_754_;
}
}
else
{
lean_object* v___x_755_; 
lean_dec(v_pre_692_);
lean_dec_ref_known(v_declName_691_, 2);
lean_dec_ref_known(v_fn_628_, 2);
lean_dec_ref_known(v_fn_571_, 2);
lean_dec_ref_known(v_fn_519_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_755_ = lean_box(0);
return v___x_755_;
}
}
else
{
lean_object* v___x_756_; 
lean_dec(v_declName_691_);
lean_dec_ref_known(v_fn_628_, 2);
lean_dec_ref_known(v_fn_571_, 2);
lean_dec_ref_known(v_fn_519_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_756_ = lean_box(0);
return v___x_756_;
}
}
else
{
lean_object* v___x_757_; 
lean_dec_ref_known(v_fn_628_, 2);
lean_dec_ref_known(v_fn_571_, 2);
lean_dec_ref_known(v_fn_519_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_757_ = lean_box(0);
return v___x_757_;
}
}
default: 
{
lean_object* v___x_758_; 
lean_dec_ref_known(v_fn_571_, 2);
lean_dec_ref_known(v_fn_519_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_758_ = lean_box(0);
return v___x_758_;
}
}
}
default: 
{
lean_object* v___x_759_; 
lean_dec_ref_known(v_fn_519_, 2);
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_759_ = lean_box(0);
return v___x_759_;
}
}
}
default: 
{
lean_object* v___x_760_; 
lean_dec_ref_known(v_fn_472_, 2);
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_760_ = lean_box(0);
return v___x_760_;
}
}
}
default: 
{
lean_object* v___x_761_; 
lean_dec_ref_known(v_fn_430_, 2);
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_761_ = lean_box(0);
return v___x_761_;
}
}
}
default: 
{
lean_object* v___x_762_; 
lean_dec_ref_known(v_fn_358_, 2);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_357_);
v___x_762_ = lean_box(0);
return v___x_762_;
}
}
}
default: 
{
lean_object* v___x_763_; 
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_fn_358_);
lean_dec_ref(v_arg_357_);
v___x_763_ = lean_box(0);
return v___x_763_;
}
}
v___jp_360_:
{
if (lean_obj_tag(v___y_361_) == 0)
{
lean_object* v___x_362_; 
lean_dec_ref(v_arg_359_);
v___x_362_ = lean_box(0);
return v___x_362_;
}
else
{
lean_object* v_val_363_; lean_object* v___x_364_; 
v_val_363_ = lean_ctor_get(v___y_361_, 0);
lean_inc(v_val_363_);
lean_dec_ref_known(v___y_361_, 1);
v___x_364_ = l_Lean_Expr_name_x3f(v_arg_359_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_dec(v_val_363_);
return v___x_364_;
}
else
{
lean_object* v_val_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_373_; 
v_val_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_373_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_val_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = l_Lean_Name_num___override(v_val_365_, v_val_363_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
case 4:
{
lean_object* v_declName_764_; 
v_declName_764_ = lean_ctor_get(v_fn_356_, 0);
lean_inc(v_declName_764_);
if (lean_obj_tag(v_declName_764_) == 1)
{
lean_object* v_pre_765_; 
v_pre_765_ = lean_ctor_get(v_declName_764_, 0);
lean_inc(v_pre_765_);
if (lean_obj_tag(v_pre_765_) == 1)
{
lean_object* v_pre_766_; 
v_pre_766_ = lean_ctor_get(v_pre_765_, 0);
lean_inc(v_pre_766_);
if (lean_obj_tag(v_pre_766_) == 1)
{
lean_object* v_pre_767_; 
v_pre_767_ = lean_ctor_get(v_pre_766_, 0);
if (lean_obj_tag(v_pre_767_) == 0)
{
lean_object* v_arg_768_; lean_object* v_str_769_; lean_object* v_str_770_; lean_object* v_str_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_arg_768_ = lean_ctor_get(v_x_334_, 1);
lean_inc_ref(v_arg_768_);
lean_dec_ref_known(v_x_334_, 2);
v_str_769_ = lean_ctor_get(v_declName_764_, 1);
lean_inc_ref(v_str_769_);
lean_dec_ref_known(v_declName_764_, 2);
v_str_770_ = lean_ctor_get(v_pre_765_, 1);
lean_inc_ref(v_str_770_);
lean_dec_ref_known(v_pre_765_, 2);
v_str_771_ = lean_ctor_get(v_pre_766_, 1);
lean_inc_ref(v_str_771_);
lean_dec_ref_known(v_pre_766_, 2);
v___x_772_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_773_ = lean_string_dec_eq(v_str_771_, v___x_772_);
lean_dec_ref(v_str_771_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; 
lean_dec_ref(v_str_770_);
lean_dec_ref(v_str_769_);
lean_dec_ref(v_arg_768_);
v___x_774_ = lean_box(0);
return v___x_774_;
}
else
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_776_ = lean_string_dec_eq(v_str_770_, v___x_775_);
lean_dec_ref(v_str_770_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; 
lean_dec_ref(v_str_769_);
lean_dec_ref(v_arg_768_);
v___x_777_ = lean_box(0);
return v___x_777_;
}
else
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__12));
v___x_779_ = lean_string_dec_eq(v_str_769_, v___x_778_);
lean_dec_ref(v_str_769_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; 
lean_dec_ref(v_arg_768_);
v___x_780_ = lean_box(0);
return v___x_780_;
}
else
{
if (lean_obj_tag(v_arg_768_) == 9)
{
lean_object* v_a_781_; 
v_a_781_ = lean_ctor_get(v_arg_768_, 0);
lean_inc_ref(v_a_781_);
lean_dec_ref_known(v_arg_768_, 1);
if (lean_obj_tag(v_a_781_) == 1)
{
lean_object* v_val_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_790_; 
v_val_782_ = lean_ctor_get(v_a_781_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v_a_781_);
if (v_isSharedCheck_790_ == 0)
{
v___x_784_ = v_a_781_;
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_val_782_);
lean_dec(v_a_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_786_ = l_Lean_Name_mkStr1(v_val_782_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_786_);
v___x_788_ = v___x_784_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
else
{
lean_object* v___x_791_; 
lean_dec_ref(v_a_781_);
v___x_791_ = lean_box(0);
return v___x_791_;
}
}
else
{
lean_object* v___x_792_; 
lean_dec_ref(v_arg_768_);
v___x_792_ = lean_box(0);
return v___x_792_;
}
}
}
}
}
else
{
lean_object* v___x_793_; 
lean_dec_ref_known(v_pre_766_, 2);
lean_dec_ref_known(v_pre_765_, 2);
lean_dec_ref_known(v_declName_764_, 2);
lean_dec_ref_known(v_x_334_, 2);
v___x_793_ = lean_box(0);
return v___x_793_;
}
}
else
{
lean_object* v___x_794_; 
lean_dec_ref_known(v_pre_765_, 2);
lean_dec(v_pre_766_);
lean_dec_ref_known(v_declName_764_, 2);
lean_dec_ref_known(v_x_334_, 2);
v___x_794_ = lean_box(0);
return v___x_794_;
}
}
else
{
lean_object* v___x_795_; 
lean_dec(v_pre_765_);
lean_dec_ref_known(v_declName_764_, 2);
lean_dec_ref_known(v_x_334_, 2);
v___x_795_ = lean_box(0);
return v___x_795_;
}
}
else
{
lean_object* v___x_796_; 
lean_dec(v_declName_764_);
lean_dec_ref_known(v_x_334_, 2);
v___x_796_ = lean_box(0);
return v___x_796_;
}
}
default: 
{
lean_object* v___x_797_; 
lean_dec_ref_known(v_x_334_, 2);
v___x_797_ = lean_box(0);
return v___x_797_;
}
}
}
default: 
{
lean_object* v___x_798_; 
lean_dec_ref(v_x_334_);
v___x_798_ = lean_box(0);
return v___x_798_;
}
}
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Recognizers(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_Recognizers(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Recognizers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_Recognizers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_Recognizers(builtin);
}
#ifdef __cplusplus
}
#endif
