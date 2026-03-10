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
LEAN_EXPORT lean_object* l_Lean_Expr_const_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_const_x3f___boxed(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app1_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app1_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app2_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app2_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app3_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app3_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app4_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app4_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_eq_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Expr_eq_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_eq_x3f___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Expr_natAdd_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_natAdd_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Expr_natAdd_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_natAdd_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_natAdd_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 189, 86, 121, 130, 22, 242, 236)}};
static const lean_object* l_Lean_Expr_natAdd_x3f___closed__2 = (const lean_object*)&l_Lean_Expr_natAdd_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Expr_natAdd_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_natAdd_x3f___boxed(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
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
uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21_x27(lean_object*);
lean_object* l_Lean_Expr_appFn_x21_x27(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_name_x3f(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Expr_const_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_const_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app1_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Expr_appArg_x21(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app1_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_app1_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app2_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appArg_x21(x_6);
lean_dec_ref(x_6);
x_8 = l_Lean_Expr_appArg_x21(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app2_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_app2_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app3_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appFn_x21(x_6);
x_8 = l_Lean_Expr_appArg_x21(x_7);
lean_dec_ref(x_7);
x_9 = l_Lean_Expr_appArg_x21(x_6);
lean_dec_ref(x_6);
x_10 = l_Lean_Expr_appArg_x21(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app3_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_app3_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app4_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appFn_x21(x_6);
x_8 = l_Lean_Expr_appFn_x21(x_7);
x_9 = l_Lean_Expr_appArg_x21(x_8);
lean_dec_ref(x_8);
x_10 = l_Lean_Expr_appArg_x21(x_7);
lean_dec_ref(x_7);
x_11 = l_Lean_Expr_appArg_x21(x_6);
lean_dec_ref(x_6);
x_12 = l_Lean_Expr_appArg_x21(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app4_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_app4_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eq_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Expr_eq_x3f___closed__1));
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appFn_x21(x_6);
x_8 = l_Lean_Expr_appArg_x21(x_7);
lean_dec_ref(x_7);
x_9 = l_Lean_Expr_appArg_x21(x_6);
lean_dec_ref(x_6);
x_10 = l_Lean_Expr_appArg_x21(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eq_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_eq_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ne_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Expr_ne_x3f___closed__1));
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appFn_x21(x_6);
x_8 = l_Lean_Expr_appArg_x21(x_7);
lean_dec_ref(x_7);
x_9 = l_Lean_Expr_appArg_x21(x_6);
lean_dec_ref(x_6);
x_10 = l_Lean_Expr_appArg_x21(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ne_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_ne_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_iff_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Expr_iff_x3f___closed__1));
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appArg_x21(x_6);
lean_dec_ref(x_6);
x_8 = l_Lean_Expr_appArg_x21(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_iff_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_iff_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqOrIff_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Expr_eq_x3f___closed__1));
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = ((lean_object*)(l_Lean_Expr_iff_x3f___closed__1));
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Expr_isAppOfArity(x_1, x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Expr_appFn_x21(x_1);
x_10 = l_Lean_Expr_appArg_x21(x_9);
lean_dec_ref(x_9);
x_11 = l_Lean_Expr_appArg_x21(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Expr_appFn_x21(x_1);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec_ref(x_14);
x_16 = l_Lean_Expr_appArg_x21(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqOrIff_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_eqOrIff_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_not_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Expr_not_x3f___closed__1));
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Expr_appArg_x21(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_not_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_not_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_notNot_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Expr_not_x3f___closed__1));
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Expr_appArg_x21(x_1);
x_7 = l_Lean_Expr_isAppOfArity(x_6, x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_6);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Expr_appArg_x21(x_6);
lean_dec_ref(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_notNot_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_notNot_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_and_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Expr_and_x3f___closed__1));
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appArg_x21(x_6);
lean_dec_ref(x_6);
x_8 = l_Lean_Expr_appArg_x21(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_and_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_and_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_heq_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Expr_heq_x3f___closed__1));
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appFn_x21(x_6);
x_8 = l_Lean_Expr_appFn_x21(x_7);
x_9 = l_Lean_Expr_appArg_x21(x_8);
lean_dec_ref(x_8);
x_10 = l_Lean_Expr_appArg_x21(x_7);
lean_dec_ref(x_7);
x_11 = l_Lean_Expr_appArg_x21(x_6);
lean_dec_ref(x_6);
x_12 = l_Lean_Expr_appArg_x21(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_heq_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_heq_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_natAdd_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Expr_natAdd_x3f___closed__2));
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appArg_x21(x_6);
lean_dec_ref(x_6);
x_8 = l_Lean_Expr_appArg_x21(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_natAdd_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_natAdd_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_arrow_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Lean_Expr_hasLooseBVars(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_arrow_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_arrow_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isEq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Expr_eq_x3f___closed__1));
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isEq___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isEq(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHEq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Expr_heq_x3f___closed__1));
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHEq___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isHEq(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isIte(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Expr_isIte___closed__1));
x_3 = lean_unsigned_to_nat(5u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isIte___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isIte(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isDIte(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Expr_isDIte___closed__1));
x_3 = lean_unsigned_to_nat(5u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isDIte___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isDIte(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = ((lean_object*)(l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2));
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Expr_isAppOfArity_x27(x_1, x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = ((lean_object*)(l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4));
x_7 = lean_unsigned_to_nat(3u);
x_8 = l_Lean_Expr_isAppOfArity_x27(x_1, x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Expr_appArg_x21_x27(x_1);
x_11 = l_Lean_Expr_appFn_x21_x27(x_1);
lean_dec_ref(x_1);
x_12 = l_Lean_Expr_appArg_x21_x27(x_11);
lean_dec_ref(x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_1 = x_10;
x_2 = x_13;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Expr_appArg_x21_x27(x_1);
lean_dec_ref(x_1);
x_16 = l_List_reverse___redArg(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_listLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_arrayLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Expr_arrayLit_x3f___closed__1));
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity_x27(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Expr_appArg_x21_x27(x_1);
x_7 = l_Lean_Expr_listLit_x3f(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_arrayLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_arrayLit_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_prod_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Expr_prod_x3f___closed__1));
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appArg_x21(x_6);
lean_dec_ref(x_6);
x_8 = l_Lean_Expr_appArg_x21(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_prod_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_prod_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_name_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_4);
x_9 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec_ref(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_13 = lean_string_dec_eq(x_7, x_12);
lean_dec_ref(x_7);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_6);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__2));
x_16 = lean_string_dec_eq(x_6, x_15);
lean_dec_ref(x_6);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_19 = lean_box(0);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec_ref(x_3);
lean_dec(x_4);
lean_dec_ref(x_2);
x_20 = lean_box(0);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec_ref(x_2);
lean_dec(x_3);
x_21 = lean_box(0);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_2);
x_22 = lean_box(0);
return x_22;
}
}
case 5:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_1, 0);
switch (lean_obj_tag(x_23)) {
case 5:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_24);
lean_dec_ref(x_1);
x_25 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_26);
lean_dec_ref(x_23);
switch (lean_obj_tag(x_25)) {
case 4:
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_25, 0);
lean_inc(x_41);
lean_dec_ref(x_25);
if (lean_obj_tag(x_41) == 1)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 1)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc_ref(x_45);
lean_dec_ref(x_41);
x_46 = lean_ctor_get(x_42, 1);
lean_inc_ref(x_46);
lean_dec_ref(x_42);
x_47 = lean_ctor_get(x_43, 1);
lean_inc_ref(x_47);
lean_dec_ref(x_43);
x_48 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_49 = lean_string_dec_eq(x_47, x_48);
lean_dec_ref(x_47);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_50 = lean_box(0);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_52 = lean_string_dec_eq(x_46, x_51);
lean_dec_ref(x_46);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec_ref(x_45);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_53 = lean_box(0);
return x_53;
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__3));
x_55 = lean_string_dec_eq(x_45, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__4));
x_57 = lean_string_dec_eq(x_45, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__5));
x_59 = lean_string_dec_eq(x_45, x_58);
lean_dec_ref(x_45);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_60 = lean_box(0);
return x_60;
}
else
{
if (lean_obj_tag(x_26) == 9)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_61);
lean_dec_ref(x_26);
if (lean_obj_tag(x_61) == 1)
{
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_62);
lean_dec_ref(x_24);
if (lean_obj_tag(x_62) == 1)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_72; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc_ref(x_63);
lean_dec_ref(x_61);
x_64 = lean_ctor_get(x_62, 0);
x_72 = !lean_is_exclusive(x_62);
if (x_72 == 0)
{
x_65 = x_62;
x_66 = x_72;
goto block_71;
}
else
{
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_box(0);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_Name_mkStr2(x_63, x_64);
if (x_66 == 0)
{
lean_ctor_set(x_65, 0, x_67);
x_68 = x_65;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
else
{
lean_object* x_73; 
lean_dec_ref(x_62);
lean_dec_ref(x_61);
x_73 = lean_box(0);
return x_73;
}
}
else
{
lean_object* x_74; 
lean_dec_ref(x_61);
lean_dec_ref(x_24);
x_74 = lean_box(0);
return x_74;
}
}
else
{
lean_object* x_75; 
lean_dec_ref(x_61);
lean_dec_ref(x_24);
x_75 = lean_box(0);
return x_75;
}
}
else
{
lean_object* x_76; 
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_76 = lean_box(0);
return x_76;
}
}
}
else
{
lean_object* x_77; 
lean_dec_ref(x_45);
lean_inc_ref(x_24);
x_77 = l_Lean_Expr_rawNatLit_x3f(x_24);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = l_Lean_Expr_nat_x3f(x_24);
x_27 = x_78;
goto block_40;
}
else
{
lean_dec_ref(x_24);
x_27 = x_77;
goto block_40;
}
}
}
else
{
lean_dec_ref(x_45);
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_79);
lean_dec_ref(x_24);
if (lean_obj_tag(x_79) == 1)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc_ref(x_80);
lean_dec_ref(x_79);
x_81 = l_Lean_Expr_name_x3f(x_26);
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_90; 
x_82 = lean_ctor_get(x_81, 0);
x_90 = !lean_is_exclusive(x_81);
if (x_90 == 0)
{
x_83 = x_81;
x_84 = x_90;
goto block_89;
}
else
{
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_85; lean_object* x_86; 
x_85 = l_Lean_Name_str___override(x_82, x_80);
if (x_84 == 0)
{
lean_ctor_set(x_83, 0, x_85);
x_86 = x_83;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_85);
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
lean_object* x_91; 
lean_dec_ref(x_79);
lean_dec_ref(x_26);
x_91 = lean_box(0);
return x_91;
}
}
else
{
lean_object* x_92; 
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_92 = lean_box(0);
return x_92;
}
}
}
}
}
else
{
lean_object* x_93; 
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_93 = lean_box(0);
return x_93;
}
}
else
{
lean_object* x_94; 
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_94 = lean_box(0);
return x_94;
}
}
else
{
lean_object* x_95; 
lean_dec_ref(x_41);
lean_dec(x_42);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_95 = lean_box(0);
return x_95;
}
}
else
{
lean_object* x_96; 
lean_dec(x_41);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_96 = lean_box(0);
return x_96;
}
}
case 5:
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_25, 0);
switch (lean_obj_tag(x_97)) {
case 4:
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 1)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 1)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 1)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 0);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_102 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_102);
lean_dec_ref(x_25);
x_103 = lean_ctor_get(x_98, 1);
lean_inc_ref(x_103);
lean_dec_ref(x_98);
x_104 = lean_ctor_get(x_99, 1);
lean_inc_ref(x_104);
lean_dec_ref(x_99);
x_105 = lean_ctor_get(x_100, 1);
lean_inc_ref(x_105);
lean_dec_ref(x_100);
x_106 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_107 = lean_string_dec_eq(x_105, x_106);
lean_dec_ref(x_105);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec_ref(x_104);
lean_dec_ref(x_103);
lean_dec_ref(x_102);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_108 = lean_box(0);
return x_108;
}
else
{
lean_object* x_109; uint8_t x_110; 
x_109 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_110 = lean_string_dec_eq(x_104, x_109);
lean_dec_ref(x_104);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec_ref(x_103);
lean_dec_ref(x_102);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_111 = lean_box(0);
return x_111;
}
else
{
lean_object* x_112; uint8_t x_113; 
x_112 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__6));
x_113 = lean_string_dec_eq(x_103, x_112);
lean_dec_ref(x_103);
if (x_113 == 0)
{
lean_object* x_114; 
lean_dec_ref(x_102);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_114 = lean_box(0);
return x_114;
}
else
{
if (lean_obj_tag(x_102) == 9)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_102, 0);
lean_inc_ref(x_115);
lean_dec_ref(x_102);
if (lean_obj_tag(x_115) == 1)
{
if (lean_obj_tag(x_26) == 9)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_116);
lean_dec_ref(x_26);
if (lean_obj_tag(x_116) == 1)
{
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_117);
lean_dec_ref(x_24);
if (lean_obj_tag(x_117) == 1)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_128; 
x_118 = lean_ctor_get(x_115, 0);
lean_inc_ref(x_118);
lean_dec_ref(x_115);
x_119 = lean_ctor_get(x_116, 0);
lean_inc_ref(x_119);
lean_dec_ref(x_116);
x_120 = lean_ctor_get(x_117, 0);
x_128 = !lean_is_exclusive(x_117);
if (x_128 == 0)
{
x_121 = x_117;
x_122 = x_128;
goto block_127;
}
else
{
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_box(0);
x_122 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_123; lean_object* x_124; 
x_123 = l_Lean_Name_mkStr3(x_118, x_119, x_120);
if (x_122 == 0)
{
lean_ctor_set(x_121, 0, x_123);
x_124 = x_121;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_123);
x_124 = x_126;
goto block_125;
}
block_125:
{
return x_124;
}
}
}
else
{
lean_object* x_129; 
lean_dec_ref(x_117);
lean_dec_ref(x_116);
lean_dec_ref(x_115);
x_129 = lean_box(0);
return x_129;
}
}
else
{
lean_object* x_130; 
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec_ref(x_24);
x_130 = lean_box(0);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec_ref(x_24);
x_131 = lean_box(0);
return x_131;
}
}
else
{
lean_object* x_132; 
lean_dec_ref(x_115);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_132 = lean_box(0);
return x_132;
}
}
else
{
lean_object* x_133; 
lean_dec_ref(x_115);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_133 = lean_box(0);
return x_133;
}
}
else
{
lean_object* x_134; 
lean_dec_ref(x_102);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_134 = lean_box(0);
return x_134;
}
}
}
}
}
else
{
lean_object* x_135; 
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_98);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_135 = lean_box(0);
return x_135;
}
}
else
{
lean_object* x_136; 
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_98);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_136 = lean_box(0);
return x_136;
}
}
else
{
lean_object* x_137; 
lean_dec_ref(x_98);
lean_dec(x_99);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_137 = lean_box(0);
return x_137;
}
}
else
{
lean_object* x_138; 
lean_dec(x_98);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_138 = lean_box(0);
return x_138;
}
}
case 5:
{
lean_object* x_139; 
lean_inc_ref(x_97);
x_139 = lean_ctor_get(x_97, 0);
switch (lean_obj_tag(x_139)) {
case 4:
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
if (lean_obj_tag(x_140) == 1)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 1)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 1)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_142, 0);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_144 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_144);
lean_dec_ref(x_25);
x_145 = lean_ctor_get(x_97, 1);
lean_inc_ref(x_145);
lean_dec_ref(x_97);
x_146 = lean_ctor_get(x_140, 1);
lean_inc_ref(x_146);
lean_dec_ref(x_140);
x_147 = lean_ctor_get(x_141, 1);
lean_inc_ref(x_147);
lean_dec_ref(x_141);
x_148 = lean_ctor_get(x_142, 1);
lean_inc_ref(x_148);
lean_dec_ref(x_142);
x_149 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_150 = lean_string_dec_eq(x_148, x_149);
lean_dec_ref(x_148);
if (x_150 == 0)
{
lean_object* x_151; 
lean_dec_ref(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_151 = lean_box(0);
return x_151;
}
else
{
lean_object* x_152; uint8_t x_153; 
x_152 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_153 = lean_string_dec_eq(x_147, x_152);
lean_dec_ref(x_147);
if (x_153 == 0)
{
lean_object* x_154; 
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_154 = lean_box(0);
return x_154;
}
else
{
lean_object* x_155; uint8_t x_156; 
x_155 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__7));
x_156 = lean_string_dec_eq(x_146, x_155);
lean_dec_ref(x_146);
if (x_156 == 0)
{
lean_object* x_157; 
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_157 = lean_box(0);
return x_157;
}
else
{
if (lean_obj_tag(x_145) == 9)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_145, 0);
lean_inc_ref(x_158);
lean_dec_ref(x_145);
if (lean_obj_tag(x_158) == 1)
{
if (lean_obj_tag(x_144) == 9)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_144, 0);
lean_inc_ref(x_159);
lean_dec_ref(x_144);
if (lean_obj_tag(x_159) == 1)
{
if (lean_obj_tag(x_26) == 9)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_160);
lean_dec_ref(x_26);
if (lean_obj_tag(x_160) == 1)
{
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_161);
lean_dec_ref(x_24);
if (lean_obj_tag(x_161) == 1)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_173; 
x_162 = lean_ctor_get(x_158, 0);
lean_inc_ref(x_162);
lean_dec_ref(x_158);
x_163 = lean_ctor_get(x_159, 0);
lean_inc_ref(x_163);
lean_dec_ref(x_159);
x_164 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_164);
lean_dec_ref(x_160);
x_165 = lean_ctor_get(x_161, 0);
x_173 = !lean_is_exclusive(x_161);
if (x_173 == 0)
{
x_166 = x_161;
x_167 = x_173;
goto block_172;
}
else
{
lean_inc(x_165);
lean_dec(x_161);
x_166 = lean_box(0);
x_167 = x_173;
goto block_172;
}
block_172:
{
lean_object* x_168; lean_object* x_169; 
x_168 = l_Lean_Name_mkStr4(x_162, x_163, x_164, x_165);
if (x_167 == 0)
{
lean_ctor_set(x_166, 0, x_168);
x_169 = x_166;
goto block_170;
}
else
{
lean_object* x_171; 
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_168);
x_169 = x_171;
goto block_170;
}
block_170:
{
return x_169;
}
}
}
else
{
lean_object* x_174; 
lean_dec_ref(x_161);
lean_dec_ref(x_160);
lean_dec_ref(x_159);
lean_dec_ref(x_158);
x_174 = lean_box(0);
return x_174;
}
}
else
{
lean_object* x_175; 
lean_dec_ref(x_160);
lean_dec_ref(x_159);
lean_dec_ref(x_158);
lean_dec_ref(x_24);
x_175 = lean_box(0);
return x_175;
}
}
else
{
lean_object* x_176; 
lean_dec_ref(x_160);
lean_dec_ref(x_159);
lean_dec_ref(x_158);
lean_dec_ref(x_24);
x_176 = lean_box(0);
return x_176;
}
}
else
{
lean_object* x_177; 
lean_dec_ref(x_159);
lean_dec_ref(x_158);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_177 = lean_box(0);
return x_177;
}
}
else
{
lean_object* x_178; 
lean_dec_ref(x_159);
lean_dec_ref(x_158);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_178 = lean_box(0);
return x_178;
}
}
else
{
lean_object* x_179; 
lean_dec_ref(x_158);
lean_dec_ref(x_144);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_179 = lean_box(0);
return x_179;
}
}
else
{
lean_object* x_180; 
lean_dec_ref(x_158);
lean_dec_ref(x_144);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_180 = lean_box(0);
return x_180;
}
}
else
{
lean_object* x_181; 
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_181 = lean_box(0);
return x_181;
}
}
}
}
}
else
{
lean_object* x_182; 
lean_dec_ref(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_182 = lean_box(0);
return x_182;
}
}
else
{
lean_object* x_183; 
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_183 = lean_box(0);
return x_183;
}
}
else
{
lean_object* x_184; 
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_184 = lean_box(0);
return x_184;
}
}
else
{
lean_object* x_185; 
lean_dec(x_140);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_185 = lean_box(0);
return x_185;
}
}
case 5:
{
lean_object* x_186; 
lean_inc_ref(x_139);
x_186 = lean_ctor_get(x_139, 0);
switch (lean_obj_tag(x_186)) {
case 4:
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 1)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 1)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
if (lean_obj_tag(x_189) == 1)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_189, 0);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_191 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_191);
lean_dec_ref(x_25);
x_192 = lean_ctor_get(x_97, 1);
lean_inc_ref(x_192);
lean_dec_ref(x_97);
x_193 = lean_ctor_get(x_139, 1);
lean_inc_ref(x_193);
lean_dec_ref(x_139);
x_194 = lean_ctor_get(x_187, 1);
lean_inc_ref(x_194);
lean_dec_ref(x_187);
x_195 = lean_ctor_get(x_188, 1);
lean_inc_ref(x_195);
lean_dec_ref(x_188);
x_196 = lean_ctor_get(x_189, 1);
lean_inc_ref(x_196);
lean_dec_ref(x_189);
x_197 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_198 = lean_string_dec_eq(x_196, x_197);
lean_dec_ref(x_196);
if (x_198 == 0)
{
lean_object* x_199; 
lean_dec_ref(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_199 = lean_box(0);
return x_199;
}
else
{
lean_object* x_200; uint8_t x_201; 
x_200 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_201 = lean_string_dec_eq(x_195, x_200);
lean_dec_ref(x_195);
if (x_201 == 0)
{
lean_object* x_202; 
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_202 = lean_box(0);
return x_202;
}
else
{
lean_object* x_203; uint8_t x_204; 
x_203 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__8));
x_204 = lean_string_dec_eq(x_194, x_203);
lean_dec_ref(x_194);
if (x_204 == 0)
{
lean_object* x_205; 
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_205 = lean_box(0);
return x_205;
}
else
{
if (lean_obj_tag(x_193) == 9)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_193, 0);
lean_inc_ref(x_206);
lean_dec_ref(x_193);
if (lean_obj_tag(x_206) == 1)
{
if (lean_obj_tag(x_192) == 9)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_192, 0);
lean_inc_ref(x_207);
lean_dec_ref(x_192);
if (lean_obj_tag(x_207) == 1)
{
if (lean_obj_tag(x_191) == 9)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_191, 0);
lean_inc_ref(x_208);
lean_dec_ref(x_191);
if (lean_obj_tag(x_208) == 1)
{
if (lean_obj_tag(x_26) == 9)
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_209);
lean_dec_ref(x_26);
if (lean_obj_tag(x_209) == 1)
{
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_210);
lean_dec_ref(x_24);
if (lean_obj_tag(x_210) == 1)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_223; 
x_211 = lean_ctor_get(x_206, 0);
lean_inc_ref(x_211);
lean_dec_ref(x_206);
x_212 = lean_ctor_get(x_207, 0);
lean_inc_ref(x_212);
lean_dec_ref(x_207);
x_213 = lean_ctor_get(x_208, 0);
lean_inc_ref(x_213);
lean_dec_ref(x_208);
x_214 = lean_ctor_get(x_209, 0);
lean_inc_ref(x_214);
lean_dec_ref(x_209);
x_215 = lean_ctor_get(x_210, 0);
x_223 = !lean_is_exclusive(x_210);
if (x_223 == 0)
{
x_216 = x_210;
x_217 = x_223;
goto block_222;
}
else
{
lean_inc(x_215);
lean_dec(x_210);
x_216 = lean_box(0);
x_217 = x_223;
goto block_222;
}
block_222:
{
lean_object* x_218; lean_object* x_219; 
x_218 = l_Lean_Name_mkStr5(x_211, x_212, x_213, x_214, x_215);
if (x_217 == 0)
{
lean_ctor_set(x_216, 0, x_218);
x_219 = x_216;
goto block_220;
}
else
{
lean_object* x_221; 
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_218);
x_219 = x_221;
goto block_220;
}
block_220:
{
return x_219;
}
}
}
else
{
lean_object* x_224; 
lean_dec_ref(x_210);
lean_dec_ref(x_209);
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
x_224 = lean_box(0);
return x_224;
}
}
else
{
lean_object* x_225; 
lean_dec_ref(x_209);
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_24);
x_225 = lean_box(0);
return x_225;
}
}
else
{
lean_object* x_226; 
lean_dec_ref(x_209);
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_24);
x_226 = lean_box(0);
return x_226;
}
}
else
{
lean_object* x_227; 
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_227 = lean_box(0);
return x_227;
}
}
else
{
lean_object* x_228; 
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_228 = lean_box(0);
return x_228;
}
}
else
{
lean_object* x_229; 
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_191);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_229 = lean_box(0);
return x_229;
}
}
else
{
lean_object* x_230; 
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_191);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_230 = lean_box(0);
return x_230;
}
}
else
{
lean_object* x_231; 
lean_dec_ref(x_206);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_231 = lean_box(0);
return x_231;
}
}
else
{
lean_object* x_232; 
lean_dec_ref(x_206);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_232 = lean_box(0);
return x_232;
}
}
else
{
lean_object* x_233; 
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_233 = lean_box(0);
return x_233;
}
}
}
}
}
else
{
lean_object* x_234; 
lean_dec_ref(x_189);
lean_dec_ref(x_188);
lean_dec_ref(x_187);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_234 = lean_box(0);
return x_234;
}
}
else
{
lean_object* x_235; 
lean_dec(x_189);
lean_dec_ref(x_188);
lean_dec_ref(x_187);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_235 = lean_box(0);
return x_235;
}
}
else
{
lean_object* x_236; 
lean_dec(x_188);
lean_dec_ref(x_187);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_236 = lean_box(0);
return x_236;
}
}
else
{
lean_object* x_237; 
lean_dec(x_187);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_237 = lean_box(0);
return x_237;
}
}
case 5:
{
lean_object* x_238; 
lean_inc_ref(x_186);
x_238 = lean_ctor_get(x_186, 0);
switch (lean_obj_tag(x_238)) {
case 4:
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
if (lean_obj_tag(x_239) == 1)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
if (lean_obj_tag(x_240) == 1)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
if (lean_obj_tag(x_241) == 1)
{
lean_object* x_242; 
x_242 = lean_ctor_get(x_241, 0);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_243 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_243);
lean_dec_ref(x_25);
x_244 = lean_ctor_get(x_97, 1);
lean_inc_ref(x_244);
lean_dec_ref(x_97);
x_245 = lean_ctor_get(x_139, 1);
lean_inc_ref(x_245);
lean_dec_ref(x_139);
x_246 = lean_ctor_get(x_186, 1);
lean_inc_ref(x_246);
lean_dec_ref(x_186);
x_247 = lean_ctor_get(x_239, 1);
lean_inc_ref(x_247);
lean_dec_ref(x_239);
x_248 = lean_ctor_get(x_240, 1);
lean_inc_ref(x_248);
lean_dec_ref(x_240);
x_249 = lean_ctor_get(x_241, 1);
lean_inc_ref(x_249);
lean_dec_ref(x_241);
x_250 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_251 = lean_string_dec_eq(x_249, x_250);
lean_dec_ref(x_249);
if (x_251 == 0)
{
lean_object* x_252; 
lean_dec_ref(x_248);
lean_dec_ref(x_247);
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_252 = lean_box(0);
return x_252;
}
else
{
lean_object* x_253; uint8_t x_254; 
x_253 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_254 = lean_string_dec_eq(x_248, x_253);
lean_dec_ref(x_248);
if (x_254 == 0)
{
lean_object* x_255; 
lean_dec_ref(x_247);
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_255 = lean_box(0);
return x_255;
}
else
{
lean_object* x_256; uint8_t x_257; 
x_256 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__9));
x_257 = lean_string_dec_eq(x_247, x_256);
lean_dec_ref(x_247);
if (x_257 == 0)
{
lean_object* x_258; 
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_258 = lean_box(0);
return x_258;
}
else
{
if (lean_obj_tag(x_246) == 9)
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_246, 0);
lean_inc_ref(x_259);
lean_dec_ref(x_246);
if (lean_obj_tag(x_259) == 1)
{
if (lean_obj_tag(x_245) == 9)
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_245, 0);
lean_inc_ref(x_260);
lean_dec_ref(x_245);
if (lean_obj_tag(x_260) == 1)
{
if (lean_obj_tag(x_244) == 9)
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_244, 0);
lean_inc_ref(x_261);
lean_dec_ref(x_244);
if (lean_obj_tag(x_261) == 1)
{
if (lean_obj_tag(x_243) == 9)
{
lean_object* x_262; 
x_262 = lean_ctor_get(x_243, 0);
lean_inc_ref(x_262);
lean_dec_ref(x_243);
if (lean_obj_tag(x_262) == 1)
{
if (lean_obj_tag(x_26) == 9)
{
lean_object* x_263; 
x_263 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_263);
lean_dec_ref(x_26);
if (lean_obj_tag(x_263) == 1)
{
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_264; 
x_264 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_264);
lean_dec_ref(x_24);
if (lean_obj_tag(x_264) == 1)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; uint8_t x_278; 
x_265 = lean_ctor_get(x_259, 0);
lean_inc_ref(x_265);
lean_dec_ref(x_259);
x_266 = lean_ctor_get(x_260, 0);
lean_inc_ref(x_266);
lean_dec_ref(x_260);
x_267 = lean_ctor_get(x_261, 0);
lean_inc_ref(x_267);
lean_dec_ref(x_261);
x_268 = lean_ctor_get(x_262, 0);
lean_inc_ref(x_268);
lean_dec_ref(x_262);
x_269 = lean_ctor_get(x_263, 0);
lean_inc_ref(x_269);
lean_dec_ref(x_263);
x_270 = lean_ctor_get(x_264, 0);
x_278 = !lean_is_exclusive(x_264);
if (x_278 == 0)
{
x_271 = x_264;
x_272 = x_278;
goto block_277;
}
else
{
lean_inc(x_270);
lean_dec(x_264);
x_271 = lean_box(0);
x_272 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_273; lean_object* x_274; 
x_273 = l_Lean_Name_mkStr6(x_265, x_266, x_267, x_268, x_269, x_270);
if (x_272 == 0)
{
lean_ctor_set(x_271, 0, x_273);
x_274 = x_271;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_273);
x_274 = x_276;
goto block_275;
}
block_275:
{
return x_274;
}
}
}
else
{
lean_object* x_279; 
lean_dec_ref(x_264);
lean_dec_ref(x_263);
lean_dec_ref(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
x_279 = lean_box(0);
return x_279;
}
}
else
{
lean_object* x_280; 
lean_dec_ref(x_263);
lean_dec_ref(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_24);
x_280 = lean_box(0);
return x_280;
}
}
else
{
lean_object* x_281; 
lean_dec_ref(x_263);
lean_dec_ref(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_24);
x_281 = lean_box(0);
return x_281;
}
}
else
{
lean_object* x_282; 
lean_dec_ref(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_282 = lean_box(0);
return x_282;
}
}
else
{
lean_object* x_283; 
lean_dec_ref(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_283 = lean_box(0);
return x_283;
}
}
else
{
lean_object* x_284; 
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_243);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_284 = lean_box(0);
return x_284;
}
}
else
{
lean_object* x_285; 
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_243);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_285 = lean_box(0);
return x_285;
}
}
else
{
lean_object* x_286; 
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_286 = lean_box(0);
return x_286;
}
}
else
{
lean_object* x_287; 
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_287 = lean_box(0);
return x_287;
}
}
else
{
lean_object* x_288; 
lean_dec_ref(x_259);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_288 = lean_box(0);
return x_288;
}
}
else
{
lean_object* x_289; 
lean_dec_ref(x_259);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_289 = lean_box(0);
return x_289;
}
}
else
{
lean_object* x_290; 
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_290 = lean_box(0);
return x_290;
}
}
}
}
}
else
{
lean_object* x_291; 
lean_dec_ref(x_241);
lean_dec_ref(x_240);
lean_dec_ref(x_239);
lean_dec_ref(x_186);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_291 = lean_box(0);
return x_291;
}
}
else
{
lean_object* x_292; 
lean_dec(x_241);
lean_dec_ref(x_240);
lean_dec_ref(x_239);
lean_dec_ref(x_186);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_292 = lean_box(0);
return x_292;
}
}
else
{
lean_object* x_293; 
lean_dec(x_240);
lean_dec_ref(x_239);
lean_dec_ref(x_186);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_293 = lean_box(0);
return x_293;
}
}
else
{
lean_object* x_294; 
lean_dec(x_239);
lean_dec_ref(x_186);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_294 = lean_box(0);
return x_294;
}
}
case 5:
{
lean_object* x_295; 
lean_inc_ref(x_238);
x_295 = lean_ctor_get(x_238, 0);
switch (lean_obj_tag(x_295)) {
case 4:
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
if (lean_obj_tag(x_296) == 1)
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
if (lean_obj_tag(x_297) == 1)
{
lean_object* x_298; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
if (lean_obj_tag(x_298) == 1)
{
lean_object* x_299; 
x_299 = lean_ctor_get(x_298, 0);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_300 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_300);
lean_dec_ref(x_25);
x_301 = lean_ctor_get(x_97, 1);
lean_inc_ref(x_301);
lean_dec_ref(x_97);
x_302 = lean_ctor_get(x_139, 1);
lean_inc_ref(x_302);
lean_dec_ref(x_139);
x_303 = lean_ctor_get(x_186, 1);
lean_inc_ref(x_303);
lean_dec_ref(x_186);
x_304 = lean_ctor_get(x_238, 1);
lean_inc_ref(x_304);
lean_dec_ref(x_238);
x_305 = lean_ctor_get(x_296, 1);
lean_inc_ref(x_305);
lean_dec_ref(x_296);
x_306 = lean_ctor_get(x_297, 1);
lean_inc_ref(x_306);
lean_dec_ref(x_297);
x_307 = lean_ctor_get(x_298, 1);
lean_inc_ref(x_307);
lean_dec_ref(x_298);
x_308 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_309 = lean_string_dec_eq(x_307, x_308);
lean_dec_ref(x_307);
if (x_309 == 0)
{
lean_object* x_310; 
lean_dec_ref(x_306);
lean_dec_ref(x_305);
lean_dec_ref(x_304);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec_ref(x_301);
lean_dec_ref(x_300);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_310 = lean_box(0);
return x_310;
}
else
{
lean_object* x_311; uint8_t x_312; 
x_311 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_312 = lean_string_dec_eq(x_306, x_311);
lean_dec_ref(x_306);
if (x_312 == 0)
{
lean_object* x_313; 
lean_dec_ref(x_305);
lean_dec_ref(x_304);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec_ref(x_301);
lean_dec_ref(x_300);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_313 = lean_box(0);
return x_313;
}
else
{
lean_object* x_314; uint8_t x_315; 
x_314 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__10));
x_315 = lean_string_dec_eq(x_305, x_314);
lean_dec_ref(x_305);
if (x_315 == 0)
{
lean_object* x_316; 
lean_dec_ref(x_304);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec_ref(x_301);
lean_dec_ref(x_300);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_316 = lean_box(0);
return x_316;
}
else
{
if (lean_obj_tag(x_304) == 9)
{
lean_object* x_317; 
x_317 = lean_ctor_get(x_304, 0);
lean_inc_ref(x_317);
lean_dec_ref(x_304);
if (lean_obj_tag(x_317) == 1)
{
if (lean_obj_tag(x_303) == 9)
{
lean_object* x_318; 
x_318 = lean_ctor_get(x_303, 0);
lean_inc_ref(x_318);
lean_dec_ref(x_303);
if (lean_obj_tag(x_318) == 1)
{
if (lean_obj_tag(x_302) == 9)
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_302, 0);
lean_inc_ref(x_319);
lean_dec_ref(x_302);
if (lean_obj_tag(x_319) == 1)
{
if (lean_obj_tag(x_301) == 9)
{
lean_object* x_320; 
x_320 = lean_ctor_get(x_301, 0);
lean_inc_ref(x_320);
lean_dec_ref(x_301);
if (lean_obj_tag(x_320) == 1)
{
if (lean_obj_tag(x_300) == 9)
{
lean_object* x_321; 
x_321 = lean_ctor_get(x_300, 0);
lean_inc_ref(x_321);
lean_dec_ref(x_300);
if (lean_obj_tag(x_321) == 1)
{
if (lean_obj_tag(x_26) == 9)
{
lean_object* x_322; 
x_322 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_322);
lean_dec_ref(x_26);
if (lean_obj_tag(x_322) == 1)
{
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_323; 
x_323 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_323);
lean_dec_ref(x_24);
if (lean_obj_tag(x_323) == 1)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; uint8_t x_338; 
x_324 = lean_ctor_get(x_317, 0);
lean_inc_ref(x_324);
lean_dec_ref(x_317);
x_325 = lean_ctor_get(x_318, 0);
lean_inc_ref(x_325);
lean_dec_ref(x_318);
x_326 = lean_ctor_get(x_319, 0);
lean_inc_ref(x_326);
lean_dec_ref(x_319);
x_327 = lean_ctor_get(x_320, 0);
lean_inc_ref(x_327);
lean_dec_ref(x_320);
x_328 = lean_ctor_get(x_321, 0);
lean_inc_ref(x_328);
lean_dec_ref(x_321);
x_329 = lean_ctor_get(x_322, 0);
lean_inc_ref(x_329);
lean_dec_ref(x_322);
x_330 = lean_ctor_get(x_323, 0);
x_338 = !lean_is_exclusive(x_323);
if (x_338 == 0)
{
x_331 = x_323;
x_332 = x_338;
goto block_337;
}
else
{
lean_inc(x_330);
lean_dec(x_323);
x_331 = lean_box(0);
x_332 = x_338;
goto block_337;
}
block_337:
{
lean_object* x_333; lean_object* x_334; 
x_333 = l_Lean_Name_mkStr7(x_324, x_325, x_326, x_327, x_328, x_329, x_330);
if (x_332 == 0)
{
lean_ctor_set(x_331, 0, x_333);
x_334 = x_331;
goto block_335;
}
else
{
lean_object* x_336; 
x_336 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_336, 0, x_333);
x_334 = x_336;
goto block_335;
}
block_335:
{
return x_334;
}
}
}
else
{
lean_object* x_339; 
lean_dec_ref(x_323);
lean_dec_ref(x_322);
lean_dec_ref(x_321);
lean_dec_ref(x_320);
lean_dec_ref(x_319);
lean_dec_ref(x_318);
lean_dec_ref(x_317);
x_339 = lean_box(0);
return x_339;
}
}
else
{
lean_object* x_340; 
lean_dec_ref(x_322);
lean_dec_ref(x_321);
lean_dec_ref(x_320);
lean_dec_ref(x_319);
lean_dec_ref(x_318);
lean_dec_ref(x_317);
lean_dec_ref(x_24);
x_340 = lean_box(0);
return x_340;
}
}
else
{
lean_object* x_341; 
lean_dec_ref(x_322);
lean_dec_ref(x_321);
lean_dec_ref(x_320);
lean_dec_ref(x_319);
lean_dec_ref(x_318);
lean_dec_ref(x_317);
lean_dec_ref(x_24);
x_341 = lean_box(0);
return x_341;
}
}
else
{
lean_object* x_342; 
lean_dec_ref(x_321);
lean_dec_ref(x_320);
lean_dec_ref(x_319);
lean_dec_ref(x_318);
lean_dec_ref(x_317);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_342 = lean_box(0);
return x_342;
}
}
else
{
lean_object* x_343; 
lean_dec_ref(x_321);
lean_dec_ref(x_320);
lean_dec_ref(x_319);
lean_dec_ref(x_318);
lean_dec_ref(x_317);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_343 = lean_box(0);
return x_343;
}
}
else
{
lean_object* x_344; 
lean_dec_ref(x_320);
lean_dec_ref(x_319);
lean_dec_ref(x_318);
lean_dec_ref(x_317);
lean_dec_ref(x_300);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_344 = lean_box(0);
return x_344;
}
}
else
{
lean_object* x_345; 
lean_dec_ref(x_320);
lean_dec_ref(x_319);
lean_dec_ref(x_318);
lean_dec_ref(x_317);
lean_dec_ref(x_300);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_345 = lean_box(0);
return x_345;
}
}
else
{
lean_object* x_346; 
lean_dec_ref(x_319);
lean_dec_ref(x_318);
lean_dec_ref(x_317);
lean_dec_ref(x_301);
lean_dec_ref(x_300);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_346 = lean_box(0);
return x_346;
}
}
else
{
lean_object* x_347; 
lean_dec_ref(x_319);
lean_dec_ref(x_318);
lean_dec_ref(x_317);
lean_dec_ref(x_301);
lean_dec_ref(x_300);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_347 = lean_box(0);
return x_347;
}
}
else
{
lean_object* x_348; 
lean_dec_ref(x_318);
lean_dec_ref(x_317);
lean_dec_ref(x_302);
lean_dec_ref(x_301);
lean_dec_ref(x_300);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_348 = lean_box(0);
return x_348;
}
}
else
{
lean_object* x_349; 
lean_dec_ref(x_318);
lean_dec_ref(x_317);
lean_dec_ref(x_302);
lean_dec_ref(x_301);
lean_dec_ref(x_300);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_349 = lean_box(0);
return x_349;
}
}
else
{
lean_object* x_350; 
lean_dec_ref(x_317);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec_ref(x_301);
lean_dec_ref(x_300);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_350 = lean_box(0);
return x_350;
}
}
else
{
lean_object* x_351; 
lean_dec_ref(x_317);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec_ref(x_301);
lean_dec_ref(x_300);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_351 = lean_box(0);
return x_351;
}
}
else
{
lean_object* x_352; 
lean_dec_ref(x_304);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec_ref(x_301);
lean_dec_ref(x_300);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_352 = lean_box(0);
return x_352;
}
}
}
}
}
else
{
lean_object* x_353; 
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_238);
lean_dec_ref(x_186);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_353 = lean_box(0);
return x_353;
}
}
else
{
lean_object* x_354; 
lean_dec(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_238);
lean_dec_ref(x_186);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_354 = lean_box(0);
return x_354;
}
}
else
{
lean_object* x_355; 
lean_dec_ref(x_296);
lean_dec(x_297);
lean_dec_ref(x_238);
lean_dec_ref(x_186);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_355 = lean_box(0);
return x_355;
}
}
else
{
lean_object* x_356; 
lean_dec(x_296);
lean_dec_ref(x_238);
lean_dec_ref(x_186);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_356 = lean_box(0);
return x_356;
}
}
case 5:
{
lean_object* x_357; 
lean_inc_ref(x_295);
x_357 = lean_ctor_get(x_295, 0);
if (lean_obj_tag(x_357) == 4)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
if (lean_obj_tag(x_358) == 1)
{
lean_object* x_359; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
if (lean_obj_tag(x_359) == 1)
{
lean_object* x_360; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
if (lean_obj_tag(x_360) == 1)
{
lean_object* x_361; 
x_361 = lean_ctor_get(x_360, 0);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; 
x_362 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_362);
lean_dec_ref(x_25);
x_363 = lean_ctor_get(x_97, 1);
lean_inc_ref(x_363);
lean_dec_ref(x_97);
x_364 = lean_ctor_get(x_139, 1);
lean_inc_ref(x_364);
lean_dec_ref(x_139);
x_365 = lean_ctor_get(x_186, 1);
lean_inc_ref(x_365);
lean_dec_ref(x_186);
x_366 = lean_ctor_get(x_238, 1);
lean_inc_ref(x_366);
lean_dec_ref(x_238);
x_367 = lean_ctor_get(x_295, 1);
lean_inc_ref(x_367);
lean_dec_ref(x_295);
x_368 = lean_ctor_get(x_358, 1);
lean_inc_ref(x_368);
lean_dec_ref(x_358);
x_369 = lean_ctor_get(x_359, 1);
lean_inc_ref(x_369);
lean_dec_ref(x_359);
x_370 = lean_ctor_get(x_360, 1);
lean_inc_ref(x_370);
lean_dec_ref(x_360);
x_371 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_372 = lean_string_dec_eq(x_370, x_371);
lean_dec_ref(x_370);
if (x_372 == 0)
{
lean_object* x_373; 
lean_dec_ref(x_369);
lean_dec_ref(x_368);
lean_dec_ref(x_367);
lean_dec_ref(x_366);
lean_dec_ref(x_365);
lean_dec_ref(x_364);
lean_dec_ref(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_373 = lean_box(0);
return x_373;
}
else
{
lean_object* x_374; uint8_t x_375; 
x_374 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_375 = lean_string_dec_eq(x_369, x_374);
lean_dec_ref(x_369);
if (x_375 == 0)
{
lean_object* x_376; 
lean_dec_ref(x_368);
lean_dec_ref(x_367);
lean_dec_ref(x_366);
lean_dec_ref(x_365);
lean_dec_ref(x_364);
lean_dec_ref(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_376 = lean_box(0);
return x_376;
}
else
{
lean_object* x_377; uint8_t x_378; 
x_377 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__11));
x_378 = lean_string_dec_eq(x_368, x_377);
lean_dec_ref(x_368);
if (x_378 == 0)
{
lean_object* x_379; 
lean_dec_ref(x_367);
lean_dec_ref(x_366);
lean_dec_ref(x_365);
lean_dec_ref(x_364);
lean_dec_ref(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_379 = lean_box(0);
return x_379;
}
else
{
if (lean_obj_tag(x_367) == 9)
{
lean_object* x_380; 
x_380 = lean_ctor_get(x_367, 0);
lean_inc_ref(x_380);
lean_dec_ref(x_367);
if (lean_obj_tag(x_380) == 1)
{
if (lean_obj_tag(x_366) == 9)
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_366, 0);
lean_inc_ref(x_381);
lean_dec_ref(x_366);
if (lean_obj_tag(x_381) == 1)
{
if (lean_obj_tag(x_365) == 9)
{
lean_object* x_382; 
x_382 = lean_ctor_get(x_365, 0);
lean_inc_ref(x_382);
lean_dec_ref(x_365);
if (lean_obj_tag(x_382) == 1)
{
if (lean_obj_tag(x_364) == 9)
{
lean_object* x_383; 
x_383 = lean_ctor_get(x_364, 0);
lean_inc_ref(x_383);
lean_dec_ref(x_364);
if (lean_obj_tag(x_383) == 1)
{
if (lean_obj_tag(x_363) == 9)
{
lean_object* x_384; 
x_384 = lean_ctor_get(x_363, 0);
lean_inc_ref(x_384);
lean_dec_ref(x_363);
if (lean_obj_tag(x_384) == 1)
{
if (lean_obj_tag(x_362) == 9)
{
lean_object* x_385; 
x_385 = lean_ctor_get(x_362, 0);
lean_inc_ref(x_385);
lean_dec_ref(x_362);
if (lean_obj_tag(x_385) == 1)
{
if (lean_obj_tag(x_26) == 9)
{
lean_object* x_386; 
x_386 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_386);
lean_dec_ref(x_26);
if (lean_obj_tag(x_386) == 1)
{
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_387; 
x_387 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_387);
lean_dec_ref(x_24);
if (lean_obj_tag(x_387) == 1)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; uint8_t x_403; 
x_388 = lean_ctor_get(x_380, 0);
lean_inc_ref(x_388);
lean_dec_ref(x_380);
x_389 = lean_ctor_get(x_381, 0);
lean_inc_ref(x_389);
lean_dec_ref(x_381);
x_390 = lean_ctor_get(x_382, 0);
lean_inc_ref(x_390);
lean_dec_ref(x_382);
x_391 = lean_ctor_get(x_383, 0);
lean_inc_ref(x_391);
lean_dec_ref(x_383);
x_392 = lean_ctor_get(x_384, 0);
lean_inc_ref(x_392);
lean_dec_ref(x_384);
x_393 = lean_ctor_get(x_385, 0);
lean_inc_ref(x_393);
lean_dec_ref(x_385);
x_394 = lean_ctor_get(x_386, 0);
lean_inc_ref(x_394);
lean_dec_ref(x_386);
x_395 = lean_ctor_get(x_387, 0);
x_403 = !lean_is_exclusive(x_387);
if (x_403 == 0)
{
x_396 = x_387;
x_397 = x_403;
goto block_402;
}
else
{
lean_inc(x_395);
lean_dec(x_387);
x_396 = lean_box(0);
x_397 = x_403;
goto block_402;
}
block_402:
{
lean_object* x_398; lean_object* x_399; 
x_398 = l_Lean_Name_mkStr8(x_388, x_389, x_390, x_391, x_392, x_393, x_394, x_395);
if (x_397 == 0)
{
lean_ctor_set(x_396, 0, x_398);
x_399 = x_396;
goto block_400;
}
else
{
lean_object* x_401; 
x_401 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_401, 0, x_398);
x_399 = x_401;
goto block_400;
}
block_400:
{
return x_399;
}
}
}
else
{
lean_object* x_404; 
lean_dec_ref(x_387);
lean_dec_ref(x_386);
lean_dec_ref(x_385);
lean_dec_ref(x_384);
lean_dec_ref(x_383);
lean_dec_ref(x_382);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
x_404 = lean_box(0);
return x_404;
}
}
else
{
lean_object* x_405; 
lean_dec_ref(x_386);
lean_dec_ref(x_385);
lean_dec_ref(x_384);
lean_dec_ref(x_383);
lean_dec_ref(x_382);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec_ref(x_24);
x_405 = lean_box(0);
return x_405;
}
}
else
{
lean_object* x_406; 
lean_dec_ref(x_386);
lean_dec_ref(x_385);
lean_dec_ref(x_384);
lean_dec_ref(x_383);
lean_dec_ref(x_382);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec_ref(x_24);
x_406 = lean_box(0);
return x_406;
}
}
else
{
lean_object* x_407; 
lean_dec_ref(x_385);
lean_dec_ref(x_384);
lean_dec_ref(x_383);
lean_dec_ref(x_382);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_407 = lean_box(0);
return x_407;
}
}
else
{
lean_object* x_408; 
lean_dec_ref(x_385);
lean_dec_ref(x_384);
lean_dec_ref(x_383);
lean_dec_ref(x_382);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_408 = lean_box(0);
return x_408;
}
}
else
{
lean_object* x_409; 
lean_dec_ref(x_384);
lean_dec_ref(x_383);
lean_dec_ref(x_382);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec_ref(x_362);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_409 = lean_box(0);
return x_409;
}
}
else
{
lean_object* x_410; 
lean_dec_ref(x_384);
lean_dec_ref(x_383);
lean_dec_ref(x_382);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec_ref(x_362);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_410 = lean_box(0);
return x_410;
}
}
else
{
lean_object* x_411; 
lean_dec_ref(x_383);
lean_dec_ref(x_382);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec_ref(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_411 = lean_box(0);
return x_411;
}
}
else
{
lean_object* x_412; 
lean_dec_ref(x_383);
lean_dec_ref(x_382);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec_ref(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_412 = lean_box(0);
return x_412;
}
}
else
{
lean_object* x_413; 
lean_dec_ref(x_382);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec_ref(x_364);
lean_dec_ref(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_413 = lean_box(0);
return x_413;
}
}
else
{
lean_object* x_414; 
lean_dec_ref(x_382);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec_ref(x_364);
lean_dec_ref(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_414 = lean_box(0);
return x_414;
}
}
else
{
lean_object* x_415; 
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec_ref(x_365);
lean_dec_ref(x_364);
lean_dec_ref(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_415 = lean_box(0);
return x_415;
}
}
else
{
lean_object* x_416; 
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec_ref(x_365);
lean_dec_ref(x_364);
lean_dec_ref(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_416 = lean_box(0);
return x_416;
}
}
else
{
lean_object* x_417; 
lean_dec_ref(x_380);
lean_dec_ref(x_366);
lean_dec_ref(x_365);
lean_dec_ref(x_364);
lean_dec_ref(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_417 = lean_box(0);
return x_417;
}
}
else
{
lean_object* x_418; 
lean_dec_ref(x_380);
lean_dec_ref(x_366);
lean_dec_ref(x_365);
lean_dec_ref(x_364);
lean_dec_ref(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_418 = lean_box(0);
return x_418;
}
}
else
{
lean_object* x_419; 
lean_dec_ref(x_367);
lean_dec_ref(x_366);
lean_dec_ref(x_365);
lean_dec_ref(x_364);
lean_dec_ref(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_419 = lean_box(0);
return x_419;
}
}
}
}
}
else
{
lean_object* x_420; 
lean_dec_ref(x_360);
lean_dec_ref(x_359);
lean_dec_ref(x_358);
lean_dec_ref(x_295);
lean_dec_ref(x_238);
lean_dec_ref(x_186);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_420 = lean_box(0);
return x_420;
}
}
else
{
lean_object* x_421; 
lean_dec(x_360);
lean_dec_ref(x_359);
lean_dec_ref(x_358);
lean_dec_ref(x_295);
lean_dec_ref(x_238);
lean_dec_ref(x_186);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_421 = lean_box(0);
return x_421;
}
}
else
{
lean_object* x_422; 
lean_dec(x_359);
lean_dec_ref(x_358);
lean_dec_ref(x_295);
lean_dec_ref(x_238);
lean_dec_ref(x_186);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_422 = lean_box(0);
return x_422;
}
}
else
{
lean_object* x_423; 
lean_dec(x_358);
lean_dec_ref(x_295);
lean_dec_ref(x_238);
lean_dec_ref(x_186);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_423 = lean_box(0);
return x_423;
}
}
else
{
lean_object* x_424; 
lean_dec_ref(x_295);
lean_dec_ref(x_238);
lean_dec_ref(x_186);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_424 = lean_box(0);
return x_424;
}
}
default: 
{
lean_object* x_425; 
lean_dec_ref(x_238);
lean_dec_ref(x_186);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_425 = lean_box(0);
return x_425;
}
}
}
default: 
{
lean_object* x_426; 
lean_dec_ref(x_186);
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_426 = lean_box(0);
return x_426;
}
}
}
default: 
{
lean_object* x_427; 
lean_dec_ref(x_139);
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_427 = lean_box(0);
return x_427;
}
}
}
default: 
{
lean_object* x_428; 
lean_dec_ref(x_97);
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_428 = lean_box(0);
return x_428;
}
}
}
default: 
{
lean_object* x_429; 
lean_dec_ref(x_25);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_429 = lean_box(0);
return x_429;
}
}
}
default: 
{
lean_object* x_430; 
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_430 = lean_box(0);
return x_430;
}
}
block_40:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec_ref(x_26);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = l_Lean_Expr_name_x3f(x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_39; 
x_31 = lean_ctor_get(x_30, 0);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
x_32 = x_30;
x_33 = x_39;
goto block_38;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_Name_num___override(x_31, x_29);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_34);
x_35 = x_32;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_34);
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
}
}
case 4:
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_23, 0);
lean_inc(x_431);
if (lean_obj_tag(x_431) == 1)
{
lean_object* x_432; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
if (lean_obj_tag(x_432) == 1)
{
lean_object* x_433; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
if (lean_obj_tag(x_433) == 1)
{
lean_object* x_434; 
x_434 = lean_ctor_get(x_433, 0);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; 
x_435 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_435);
lean_dec_ref(x_1);
x_436 = lean_ctor_get(x_431, 1);
lean_inc_ref(x_436);
lean_dec_ref(x_431);
x_437 = lean_ctor_get(x_432, 1);
lean_inc_ref(x_437);
lean_dec_ref(x_432);
x_438 = lean_ctor_get(x_433, 1);
lean_inc_ref(x_438);
lean_dec_ref(x_433);
x_439 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_440 = lean_string_dec_eq(x_438, x_439);
lean_dec_ref(x_438);
if (x_440 == 0)
{
lean_object* x_441; 
lean_dec_ref(x_437);
lean_dec_ref(x_436);
lean_dec_ref(x_435);
x_441 = lean_box(0);
return x_441;
}
else
{
lean_object* x_442; uint8_t x_443; 
x_442 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_443 = lean_string_dec_eq(x_437, x_442);
lean_dec_ref(x_437);
if (x_443 == 0)
{
lean_object* x_444; 
lean_dec_ref(x_436);
lean_dec_ref(x_435);
x_444 = lean_box(0);
return x_444;
}
else
{
lean_object* x_445; uint8_t x_446; 
x_445 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__12));
x_446 = lean_string_dec_eq(x_436, x_445);
lean_dec_ref(x_436);
if (x_446 == 0)
{
lean_object* x_447; 
lean_dec_ref(x_435);
x_447 = lean_box(0);
return x_447;
}
else
{
if (lean_obj_tag(x_435) == 9)
{
lean_object* x_448; 
x_448 = lean_ctor_get(x_435, 0);
lean_inc_ref(x_448);
lean_dec_ref(x_435);
if (lean_obj_tag(x_448) == 1)
{
lean_object* x_449; lean_object* x_450; uint8_t x_451; uint8_t x_457; 
x_449 = lean_ctor_get(x_448, 0);
x_457 = !lean_is_exclusive(x_448);
if (x_457 == 0)
{
x_450 = x_448;
x_451 = x_457;
goto block_456;
}
else
{
lean_inc(x_449);
lean_dec(x_448);
x_450 = lean_box(0);
x_451 = x_457;
goto block_456;
}
block_456:
{
lean_object* x_452; lean_object* x_453; 
x_452 = l_Lean_Name_mkStr1(x_449);
if (x_451 == 0)
{
lean_ctor_set(x_450, 0, x_452);
x_453 = x_450;
goto block_454;
}
else
{
lean_object* x_455; 
x_455 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_455, 0, x_452);
x_453 = x_455;
goto block_454;
}
block_454:
{
return x_453;
}
}
}
else
{
lean_object* x_458; 
lean_dec_ref(x_448);
x_458 = lean_box(0);
return x_458;
}
}
else
{
lean_object* x_459; 
lean_dec_ref(x_435);
x_459 = lean_box(0);
return x_459;
}
}
}
}
}
else
{
lean_object* x_460; 
lean_dec_ref(x_433);
lean_dec_ref(x_432);
lean_dec_ref(x_431);
lean_dec_ref(x_1);
x_460 = lean_box(0);
return x_460;
}
}
else
{
lean_object* x_461; 
lean_dec_ref(x_432);
lean_dec(x_433);
lean_dec_ref(x_431);
lean_dec_ref(x_1);
x_461 = lean_box(0);
return x_461;
}
}
else
{
lean_object* x_462; 
lean_dec(x_432);
lean_dec_ref(x_431);
lean_dec_ref(x_1);
x_462 = lean_box(0);
return x_462;
}
}
else
{
lean_object* x_463; 
lean_dec(x_431);
lean_dec_ref(x_1);
x_463 = lean_box(0);
return x_463;
}
}
default: 
{
lean_object* x_464; 
lean_dec_ref(x_1);
x_464 = lean_box(0);
return x_464;
}
}
}
default: 
{
lean_object* x_465; 
lean_dec_ref(x_1);
x_465 = lean_box(0);
return x_465;
}
}
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Recognizers(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Environment(builtin)
;
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
res = initialize_Lean_Environment(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Recognizers(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_Recognizers(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_Recognizers(builtin);
}
#ifdef __cplusplus
}
#endif
