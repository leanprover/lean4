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
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_20 = lean_box(0);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_object* x_38; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec_ref(x_25);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc_ref(x_42);
lean_dec_ref(x_38);
x_43 = lean_ctor_get(x_39, 1);
lean_inc_ref(x_43);
lean_dec_ref(x_39);
x_44 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_44);
lean_dec_ref(x_40);
x_45 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_46 = lean_string_dec_eq(x_44, x_45);
lean_dec_ref(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_47 = lean_box(0);
return x_47;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_49 = lean_string_dec_eq(x_43, x_48);
lean_dec_ref(x_43);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec_ref(x_42);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_50 = lean_box(0);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__3));
x_52 = lean_string_dec_eq(x_42, x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__4));
x_54 = lean_string_dec_eq(x_42, x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__5));
x_56 = lean_string_dec_eq(x_42, x_55);
lean_dec_ref(x_42);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_57 = lean_box(0);
return x_57;
}
else
{
if (lean_obj_tag(x_26) == 9)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_58);
lean_dec_ref(x_26);
if (lean_obj_tag(x_58) == 1)
{
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_59);
lean_dec_ref(x_24);
if (lean_obj_tag(x_59) == 1)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc_ref(x_60);
lean_dec_ref(x_58);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = l_Lean_Name_mkStr2(x_60, x_62);
lean_ctor_set(x_59, 0, x_63);
return x_59;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
lean_dec(x_59);
x_65 = l_Lean_Name_mkStr2(x_60, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
else
{
lean_object* x_67; 
lean_dec_ref(x_59);
lean_dec_ref(x_58);
x_67 = lean_box(0);
return x_67;
}
}
else
{
lean_object* x_68; 
lean_dec_ref(x_58);
lean_dec_ref(x_24);
x_68 = lean_box(0);
return x_68;
}
}
else
{
lean_object* x_69; 
lean_dec_ref(x_58);
lean_dec_ref(x_24);
x_69 = lean_box(0);
return x_69;
}
}
else
{
lean_object* x_70; 
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_70 = lean_box(0);
return x_70;
}
}
}
else
{
lean_object* x_71; 
lean_dec_ref(x_42);
lean_inc_ref(x_24);
x_71 = l_Lean_Expr_rawNatLit_x3f(x_24);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = l_Lean_Expr_nat_x3f(x_24);
x_27 = x_72;
goto block_37;
}
else
{
lean_dec_ref(x_24);
x_27 = x_71;
goto block_37;
}
}
}
else
{
lean_dec_ref(x_42);
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_73);
lean_dec_ref(x_24);
if (lean_obj_tag(x_73) == 1)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_74);
lean_dec_ref(x_73);
x_75 = l_Lean_Expr_name_x3f(x_26);
if (lean_obj_tag(x_75) == 0)
{
lean_dec_ref(x_74);
return x_75;
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = l_Lean_Name_str___override(x_77, x_74);
lean_ctor_set(x_75, 0, x_78);
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
lean_dec(x_75);
x_80 = l_Lean_Name_str___override(x_79, x_74);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; 
lean_dec_ref(x_73);
lean_dec_ref(x_26);
x_82 = lean_box(0);
return x_82;
}
}
else
{
lean_object* x_83; 
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_83 = lean_box(0);
return x_83;
}
}
}
}
}
else
{
lean_object* x_84; 
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_84 = lean_box(0);
return x_84;
}
}
else
{
lean_object* x_85; 
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_85 = lean_box(0);
return x_85;
}
}
else
{
lean_object* x_86; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_86 = lean_box(0);
return x_86;
}
}
else
{
lean_object* x_87; 
lean_dec(x_38);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_87 = lean_box(0);
return x_87;
}
}
case 5:
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_25, 0);
switch (lean_obj_tag(x_88)) {
case 4:
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 1)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 1)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 1)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_93 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_93);
lean_dec_ref(x_25);
x_94 = lean_ctor_get(x_89, 1);
lean_inc_ref(x_94);
lean_dec_ref(x_89);
x_95 = lean_ctor_get(x_90, 1);
lean_inc_ref(x_95);
lean_dec_ref(x_90);
x_96 = lean_ctor_get(x_91, 1);
lean_inc_ref(x_96);
lean_dec_ref(x_91);
x_97 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_98 = lean_string_dec_eq(x_96, x_97);
lean_dec_ref(x_96);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec_ref(x_95);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_99 = lean_box(0);
return x_99;
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_101 = lean_string_dec_eq(x_95, x_100);
lean_dec_ref(x_95);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_102 = lean_box(0);
return x_102;
}
else
{
lean_object* x_103; uint8_t x_104; 
x_103 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__6));
x_104 = lean_string_dec_eq(x_94, x_103);
lean_dec_ref(x_94);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec_ref(x_93);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_105 = lean_box(0);
return x_105;
}
else
{
if (lean_obj_tag(x_93) == 9)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_93, 0);
lean_inc_ref(x_106);
lean_dec_ref(x_93);
if (lean_obj_tag(x_106) == 1)
{
if (lean_obj_tag(x_26) == 9)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_107);
lean_dec_ref(x_26);
if (lean_obj_tag(x_107) == 1)
{
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_108);
lean_dec_ref(x_24);
if (lean_obj_tag(x_108) == 1)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_ctor_get(x_106, 0);
lean_inc_ref(x_109);
lean_dec_ref(x_106);
x_110 = lean_ctor_get(x_107, 0);
lean_inc_ref(x_110);
lean_dec_ref(x_107);
x_111 = !lean_is_exclusive(x_108);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_108, 0);
x_113 = l_Lean_Name_mkStr3(x_109, x_110, x_112);
lean_ctor_set(x_108, 0, x_113);
return x_108;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_108, 0);
lean_inc(x_114);
lean_dec(x_108);
x_115 = l_Lean_Name_mkStr3(x_109, x_110, x_114);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_106);
x_117 = lean_box(0);
return x_117;
}
}
else
{
lean_object* x_118; 
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_24);
x_118 = lean_box(0);
return x_118;
}
}
else
{
lean_object* x_119; 
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_24);
x_119 = lean_box(0);
return x_119;
}
}
else
{
lean_object* x_120; 
lean_dec_ref(x_106);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_120 = lean_box(0);
return x_120;
}
}
else
{
lean_object* x_121; 
lean_dec_ref(x_106);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_121 = lean_box(0);
return x_121;
}
}
else
{
lean_object* x_122; 
lean_dec_ref(x_93);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_122 = lean_box(0);
return x_122;
}
}
}
}
}
else
{
lean_object* x_123; 
lean_dec_ref(x_91);
lean_dec_ref(x_90);
lean_dec_ref(x_89);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_123 = lean_box(0);
return x_123;
}
}
else
{
lean_object* x_124; 
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec_ref(x_89);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_124 = lean_box(0);
return x_124;
}
}
else
{
lean_object* x_125; 
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_125 = lean_box(0);
return x_125;
}
}
else
{
lean_object* x_126; 
lean_dec(x_89);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_126 = lean_box(0);
return x_126;
}
}
case 5:
{
lean_object* x_127; 
lean_inc_ref(x_88);
x_127 = lean_ctor_get(x_88, 0);
switch (lean_obj_tag(x_127)) {
case 4:
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 1)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 1)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 1)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_130, 0);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_132 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_132);
lean_dec_ref(x_25);
x_133 = lean_ctor_get(x_88, 1);
lean_inc_ref(x_133);
lean_dec_ref(x_88);
x_134 = lean_ctor_get(x_128, 1);
lean_inc_ref(x_134);
lean_dec_ref(x_128);
x_135 = lean_ctor_get(x_129, 1);
lean_inc_ref(x_135);
lean_dec_ref(x_129);
x_136 = lean_ctor_get(x_130, 1);
lean_inc_ref(x_136);
lean_dec_ref(x_130);
x_137 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_138 = lean_string_dec_eq(x_136, x_137);
lean_dec_ref(x_136);
if (x_138 == 0)
{
lean_object* x_139; 
lean_dec_ref(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_139 = lean_box(0);
return x_139;
}
else
{
lean_object* x_140; uint8_t x_141; 
x_140 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_141 = lean_string_dec_eq(x_135, x_140);
lean_dec_ref(x_135);
if (x_141 == 0)
{
lean_object* x_142; 
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_142 = lean_box(0);
return x_142;
}
else
{
lean_object* x_143; uint8_t x_144; 
x_143 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__7));
x_144 = lean_string_dec_eq(x_134, x_143);
lean_dec_ref(x_134);
if (x_144 == 0)
{
lean_object* x_145; 
lean_dec_ref(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_145 = lean_box(0);
return x_145;
}
else
{
if (lean_obj_tag(x_133) == 9)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_133, 0);
lean_inc_ref(x_146);
lean_dec_ref(x_133);
if (lean_obj_tag(x_146) == 1)
{
if (lean_obj_tag(x_132) == 9)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_132, 0);
lean_inc_ref(x_147);
lean_dec_ref(x_132);
if (lean_obj_tag(x_147) == 1)
{
if (lean_obj_tag(x_26) == 9)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_148);
lean_dec_ref(x_26);
if (lean_obj_tag(x_148) == 1)
{
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_149);
lean_dec_ref(x_24);
if (lean_obj_tag(x_149) == 1)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_150 = lean_ctor_get(x_146, 0);
lean_inc_ref(x_150);
lean_dec_ref(x_146);
x_151 = lean_ctor_get(x_147, 0);
lean_inc_ref(x_151);
lean_dec_ref(x_147);
x_152 = lean_ctor_get(x_148, 0);
lean_inc_ref(x_152);
lean_dec_ref(x_148);
x_153 = !lean_is_exclusive(x_149);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_149, 0);
x_155 = l_Lean_Name_mkStr4(x_150, x_151, x_152, x_154);
lean_ctor_set(x_149, 0, x_155);
return x_149;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_149, 0);
lean_inc(x_156);
lean_dec(x_149);
x_157 = l_Lean_Name_mkStr4(x_150, x_151, x_152, x_156);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
}
else
{
lean_object* x_159; 
lean_dec_ref(x_149);
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec_ref(x_146);
x_159 = lean_box(0);
return x_159;
}
}
else
{
lean_object* x_160; 
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_24);
x_160 = lean_box(0);
return x_160;
}
}
else
{
lean_object* x_161; 
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_24);
x_161 = lean_box(0);
return x_161;
}
}
else
{
lean_object* x_162; 
lean_dec_ref(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_162 = lean_box(0);
return x_162;
}
}
else
{
lean_object* x_163; 
lean_dec_ref(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_163 = lean_box(0);
return x_163;
}
}
else
{
lean_object* x_164; 
lean_dec_ref(x_146);
lean_dec_ref(x_132);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_164 = lean_box(0);
return x_164;
}
}
else
{
lean_object* x_165; 
lean_dec_ref(x_146);
lean_dec_ref(x_132);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_165 = lean_box(0);
return x_165;
}
}
else
{
lean_object* x_166; 
lean_dec_ref(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_166 = lean_box(0);
return x_166;
}
}
}
}
}
else
{
lean_object* x_167; 
lean_dec_ref(x_130);
lean_dec_ref(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_167 = lean_box(0);
return x_167;
}
}
else
{
lean_object* x_168; 
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_168 = lean_box(0);
return x_168;
}
}
else
{
lean_object* x_169; 
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_169 = lean_box(0);
return x_169;
}
}
else
{
lean_object* x_170; 
lean_dec(x_128);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_170 = lean_box(0);
return x_170;
}
}
case 5:
{
lean_object* x_171; 
lean_inc_ref(x_127);
x_171 = lean_ctor_get(x_127, 0);
switch (lean_obj_tag(x_171)) {
case 4:
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 1)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_obj_tag(x_173) == 1)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_obj_tag(x_174) == 1)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_174, 0);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_176 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_176);
lean_dec_ref(x_25);
x_177 = lean_ctor_get(x_88, 1);
lean_inc_ref(x_177);
lean_dec_ref(x_88);
x_178 = lean_ctor_get(x_127, 1);
lean_inc_ref(x_178);
lean_dec_ref(x_127);
x_179 = lean_ctor_get(x_172, 1);
lean_inc_ref(x_179);
lean_dec_ref(x_172);
x_180 = lean_ctor_get(x_173, 1);
lean_inc_ref(x_180);
lean_dec_ref(x_173);
x_181 = lean_ctor_get(x_174, 1);
lean_inc_ref(x_181);
lean_dec_ref(x_174);
x_182 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_183 = lean_string_dec_eq(x_181, x_182);
lean_dec_ref(x_181);
if (x_183 == 0)
{
lean_object* x_184; 
lean_dec_ref(x_180);
lean_dec_ref(x_179);
lean_dec_ref(x_178);
lean_dec_ref(x_177);
lean_dec_ref(x_176);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_184 = lean_box(0);
return x_184;
}
else
{
lean_object* x_185; uint8_t x_186; 
x_185 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_186 = lean_string_dec_eq(x_180, x_185);
lean_dec_ref(x_180);
if (x_186 == 0)
{
lean_object* x_187; 
lean_dec_ref(x_179);
lean_dec_ref(x_178);
lean_dec_ref(x_177);
lean_dec_ref(x_176);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_187 = lean_box(0);
return x_187;
}
else
{
lean_object* x_188; uint8_t x_189; 
x_188 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__8));
x_189 = lean_string_dec_eq(x_179, x_188);
lean_dec_ref(x_179);
if (x_189 == 0)
{
lean_object* x_190; 
lean_dec_ref(x_178);
lean_dec_ref(x_177);
lean_dec_ref(x_176);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_190 = lean_box(0);
return x_190;
}
else
{
if (lean_obj_tag(x_178) == 9)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_178, 0);
lean_inc_ref(x_191);
lean_dec_ref(x_178);
if (lean_obj_tag(x_191) == 1)
{
if (lean_obj_tag(x_177) == 9)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_177, 0);
lean_inc_ref(x_192);
lean_dec_ref(x_177);
if (lean_obj_tag(x_192) == 1)
{
if (lean_obj_tag(x_176) == 9)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_176, 0);
lean_inc_ref(x_193);
lean_dec_ref(x_176);
if (lean_obj_tag(x_193) == 1)
{
if (lean_obj_tag(x_26) == 9)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_194);
lean_dec_ref(x_26);
if (lean_obj_tag(x_194) == 1)
{
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_195);
lean_dec_ref(x_24);
if (lean_obj_tag(x_195) == 1)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_196 = lean_ctor_get(x_191, 0);
lean_inc_ref(x_196);
lean_dec_ref(x_191);
x_197 = lean_ctor_get(x_192, 0);
lean_inc_ref(x_197);
lean_dec_ref(x_192);
x_198 = lean_ctor_get(x_193, 0);
lean_inc_ref(x_198);
lean_dec_ref(x_193);
x_199 = lean_ctor_get(x_194, 0);
lean_inc_ref(x_199);
lean_dec_ref(x_194);
x_200 = !lean_is_exclusive(x_195);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_195, 0);
x_202 = l_Lean_Name_mkStr5(x_196, x_197, x_198, x_199, x_201);
lean_ctor_set(x_195, 0, x_202);
return x_195;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_195, 0);
lean_inc(x_203);
lean_dec(x_195);
x_204 = l_Lean_Name_mkStr5(x_196, x_197, x_198, x_199, x_203);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
}
else
{
lean_object* x_206; 
lean_dec_ref(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
x_206 = lean_box(0);
return x_206;
}
}
else
{
lean_object* x_207; 
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_24);
x_207 = lean_box(0);
return x_207;
}
}
else
{
lean_object* x_208; 
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_24);
x_208 = lean_box(0);
return x_208;
}
}
else
{
lean_object* x_209; 
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_209 = lean_box(0);
return x_209;
}
}
else
{
lean_object* x_210; 
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_210 = lean_box(0);
return x_210;
}
}
else
{
lean_object* x_211; 
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_176);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_211 = lean_box(0);
return x_211;
}
}
else
{
lean_object* x_212; 
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec_ref(x_176);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_212 = lean_box(0);
return x_212;
}
}
else
{
lean_object* x_213; 
lean_dec_ref(x_191);
lean_dec_ref(x_177);
lean_dec_ref(x_176);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_213 = lean_box(0);
return x_213;
}
}
else
{
lean_object* x_214; 
lean_dec_ref(x_191);
lean_dec_ref(x_177);
lean_dec_ref(x_176);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_214 = lean_box(0);
return x_214;
}
}
else
{
lean_object* x_215; 
lean_dec_ref(x_178);
lean_dec_ref(x_177);
lean_dec_ref(x_176);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_215 = lean_box(0);
return x_215;
}
}
}
}
}
else
{
lean_object* x_216; 
lean_dec_ref(x_174);
lean_dec_ref(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_216 = lean_box(0);
return x_216;
}
}
else
{
lean_object* x_217; 
lean_dec(x_174);
lean_dec_ref(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_217 = lean_box(0);
return x_217;
}
}
else
{
lean_object* x_218; 
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_218 = lean_box(0);
return x_218;
}
}
else
{
lean_object* x_219; 
lean_dec(x_172);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_219 = lean_box(0);
return x_219;
}
}
case 5:
{
lean_object* x_220; 
lean_inc_ref(x_171);
x_220 = lean_ctor_get(x_171, 0);
switch (lean_obj_tag(x_220)) {
case 4:
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
if (lean_obj_tag(x_221) == 1)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
if (lean_obj_tag(x_222) == 1)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_obj_tag(x_223) == 1)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_223, 0);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_225 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_225);
lean_dec_ref(x_25);
x_226 = lean_ctor_get(x_88, 1);
lean_inc_ref(x_226);
lean_dec_ref(x_88);
x_227 = lean_ctor_get(x_127, 1);
lean_inc_ref(x_227);
lean_dec_ref(x_127);
x_228 = lean_ctor_get(x_171, 1);
lean_inc_ref(x_228);
lean_dec_ref(x_171);
x_229 = lean_ctor_get(x_221, 1);
lean_inc_ref(x_229);
lean_dec_ref(x_221);
x_230 = lean_ctor_get(x_222, 1);
lean_inc_ref(x_230);
lean_dec_ref(x_222);
x_231 = lean_ctor_get(x_223, 1);
lean_inc_ref(x_231);
lean_dec_ref(x_223);
x_232 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_233 = lean_string_dec_eq(x_231, x_232);
lean_dec_ref(x_231);
if (x_233 == 0)
{
lean_object* x_234; 
lean_dec_ref(x_230);
lean_dec_ref(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_234 = lean_box(0);
return x_234;
}
else
{
lean_object* x_235; uint8_t x_236; 
x_235 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_236 = lean_string_dec_eq(x_230, x_235);
lean_dec_ref(x_230);
if (x_236 == 0)
{
lean_object* x_237; 
lean_dec_ref(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_237 = lean_box(0);
return x_237;
}
else
{
lean_object* x_238; uint8_t x_239; 
x_238 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__9));
x_239 = lean_string_dec_eq(x_229, x_238);
lean_dec_ref(x_229);
if (x_239 == 0)
{
lean_object* x_240; 
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_240 = lean_box(0);
return x_240;
}
else
{
if (lean_obj_tag(x_228) == 9)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_228, 0);
lean_inc_ref(x_241);
lean_dec_ref(x_228);
if (lean_obj_tag(x_241) == 1)
{
if (lean_obj_tag(x_227) == 9)
{
lean_object* x_242; 
x_242 = lean_ctor_get(x_227, 0);
lean_inc_ref(x_242);
lean_dec_ref(x_227);
if (lean_obj_tag(x_242) == 1)
{
if (lean_obj_tag(x_226) == 9)
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_226, 0);
lean_inc_ref(x_243);
lean_dec_ref(x_226);
if (lean_obj_tag(x_243) == 1)
{
if (lean_obj_tag(x_225) == 9)
{
lean_object* x_244; 
x_244 = lean_ctor_get(x_225, 0);
lean_inc_ref(x_244);
lean_dec_ref(x_225);
if (lean_obj_tag(x_244) == 1)
{
if (lean_obj_tag(x_26) == 9)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_245);
lean_dec_ref(x_26);
if (lean_obj_tag(x_245) == 1)
{
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_246);
lean_dec_ref(x_24);
if (lean_obj_tag(x_246) == 1)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_247 = lean_ctor_get(x_241, 0);
lean_inc_ref(x_247);
lean_dec_ref(x_241);
x_248 = lean_ctor_get(x_242, 0);
lean_inc_ref(x_248);
lean_dec_ref(x_242);
x_249 = lean_ctor_get(x_243, 0);
lean_inc_ref(x_249);
lean_dec_ref(x_243);
x_250 = lean_ctor_get(x_244, 0);
lean_inc_ref(x_250);
lean_dec_ref(x_244);
x_251 = lean_ctor_get(x_245, 0);
lean_inc_ref(x_251);
lean_dec_ref(x_245);
x_252 = !lean_is_exclusive(x_246);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_246, 0);
x_254 = l_Lean_Name_mkStr6(x_247, x_248, x_249, x_250, x_251, x_253);
lean_ctor_set(x_246, 0, x_254);
return x_246;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_246, 0);
lean_inc(x_255);
lean_dec(x_246);
x_256 = l_Lean_Name_mkStr6(x_247, x_248, x_249, x_250, x_251, x_255);
x_257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_257, 0, x_256);
return x_257;
}
}
else
{
lean_object* x_258; 
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
x_258 = lean_box(0);
return x_258;
}
}
else
{
lean_object* x_259; 
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_dec_ref(x_24);
x_259 = lean_box(0);
return x_259;
}
}
else
{
lean_object* x_260; 
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_dec_ref(x_24);
x_260 = lean_box(0);
return x_260;
}
}
else
{
lean_object* x_261; 
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_261 = lean_box(0);
return x_261;
}
}
else
{
lean_object* x_262; 
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_262 = lean_box(0);
return x_262;
}
}
else
{
lean_object* x_263; 
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_dec_ref(x_225);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_263 = lean_box(0);
return x_263;
}
}
else
{
lean_object* x_264; 
lean_dec_ref(x_243);
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_dec_ref(x_225);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_264 = lean_box(0);
return x_264;
}
}
else
{
lean_object* x_265; 
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_265 = lean_box(0);
return x_265;
}
}
else
{
lean_object* x_266; 
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_266 = lean_box(0);
return x_266;
}
}
else
{
lean_object* x_267; 
lean_dec_ref(x_241);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_267 = lean_box(0);
return x_267;
}
}
else
{
lean_object* x_268; 
lean_dec_ref(x_241);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_268 = lean_box(0);
return x_268;
}
}
else
{
lean_object* x_269; 
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_269 = lean_box(0);
return x_269;
}
}
}
}
}
else
{
lean_object* x_270; 
lean_dec_ref(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec_ref(x_171);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_270 = lean_box(0);
return x_270;
}
}
else
{
lean_object* x_271; 
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_221);
lean_dec_ref(x_171);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_271 = lean_box(0);
return x_271;
}
}
else
{
lean_object* x_272; 
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec_ref(x_171);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_272 = lean_box(0);
return x_272;
}
}
else
{
lean_object* x_273; 
lean_dec(x_221);
lean_dec_ref(x_171);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_273 = lean_box(0);
return x_273;
}
}
case 5:
{
lean_object* x_274; 
lean_inc_ref(x_220);
x_274 = lean_ctor_get(x_220, 0);
switch (lean_obj_tag(x_274)) {
case 4:
{
lean_object* x_275; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
if (lean_obj_tag(x_275) == 1)
{
lean_object* x_276; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
if (lean_obj_tag(x_276) == 1)
{
lean_object* x_277; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
if (lean_obj_tag(x_277) == 1)
{
lean_object* x_278; 
x_278 = lean_ctor_get(x_277, 0);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_279 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_279);
lean_dec_ref(x_25);
x_280 = lean_ctor_get(x_88, 1);
lean_inc_ref(x_280);
lean_dec_ref(x_88);
x_281 = lean_ctor_get(x_127, 1);
lean_inc_ref(x_281);
lean_dec_ref(x_127);
x_282 = lean_ctor_get(x_171, 1);
lean_inc_ref(x_282);
lean_dec_ref(x_171);
x_283 = lean_ctor_get(x_220, 1);
lean_inc_ref(x_283);
lean_dec_ref(x_220);
x_284 = lean_ctor_get(x_275, 1);
lean_inc_ref(x_284);
lean_dec_ref(x_275);
x_285 = lean_ctor_get(x_276, 1);
lean_inc_ref(x_285);
lean_dec_ref(x_276);
x_286 = lean_ctor_get(x_277, 1);
lean_inc_ref(x_286);
lean_dec_ref(x_277);
x_287 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_288 = lean_string_dec_eq(x_286, x_287);
lean_dec_ref(x_286);
if (x_288 == 0)
{
lean_object* x_289; 
lean_dec_ref(x_285);
lean_dec_ref(x_284);
lean_dec_ref(x_283);
lean_dec_ref(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_289 = lean_box(0);
return x_289;
}
else
{
lean_object* x_290; uint8_t x_291; 
x_290 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_291 = lean_string_dec_eq(x_285, x_290);
lean_dec_ref(x_285);
if (x_291 == 0)
{
lean_object* x_292; 
lean_dec_ref(x_284);
lean_dec_ref(x_283);
lean_dec_ref(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_292 = lean_box(0);
return x_292;
}
else
{
lean_object* x_293; uint8_t x_294; 
x_293 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__10));
x_294 = lean_string_dec_eq(x_284, x_293);
lean_dec_ref(x_284);
if (x_294 == 0)
{
lean_object* x_295; 
lean_dec_ref(x_283);
lean_dec_ref(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_295 = lean_box(0);
return x_295;
}
else
{
if (lean_obj_tag(x_283) == 9)
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_283, 0);
lean_inc_ref(x_296);
lean_dec_ref(x_283);
if (lean_obj_tag(x_296) == 1)
{
if (lean_obj_tag(x_282) == 9)
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_282, 0);
lean_inc_ref(x_297);
lean_dec_ref(x_282);
if (lean_obj_tag(x_297) == 1)
{
if (lean_obj_tag(x_281) == 9)
{
lean_object* x_298; 
x_298 = lean_ctor_get(x_281, 0);
lean_inc_ref(x_298);
lean_dec_ref(x_281);
if (lean_obj_tag(x_298) == 1)
{
if (lean_obj_tag(x_280) == 9)
{
lean_object* x_299; 
x_299 = lean_ctor_get(x_280, 0);
lean_inc_ref(x_299);
lean_dec_ref(x_280);
if (lean_obj_tag(x_299) == 1)
{
if (lean_obj_tag(x_279) == 9)
{
lean_object* x_300; 
x_300 = lean_ctor_get(x_279, 0);
lean_inc_ref(x_300);
lean_dec_ref(x_279);
if (lean_obj_tag(x_300) == 1)
{
if (lean_obj_tag(x_26) == 9)
{
lean_object* x_301; 
x_301 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_301);
lean_dec_ref(x_26);
if (lean_obj_tag(x_301) == 1)
{
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_302; 
x_302 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_302);
lean_dec_ref(x_24);
if (lean_obj_tag(x_302) == 1)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_303 = lean_ctor_get(x_296, 0);
lean_inc_ref(x_303);
lean_dec_ref(x_296);
x_304 = lean_ctor_get(x_297, 0);
lean_inc_ref(x_304);
lean_dec_ref(x_297);
x_305 = lean_ctor_get(x_298, 0);
lean_inc_ref(x_305);
lean_dec_ref(x_298);
x_306 = lean_ctor_get(x_299, 0);
lean_inc_ref(x_306);
lean_dec_ref(x_299);
x_307 = lean_ctor_get(x_300, 0);
lean_inc_ref(x_307);
lean_dec_ref(x_300);
x_308 = lean_ctor_get(x_301, 0);
lean_inc_ref(x_308);
lean_dec_ref(x_301);
x_309 = !lean_is_exclusive(x_302);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_302, 0);
x_311 = l_Lean_Name_mkStr7(x_303, x_304, x_305, x_306, x_307, x_308, x_310);
lean_ctor_set(x_302, 0, x_311);
return x_302;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_302, 0);
lean_inc(x_312);
lean_dec(x_302);
x_313 = l_Lean_Name_mkStr7(x_303, x_304, x_305, x_306, x_307, x_308, x_312);
x_314 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_314, 0, x_313);
return x_314;
}
}
else
{
lean_object* x_315; 
lean_dec_ref(x_302);
lean_dec_ref(x_301);
lean_dec_ref(x_300);
lean_dec_ref(x_299);
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
x_315 = lean_box(0);
return x_315;
}
}
else
{
lean_object* x_316; 
lean_dec_ref(x_301);
lean_dec_ref(x_300);
lean_dec_ref(x_299);
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_24);
x_316 = lean_box(0);
return x_316;
}
}
else
{
lean_object* x_317; 
lean_dec_ref(x_301);
lean_dec_ref(x_300);
lean_dec_ref(x_299);
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_24);
x_317 = lean_box(0);
return x_317;
}
}
else
{
lean_object* x_318; 
lean_dec_ref(x_300);
lean_dec_ref(x_299);
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_318 = lean_box(0);
return x_318;
}
}
else
{
lean_object* x_319; 
lean_dec_ref(x_300);
lean_dec_ref(x_299);
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_319 = lean_box(0);
return x_319;
}
}
else
{
lean_object* x_320; 
lean_dec_ref(x_299);
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_279);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_320 = lean_box(0);
return x_320;
}
}
else
{
lean_object* x_321; 
lean_dec_ref(x_299);
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_279);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_321 = lean_box(0);
return x_321;
}
}
else
{
lean_object* x_322; 
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_322 = lean_box(0);
return x_322;
}
}
else
{
lean_object* x_323; 
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_323 = lean_box(0);
return x_323;
}
}
else
{
lean_object* x_324; 
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_324 = lean_box(0);
return x_324;
}
}
else
{
lean_object* x_325; 
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_325 = lean_box(0);
return x_325;
}
}
else
{
lean_object* x_326; 
lean_dec_ref(x_296);
lean_dec_ref(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_326 = lean_box(0);
return x_326;
}
}
else
{
lean_object* x_327; 
lean_dec_ref(x_296);
lean_dec_ref(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_327 = lean_box(0);
return x_327;
}
}
else
{
lean_object* x_328; 
lean_dec_ref(x_283);
lean_dec_ref(x_282);
lean_dec_ref(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_328 = lean_box(0);
return x_328;
}
}
}
}
}
else
{
lean_object* x_329; 
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec_ref(x_275);
lean_dec_ref(x_220);
lean_dec_ref(x_171);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_329 = lean_box(0);
return x_329;
}
}
else
{
lean_object* x_330; 
lean_dec(x_277);
lean_dec_ref(x_276);
lean_dec_ref(x_275);
lean_dec_ref(x_220);
lean_dec_ref(x_171);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_330 = lean_box(0);
return x_330;
}
}
else
{
lean_object* x_331; 
lean_dec(x_276);
lean_dec_ref(x_275);
lean_dec_ref(x_220);
lean_dec_ref(x_171);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_331 = lean_box(0);
return x_331;
}
}
else
{
lean_object* x_332; 
lean_dec(x_275);
lean_dec_ref(x_220);
lean_dec_ref(x_171);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_332 = lean_box(0);
return x_332;
}
}
case 5:
{
lean_object* x_333; 
lean_inc_ref(x_274);
x_333 = lean_ctor_get(x_274, 0);
if (lean_obj_tag(x_333) == 4)
{
lean_object* x_334; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
if (lean_obj_tag(x_334) == 1)
{
lean_object* x_335; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
if (lean_obj_tag(x_335) == 1)
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
if (lean_obj_tag(x_336) == 1)
{
lean_object* x_337; 
x_337 = lean_ctor_get(x_336, 0);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_338 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_338);
lean_dec_ref(x_25);
x_339 = lean_ctor_get(x_88, 1);
lean_inc_ref(x_339);
lean_dec_ref(x_88);
x_340 = lean_ctor_get(x_127, 1);
lean_inc_ref(x_340);
lean_dec_ref(x_127);
x_341 = lean_ctor_get(x_171, 1);
lean_inc_ref(x_341);
lean_dec_ref(x_171);
x_342 = lean_ctor_get(x_220, 1);
lean_inc_ref(x_342);
lean_dec_ref(x_220);
x_343 = lean_ctor_get(x_274, 1);
lean_inc_ref(x_343);
lean_dec_ref(x_274);
x_344 = lean_ctor_get(x_334, 1);
lean_inc_ref(x_344);
lean_dec_ref(x_334);
x_345 = lean_ctor_get(x_335, 1);
lean_inc_ref(x_345);
lean_dec_ref(x_335);
x_346 = lean_ctor_get(x_336, 1);
lean_inc_ref(x_346);
lean_dec_ref(x_336);
x_347 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_348 = lean_string_dec_eq(x_346, x_347);
lean_dec_ref(x_346);
if (x_348 == 0)
{
lean_object* x_349; 
lean_dec_ref(x_345);
lean_dec_ref(x_344);
lean_dec_ref(x_343);
lean_dec_ref(x_342);
lean_dec_ref(x_341);
lean_dec_ref(x_340);
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_349 = lean_box(0);
return x_349;
}
else
{
lean_object* x_350; uint8_t x_351; 
x_350 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_351 = lean_string_dec_eq(x_345, x_350);
lean_dec_ref(x_345);
if (x_351 == 0)
{
lean_object* x_352; 
lean_dec_ref(x_344);
lean_dec_ref(x_343);
lean_dec_ref(x_342);
lean_dec_ref(x_341);
lean_dec_ref(x_340);
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_352 = lean_box(0);
return x_352;
}
else
{
lean_object* x_353; uint8_t x_354; 
x_353 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__11));
x_354 = lean_string_dec_eq(x_344, x_353);
lean_dec_ref(x_344);
if (x_354 == 0)
{
lean_object* x_355; 
lean_dec_ref(x_343);
lean_dec_ref(x_342);
lean_dec_ref(x_341);
lean_dec_ref(x_340);
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_355 = lean_box(0);
return x_355;
}
else
{
if (lean_obj_tag(x_343) == 9)
{
lean_object* x_356; 
x_356 = lean_ctor_get(x_343, 0);
lean_inc_ref(x_356);
lean_dec_ref(x_343);
if (lean_obj_tag(x_356) == 1)
{
if (lean_obj_tag(x_342) == 9)
{
lean_object* x_357; 
x_357 = lean_ctor_get(x_342, 0);
lean_inc_ref(x_357);
lean_dec_ref(x_342);
if (lean_obj_tag(x_357) == 1)
{
if (lean_obj_tag(x_341) == 9)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_341, 0);
lean_inc_ref(x_358);
lean_dec_ref(x_341);
if (lean_obj_tag(x_358) == 1)
{
if (lean_obj_tag(x_340) == 9)
{
lean_object* x_359; 
x_359 = lean_ctor_get(x_340, 0);
lean_inc_ref(x_359);
lean_dec_ref(x_340);
if (lean_obj_tag(x_359) == 1)
{
if (lean_obj_tag(x_339) == 9)
{
lean_object* x_360; 
x_360 = lean_ctor_get(x_339, 0);
lean_inc_ref(x_360);
lean_dec_ref(x_339);
if (lean_obj_tag(x_360) == 1)
{
if (lean_obj_tag(x_338) == 9)
{
lean_object* x_361; 
x_361 = lean_ctor_get(x_338, 0);
lean_inc_ref(x_361);
lean_dec_ref(x_338);
if (lean_obj_tag(x_361) == 1)
{
if (lean_obj_tag(x_26) == 9)
{
lean_object* x_362; 
x_362 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_362);
lean_dec_ref(x_26);
if (lean_obj_tag(x_362) == 1)
{
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_363; 
x_363 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_363);
lean_dec_ref(x_24);
if (lean_obj_tag(x_363) == 1)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_364 = lean_ctor_get(x_356, 0);
lean_inc_ref(x_364);
lean_dec_ref(x_356);
x_365 = lean_ctor_get(x_357, 0);
lean_inc_ref(x_365);
lean_dec_ref(x_357);
x_366 = lean_ctor_get(x_358, 0);
lean_inc_ref(x_366);
lean_dec_ref(x_358);
x_367 = lean_ctor_get(x_359, 0);
lean_inc_ref(x_367);
lean_dec_ref(x_359);
x_368 = lean_ctor_get(x_360, 0);
lean_inc_ref(x_368);
lean_dec_ref(x_360);
x_369 = lean_ctor_get(x_361, 0);
lean_inc_ref(x_369);
lean_dec_ref(x_361);
x_370 = lean_ctor_get(x_362, 0);
lean_inc_ref(x_370);
lean_dec_ref(x_362);
x_371 = !lean_is_exclusive(x_363);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_363, 0);
x_373 = l_Lean_Name_mkStr8(x_364, x_365, x_366, x_367, x_368, x_369, x_370, x_372);
lean_ctor_set(x_363, 0, x_373);
return x_363;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_363, 0);
lean_inc(x_374);
lean_dec(x_363);
x_375 = l_Lean_Name_mkStr8(x_364, x_365, x_366, x_367, x_368, x_369, x_370, x_374);
x_376 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_376, 0, x_375);
return x_376;
}
}
else
{
lean_object* x_377; 
lean_dec_ref(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_361);
lean_dec_ref(x_360);
lean_dec_ref(x_359);
lean_dec_ref(x_358);
lean_dec_ref(x_357);
lean_dec_ref(x_356);
x_377 = lean_box(0);
return x_377;
}
}
else
{
lean_object* x_378; 
lean_dec_ref(x_362);
lean_dec_ref(x_361);
lean_dec_ref(x_360);
lean_dec_ref(x_359);
lean_dec_ref(x_358);
lean_dec_ref(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_24);
x_378 = lean_box(0);
return x_378;
}
}
else
{
lean_object* x_379; 
lean_dec_ref(x_362);
lean_dec_ref(x_361);
lean_dec_ref(x_360);
lean_dec_ref(x_359);
lean_dec_ref(x_358);
lean_dec_ref(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_24);
x_379 = lean_box(0);
return x_379;
}
}
else
{
lean_object* x_380; 
lean_dec_ref(x_361);
lean_dec_ref(x_360);
lean_dec_ref(x_359);
lean_dec_ref(x_358);
lean_dec_ref(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_380 = lean_box(0);
return x_380;
}
}
else
{
lean_object* x_381; 
lean_dec_ref(x_361);
lean_dec_ref(x_360);
lean_dec_ref(x_359);
lean_dec_ref(x_358);
lean_dec_ref(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_381 = lean_box(0);
return x_381;
}
}
else
{
lean_object* x_382; 
lean_dec_ref(x_360);
lean_dec_ref(x_359);
lean_dec_ref(x_358);
lean_dec_ref(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_338);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_382 = lean_box(0);
return x_382;
}
}
else
{
lean_object* x_383; 
lean_dec_ref(x_360);
lean_dec_ref(x_359);
lean_dec_ref(x_358);
lean_dec_ref(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_338);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_383 = lean_box(0);
return x_383;
}
}
else
{
lean_object* x_384; 
lean_dec_ref(x_359);
lean_dec_ref(x_358);
lean_dec_ref(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_384 = lean_box(0);
return x_384;
}
}
else
{
lean_object* x_385; 
lean_dec_ref(x_359);
lean_dec_ref(x_358);
lean_dec_ref(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_385 = lean_box(0);
return x_385;
}
}
else
{
lean_object* x_386; 
lean_dec_ref(x_358);
lean_dec_ref(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_340);
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_386 = lean_box(0);
return x_386;
}
}
else
{
lean_object* x_387; 
lean_dec_ref(x_358);
lean_dec_ref(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_340);
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_387 = lean_box(0);
return x_387;
}
}
else
{
lean_object* x_388; 
lean_dec_ref(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_341);
lean_dec_ref(x_340);
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_388 = lean_box(0);
return x_388;
}
}
else
{
lean_object* x_389; 
lean_dec_ref(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_341);
lean_dec_ref(x_340);
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_389 = lean_box(0);
return x_389;
}
}
else
{
lean_object* x_390; 
lean_dec_ref(x_356);
lean_dec_ref(x_342);
lean_dec_ref(x_341);
lean_dec_ref(x_340);
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_390 = lean_box(0);
return x_390;
}
}
else
{
lean_object* x_391; 
lean_dec_ref(x_356);
lean_dec_ref(x_342);
lean_dec_ref(x_341);
lean_dec_ref(x_340);
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_391 = lean_box(0);
return x_391;
}
}
else
{
lean_object* x_392; 
lean_dec_ref(x_343);
lean_dec_ref(x_342);
lean_dec_ref(x_341);
lean_dec_ref(x_340);
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_392 = lean_box(0);
return x_392;
}
}
}
}
}
else
{
lean_object* x_393; 
lean_dec_ref(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_274);
lean_dec_ref(x_220);
lean_dec_ref(x_171);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_393 = lean_box(0);
return x_393;
}
}
else
{
lean_object* x_394; 
lean_dec(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_274);
lean_dec_ref(x_220);
lean_dec_ref(x_171);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_394 = lean_box(0);
return x_394;
}
}
else
{
lean_object* x_395; 
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec_ref(x_274);
lean_dec_ref(x_220);
lean_dec_ref(x_171);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_395 = lean_box(0);
return x_395;
}
}
else
{
lean_object* x_396; 
lean_dec(x_334);
lean_dec_ref(x_274);
lean_dec_ref(x_220);
lean_dec_ref(x_171);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_396 = lean_box(0);
return x_396;
}
}
else
{
lean_object* x_397; 
lean_dec_ref(x_274);
lean_dec_ref(x_220);
lean_dec_ref(x_171);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_397 = lean_box(0);
return x_397;
}
}
default: 
{
lean_object* x_398; 
lean_dec_ref(x_220);
lean_dec_ref(x_171);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_398 = lean_box(0);
return x_398;
}
}
}
default: 
{
lean_object* x_399; 
lean_dec_ref(x_171);
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_399 = lean_box(0);
return x_399;
}
}
}
default: 
{
lean_object* x_400; 
lean_dec_ref(x_127);
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_400 = lean_box(0);
return x_400;
}
}
}
default: 
{
lean_object* x_401; 
lean_dec_ref(x_88);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_401 = lean_box(0);
return x_401;
}
}
}
default: 
{
lean_object* x_402; 
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_402 = lean_box(0);
return x_402;
}
}
}
default: 
{
lean_object* x_403; 
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_403 = lean_box(0);
return x_403;
}
}
block_37:
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
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l_Lean_Name_num___override(x_32, x_29);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = l_Lean_Name_num___override(x_34, x_29);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
case 4:
{
lean_object* x_404; 
x_404 = lean_ctor_get(x_23, 0);
lean_inc(x_404);
if (lean_obj_tag(x_404) == 1)
{
lean_object* x_405; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
if (lean_obj_tag(x_405) == 1)
{
lean_object* x_406; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
if (lean_obj_tag(x_406) == 1)
{
lean_object* x_407; 
x_407 = lean_ctor_get(x_406, 0);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_408 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_408);
lean_dec_ref(x_1);
x_409 = lean_ctor_get(x_404, 1);
lean_inc_ref(x_409);
lean_dec_ref(x_404);
x_410 = lean_ctor_get(x_405, 1);
lean_inc_ref(x_410);
lean_dec_ref(x_405);
x_411 = lean_ctor_get(x_406, 1);
lean_inc_ref(x_411);
lean_dec_ref(x_406);
x_412 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
x_413 = lean_string_dec_eq(x_411, x_412);
lean_dec_ref(x_411);
if (x_413 == 0)
{
lean_object* x_414; 
lean_dec_ref(x_410);
lean_dec_ref(x_409);
lean_dec_ref(x_408);
x_414 = lean_box(0);
return x_414;
}
else
{
lean_object* x_415; uint8_t x_416; 
x_415 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
x_416 = lean_string_dec_eq(x_410, x_415);
lean_dec_ref(x_410);
if (x_416 == 0)
{
lean_object* x_417; 
lean_dec_ref(x_409);
lean_dec_ref(x_408);
x_417 = lean_box(0);
return x_417;
}
else
{
lean_object* x_418; uint8_t x_419; 
x_418 = ((lean_object*)(l_Lean_Expr_name_x3f___closed__12));
x_419 = lean_string_dec_eq(x_409, x_418);
lean_dec_ref(x_409);
if (x_419 == 0)
{
lean_object* x_420; 
lean_dec_ref(x_408);
x_420 = lean_box(0);
return x_420;
}
else
{
if (lean_obj_tag(x_408) == 9)
{
lean_object* x_421; 
x_421 = lean_ctor_get(x_408, 0);
lean_inc_ref(x_421);
lean_dec_ref(x_408);
if (lean_obj_tag(x_421) == 1)
{
uint8_t x_422; 
x_422 = !lean_is_exclusive(x_421);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; 
x_423 = lean_ctor_get(x_421, 0);
x_424 = l_Lean_Name_mkStr1(x_423);
lean_ctor_set(x_421, 0, x_424);
return x_421;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_421, 0);
lean_inc(x_425);
lean_dec(x_421);
x_426 = l_Lean_Name_mkStr1(x_425);
x_427 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_427, 0, x_426);
return x_427;
}
}
else
{
lean_object* x_428; 
lean_dec_ref(x_421);
x_428 = lean_box(0);
return x_428;
}
}
else
{
lean_object* x_429; 
lean_dec_ref(x_408);
x_429 = lean_box(0);
return x_429;
}
}
}
}
}
else
{
lean_object* x_430; 
lean_dec_ref(x_406);
lean_dec_ref(x_405);
lean_dec_ref(x_404);
lean_dec_ref(x_1);
x_430 = lean_box(0);
return x_430;
}
}
else
{
lean_object* x_431; 
lean_dec(x_406);
lean_dec_ref(x_405);
lean_dec_ref(x_404);
lean_dec_ref(x_1);
x_431 = lean_box(0);
return x_431;
}
}
else
{
lean_object* x_432; 
lean_dec(x_405);
lean_dec_ref(x_404);
lean_dec_ref(x_1);
x_432 = lean_box(0);
return x_432;
}
}
else
{
lean_object* x_433; 
lean_dec(x_404);
lean_dec_ref(x_1);
x_433 = lean_box(0);
return x_433;
}
}
default: 
{
lean_object* x_434; 
lean_dec_ref(x_1);
x_434 = lean_box(0);
return x_434;
}
}
}
default: 
{
lean_object* x_435; 
lean_dec_ref(x_1);
x_435 = lean_box(0);
return x_435;
}
}
}
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
