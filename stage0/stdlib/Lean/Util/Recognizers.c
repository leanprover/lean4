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
LEAN_EXPORT uint8_t l_Lean_Expr_isEq(lean_object* v_e_225_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_226_ = ((lean_object*)(l_Lean_Expr_eq_x3f___closed__1));
v___x_227_ = lean_unsigned_to_nat(3u);
v___x_228_ = l_Lean_Expr_isAppOfArity(v_e_225_, v___x_226_, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isEq___boxed(lean_object* v_e_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_Lean_Expr_isEq(v_e_229_);
lean_dec_ref(v_e_229_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHEq(lean_object* v_e_232_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_233_ = ((lean_object*)(l_Lean_Expr_heq_x3f___closed__1));
v___x_234_ = lean_unsigned_to_nat(4u);
v___x_235_ = l_Lean_Expr_isAppOfArity(v_e_232_, v___x_233_, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHEq___boxed(lean_object* v_e_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Lean_Expr_isHEq(v_e_236_);
lean_dec_ref(v_e_236_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isIte(lean_object* v_e_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_243_ = ((lean_object*)(l_Lean_Expr_isIte___closed__1));
v___x_244_ = lean_unsigned_to_nat(5u);
v___x_245_ = l_Lean_Expr_isAppOfArity(v_e_242_, v___x_243_, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isIte___boxed(lean_object* v_e_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Lean_Expr_isIte(v_e_246_);
lean_dec_ref(v_e_246_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isDIte(lean_object* v_e_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_253_ = ((lean_object*)(l_Lean_Expr_isDIte___closed__1));
v___x_254_ = lean_unsigned_to_nat(5u);
v___x_255_ = l_Lean_Expr_isAppOfArity(v_e_252_, v___x_253_, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isDIte___boxed(lean_object* v_e_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Lean_Expr_isDIte(v_e_256_);
lean_dec_ref(v_e_256_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop(lean_object* v_e_268_, lean_object* v_acc_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_270_ = ((lean_object*)(l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2));
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = l_Lean_Expr_isAppOfArity_x27(v_e_268_, v___x_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_273_ = ((lean_object*)(l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4));
v___x_274_ = lean_unsigned_to_nat(3u);
v___x_275_ = l_Lean_Expr_isAppOfArity_x27(v_e_268_, v___x_273_, v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
lean_dec(v_acc_269_);
lean_dec_ref(v_e_268_);
v___x_276_ = lean_box(0);
return v___x_276_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_277_ = l_Lean_Expr_appArg_x21_x27(v_e_268_);
v___x_278_ = l_Lean_Expr_appFn_x21_x27(v_e_268_);
lean_dec_ref(v_e_268_);
v___x_279_ = l_Lean_Expr_appArg_x21_x27(v___x_278_);
lean_dec_ref(v___x_278_);
v___x_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v_acc_269_);
v_e_268_ = v___x_277_;
v_acc_269_ = v___x_280_;
goto _start;
}
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_282_ = l_Lean_Expr_appArg_x21_x27(v_e_268_);
lean_dec_ref(v_e_268_);
v___x_283_ = l_List_reverse___redArg(v_acc_269_);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_listLit_x3f(lean_object* v_e_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_box(0);
v___x_288_ = l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop(v_e_286_, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_arrayLit_x3f(lean_object* v_e_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_294_ = ((lean_object*)(l_Lean_Expr_arrayLit_x3f___closed__1));
v___x_295_ = lean_unsigned_to_nat(2u);
v___x_296_ = l_Lean_Expr_isAppOfArity_x27(v_e_293_, v___x_294_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_box(0);
return v___x_297_;
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = l_Lean_Expr_appArg_x21_x27(v_e_293_);
v___x_299_ = l_Lean_Expr_listLit_x3f(v___x_298_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_arrayLit_x3f___boxed(lean_object* v_e_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Expr_arrayLit_x3f(v_e_300_);
lean_dec_ref(v_e_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_prod_x3f(lean_object* v_e_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_306_ = ((lean_object*)(l_Lean_Expr_prod_x3f___closed__1));
v___x_307_ = lean_unsigned_to_nat(2u);
v___x_308_ = l_Lean_Expr_isAppOfArity(v_e_305_, v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
v___x_309_ = lean_box(0);
return v___x_309_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_310_ = l_Lean_Expr_appFn_x21(v_e_305_);
v___x_311_ = l_Lean_Expr_appArg_x21(v___x_310_);
lean_dec_ref(v___x_310_);
v___x_312_ = l_Lean_Expr_appArg_x21(v_e_305_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_prod_x3f___boxed(lean_object* v_e_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Expr_prod_x3f(v_e_315_);
lean_dec_ref(v_e_315_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_name_x3f(lean_object* v_x_330_){
_start:
{
switch(lean_obj_tag(v_x_330_))
{
case 4:
{
lean_object* v_declName_331_; 
v_declName_331_ = lean_ctor_get(v_x_330_, 0);
lean_inc(v_declName_331_);
lean_dec_ref(v_x_330_);
if (lean_obj_tag(v_declName_331_) == 1)
{
lean_object* v_pre_332_; 
v_pre_332_ = lean_ctor_get(v_declName_331_, 0);
lean_inc(v_pre_332_);
if (lean_obj_tag(v_pre_332_) == 1)
{
lean_object* v_pre_333_; 
v_pre_333_ = lean_ctor_get(v_pre_332_, 0);
lean_inc(v_pre_333_);
if (lean_obj_tag(v_pre_333_) == 1)
{
lean_object* v_pre_334_; 
v_pre_334_ = lean_ctor_get(v_pre_333_, 0);
lean_inc(v_pre_334_);
if (lean_obj_tag(v_pre_334_) == 0)
{
lean_object* v_str_335_; lean_object* v_str_336_; lean_object* v_str_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_str_335_ = lean_ctor_get(v_declName_331_, 1);
lean_inc_ref(v_str_335_);
lean_dec_ref(v_declName_331_);
v_str_336_ = lean_ctor_get(v_pre_332_, 1);
lean_inc_ref(v_str_336_);
lean_dec_ref(v_pre_332_);
v_str_337_ = lean_ctor_get(v_pre_333_, 1);
lean_inc_ref(v_str_337_);
lean_dec_ref(v_pre_333_);
v___x_338_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_339_ = lean_string_dec_eq(v_str_337_, v___x_338_);
lean_dec_ref(v_str_337_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; 
lean_dec_ref(v_str_336_);
lean_dec_ref(v_str_335_);
v___x_340_ = lean_box(0);
return v___x_340_;
}
else
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_342_ = lean_string_dec_eq(v_str_336_, v___x_341_);
lean_dec_ref(v_str_336_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_dec_ref(v_str_335_);
v___x_343_ = lean_box(0);
return v___x_343_;
}
else
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__2));
v___x_345_ = lean_string_dec_eq(v_str_335_, v___x_344_);
lean_dec_ref(v_str_335_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
v___x_346_ = lean_box(0);
return v___x_346_;
}
else
{
lean_object* v___x_347_; 
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v_pre_334_);
return v___x_347_;
}
}
}
}
else
{
lean_object* v___x_348_; 
lean_dec(v_pre_334_);
lean_dec_ref(v_pre_333_);
lean_dec_ref(v_pre_332_);
lean_dec_ref(v_declName_331_);
v___x_348_ = lean_box(0);
return v___x_348_;
}
}
else
{
lean_object* v___x_349_; 
lean_dec_ref(v_pre_332_);
lean_dec(v_pre_333_);
lean_dec_ref(v_declName_331_);
v___x_349_ = lean_box(0);
return v___x_349_;
}
}
else
{
lean_object* v___x_350_; 
lean_dec_ref(v_declName_331_);
lean_dec(v_pre_332_);
v___x_350_ = lean_box(0);
return v___x_350_;
}
}
else
{
lean_object* v___x_351_; 
lean_dec(v_declName_331_);
v___x_351_ = lean_box(0);
return v___x_351_;
}
}
case 5:
{
lean_object* v_fn_352_; 
v_fn_352_ = lean_ctor_get(v_x_330_, 0);
switch(lean_obj_tag(v_fn_352_))
{
case 5:
{
lean_object* v_arg_353_; lean_object* v_fn_354_; lean_object* v_arg_355_; lean_object* v___y_357_; 
lean_inc_ref(v_fn_352_);
v_arg_353_ = lean_ctor_get(v_x_330_, 1);
lean_inc_ref(v_arg_353_);
lean_dec_ref(v_x_330_);
v_fn_354_ = lean_ctor_get(v_fn_352_, 0);
lean_inc_ref(v_fn_354_);
v_arg_355_ = lean_ctor_get(v_fn_352_, 1);
lean_inc_ref(v_arg_355_);
lean_dec_ref(v_fn_352_);
switch(lean_obj_tag(v_fn_354_))
{
case 4:
{
lean_object* v_declName_370_; 
v_declName_370_ = lean_ctor_get(v_fn_354_, 0);
lean_inc(v_declName_370_);
lean_dec_ref(v_fn_354_);
if (lean_obj_tag(v_declName_370_) == 1)
{
lean_object* v_pre_371_; 
v_pre_371_ = lean_ctor_get(v_declName_370_, 0);
lean_inc(v_pre_371_);
if (lean_obj_tag(v_pre_371_) == 1)
{
lean_object* v_pre_372_; 
v_pre_372_ = lean_ctor_get(v_pre_371_, 0);
lean_inc(v_pre_372_);
if (lean_obj_tag(v_pre_372_) == 1)
{
lean_object* v_pre_373_; 
v_pre_373_ = lean_ctor_get(v_pre_372_, 0);
if (lean_obj_tag(v_pre_373_) == 0)
{
lean_object* v_str_374_; lean_object* v_str_375_; lean_object* v_str_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v_str_374_ = lean_ctor_get(v_declName_370_, 1);
lean_inc_ref(v_str_374_);
lean_dec_ref(v_declName_370_);
v_str_375_ = lean_ctor_get(v_pre_371_, 1);
lean_inc_ref(v_str_375_);
lean_dec_ref(v_pre_371_);
v_str_376_ = lean_ctor_get(v_pre_372_, 1);
lean_inc_ref(v_str_376_);
lean_dec_ref(v_pre_372_);
v___x_377_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_378_ = lean_string_dec_eq(v_str_376_, v___x_377_);
lean_dec_ref(v_str_376_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
lean_dec_ref(v_str_375_);
lean_dec_ref(v_str_374_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_379_ = lean_box(0);
return v___x_379_;
}
else
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_381_ = lean_string_dec_eq(v_str_375_, v___x_380_);
lean_dec_ref(v_str_375_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; 
lean_dec_ref(v_str_374_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_382_ = lean_box(0);
return v___x_382_;
}
else
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__3));
v___x_384_ = lean_string_dec_eq(v_str_374_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__4));
v___x_386_ = lean_string_dec_eq(v_str_374_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__5));
v___x_388_ = lean_string_dec_eq(v_str_374_, v___x_387_);
lean_dec_ref(v_str_374_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_389_ = lean_box(0);
return v___x_389_;
}
else
{
if (lean_obj_tag(v_arg_355_) == 9)
{
lean_object* v_a_390_; 
v_a_390_ = lean_ctor_get(v_arg_355_, 0);
lean_inc_ref(v_a_390_);
lean_dec_ref(v_arg_355_);
if (lean_obj_tag(v_a_390_) == 1)
{
if (lean_obj_tag(v_arg_353_) == 9)
{
lean_object* v_a_391_; 
v_a_391_ = lean_ctor_get(v_arg_353_, 0);
lean_inc_ref(v_a_391_);
lean_dec_ref(v_arg_353_);
if (lean_obj_tag(v_a_391_) == 1)
{
lean_object* v_val_392_; lean_object* v_val_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_val_392_ = lean_ctor_get(v_a_390_, 0);
lean_inc_ref(v_val_392_);
lean_dec_ref(v_a_390_);
v_val_393_ = lean_ctor_get(v_a_391_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_a_391_);
if (v_isSharedCheck_401_ == 0)
{
v___x_395_ = v_a_391_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_val_393_);
lean_dec(v_a_391_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = l_Lean_Name_mkStr2(v_val_392_, v_val_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
else
{
lean_object* v___x_402_; 
lean_dec_ref(v_a_391_);
lean_dec_ref(v_a_390_);
v___x_402_ = lean_box(0);
return v___x_402_;
}
}
else
{
lean_object* v___x_403_; 
lean_dec_ref(v_a_390_);
lean_dec_ref(v_arg_353_);
v___x_403_ = lean_box(0);
return v___x_403_;
}
}
else
{
lean_object* v___x_404_; 
lean_dec_ref(v_a_390_);
lean_dec_ref(v_arg_353_);
v___x_404_ = lean_box(0);
return v___x_404_;
}
}
else
{
lean_object* v___x_405_; 
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_405_ = lean_box(0);
return v___x_405_;
}
}
}
else
{
lean_object* v___x_406_; 
lean_dec_ref(v_str_374_);
lean_inc_ref(v_arg_353_);
v___x_406_ = l_Lean_Expr_rawNatLit_x3f(v_arg_353_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Expr_nat_x3f(v_arg_353_);
v___y_357_ = v___x_407_;
goto v___jp_356_;
}
else
{
lean_dec_ref(v_arg_353_);
v___y_357_ = v___x_406_;
goto v___jp_356_;
}
}
}
else
{
lean_dec_ref(v_str_374_);
if (lean_obj_tag(v_arg_353_) == 9)
{
lean_object* v_a_408_; 
v_a_408_ = lean_ctor_get(v_arg_353_, 0);
lean_inc_ref(v_a_408_);
lean_dec_ref(v_arg_353_);
if (lean_obj_tag(v_a_408_) == 1)
{
lean_object* v_val_409_; lean_object* v___x_410_; 
v_val_409_ = lean_ctor_get(v_a_408_, 0);
lean_inc_ref(v_val_409_);
lean_dec_ref(v_a_408_);
v___x_410_ = l_Lean_Expr_name_x3f(v_arg_355_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_dec_ref(v_val_409_);
return v___x_410_;
}
else
{
lean_object* v_val_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_419_; 
v_val_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_419_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_val_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = l_Lean_Name_str___override(v_val_411_, v_val_409_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_415_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_object* v___x_420_; 
lean_dec_ref(v_a_408_);
lean_dec_ref(v_arg_355_);
v___x_420_ = lean_box(0);
return v___x_420_;
}
}
else
{
lean_object* v___x_421_; 
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_421_ = lean_box(0);
return v___x_421_;
}
}
}
}
}
else
{
lean_object* v___x_422_; 
lean_dec_ref(v_pre_372_);
lean_dec_ref(v_pre_371_);
lean_dec_ref(v_declName_370_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_422_ = lean_box(0);
return v___x_422_;
}
}
else
{
lean_object* v___x_423_; 
lean_dec(v_pre_372_);
lean_dec_ref(v_pre_371_);
lean_dec_ref(v_declName_370_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_423_ = lean_box(0);
return v___x_423_;
}
}
else
{
lean_object* v___x_424_; 
lean_dec_ref(v_declName_370_);
lean_dec(v_pre_371_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_424_ = lean_box(0);
return v___x_424_;
}
}
else
{
lean_object* v___x_425_; 
lean_dec(v_declName_370_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_425_ = lean_box(0);
return v___x_425_;
}
}
case 5:
{
lean_object* v_fn_426_; 
v_fn_426_ = lean_ctor_get(v_fn_354_, 0);
switch(lean_obj_tag(v_fn_426_))
{
case 4:
{
lean_object* v_declName_427_; 
v_declName_427_ = lean_ctor_get(v_fn_426_, 0);
lean_inc(v_declName_427_);
if (lean_obj_tag(v_declName_427_) == 1)
{
lean_object* v_pre_428_; 
v_pre_428_ = lean_ctor_get(v_declName_427_, 0);
lean_inc(v_pre_428_);
if (lean_obj_tag(v_pre_428_) == 1)
{
lean_object* v_pre_429_; 
v_pre_429_ = lean_ctor_get(v_pre_428_, 0);
lean_inc(v_pre_429_);
if (lean_obj_tag(v_pre_429_) == 1)
{
lean_object* v_pre_430_; 
v_pre_430_ = lean_ctor_get(v_pre_429_, 0);
if (lean_obj_tag(v_pre_430_) == 0)
{
lean_object* v_arg_431_; lean_object* v_str_432_; lean_object* v_str_433_; lean_object* v_str_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_arg_431_ = lean_ctor_get(v_fn_354_, 1);
lean_inc_ref(v_arg_431_);
lean_dec_ref(v_fn_354_);
v_str_432_ = lean_ctor_get(v_declName_427_, 1);
lean_inc_ref(v_str_432_);
lean_dec_ref(v_declName_427_);
v_str_433_ = lean_ctor_get(v_pre_428_, 1);
lean_inc_ref(v_str_433_);
lean_dec_ref(v_pre_428_);
v_str_434_ = lean_ctor_get(v_pre_429_, 1);
lean_inc_ref(v_str_434_);
lean_dec_ref(v_pre_429_);
v___x_435_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_436_ = lean_string_dec_eq(v_str_434_, v___x_435_);
lean_dec_ref(v_str_434_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; 
lean_dec_ref(v_str_433_);
lean_dec_ref(v_str_432_);
lean_dec_ref(v_arg_431_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_437_ = lean_box(0);
return v___x_437_;
}
else
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_439_ = lean_string_dec_eq(v_str_433_, v___x_438_);
lean_dec_ref(v_str_433_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
lean_dec_ref(v_str_432_);
lean_dec_ref(v_arg_431_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_440_ = lean_box(0);
return v___x_440_;
}
else
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__6));
v___x_442_ = lean_string_dec_eq(v_str_432_, v___x_441_);
lean_dec_ref(v_str_432_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
lean_dec_ref(v_arg_431_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_443_ = lean_box(0);
return v___x_443_;
}
else
{
if (lean_obj_tag(v_arg_431_) == 9)
{
lean_object* v_a_444_; 
v_a_444_ = lean_ctor_get(v_arg_431_, 0);
lean_inc_ref(v_a_444_);
lean_dec_ref(v_arg_431_);
if (lean_obj_tag(v_a_444_) == 1)
{
if (lean_obj_tag(v_arg_355_) == 9)
{
lean_object* v_a_445_; 
v_a_445_ = lean_ctor_get(v_arg_355_, 0);
lean_inc_ref(v_a_445_);
lean_dec_ref(v_arg_355_);
if (lean_obj_tag(v_a_445_) == 1)
{
if (lean_obj_tag(v_arg_353_) == 9)
{
lean_object* v_a_446_; 
v_a_446_ = lean_ctor_get(v_arg_353_, 0);
lean_inc_ref(v_a_446_);
lean_dec_ref(v_arg_353_);
if (lean_obj_tag(v_a_446_) == 1)
{
lean_object* v_val_447_; lean_object* v_val_448_; lean_object* v_val_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_457_; 
v_val_447_ = lean_ctor_get(v_a_444_, 0);
lean_inc_ref(v_val_447_);
lean_dec_ref(v_a_444_);
v_val_448_ = lean_ctor_get(v_a_445_, 0);
lean_inc_ref(v_val_448_);
lean_dec_ref(v_a_445_);
v_val_449_ = lean_ctor_get(v_a_446_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_a_446_);
if (v_isSharedCheck_457_ == 0)
{
v___x_451_ = v_a_446_;
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_val_449_);
lean_dec(v_a_446_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = l_Lean_Name_mkStr3(v_val_447_, v_val_448_, v_val_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_453_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
else
{
lean_object* v___x_458_; 
lean_dec_ref(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec_ref(v_a_444_);
v___x_458_ = lean_box(0);
return v___x_458_;
}
}
else
{
lean_object* v___x_459_; 
lean_dec_ref(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec_ref(v_arg_353_);
v___x_459_ = lean_box(0);
return v___x_459_;
}
}
else
{
lean_object* v___x_460_; 
lean_dec_ref(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec_ref(v_arg_353_);
v___x_460_ = lean_box(0);
return v___x_460_;
}
}
else
{
lean_object* v___x_461_; 
lean_dec_ref(v_a_444_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_461_ = lean_box(0);
return v___x_461_;
}
}
else
{
lean_object* v___x_462_; 
lean_dec_ref(v_a_444_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_462_ = lean_box(0);
return v___x_462_;
}
}
else
{
lean_object* v___x_463_; 
lean_dec_ref(v_arg_431_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_463_ = lean_box(0);
return v___x_463_;
}
}
}
}
}
else
{
lean_object* v___x_464_; 
lean_dec_ref(v_pre_429_);
lean_dec_ref(v_pre_428_);
lean_dec_ref(v_declName_427_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_464_ = lean_box(0);
return v___x_464_;
}
}
else
{
lean_object* v___x_465_; 
lean_dec(v_pre_429_);
lean_dec_ref(v_pre_428_);
lean_dec_ref(v_declName_427_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_465_ = lean_box(0);
return v___x_465_;
}
}
else
{
lean_object* v___x_466_; 
lean_dec_ref(v_declName_427_);
lean_dec(v_pre_428_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_466_ = lean_box(0);
return v___x_466_;
}
}
else
{
lean_object* v___x_467_; 
lean_dec(v_declName_427_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_467_ = lean_box(0);
return v___x_467_;
}
}
case 5:
{
lean_object* v_fn_468_; 
lean_inc_ref(v_fn_426_);
v_fn_468_ = lean_ctor_get(v_fn_426_, 0);
switch(lean_obj_tag(v_fn_468_))
{
case 4:
{
lean_object* v_declName_469_; 
v_declName_469_ = lean_ctor_get(v_fn_468_, 0);
lean_inc(v_declName_469_);
if (lean_obj_tag(v_declName_469_) == 1)
{
lean_object* v_pre_470_; 
v_pre_470_ = lean_ctor_get(v_declName_469_, 0);
lean_inc(v_pre_470_);
if (lean_obj_tag(v_pre_470_) == 1)
{
lean_object* v_pre_471_; 
v_pre_471_ = lean_ctor_get(v_pre_470_, 0);
lean_inc(v_pre_471_);
if (lean_obj_tag(v_pre_471_) == 1)
{
lean_object* v_pre_472_; 
v_pre_472_ = lean_ctor_get(v_pre_471_, 0);
if (lean_obj_tag(v_pre_472_) == 0)
{
lean_object* v_arg_473_; lean_object* v_arg_474_; lean_object* v_str_475_; lean_object* v_str_476_; lean_object* v_str_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v_arg_473_ = lean_ctor_get(v_fn_354_, 1);
lean_inc_ref(v_arg_473_);
lean_dec_ref(v_fn_354_);
v_arg_474_ = lean_ctor_get(v_fn_426_, 1);
lean_inc_ref(v_arg_474_);
lean_dec_ref(v_fn_426_);
v_str_475_ = lean_ctor_get(v_declName_469_, 1);
lean_inc_ref(v_str_475_);
lean_dec_ref(v_declName_469_);
v_str_476_ = lean_ctor_get(v_pre_470_, 1);
lean_inc_ref(v_str_476_);
lean_dec_ref(v_pre_470_);
v_str_477_ = lean_ctor_get(v_pre_471_, 1);
lean_inc_ref(v_str_477_);
lean_dec_ref(v_pre_471_);
v___x_478_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_479_ = lean_string_dec_eq(v_str_477_, v___x_478_);
lean_dec_ref(v_str_477_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
lean_dec_ref(v_str_476_);
lean_dec_ref(v_str_475_);
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_480_ = lean_box(0);
return v___x_480_;
}
else
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_482_ = lean_string_dec_eq(v_str_476_, v___x_481_);
lean_dec_ref(v_str_476_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
lean_dec_ref(v_str_475_);
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_483_ = lean_box(0);
return v___x_483_;
}
else
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__7));
v___x_485_ = lean_string_dec_eq(v_str_475_, v___x_484_);
lean_dec_ref(v_str_475_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_486_ = lean_box(0);
return v___x_486_;
}
else
{
if (lean_obj_tag(v_arg_474_) == 9)
{
lean_object* v_a_487_; 
v_a_487_ = lean_ctor_get(v_arg_474_, 0);
lean_inc_ref(v_a_487_);
lean_dec_ref(v_arg_474_);
if (lean_obj_tag(v_a_487_) == 1)
{
if (lean_obj_tag(v_arg_473_) == 9)
{
lean_object* v_a_488_; 
v_a_488_ = lean_ctor_get(v_arg_473_, 0);
lean_inc_ref(v_a_488_);
lean_dec_ref(v_arg_473_);
if (lean_obj_tag(v_a_488_) == 1)
{
if (lean_obj_tag(v_arg_355_) == 9)
{
lean_object* v_a_489_; 
v_a_489_ = lean_ctor_get(v_arg_355_, 0);
lean_inc_ref(v_a_489_);
lean_dec_ref(v_arg_355_);
if (lean_obj_tag(v_a_489_) == 1)
{
if (lean_obj_tag(v_arg_353_) == 9)
{
lean_object* v_a_490_; 
v_a_490_ = lean_ctor_get(v_arg_353_, 0);
lean_inc_ref(v_a_490_);
lean_dec_ref(v_arg_353_);
if (lean_obj_tag(v_a_490_) == 1)
{
lean_object* v_val_491_; lean_object* v_val_492_; lean_object* v_val_493_; lean_object* v_val_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_502_; 
v_val_491_ = lean_ctor_get(v_a_487_, 0);
lean_inc_ref(v_val_491_);
lean_dec_ref(v_a_487_);
v_val_492_ = lean_ctor_get(v_a_488_, 0);
lean_inc_ref(v_val_492_);
lean_dec_ref(v_a_488_);
v_val_493_ = lean_ctor_get(v_a_489_, 0);
lean_inc_ref(v_val_493_);
lean_dec_ref(v_a_489_);
v_val_494_ = lean_ctor_get(v_a_490_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v_a_490_);
if (v_isSharedCheck_502_ == 0)
{
v___x_496_ = v_a_490_;
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_val_494_);
lean_dec(v_a_490_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_498_ = l_Lean_Name_mkStr4(v_val_491_, v_val_492_, v_val_493_, v_val_494_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_498_);
v___x_500_ = v___x_496_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
else
{
lean_object* v___x_503_; 
lean_dec_ref(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec_ref(v_a_487_);
v___x_503_ = lean_box(0);
return v___x_503_;
}
}
else
{
lean_object* v___x_504_; 
lean_dec_ref(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec_ref(v_arg_353_);
v___x_504_ = lean_box(0);
return v___x_504_;
}
}
else
{
lean_object* v___x_505_; 
lean_dec_ref(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec_ref(v_arg_353_);
v___x_505_ = lean_box(0);
return v___x_505_;
}
}
else
{
lean_object* v___x_506_; 
lean_dec_ref(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_506_ = lean_box(0);
return v___x_506_;
}
}
else
{
lean_object* v___x_507_; 
lean_dec_ref(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_507_ = lean_box(0);
return v___x_507_;
}
}
else
{
lean_object* v___x_508_; 
lean_dec_ref(v_a_487_);
lean_dec_ref(v_arg_473_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_508_ = lean_box(0);
return v___x_508_;
}
}
else
{
lean_object* v___x_509_; 
lean_dec_ref(v_a_487_);
lean_dec_ref(v_arg_473_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_509_ = lean_box(0);
return v___x_509_;
}
}
else
{
lean_object* v___x_510_; 
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_510_ = lean_box(0);
return v___x_510_;
}
}
}
}
}
else
{
lean_object* v___x_511_; 
lean_dec_ref(v_pre_471_);
lean_dec_ref(v_pre_470_);
lean_dec_ref(v_declName_469_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_511_ = lean_box(0);
return v___x_511_;
}
}
else
{
lean_object* v___x_512_; 
lean_dec(v_pre_471_);
lean_dec_ref(v_pre_470_);
lean_dec_ref(v_declName_469_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_512_ = lean_box(0);
return v___x_512_;
}
}
else
{
lean_object* v___x_513_; 
lean_dec(v_pre_470_);
lean_dec_ref(v_declName_469_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_513_ = lean_box(0);
return v___x_513_;
}
}
else
{
lean_object* v___x_514_; 
lean_dec(v_declName_469_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_514_ = lean_box(0);
return v___x_514_;
}
}
case 5:
{
lean_object* v_fn_515_; 
lean_inc_ref(v_fn_468_);
v_fn_515_ = lean_ctor_get(v_fn_468_, 0);
switch(lean_obj_tag(v_fn_515_))
{
case 4:
{
lean_object* v_declName_516_; 
v_declName_516_ = lean_ctor_get(v_fn_515_, 0);
lean_inc(v_declName_516_);
if (lean_obj_tag(v_declName_516_) == 1)
{
lean_object* v_pre_517_; 
v_pre_517_ = lean_ctor_get(v_declName_516_, 0);
lean_inc(v_pre_517_);
if (lean_obj_tag(v_pre_517_) == 1)
{
lean_object* v_pre_518_; 
v_pre_518_ = lean_ctor_get(v_pre_517_, 0);
lean_inc(v_pre_518_);
if (lean_obj_tag(v_pre_518_) == 1)
{
lean_object* v_pre_519_; 
v_pre_519_ = lean_ctor_get(v_pre_518_, 0);
if (lean_obj_tag(v_pre_519_) == 0)
{
lean_object* v_arg_520_; lean_object* v_arg_521_; lean_object* v_arg_522_; lean_object* v_str_523_; lean_object* v_str_524_; lean_object* v_str_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v_arg_520_ = lean_ctor_get(v_fn_354_, 1);
lean_inc_ref(v_arg_520_);
lean_dec_ref(v_fn_354_);
v_arg_521_ = lean_ctor_get(v_fn_426_, 1);
lean_inc_ref(v_arg_521_);
lean_dec_ref(v_fn_426_);
v_arg_522_ = lean_ctor_get(v_fn_468_, 1);
lean_inc_ref(v_arg_522_);
lean_dec_ref(v_fn_468_);
v_str_523_ = lean_ctor_get(v_declName_516_, 1);
lean_inc_ref(v_str_523_);
lean_dec_ref(v_declName_516_);
v_str_524_ = lean_ctor_get(v_pre_517_, 1);
lean_inc_ref(v_str_524_);
lean_dec_ref(v_pre_517_);
v_str_525_ = lean_ctor_get(v_pre_518_, 1);
lean_inc_ref(v_str_525_);
lean_dec_ref(v_pre_518_);
v___x_526_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_527_ = lean_string_dec_eq(v_str_525_, v___x_526_);
lean_dec_ref(v_str_525_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
lean_dec_ref(v_str_524_);
lean_dec_ref(v_str_523_);
lean_dec_ref(v_arg_522_);
lean_dec_ref(v_arg_521_);
lean_dec_ref(v_arg_520_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_528_ = lean_box(0);
return v___x_528_;
}
else
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_530_ = lean_string_dec_eq(v_str_524_, v___x_529_);
lean_dec_ref(v_str_524_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; 
lean_dec_ref(v_str_523_);
lean_dec_ref(v_arg_522_);
lean_dec_ref(v_arg_521_);
lean_dec_ref(v_arg_520_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_531_ = lean_box(0);
return v___x_531_;
}
else
{
lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__8));
v___x_533_ = lean_string_dec_eq(v_str_523_, v___x_532_);
lean_dec_ref(v_str_523_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; 
lean_dec_ref(v_arg_522_);
lean_dec_ref(v_arg_521_);
lean_dec_ref(v_arg_520_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_534_ = lean_box(0);
return v___x_534_;
}
else
{
if (lean_obj_tag(v_arg_522_) == 9)
{
lean_object* v_a_535_; 
v_a_535_ = lean_ctor_get(v_arg_522_, 0);
lean_inc_ref(v_a_535_);
lean_dec_ref(v_arg_522_);
if (lean_obj_tag(v_a_535_) == 1)
{
if (lean_obj_tag(v_arg_521_) == 9)
{
lean_object* v_a_536_; 
v_a_536_ = lean_ctor_get(v_arg_521_, 0);
lean_inc_ref(v_a_536_);
lean_dec_ref(v_arg_521_);
if (lean_obj_tag(v_a_536_) == 1)
{
if (lean_obj_tag(v_arg_520_) == 9)
{
lean_object* v_a_537_; 
v_a_537_ = lean_ctor_get(v_arg_520_, 0);
lean_inc_ref(v_a_537_);
lean_dec_ref(v_arg_520_);
if (lean_obj_tag(v_a_537_) == 1)
{
if (lean_obj_tag(v_arg_355_) == 9)
{
lean_object* v_a_538_; 
v_a_538_ = lean_ctor_get(v_arg_355_, 0);
lean_inc_ref(v_a_538_);
lean_dec_ref(v_arg_355_);
if (lean_obj_tag(v_a_538_) == 1)
{
if (lean_obj_tag(v_arg_353_) == 9)
{
lean_object* v_a_539_; 
v_a_539_ = lean_ctor_get(v_arg_353_, 0);
lean_inc_ref(v_a_539_);
lean_dec_ref(v_arg_353_);
if (lean_obj_tag(v_a_539_) == 1)
{
lean_object* v_val_540_; lean_object* v_val_541_; lean_object* v_val_542_; lean_object* v_val_543_; lean_object* v_val_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_552_; 
v_val_540_ = lean_ctor_get(v_a_535_, 0);
lean_inc_ref(v_val_540_);
lean_dec_ref(v_a_535_);
v_val_541_ = lean_ctor_get(v_a_536_, 0);
lean_inc_ref(v_val_541_);
lean_dec_ref(v_a_536_);
v_val_542_ = lean_ctor_get(v_a_537_, 0);
lean_inc_ref(v_val_542_);
lean_dec_ref(v_a_537_);
v_val_543_ = lean_ctor_get(v_a_538_, 0);
lean_inc_ref(v_val_543_);
lean_dec_ref(v_a_538_);
v_val_544_ = lean_ctor_get(v_a_539_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v_a_539_);
if (v_isSharedCheck_552_ == 0)
{
v___x_546_ = v_a_539_;
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_val_544_);
lean_dec(v_a_539_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = l_Lean_Name_mkStr5(v_val_540_, v_val_541_, v_val_542_, v_val_543_, v_val_544_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_548_);
v___x_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
else
{
lean_object* v___x_553_; 
lean_dec_ref(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec_ref(v_a_535_);
v___x_553_ = lean_box(0);
return v___x_553_;
}
}
else
{
lean_object* v___x_554_; 
lean_dec_ref(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec_ref(v_arg_353_);
v___x_554_ = lean_box(0);
return v___x_554_;
}
}
else
{
lean_object* v___x_555_; 
lean_dec_ref(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec_ref(v_arg_353_);
v___x_555_ = lean_box(0);
return v___x_555_;
}
}
else
{
lean_object* v___x_556_; 
lean_dec_ref(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_556_ = lean_box(0);
return v___x_556_;
}
}
else
{
lean_object* v___x_557_; 
lean_dec_ref(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_557_ = lean_box(0);
return v___x_557_;
}
}
else
{
lean_object* v___x_558_; 
lean_dec_ref(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec_ref(v_arg_520_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_558_ = lean_box(0);
return v___x_558_;
}
}
else
{
lean_object* v___x_559_; 
lean_dec_ref(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec_ref(v_arg_520_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_559_ = lean_box(0);
return v___x_559_;
}
}
else
{
lean_object* v___x_560_; 
lean_dec_ref(v_a_535_);
lean_dec_ref(v_arg_521_);
lean_dec_ref(v_arg_520_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_560_ = lean_box(0);
return v___x_560_;
}
}
else
{
lean_object* v___x_561_; 
lean_dec_ref(v_a_535_);
lean_dec_ref(v_arg_521_);
lean_dec_ref(v_arg_520_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_561_ = lean_box(0);
return v___x_561_;
}
}
else
{
lean_object* v___x_562_; 
lean_dec_ref(v_arg_522_);
lean_dec_ref(v_arg_521_);
lean_dec_ref(v_arg_520_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_562_ = lean_box(0);
return v___x_562_;
}
}
}
}
}
else
{
lean_object* v___x_563_; 
lean_dec_ref(v_pre_518_);
lean_dec_ref(v_pre_517_);
lean_dec_ref(v_declName_516_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_563_ = lean_box(0);
return v___x_563_;
}
}
else
{
lean_object* v___x_564_; 
lean_dec(v_pre_518_);
lean_dec_ref(v_pre_517_);
lean_dec_ref(v_declName_516_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_564_ = lean_box(0);
return v___x_564_;
}
}
else
{
lean_object* v___x_565_; 
lean_dec(v_pre_517_);
lean_dec_ref(v_declName_516_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_565_ = lean_box(0);
return v___x_565_;
}
}
else
{
lean_object* v___x_566_; 
lean_dec(v_declName_516_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_566_ = lean_box(0);
return v___x_566_;
}
}
case 5:
{
lean_object* v_fn_567_; 
lean_inc_ref(v_fn_515_);
v_fn_567_ = lean_ctor_get(v_fn_515_, 0);
switch(lean_obj_tag(v_fn_567_))
{
case 4:
{
lean_object* v_declName_568_; 
v_declName_568_ = lean_ctor_get(v_fn_567_, 0);
lean_inc(v_declName_568_);
if (lean_obj_tag(v_declName_568_) == 1)
{
lean_object* v_pre_569_; 
v_pre_569_ = lean_ctor_get(v_declName_568_, 0);
lean_inc(v_pre_569_);
if (lean_obj_tag(v_pre_569_) == 1)
{
lean_object* v_pre_570_; 
v_pre_570_ = lean_ctor_get(v_pre_569_, 0);
lean_inc(v_pre_570_);
if (lean_obj_tag(v_pre_570_) == 1)
{
lean_object* v_pre_571_; 
v_pre_571_ = lean_ctor_get(v_pre_570_, 0);
if (lean_obj_tag(v_pre_571_) == 0)
{
lean_object* v_arg_572_; lean_object* v_arg_573_; lean_object* v_arg_574_; lean_object* v_arg_575_; lean_object* v_str_576_; lean_object* v_str_577_; lean_object* v_str_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_arg_572_ = lean_ctor_get(v_fn_354_, 1);
lean_inc_ref(v_arg_572_);
lean_dec_ref(v_fn_354_);
v_arg_573_ = lean_ctor_get(v_fn_426_, 1);
lean_inc_ref(v_arg_573_);
lean_dec_ref(v_fn_426_);
v_arg_574_ = lean_ctor_get(v_fn_468_, 1);
lean_inc_ref(v_arg_574_);
lean_dec_ref(v_fn_468_);
v_arg_575_ = lean_ctor_get(v_fn_515_, 1);
lean_inc_ref(v_arg_575_);
lean_dec_ref(v_fn_515_);
v_str_576_ = lean_ctor_get(v_declName_568_, 1);
lean_inc_ref(v_str_576_);
lean_dec_ref(v_declName_568_);
v_str_577_ = lean_ctor_get(v_pre_569_, 1);
lean_inc_ref(v_str_577_);
lean_dec_ref(v_pre_569_);
v_str_578_ = lean_ctor_get(v_pre_570_, 1);
lean_inc_ref(v_str_578_);
lean_dec_ref(v_pre_570_);
v___x_579_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_580_ = lean_string_dec_eq(v_str_578_, v___x_579_);
lean_dec_ref(v_str_578_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
lean_dec_ref(v_str_577_);
lean_dec_ref(v_str_576_);
lean_dec_ref(v_arg_575_);
lean_dec_ref(v_arg_574_);
lean_dec_ref(v_arg_573_);
lean_dec_ref(v_arg_572_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_581_ = lean_box(0);
return v___x_581_;
}
else
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_583_ = lean_string_dec_eq(v_str_577_, v___x_582_);
lean_dec_ref(v_str_577_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
lean_dec_ref(v_str_576_);
lean_dec_ref(v_arg_575_);
lean_dec_ref(v_arg_574_);
lean_dec_ref(v_arg_573_);
lean_dec_ref(v_arg_572_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_584_ = lean_box(0);
return v___x_584_;
}
else
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__9));
v___x_586_ = lean_string_dec_eq(v_str_576_, v___x_585_);
lean_dec_ref(v_str_576_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
lean_dec_ref(v_arg_575_);
lean_dec_ref(v_arg_574_);
lean_dec_ref(v_arg_573_);
lean_dec_ref(v_arg_572_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_587_ = lean_box(0);
return v___x_587_;
}
else
{
if (lean_obj_tag(v_arg_575_) == 9)
{
lean_object* v_a_588_; 
v_a_588_ = lean_ctor_get(v_arg_575_, 0);
lean_inc_ref(v_a_588_);
lean_dec_ref(v_arg_575_);
if (lean_obj_tag(v_a_588_) == 1)
{
if (lean_obj_tag(v_arg_574_) == 9)
{
lean_object* v_a_589_; 
v_a_589_ = lean_ctor_get(v_arg_574_, 0);
lean_inc_ref(v_a_589_);
lean_dec_ref(v_arg_574_);
if (lean_obj_tag(v_a_589_) == 1)
{
if (lean_obj_tag(v_arg_573_) == 9)
{
lean_object* v_a_590_; 
v_a_590_ = lean_ctor_get(v_arg_573_, 0);
lean_inc_ref(v_a_590_);
lean_dec_ref(v_arg_573_);
if (lean_obj_tag(v_a_590_) == 1)
{
if (lean_obj_tag(v_arg_572_) == 9)
{
lean_object* v_a_591_; 
v_a_591_ = lean_ctor_get(v_arg_572_, 0);
lean_inc_ref(v_a_591_);
lean_dec_ref(v_arg_572_);
if (lean_obj_tag(v_a_591_) == 1)
{
if (lean_obj_tag(v_arg_355_) == 9)
{
lean_object* v_a_592_; 
v_a_592_ = lean_ctor_get(v_arg_355_, 0);
lean_inc_ref(v_a_592_);
lean_dec_ref(v_arg_355_);
if (lean_obj_tag(v_a_592_) == 1)
{
if (lean_obj_tag(v_arg_353_) == 9)
{
lean_object* v_a_593_; 
v_a_593_ = lean_ctor_get(v_arg_353_, 0);
lean_inc_ref(v_a_593_);
lean_dec_ref(v_arg_353_);
if (lean_obj_tag(v_a_593_) == 1)
{
lean_object* v_val_594_; lean_object* v_val_595_; lean_object* v_val_596_; lean_object* v_val_597_; lean_object* v_val_598_; lean_object* v_val_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_607_; 
v_val_594_ = lean_ctor_get(v_a_588_, 0);
lean_inc_ref(v_val_594_);
lean_dec_ref(v_a_588_);
v_val_595_ = lean_ctor_get(v_a_589_, 0);
lean_inc_ref(v_val_595_);
lean_dec_ref(v_a_589_);
v_val_596_ = lean_ctor_get(v_a_590_, 0);
lean_inc_ref(v_val_596_);
lean_dec_ref(v_a_590_);
v_val_597_ = lean_ctor_get(v_a_591_, 0);
lean_inc_ref(v_val_597_);
lean_dec_ref(v_a_591_);
v_val_598_ = lean_ctor_get(v_a_592_, 0);
lean_inc_ref(v_val_598_);
lean_dec_ref(v_a_592_);
v_val_599_ = lean_ctor_get(v_a_593_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v_a_593_);
if (v_isSharedCheck_607_ == 0)
{
v___x_601_ = v_a_593_;
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_val_599_);
lean_dec(v_a_593_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = l_Lean_Name_mkStr6(v_val_594_, v_val_595_, v_val_596_, v_val_597_, v_val_598_, v_val_599_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_603_);
v___x_605_ = v___x_601_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
else
{
lean_object* v___x_608_; 
lean_dec_ref(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec_ref(v_a_588_);
v___x_608_ = lean_box(0);
return v___x_608_;
}
}
else
{
lean_object* v___x_609_; 
lean_dec_ref(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec_ref(v_arg_353_);
v___x_609_ = lean_box(0);
return v___x_609_;
}
}
else
{
lean_object* v___x_610_; 
lean_dec_ref(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec_ref(v_arg_353_);
v___x_610_ = lean_box(0);
return v___x_610_;
}
}
else
{
lean_object* v___x_611_; 
lean_dec_ref(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_611_ = lean_box(0);
return v___x_611_;
}
}
else
{
lean_object* v___x_612_; 
lean_dec_ref(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_612_ = lean_box(0);
return v___x_612_;
}
}
else
{
lean_object* v___x_613_; 
lean_dec_ref(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec_ref(v_arg_572_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_613_ = lean_box(0);
return v___x_613_;
}
}
else
{
lean_object* v___x_614_; 
lean_dec_ref(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec_ref(v_arg_572_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_614_ = lean_box(0);
return v___x_614_;
}
}
else
{
lean_object* v___x_615_; 
lean_dec_ref(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec_ref(v_arg_573_);
lean_dec_ref(v_arg_572_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_615_ = lean_box(0);
return v___x_615_;
}
}
else
{
lean_object* v___x_616_; 
lean_dec_ref(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec_ref(v_arg_573_);
lean_dec_ref(v_arg_572_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_616_ = lean_box(0);
return v___x_616_;
}
}
else
{
lean_object* v___x_617_; 
lean_dec_ref(v_a_588_);
lean_dec_ref(v_arg_574_);
lean_dec_ref(v_arg_573_);
lean_dec_ref(v_arg_572_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_617_ = lean_box(0);
return v___x_617_;
}
}
else
{
lean_object* v___x_618_; 
lean_dec_ref(v_a_588_);
lean_dec_ref(v_arg_574_);
lean_dec_ref(v_arg_573_);
lean_dec_ref(v_arg_572_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_618_ = lean_box(0);
return v___x_618_;
}
}
else
{
lean_object* v___x_619_; 
lean_dec_ref(v_arg_575_);
lean_dec_ref(v_arg_574_);
lean_dec_ref(v_arg_573_);
lean_dec_ref(v_arg_572_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_619_ = lean_box(0);
return v___x_619_;
}
}
}
}
}
else
{
lean_object* v___x_620_; 
lean_dec_ref(v_pre_570_);
lean_dec_ref(v_pre_569_);
lean_dec_ref(v_declName_568_);
lean_dec_ref(v_fn_515_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_620_ = lean_box(0);
return v___x_620_;
}
}
else
{
lean_object* v___x_621_; 
lean_dec(v_pre_570_);
lean_dec_ref(v_pre_569_);
lean_dec_ref(v_declName_568_);
lean_dec_ref(v_fn_515_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_621_ = lean_box(0);
return v___x_621_;
}
}
else
{
lean_object* v___x_622_; 
lean_dec(v_pre_569_);
lean_dec_ref(v_declName_568_);
lean_dec_ref(v_fn_515_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_622_ = lean_box(0);
return v___x_622_;
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v_declName_568_);
lean_dec_ref(v_fn_515_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_623_ = lean_box(0);
return v___x_623_;
}
}
case 5:
{
lean_object* v_fn_624_; 
lean_inc_ref(v_fn_567_);
v_fn_624_ = lean_ctor_get(v_fn_567_, 0);
switch(lean_obj_tag(v_fn_624_))
{
case 4:
{
lean_object* v_declName_625_; 
v_declName_625_ = lean_ctor_get(v_fn_624_, 0);
lean_inc(v_declName_625_);
if (lean_obj_tag(v_declName_625_) == 1)
{
lean_object* v_pre_626_; 
v_pre_626_ = lean_ctor_get(v_declName_625_, 0);
lean_inc(v_pre_626_);
if (lean_obj_tag(v_pre_626_) == 1)
{
lean_object* v_pre_627_; 
v_pre_627_ = lean_ctor_get(v_pre_626_, 0);
lean_inc(v_pre_627_);
if (lean_obj_tag(v_pre_627_) == 1)
{
lean_object* v_pre_628_; 
v_pre_628_ = lean_ctor_get(v_pre_627_, 0);
if (lean_obj_tag(v_pre_628_) == 0)
{
lean_object* v_arg_629_; lean_object* v_arg_630_; lean_object* v_arg_631_; lean_object* v_arg_632_; lean_object* v_arg_633_; lean_object* v_str_634_; lean_object* v_str_635_; lean_object* v_str_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_arg_629_ = lean_ctor_get(v_fn_354_, 1);
lean_inc_ref(v_arg_629_);
lean_dec_ref(v_fn_354_);
v_arg_630_ = lean_ctor_get(v_fn_426_, 1);
lean_inc_ref(v_arg_630_);
lean_dec_ref(v_fn_426_);
v_arg_631_ = lean_ctor_get(v_fn_468_, 1);
lean_inc_ref(v_arg_631_);
lean_dec_ref(v_fn_468_);
v_arg_632_ = lean_ctor_get(v_fn_515_, 1);
lean_inc_ref(v_arg_632_);
lean_dec_ref(v_fn_515_);
v_arg_633_ = lean_ctor_get(v_fn_567_, 1);
lean_inc_ref(v_arg_633_);
lean_dec_ref(v_fn_567_);
v_str_634_ = lean_ctor_get(v_declName_625_, 1);
lean_inc_ref(v_str_634_);
lean_dec_ref(v_declName_625_);
v_str_635_ = lean_ctor_get(v_pre_626_, 1);
lean_inc_ref(v_str_635_);
lean_dec_ref(v_pre_626_);
v_str_636_ = lean_ctor_get(v_pre_627_, 1);
lean_inc_ref(v_str_636_);
lean_dec_ref(v_pre_627_);
v___x_637_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_638_ = lean_string_dec_eq(v_str_636_, v___x_637_);
lean_dec_ref(v_str_636_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
lean_dec_ref(v_str_635_);
lean_dec_ref(v_str_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_632_);
lean_dec_ref(v_arg_631_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_639_ = lean_box(0);
return v___x_639_;
}
else
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_641_ = lean_string_dec_eq(v_str_635_, v___x_640_);
lean_dec_ref(v_str_635_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
lean_dec_ref(v_str_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_632_);
lean_dec_ref(v_arg_631_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_642_ = lean_box(0);
return v___x_642_;
}
else
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__10));
v___x_644_ = lean_string_dec_eq(v_str_634_, v___x_643_);
lean_dec_ref(v_str_634_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_632_);
lean_dec_ref(v_arg_631_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_645_ = lean_box(0);
return v___x_645_;
}
else
{
if (lean_obj_tag(v_arg_633_) == 9)
{
lean_object* v_a_646_; 
v_a_646_ = lean_ctor_get(v_arg_633_, 0);
lean_inc_ref(v_a_646_);
lean_dec_ref(v_arg_633_);
if (lean_obj_tag(v_a_646_) == 1)
{
if (lean_obj_tag(v_arg_632_) == 9)
{
lean_object* v_a_647_; 
v_a_647_ = lean_ctor_get(v_arg_632_, 0);
lean_inc_ref(v_a_647_);
lean_dec_ref(v_arg_632_);
if (lean_obj_tag(v_a_647_) == 1)
{
if (lean_obj_tag(v_arg_631_) == 9)
{
lean_object* v_a_648_; 
v_a_648_ = lean_ctor_get(v_arg_631_, 0);
lean_inc_ref(v_a_648_);
lean_dec_ref(v_arg_631_);
if (lean_obj_tag(v_a_648_) == 1)
{
if (lean_obj_tag(v_arg_630_) == 9)
{
lean_object* v_a_649_; 
v_a_649_ = lean_ctor_get(v_arg_630_, 0);
lean_inc_ref(v_a_649_);
lean_dec_ref(v_arg_630_);
if (lean_obj_tag(v_a_649_) == 1)
{
if (lean_obj_tag(v_arg_629_) == 9)
{
lean_object* v_a_650_; 
v_a_650_ = lean_ctor_get(v_arg_629_, 0);
lean_inc_ref(v_a_650_);
lean_dec_ref(v_arg_629_);
if (lean_obj_tag(v_a_650_) == 1)
{
if (lean_obj_tag(v_arg_355_) == 9)
{
lean_object* v_a_651_; 
v_a_651_ = lean_ctor_get(v_arg_355_, 0);
lean_inc_ref(v_a_651_);
lean_dec_ref(v_arg_355_);
if (lean_obj_tag(v_a_651_) == 1)
{
if (lean_obj_tag(v_arg_353_) == 9)
{
lean_object* v_a_652_; 
v_a_652_ = lean_ctor_get(v_arg_353_, 0);
lean_inc_ref(v_a_652_);
lean_dec_ref(v_arg_353_);
if (lean_obj_tag(v_a_652_) == 1)
{
lean_object* v_val_653_; lean_object* v_val_654_; lean_object* v_val_655_; lean_object* v_val_656_; lean_object* v_val_657_; lean_object* v_val_658_; lean_object* v_val_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_667_; 
v_val_653_ = lean_ctor_get(v_a_646_, 0);
lean_inc_ref(v_val_653_);
lean_dec_ref(v_a_646_);
v_val_654_ = lean_ctor_get(v_a_647_, 0);
lean_inc_ref(v_val_654_);
lean_dec_ref(v_a_647_);
v_val_655_ = lean_ctor_get(v_a_648_, 0);
lean_inc_ref(v_val_655_);
lean_dec_ref(v_a_648_);
v_val_656_ = lean_ctor_get(v_a_649_, 0);
lean_inc_ref(v_val_656_);
lean_dec_ref(v_a_649_);
v_val_657_ = lean_ctor_get(v_a_650_, 0);
lean_inc_ref(v_val_657_);
lean_dec_ref(v_a_650_);
v_val_658_ = lean_ctor_get(v_a_651_, 0);
lean_inc_ref(v_val_658_);
lean_dec_ref(v_a_651_);
v_val_659_ = lean_ctor_get(v_a_652_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v_a_652_);
if (v_isSharedCheck_667_ == 0)
{
v___x_661_ = v_a_652_;
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_val_659_);
lean_dec(v_a_652_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_663_ = l_Lean_Name_mkStr7(v_val_653_, v_val_654_, v_val_655_, v_val_656_, v_val_657_, v_val_658_, v_val_659_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_663_);
v___x_665_ = v___x_661_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
else
{
lean_object* v___x_668_; 
lean_dec_ref(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_646_);
v___x_668_ = lean_box(0);
return v___x_668_;
}
}
else
{
lean_object* v___x_669_; 
lean_dec_ref(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec_ref(v_arg_353_);
v___x_669_ = lean_box(0);
return v___x_669_;
}
}
else
{
lean_object* v___x_670_; 
lean_dec_ref(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec_ref(v_arg_353_);
v___x_670_ = lean_box(0);
return v___x_670_;
}
}
else
{
lean_object* v___x_671_; 
lean_dec_ref(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_671_ = lean_box(0);
return v___x_671_;
}
}
else
{
lean_object* v___x_672_; 
lean_dec_ref(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_672_ = lean_box(0);
return v___x_672_;
}
}
else
{
lean_object* v___x_673_; 
lean_dec_ref(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_673_ = lean_box(0);
return v___x_673_;
}
}
else
{
lean_object* v___x_674_; 
lean_dec_ref(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_674_ = lean_box(0);
return v___x_674_;
}
}
else
{
lean_object* v___x_675_; 
lean_dec_ref(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_675_ = lean_box(0);
return v___x_675_;
}
}
else
{
lean_object* v___x_676_; 
lean_dec_ref(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_676_ = lean_box(0);
return v___x_676_;
}
}
else
{
lean_object* v___x_677_; 
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec_ref(v_arg_631_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_677_ = lean_box(0);
return v___x_677_;
}
}
else
{
lean_object* v___x_678_; 
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec_ref(v_arg_631_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_678_ = lean_box(0);
return v___x_678_;
}
}
else
{
lean_object* v___x_679_; 
lean_dec_ref(v_a_646_);
lean_dec_ref(v_arg_632_);
lean_dec_ref(v_arg_631_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_679_ = lean_box(0);
return v___x_679_;
}
}
else
{
lean_object* v___x_680_; 
lean_dec_ref(v_a_646_);
lean_dec_ref(v_arg_632_);
lean_dec_ref(v_arg_631_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_680_ = lean_box(0);
return v___x_680_;
}
}
else
{
lean_object* v___x_681_; 
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_632_);
lean_dec_ref(v_arg_631_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_681_ = lean_box(0);
return v___x_681_;
}
}
}
}
}
else
{
lean_object* v___x_682_; 
lean_dec_ref(v_pre_627_);
lean_dec_ref(v_pre_626_);
lean_dec_ref(v_declName_625_);
lean_dec_ref(v_fn_567_);
lean_dec_ref(v_fn_515_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_682_ = lean_box(0);
return v___x_682_;
}
}
else
{
lean_object* v___x_683_; 
lean_dec(v_pre_627_);
lean_dec_ref(v_pre_626_);
lean_dec_ref(v_declName_625_);
lean_dec_ref(v_fn_567_);
lean_dec_ref(v_fn_515_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_683_ = lean_box(0);
return v___x_683_;
}
}
else
{
lean_object* v___x_684_; 
lean_dec_ref(v_declName_625_);
lean_dec(v_pre_626_);
lean_dec_ref(v_fn_567_);
lean_dec_ref(v_fn_515_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_684_ = lean_box(0);
return v___x_684_;
}
}
else
{
lean_object* v___x_685_; 
lean_dec(v_declName_625_);
lean_dec_ref(v_fn_567_);
lean_dec_ref(v_fn_515_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_685_ = lean_box(0);
return v___x_685_;
}
}
case 5:
{
lean_object* v_fn_686_; 
lean_inc_ref(v_fn_624_);
v_fn_686_ = lean_ctor_get(v_fn_624_, 0);
if (lean_obj_tag(v_fn_686_) == 4)
{
lean_object* v_declName_687_; 
v_declName_687_ = lean_ctor_get(v_fn_686_, 0);
lean_inc(v_declName_687_);
if (lean_obj_tag(v_declName_687_) == 1)
{
lean_object* v_pre_688_; 
v_pre_688_ = lean_ctor_get(v_declName_687_, 0);
lean_inc(v_pre_688_);
if (lean_obj_tag(v_pre_688_) == 1)
{
lean_object* v_pre_689_; 
v_pre_689_ = lean_ctor_get(v_pre_688_, 0);
lean_inc(v_pre_689_);
if (lean_obj_tag(v_pre_689_) == 1)
{
lean_object* v_pre_690_; 
v_pre_690_ = lean_ctor_get(v_pre_689_, 0);
if (lean_obj_tag(v_pre_690_) == 0)
{
lean_object* v_arg_691_; lean_object* v_arg_692_; lean_object* v_arg_693_; lean_object* v_arg_694_; lean_object* v_arg_695_; lean_object* v_arg_696_; lean_object* v_str_697_; lean_object* v_str_698_; lean_object* v_str_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v_arg_691_ = lean_ctor_get(v_fn_354_, 1);
lean_inc_ref(v_arg_691_);
lean_dec_ref(v_fn_354_);
v_arg_692_ = lean_ctor_get(v_fn_426_, 1);
lean_inc_ref(v_arg_692_);
lean_dec_ref(v_fn_426_);
v_arg_693_ = lean_ctor_get(v_fn_468_, 1);
lean_inc_ref(v_arg_693_);
lean_dec_ref(v_fn_468_);
v_arg_694_ = lean_ctor_get(v_fn_515_, 1);
lean_inc_ref(v_arg_694_);
lean_dec_ref(v_fn_515_);
v_arg_695_ = lean_ctor_get(v_fn_567_, 1);
lean_inc_ref(v_arg_695_);
lean_dec_ref(v_fn_567_);
v_arg_696_ = lean_ctor_get(v_fn_624_, 1);
lean_inc_ref(v_arg_696_);
lean_dec_ref(v_fn_624_);
v_str_697_ = lean_ctor_get(v_declName_687_, 1);
lean_inc_ref(v_str_697_);
lean_dec_ref(v_declName_687_);
v_str_698_ = lean_ctor_get(v_pre_688_, 1);
lean_inc_ref(v_str_698_);
lean_dec_ref(v_pre_688_);
v_str_699_ = lean_ctor_get(v_pre_689_, 1);
lean_inc_ref(v_str_699_);
lean_dec_ref(v_pre_689_);
v___x_700_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_701_ = lean_string_dec_eq(v_str_699_, v___x_700_);
lean_dec_ref(v_str_699_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
lean_dec_ref(v_str_698_);
lean_dec_ref(v_str_697_);
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_694_);
lean_dec_ref(v_arg_693_);
lean_dec_ref(v_arg_692_);
lean_dec_ref(v_arg_691_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_702_ = lean_box(0);
return v___x_702_;
}
else
{
lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_703_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_704_ = lean_string_dec_eq(v_str_698_, v___x_703_);
lean_dec_ref(v_str_698_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; 
lean_dec_ref(v_str_697_);
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_694_);
lean_dec_ref(v_arg_693_);
lean_dec_ref(v_arg_692_);
lean_dec_ref(v_arg_691_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_705_ = lean_box(0);
return v___x_705_;
}
else
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__11));
v___x_707_ = lean_string_dec_eq(v_str_697_, v___x_706_);
lean_dec_ref(v_str_697_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; 
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_694_);
lean_dec_ref(v_arg_693_);
lean_dec_ref(v_arg_692_);
lean_dec_ref(v_arg_691_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_708_ = lean_box(0);
return v___x_708_;
}
else
{
if (lean_obj_tag(v_arg_696_) == 9)
{
lean_object* v_a_709_; 
v_a_709_ = lean_ctor_get(v_arg_696_, 0);
lean_inc_ref(v_a_709_);
lean_dec_ref(v_arg_696_);
if (lean_obj_tag(v_a_709_) == 1)
{
if (lean_obj_tag(v_arg_695_) == 9)
{
lean_object* v_a_710_; 
v_a_710_ = lean_ctor_get(v_arg_695_, 0);
lean_inc_ref(v_a_710_);
lean_dec_ref(v_arg_695_);
if (lean_obj_tag(v_a_710_) == 1)
{
if (lean_obj_tag(v_arg_694_) == 9)
{
lean_object* v_a_711_; 
v_a_711_ = lean_ctor_get(v_arg_694_, 0);
lean_inc_ref(v_a_711_);
lean_dec_ref(v_arg_694_);
if (lean_obj_tag(v_a_711_) == 1)
{
if (lean_obj_tag(v_arg_693_) == 9)
{
lean_object* v_a_712_; 
v_a_712_ = lean_ctor_get(v_arg_693_, 0);
lean_inc_ref(v_a_712_);
lean_dec_ref(v_arg_693_);
if (lean_obj_tag(v_a_712_) == 1)
{
if (lean_obj_tag(v_arg_692_) == 9)
{
lean_object* v_a_713_; 
v_a_713_ = lean_ctor_get(v_arg_692_, 0);
lean_inc_ref(v_a_713_);
lean_dec_ref(v_arg_692_);
if (lean_obj_tag(v_a_713_) == 1)
{
if (lean_obj_tag(v_arg_691_) == 9)
{
lean_object* v_a_714_; 
v_a_714_ = lean_ctor_get(v_arg_691_, 0);
lean_inc_ref(v_a_714_);
lean_dec_ref(v_arg_691_);
if (lean_obj_tag(v_a_714_) == 1)
{
if (lean_obj_tag(v_arg_355_) == 9)
{
lean_object* v_a_715_; 
v_a_715_ = lean_ctor_get(v_arg_355_, 0);
lean_inc_ref(v_a_715_);
lean_dec_ref(v_arg_355_);
if (lean_obj_tag(v_a_715_) == 1)
{
if (lean_obj_tag(v_arg_353_) == 9)
{
lean_object* v_a_716_; 
v_a_716_ = lean_ctor_get(v_arg_353_, 0);
lean_inc_ref(v_a_716_);
lean_dec_ref(v_arg_353_);
if (lean_obj_tag(v_a_716_) == 1)
{
lean_object* v_val_717_; lean_object* v_val_718_; lean_object* v_val_719_; lean_object* v_val_720_; lean_object* v_val_721_; lean_object* v_val_722_; lean_object* v_val_723_; lean_object* v_val_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_732_; 
v_val_717_ = lean_ctor_get(v_a_709_, 0);
lean_inc_ref(v_val_717_);
lean_dec_ref(v_a_709_);
v_val_718_ = lean_ctor_get(v_a_710_, 0);
lean_inc_ref(v_val_718_);
lean_dec_ref(v_a_710_);
v_val_719_ = lean_ctor_get(v_a_711_, 0);
lean_inc_ref(v_val_719_);
lean_dec_ref(v_a_711_);
v_val_720_ = lean_ctor_get(v_a_712_, 0);
lean_inc_ref(v_val_720_);
lean_dec_ref(v_a_712_);
v_val_721_ = lean_ctor_get(v_a_713_, 0);
lean_inc_ref(v_val_721_);
lean_dec_ref(v_a_713_);
v_val_722_ = lean_ctor_get(v_a_714_, 0);
lean_inc_ref(v_val_722_);
lean_dec_ref(v_a_714_);
v_val_723_ = lean_ctor_get(v_a_715_, 0);
lean_inc_ref(v_val_723_);
lean_dec_ref(v_a_715_);
v_val_724_ = lean_ctor_get(v_a_716_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_a_716_);
if (v_isSharedCheck_732_ == 0)
{
v___x_726_ = v_a_716_;
v_isShared_727_ = v_isSharedCheck_732_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_val_724_);
lean_dec(v_a_716_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_732_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_728_ = l_Lean_Name_mkStr8(v_val_717_, v_val_718_, v_val_719_, v_val_720_, v_val_721_, v_val_722_, v_val_723_, v_val_724_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_728_);
v___x_730_ = v___x_726_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_object* v___x_733_; 
lean_dec_ref(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec_ref(v_a_709_);
v___x_733_ = lean_box(0);
return v___x_733_;
}
}
else
{
lean_object* v___x_734_; 
lean_dec_ref(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_arg_353_);
v___x_734_ = lean_box(0);
return v___x_734_;
}
}
else
{
lean_object* v___x_735_; 
lean_dec_ref(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_arg_353_);
v___x_735_ = lean_box(0);
return v___x_735_;
}
}
else
{
lean_object* v___x_736_; 
lean_dec_ref(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_736_ = lean_box(0);
return v___x_736_;
}
}
else
{
lean_object* v___x_737_; 
lean_dec_ref(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_737_ = lean_box(0);
return v___x_737_;
}
}
else
{
lean_object* v___x_738_; 
lean_dec_ref(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_arg_691_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_738_ = lean_box(0);
return v___x_738_;
}
}
else
{
lean_object* v___x_739_; 
lean_dec_ref(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_arg_691_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_739_ = lean_box(0);
return v___x_739_;
}
}
else
{
lean_object* v___x_740_; 
lean_dec_ref(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_arg_692_);
lean_dec_ref(v_arg_691_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_740_ = lean_box(0);
return v___x_740_;
}
}
else
{
lean_object* v___x_741_; 
lean_dec_ref(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_arg_692_);
lean_dec_ref(v_arg_691_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_741_ = lean_box(0);
return v___x_741_;
}
}
else
{
lean_object* v___x_742_; 
lean_dec_ref(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_arg_693_);
lean_dec_ref(v_arg_692_);
lean_dec_ref(v_arg_691_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_742_ = lean_box(0);
return v___x_742_;
}
}
else
{
lean_object* v___x_743_; 
lean_dec_ref(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_arg_693_);
lean_dec_ref(v_arg_692_);
lean_dec_ref(v_arg_691_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_743_ = lean_box(0);
return v___x_743_;
}
}
else
{
lean_object* v___x_744_; 
lean_dec_ref(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_arg_694_);
lean_dec_ref(v_arg_693_);
lean_dec_ref(v_arg_692_);
lean_dec_ref(v_arg_691_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_744_ = lean_box(0);
return v___x_744_;
}
}
else
{
lean_object* v___x_745_; 
lean_dec_ref(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_arg_694_);
lean_dec_ref(v_arg_693_);
lean_dec_ref(v_arg_692_);
lean_dec_ref(v_arg_691_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_745_ = lean_box(0);
return v___x_745_;
}
}
else
{
lean_object* v___x_746_; 
lean_dec_ref(v_a_709_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_694_);
lean_dec_ref(v_arg_693_);
lean_dec_ref(v_arg_692_);
lean_dec_ref(v_arg_691_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_746_ = lean_box(0);
return v___x_746_;
}
}
else
{
lean_object* v___x_747_; 
lean_dec_ref(v_a_709_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_694_);
lean_dec_ref(v_arg_693_);
lean_dec_ref(v_arg_692_);
lean_dec_ref(v_arg_691_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_747_ = lean_box(0);
return v___x_747_;
}
}
else
{
lean_object* v___x_748_; 
lean_dec_ref(v_arg_696_);
lean_dec_ref(v_arg_695_);
lean_dec_ref(v_arg_694_);
lean_dec_ref(v_arg_693_);
lean_dec_ref(v_arg_692_);
lean_dec_ref(v_arg_691_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_748_ = lean_box(0);
return v___x_748_;
}
}
}
}
}
else
{
lean_object* v___x_749_; 
lean_dec_ref(v_pre_689_);
lean_dec_ref(v_pre_688_);
lean_dec_ref(v_declName_687_);
lean_dec_ref(v_fn_624_);
lean_dec_ref(v_fn_567_);
lean_dec_ref(v_fn_515_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_749_ = lean_box(0);
return v___x_749_;
}
}
else
{
lean_object* v___x_750_; 
lean_dec(v_pre_689_);
lean_dec_ref(v_pre_688_);
lean_dec_ref(v_declName_687_);
lean_dec_ref(v_fn_624_);
lean_dec_ref(v_fn_567_);
lean_dec_ref(v_fn_515_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_750_ = lean_box(0);
return v___x_750_;
}
}
else
{
lean_object* v___x_751_; 
lean_dec(v_pre_688_);
lean_dec_ref(v_declName_687_);
lean_dec_ref(v_fn_624_);
lean_dec_ref(v_fn_567_);
lean_dec_ref(v_fn_515_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_751_ = lean_box(0);
return v___x_751_;
}
}
else
{
lean_object* v___x_752_; 
lean_dec(v_declName_687_);
lean_dec_ref(v_fn_624_);
lean_dec_ref(v_fn_567_);
lean_dec_ref(v_fn_515_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_752_ = lean_box(0);
return v___x_752_;
}
}
else
{
lean_object* v___x_753_; 
lean_dec_ref(v_fn_624_);
lean_dec_ref(v_fn_567_);
lean_dec_ref(v_fn_515_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_753_ = lean_box(0);
return v___x_753_;
}
}
default: 
{
lean_object* v___x_754_; 
lean_dec_ref(v_fn_567_);
lean_dec_ref(v_fn_515_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_754_ = lean_box(0);
return v___x_754_;
}
}
}
default: 
{
lean_object* v___x_755_; 
lean_dec_ref(v_fn_515_);
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_755_ = lean_box(0);
return v___x_755_;
}
}
}
default: 
{
lean_object* v___x_756_; 
lean_dec_ref(v_fn_468_);
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_756_ = lean_box(0);
return v___x_756_;
}
}
}
default: 
{
lean_object* v___x_757_; 
lean_dec_ref(v_fn_426_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_757_ = lean_box(0);
return v___x_757_;
}
}
}
default: 
{
lean_object* v___x_758_; 
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_arg_353_);
v___x_758_ = lean_box(0);
return v___x_758_;
}
}
}
default: 
{
lean_object* v___x_759_; 
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_fn_354_);
lean_dec_ref(v_arg_353_);
v___x_759_ = lean_box(0);
return v___x_759_;
}
}
v___jp_356_:
{
if (lean_obj_tag(v___y_357_) == 0)
{
lean_object* v___x_358_; 
lean_dec_ref(v_arg_355_);
v___x_358_ = lean_box(0);
return v___x_358_;
}
else
{
lean_object* v_val_359_; lean_object* v___x_360_; 
v_val_359_ = lean_ctor_get(v___y_357_, 0);
lean_inc(v_val_359_);
lean_dec_ref(v___y_357_);
v___x_360_ = l_Lean_Expr_name_x3f(v_arg_355_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_dec(v_val_359_);
return v___x_360_;
}
else
{
lean_object* v_val_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_369_; 
v_val_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_369_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_369_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_val_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_369_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_365_ = l_Lean_Name_num___override(v_val_361_, v_val_359_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_365_);
v___x_367_ = v___x_363_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
}
case 4:
{
lean_object* v_declName_760_; 
v_declName_760_ = lean_ctor_get(v_fn_352_, 0);
lean_inc(v_declName_760_);
if (lean_obj_tag(v_declName_760_) == 1)
{
lean_object* v_pre_761_; 
v_pre_761_ = lean_ctor_get(v_declName_760_, 0);
lean_inc(v_pre_761_);
if (lean_obj_tag(v_pre_761_) == 1)
{
lean_object* v_pre_762_; 
v_pre_762_ = lean_ctor_get(v_pre_761_, 0);
lean_inc(v_pre_762_);
if (lean_obj_tag(v_pre_762_) == 1)
{
lean_object* v_pre_763_; 
v_pre_763_ = lean_ctor_get(v_pre_762_, 0);
if (lean_obj_tag(v_pre_763_) == 0)
{
lean_object* v_arg_764_; lean_object* v_str_765_; lean_object* v_str_766_; lean_object* v_str_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v_arg_764_ = lean_ctor_get(v_x_330_, 1);
lean_inc_ref(v_arg_764_);
lean_dec_ref(v_x_330_);
v_str_765_ = lean_ctor_get(v_declName_760_, 1);
lean_inc_ref(v_str_765_);
lean_dec_ref(v_declName_760_);
v_str_766_ = lean_ctor_get(v_pre_761_, 1);
lean_inc_ref(v_str_766_);
lean_dec_ref(v_pre_761_);
v_str_767_ = lean_ctor_get(v_pre_762_, 1);
lean_inc_ref(v_str_767_);
lean_dec_ref(v_pre_762_);
v___x_768_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__0));
v___x_769_ = lean_string_dec_eq(v_str_767_, v___x_768_);
lean_dec_ref(v_str_767_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_dec_ref(v_str_766_);
lean_dec_ref(v_str_765_);
lean_dec_ref(v_arg_764_);
v___x_770_ = lean_box(0);
return v___x_770_;
}
else
{
lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_771_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__1));
v___x_772_ = lean_string_dec_eq(v_str_766_, v___x_771_);
lean_dec_ref(v_str_766_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; 
lean_dec_ref(v_str_765_);
lean_dec_ref(v_arg_764_);
v___x_773_ = lean_box(0);
return v___x_773_;
}
else
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = ((lean_object*)(l_Lean_Expr_name_x3f___closed__12));
v___x_775_ = lean_string_dec_eq(v_str_765_, v___x_774_);
lean_dec_ref(v_str_765_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
lean_dec_ref(v_arg_764_);
v___x_776_ = lean_box(0);
return v___x_776_;
}
else
{
if (lean_obj_tag(v_arg_764_) == 9)
{
lean_object* v_a_777_; 
v_a_777_ = lean_ctor_get(v_arg_764_, 0);
lean_inc_ref(v_a_777_);
lean_dec_ref(v_arg_764_);
if (lean_obj_tag(v_a_777_) == 1)
{
lean_object* v_val_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_786_; 
v_val_778_ = lean_ctor_get(v_a_777_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v_a_777_);
if (v_isSharedCheck_786_ == 0)
{
v___x_780_ = v_a_777_;
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_val_778_);
lean_dec(v_a_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = l_Lean_Name_mkStr1(v_val_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v___x_787_; 
lean_dec_ref(v_a_777_);
v___x_787_ = lean_box(0);
return v___x_787_;
}
}
else
{
lean_object* v___x_788_; 
lean_dec_ref(v_arg_764_);
v___x_788_ = lean_box(0);
return v___x_788_;
}
}
}
}
}
else
{
lean_object* v___x_789_; 
lean_dec_ref(v_pre_762_);
lean_dec_ref(v_pre_761_);
lean_dec_ref(v_declName_760_);
lean_dec_ref(v_x_330_);
v___x_789_ = lean_box(0);
return v___x_789_;
}
}
else
{
lean_object* v___x_790_; 
lean_dec_ref(v_pre_761_);
lean_dec(v_pre_762_);
lean_dec_ref(v_declName_760_);
lean_dec_ref(v_x_330_);
v___x_790_ = lean_box(0);
return v___x_790_;
}
}
else
{
lean_object* v___x_791_; 
lean_dec(v_pre_761_);
lean_dec_ref(v_declName_760_);
lean_dec_ref(v_x_330_);
v___x_791_ = lean_box(0);
return v___x_791_;
}
}
else
{
lean_object* v___x_792_; 
lean_dec(v_declName_760_);
lean_dec_ref(v_x_330_);
v___x_792_ = lean_box(0);
return v___x_792_;
}
}
default: 
{
lean_object* v___x_793_; 
lean_dec_ref(v_x_330_);
v___x_793_ = lean_box(0);
return v___x_793_;
}
}
}
default: 
{
lean_object* v___x_794_; 
lean_dec_ref(v_x_330_);
v___x_794_ = lean_box(0);
return v___x_794_;
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
