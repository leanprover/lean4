// Lean compiler output
// Module: Init.Data.Int.Basic
// Imports: public import Init.Data.Cast public import Init.Data.Nat.Basic
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
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Int_ofNat___boxed(lean_object*);
lean_object* lean_int_neg_succ_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Int_negSucc___boxed(lean_object*);
static const lean_closure_object l_instNatCastInt_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
LEAN_EXPORT const lean_object* l_instNatCastInt = (const lean_object*)&l_instNatCastInt_value;
LEAN_EXPORT lean_object* l_instOfNat(lean_object*);
static const lean_string_object l_Int_term_x2d_x5b___x2b1_x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__0 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__0_value;
static const lean_string_object l_Int_term_x2d_x5b___x2b1_x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term-[_+1]"};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__1 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Int_term_x2d_x5b___x2b1_x5d___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_term_x2d_x5b___x2b1_x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__2_value_aux_0),((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(13, 210, 79, 129, 91, 108, 255, 221)}};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__2 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__2_value;
static const lean_string_object l_Int_term_x2d_x5b___x2b1_x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__3 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__3_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Int_term_x2d_x5b___x2b1_x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__4 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__4_value;
static const lean_string_object l_Int_term_x2d_x5b___x2b1_x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-["};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__5 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__5_value;
static const lean_ctor_object l_Int_term_x2d_x5b___x2b1_x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__5_value)}};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__6 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__6_value;
static const lean_string_object l_Int_term_x2d_x5b___x2b1_x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__7 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__7_value;
static const lean_ctor_object l_Int_term_x2d_x5b___x2b1_x5d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__7_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__8 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__8_value;
static const lean_ctor_object l_Int_term_x2d_x5b___x2b1_x5d___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__9 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__9_value;
static const lean_ctor_object l_Int_term_x2d_x5b___x2b1_x5d___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__4_value),((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__6_value),((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__9_value)}};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__10 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__10_value;
static const lean_string_object l_Int_term_x2d_x5b___x2b1_x5d___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "+1]"};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__11 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__11_value;
static const lean_ctor_object l_Int_term_x2d_x5b___x2b1_x5d___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__11_value)}};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__12 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__12_value;
static const lean_ctor_object l_Int_term_x2d_x5b___x2b1_x5d___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__4_value),((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__10_value),((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__12_value)}};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__13 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__13_value;
static const lean_ctor_object l_Int_term_x2d_x5b___x2b1_x5d___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__13_value)}};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__14 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__14_value;
LEAN_EXPORT const lean_object* l_Int_term_x2d_x5b___x2b1_x5d = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__14_value;
static const lean_string_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__0 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__0_value;
static const lean_string_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__1 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__1_value;
static const lean_string_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__2 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__2_value;
static const lean_string_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__3 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_0),((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_1),((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_2),((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value;
static const lean_string_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "negSucc"};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6;
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(179, 90, 75, 184, 85, 230, 187, 139)}};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__7 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__7_value;
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__8_value_aux_0),((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(181, 236, 205, 0, 179, 53, 99, 201)}};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__8 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__8_value;
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__9 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__9_value;
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__8_value)}};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__10 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__10_value;
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__11 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__11_value;
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__9_value),((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__11_value)}};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__12 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__12_value;
static const lean_string_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__13 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__13_value;
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__14 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__14_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__0 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__0_value;
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__1 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__1_value;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_Int_instInhabited;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_negOfNat(lean_object*);
LEAN_EXPORT lean_object* l_Int_negOfNat___boxed(lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Int_neg___boxed(lean_object*);
static const lean_closure_object l_Int_instNegInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instNegInt___closed__0 = (const lean_object*)&l_Int_instNegInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instNegInt = (const lean_object*)&l_Int_instNegInt___closed__0_value;
LEAN_EXPORT lean_object* l_Int_subNatNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_subNatNat___boxed(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_add___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_instAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instAdd___closed__0 = (const lean_object*)&l_Int_instAdd___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instAdd = (const lean_object*)&l_Int_instAdd___closed__0_value;
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_mul___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_instMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instMul___closed__0 = (const lean_object*)&l_Int_instMul___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instMul = (const lean_object*)&l_Int_instMul___closed__0_value;
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_instSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instSub___closed__0 = (const lean_object*)&l_Int_instSub___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instSub = (const lean_object*)&l_Int_instSub___closed__0_value;
LEAN_EXPORT lean_object* l_Int_instLEInt;
LEAN_EXPORT lean_object* l_Int_instLTInt;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_instDecidableEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_nonneg(lean_object*);
LEAN_EXPORT lean_object* l_Int_decNonneg___boxed(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_decLe___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_decLt___boxed(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Int_natAbs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Int_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_ofNat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_ofNat_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_ofNat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_ofNat_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_negSucc_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_negSucc_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_negSucc_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_negSucc_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_sign___closed__0;
static lean_object* l_Int_sign___closed__1;
LEAN_EXPORT lean_object* l_Int_sign(lean_object*);
LEAN_EXPORT lean_object* l_Int_sign___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Int_toNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Int_toNat_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_instDvd;
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_pow___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_instNatPow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instNatPow___closed__0 = (const lean_object*)&l_Int_instNatPow___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instNatPow = (const lean_object*)&l_Int_instNatPow___closed__0_value;
LEAN_EXPORT lean_object* l_Int_instMin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_instMin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_instMin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instMin___closed__0 = (const lean_object*)&l_Int_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instMin = (const lean_object*)&l_Int_instMin___closed__0_value;
LEAN_EXPORT lean_object* l_Int_instMax___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_instMax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instMax___closed__0 = (const lean_object*)&l_Int_instMax___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instMax = (const lean_object*)&l_Int_instMax___closed__0_value;
LEAN_EXPORT lean_object* l_instIntCastInt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instIntCastInt___lam__0___boxed(lean_object*);
static const lean_closure_object l_instIntCastInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instIntCastInt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instIntCastInt___closed__0 = (const lean_object*)&l_instIntCastInt___closed__0_value;
LEAN_EXPORT const lean_object* l_instIntCastInt = (const lean_object*)&l_instIntCastInt___closed__0_value;
LEAN_EXPORT lean_object* l_Int_cast___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instCoeTailIntOfIntCast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instCoeTailIntOfIntCast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instCoeHTCTIntOfIntCast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instCoeHTCTIntOfIntCast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_ofNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_negSucc___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_int_neg_succ_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instOfNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Int_term_x2d_x5b___x2b1_x5d___closed__2));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_10, x_13);
lean_dec(x_10);
x_15 = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4));
x_16 = l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6;
x_17 = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__7));
x_18 = l_Lean_addMacroScope(x_8, x_17, x_9);
x_19 = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__12));
lean_inc(x_14);
x_20 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
x_21 = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__14));
lean_inc(x_14);
x_22 = l_Lean_Syntax_node1(x_14, x_21, x_12);
x_23 = l_Lean_Syntax_node2(x_14, x_15, x_20, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__1));
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
lean_inc(x_15);
x_16 = l_Lean_Syntax_matchesNull(x_15, x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_9);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = l_Lean_Syntax_getArg(x_15, x_8);
lean_dec(x_15);
x_20 = l_Lean_replaceRef(x_9, x_2);
lean_dec(x_9);
x_21 = 0;
x_22 = l_Lean_SourceInfo_fromRef(x_20, x_21);
lean_dec(x_20);
x_23 = ((lean_object*)(l_Int_term_x2d_x5b___x2b1_x5d___closed__2));
x_24 = ((lean_object*)(l_Int_term_x2d_x5b___x2b1_x5d___closed__5));
lean_inc(x_22);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = ((lean_object*)(l_Int_term_x2d_x5b___x2b1_x5d___closed__11));
lean_inc(x_22);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Syntax_node3(x_22, x_23, x_25, x_19, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Int_instInhabited___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_instInhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instInhabited___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Int_negOfNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 1)
{
lean_object* x_4; 
x_4 = l_Int_instInhabited___closed__0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = lean_int_neg_succ_of_nat(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int_negOfNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_negOfNat(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_neg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_int_neg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_subNatNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_nat_sub(x_2, x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_nat_sub(x_1, x_2);
x_7 = lean_nat_to_int(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_int_neg_succ_of_nat(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Int_subNatNat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_subNatNat(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_add(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_mul(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_sub(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_instLEInt() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Int_instLTInt() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Int_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_int_dec_eq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Int_instDecidableEq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_instDecidableEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_instDecidableEq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_decNonneg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_int_dec_nonneg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_int_dec_le(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_int_dec_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_natAbs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_abs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Int_instInhabited___closed__0;
x_4 = lean_int_dec_lt(x_1, x_3);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(1u);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Int_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Int_instInhabited___closed__0;
x_4 = lean_int_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_nat_abs(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_nat_abs(x_1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Int_ctorElim___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_ctorElim___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Int_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Int_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int_ofNat_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_ofNat_elim___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_ofNat_elim___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_ofNat_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Int_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_ofNat_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Int_ofNat_elim(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_negSucc_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_negSucc_elim___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_negSucc_elim___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_negSucc_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Int_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_negSucc_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Int_negSucc_elim(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Int_sign___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_sign___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_sign___closed__0;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_sign(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Int_instInhabited___closed__0;
x_4 = lean_int_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_nat_abs(x_1);
x_6 = lean_nat_dec_eq(x_5, x_2);
lean_dec(x_5);
if (x_6 == 1)
{
return x_3;
}
else
{
lean_object* x_7; 
x_7 = l_Int_sign___closed__0;
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = l_Int_sign___closed__1;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Int_sign___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_sign(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_toNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Int_instInhabited___closed__0;
x_4 = lean_int_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_nat_abs(x_1);
return x_5;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Int_toNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_toNat(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_toNat_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Int_instInhabited___closed__0;
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_abs(x_1);
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
LEAN_EXPORT lean_object* l_Int_toNat_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_toNat_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_instDvd() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Int_pow(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Int_instInhabited___closed__0;
x_5 = lean_int_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_nat_abs(x_1);
x_7 = lean_nat_pow(x_6, x_2);
lean_dec(x_6);
x_8 = lean_nat_to_int(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_mod(x_2, x_9);
x_11 = lean_nat_dec_eq(x_10, x_3);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_nat_abs(x_1);
x_13 = lean_nat_pow(x_12, x_2);
lean_dec(x_12);
x_14 = lean_nat_to_int(x_13);
x_15 = lean_int_neg(x_14);
lean_dec(x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_nat_abs(x_1);
x_17 = lean_nat_pow(x_16, x_2);
lean_dec(x_16);
x_18 = lean_nat_to_int(x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_pow(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_instMin___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Int_instMin___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_instMin___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_instMax___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Int_instMax___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_instMax___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instIntCastInt___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instIntCastInt___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instIntCastInt___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_cast___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_cast(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instCoeTailIntOfIntCast___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Int_cast), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instCoeTailIntOfIntCast(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Int_cast), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instCoeHTCTIntOfIntCast___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Int_cast), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instCoeHTCTIntOfIntCast(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Int_cast), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_Cast(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Cast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6 = _init_l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6();
lean_mark_persistent(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6);
l_Int_instInhabited___closed__0 = _init_l_Int_instInhabited___closed__0();
lean_mark_persistent(l_Int_instInhabited___closed__0);
l_Int_instInhabited = _init_l_Int_instInhabited();
lean_mark_persistent(l_Int_instInhabited);
l_Int_instLEInt = _init_l_Int_instLEInt();
lean_mark_persistent(l_Int_instLEInt);
l_Int_instLTInt = _init_l_Int_instLTInt();
lean_mark_persistent(l_Int_instLTInt);
l_Int_sign___closed__0 = _init_l_Int_sign___closed__0();
lean_mark_persistent(l_Int_sign___closed__0);
l_Int_sign___closed__1 = _init_l_Int_sign___closed__1();
lean_mark_persistent(l_Int_sign___closed__1);
l_Int_instDvd = _init_l_Int_instDvd();
lean_mark_persistent(l_Int_instDvd);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
