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
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Int_term_x2d_x5b___x2b1_x5d___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Int_term_x2d_x5b___x2b1_x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__2_value_aux_0),((lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(13, 210, 79, 129, 91, 108, 255, 221)}};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__2 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__2_value;
static const lean_string_object l_Int_term_x2d_x5b___x2b1_x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Int_term_x2d_x5b___x2b1_x5d___closed__3 = (const lean_object*)&l_Int_term_x2d_x5b___x2b1_x5d___closed__3_value;
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
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_0),((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_1),((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_2),((lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value;
static const lean_string_object l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "negSucc"};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5_value;
static lean_once_cell_t l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
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
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__0 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__0_value;
static const lean_ctor_object l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__1 = (const lean_object*)&l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__1_value;
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Int_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_Int_instInhabited;
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
static lean_once_cell_t l_Int_sign___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_sign___closed__0;
static lean_once_cell_t l_Int_sign___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_sign___closed__1;
LEAN_EXPORT lean_object* l_Int_sign(lean_object*);
LEAN_EXPORT lean_object* l_Int_sign___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Int_toNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Int_toNat_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_instDvd;
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
LEAN_EXPORT void l_Int_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_1_ = stack[0].m_obj;
lean_object* v_res_2_;
v_res_2_ = lean_nat_to_int(v_a_00___x40___internal___hyg_1_);
stack->m_obj
 = v_res_2_;
}
LEAN_EXPORT lean_object* l_Int_ofNat___boxed(lean_object* v_a_00___x40___internal___hyg_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lean_nat_to_int(v_a_00___x40___internal___hyg_3_);
return v_res_4_;
}
}
LEAN_EXPORT void l_Int_negSucc_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_5_ = stack[0].m_obj;
lean_object* v_res_6_;
v_res_6_ = lean_int_neg_succ_of_nat(v_a_00___x40___internal___hyg_5_);
stack->m_obj
 = v_res_6_;
}
LEAN_EXPORT lean_object* l_Int_negSucc___boxed(lean_object* v_a_00___x40___internal___hyg_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lean_int_neg_succ_of_nat(v_a_00___x40___internal___hyg_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_instOfNat(lean_object* v_n_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_nat_to_int(v_n_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5));
v___x_56_ = l_String_toRawSubstring_x27(v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1(lean_object* v_x_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = ((lean_object*)(l_Int_term_x2d_x5b___x2b1_x5d___closed__2));
lean_inc(v_x_76_);
v___x_80_ = l_Lean_Syntax_isOfKind(v_x_76_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_x_76_);
v___x_81_ = lean_box(1);
v___x_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v_a_78_);
return v___x_82_;
}
else
{
lean_object* v_quotContext_83_; lean_object* v_currMacroScope_84_; lean_object* v_ref_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_quotContext_83_ = lean_ctor_get(v_a_77_, 1);
v_currMacroScope_84_ = lean_ctor_get(v_a_77_, 2);
v_ref_85_ = lean_ctor_get(v_a_77_, 5);
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = l_Lean_Syntax_getArg(v_x_76_, v___x_86_);
lean_dec(v_x_76_);
v___x_88_ = 0;
v___x_89_ = l_Lean_SourceInfo_fromRef(v_ref_85_, v___x_88_);
v___x_90_ = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4));
v___x_91_ = lean_obj_once(&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6, &l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6_once, _init_l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6);
v___x_92_ = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__7));
lean_inc(v_currMacroScope_84_);
lean_inc(v_quotContext_83_);
v___x_93_ = l_Lean_addMacroScope(v_quotContext_83_, v___x_92_, v_currMacroScope_84_);
v___x_94_ = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__12));
lean_inc_n(v___x_89_, 2);
v___x_95_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_95_, 0, v___x_89_);
lean_ctor_set(v___x_95_, 1, v___x_91_);
lean_ctor_set(v___x_95_, 2, v___x_93_);
lean_ctor_set(v___x_95_, 3, v___x_94_);
v___x_96_ = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__14));
v___x_97_ = l_Lean_Syntax_node1(v___x_89_, v___x_96_, v___x_87_);
v___x_98_ = l_Lean_Syntax_node2(v___x_89_, v___x_90_, v___x_95_, v___x_97_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v_a_78_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___boxed(lean_object* v_x_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1(v_x_100_, v_a_101_, v_a_102_);
lean_dec_ref(v_a_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1(lean_object* v_x_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4));
lean_inc(v_x_107_);
v___x_111_ = l_Lean_Syntax_isOfKind(v_x_107_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v_x_107_);
v___x_112_ = lean_box(0);
v___x_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v_a_109_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = l_Lean_Syntax_getArg(v_x_107_, v___x_114_);
v___x_116_ = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__1));
lean_inc(v___x_115_);
v___x_117_ = l_Lean_Syntax_isOfKind(v___x_115_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec(v___x_115_);
lean_dec(v_x_107_);
v___x_118_ = lean_box(0);
v___x_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_a_109_);
return v___x_119_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = l_Lean_Syntax_getArg(v_x_107_, v___x_120_);
lean_dec(v_x_107_);
lean_inc(v___x_121_);
v___x_122_ = l_Lean_Syntax_matchesNull(v___x_121_, v___x_120_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec(v___x_121_);
lean_dec(v___x_115_);
v___x_123_ = lean_box(0);
v___x_124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v_a_109_);
return v___x_124_;
}
else
{
lean_object* v___x_125_; lean_object* v_ref_126_; uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_125_ = l_Lean_Syntax_getArg(v___x_121_, v___x_114_);
lean_dec(v___x_121_);
v_ref_126_ = l_Lean_replaceRef(v___x_115_, v_a_108_);
lean_dec(v___x_115_);
v___x_127_ = 0;
v___x_128_ = l_Lean_SourceInfo_fromRef(v_ref_126_, v___x_127_);
lean_dec(v_ref_126_);
v___x_129_ = ((lean_object*)(l_Int_term_x2d_x5b___x2b1_x5d___closed__2));
v___x_130_ = ((lean_object*)(l_Int_term_x2d_x5b___x2b1_x5d___closed__5));
lean_inc_n(v___x_128_, 2);
v___x_131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_128_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = ((lean_object*)(l_Int_term_x2d_x5b___x2b1_x5d___closed__11));
v___x_133_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_128_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = l_Lean_Syntax_node3(v___x_128_, v___x_129_, v___x_131_, v___x_125_, v___x_133_);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v_a_109_);
return v___x_135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___boxed(lean_object* v_x_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1(v_x_136_, v_a_137_, v_a_138_);
lean_dec(v_a_137_);
return v_res_139_;
}
}
static lean_object* _init_l_Int_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_nat_to_int(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l_Int_instInhabited(void){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Int_negOfNat(lean_object* v_x_143_){
_start:
{
lean_object* v_zero_144_; uint8_t v_isZero_145_; 
v_zero_144_ = lean_unsigned_to_nat(0u);
v_isZero_145_ = lean_nat_dec_eq(v_x_143_, v_zero_144_);
if (v_isZero_145_ == 1)
{
lean_object* v___x_146_; 
v___x_146_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
return v___x_146_;
}
else
{
lean_object* v_one_147_; lean_object* v_n_148_; lean_object* v___x_149_; 
v_one_147_ = lean_unsigned_to_nat(1u);
v_n_148_ = lean_nat_sub(v_x_143_, v_one_147_);
v___x_149_ = lean_int_neg_succ_of_nat(v_n_148_);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l_Int_negOfNat___boxed(lean_object* v_x_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Int_negOfNat(v_x_150_);
lean_dec(v_x_150_);
return v_res_151_;
}
}
LEAN_EXPORT void l_Int_neg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_152_ = stack[0].m_obj;
lean_object* v_res_153_;
v_res_153_ = lean_int_neg(v_n_152_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l_Int_neg___boxed(lean_object* v_n_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = lean_int_neg(v_n_154_);
lean_dec(v_n_154_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Int_subNatNat(lean_object* v_m_158_, lean_object* v_n_159_){
_start:
{
lean_object* v___x_160_; lean_object* v_zero_161_; uint8_t v_isZero_162_; 
v___x_160_ = lean_nat_sub(v_n_159_, v_m_158_);
v_zero_161_ = lean_unsigned_to_nat(0u);
v_isZero_162_ = lean_nat_dec_eq(v___x_160_, v_zero_161_);
if (v_isZero_162_ == 1)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v___x_160_);
v___x_163_ = lean_nat_sub(v_m_158_, v_n_159_);
v___x_164_ = lean_nat_to_int(v___x_163_);
return v___x_164_;
}
else
{
lean_object* v_one_165_; lean_object* v_n_166_; lean_object* v___x_167_; 
v_one_165_ = lean_unsigned_to_nat(1u);
v_n_166_ = lean_nat_sub(v___x_160_, v_one_165_);
lean_dec(v___x_160_);
v___x_167_ = lean_int_neg_succ_of_nat(v_n_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_Int_subNatNat___boxed(lean_object* v_m_168_, lean_object* v_n_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Int_subNatNat(v_m_168_, v_n_169_);
lean_dec(v_n_169_);
lean_dec(v_m_168_);
return v_res_170_;
}
}
LEAN_EXPORT void l_Int_add_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_171_ = stack[0].m_obj;
lean_object* v_n_172_ = stack[1].m_obj;
lean_object* v_res_173_;
v_res_173_ = lean_int_add(v_m_171_, v_n_172_);
stack->m_obj
 = v_res_173_;
}
LEAN_EXPORT lean_object* l_Int_add___boxed(lean_object* v_m_174_, lean_object* v_n_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = lean_int_add(v_m_174_, v_n_175_);
lean_dec(v_n_175_);
lean_dec(v_m_174_);
return v_res_176_;
}
}
LEAN_EXPORT void l_Int_mul_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_179_ = stack[0].m_obj;
lean_object* v_n_180_ = stack[1].m_obj;
lean_object* v_res_181_;
v_res_181_ = lean_int_mul(v_m_179_, v_n_180_);
stack->m_obj
 = v_res_181_;
}
LEAN_EXPORT lean_object* l_Int_mul___boxed(lean_object* v_m_182_, lean_object* v_n_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = lean_int_mul(v_m_182_, v_n_183_);
lean_dec(v_n_183_);
lean_dec(v_m_182_);
return v_res_184_;
}
}
LEAN_EXPORT void l_Int_sub_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_187_ = stack[0].m_obj;
lean_object* v_n_188_ = stack[1].m_obj;
lean_object* v_res_189_;
v_res_189_ = lean_int_sub(v_m_187_, v_n_188_);
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l_Int_sub___boxed(lean_object* v_m_190_, lean_object* v_n_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = lean_int_sub(v_m_190_, v_n_191_);
lean_dec(v_n_191_);
lean_dec(v_m_190_);
return v_res_192_;
}
}
static lean_object* _init_l_Int_instLEInt(void){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(0);
return v___x_195_;
}
}
static lean_object* _init_l_Int_instLTInt(void){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_box(0);
return v___x_196_;
}
}
LEAN_EXPORT void l_Int_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_197_ = stack[0].m_obj;
lean_object* v_b_198_ = stack[1].m_obj;
uint8_t v_res_199_;
v_res_199_ = lean_int_dec_eq(v_a_197_, v_b_198_);
stack->m_num = v_res_199_;
}
LEAN_EXPORT lean_object* l_Int_decEq___boxed(lean_object* v_a_200_, lean_object* v_b_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = lean_int_dec_eq(v_a_200_, v_b_201_);
lean_dec(v_b_201_);
lean_dec(v_a_200_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
uint8_t l_Int_instDecidableEq(lean_object* v_a_204_, lean_object* v_b_205_){
_start:
{
uint8_t v___x_206_; 
v___x_206_ = lean_int_dec_eq(v_a_204_, v_b_205_);
return v___x_206_;
}
}
LEAN_EXPORT void l_Int_instDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_204_ = stack[0].m_obj;
lean_object* v_b_205_ = stack[1].m_obj;
uint8_t v_res_207_;
v_res_207_ = l_Int_instDecidableEq(v_a_204_, v_b_205_);
stack->m_num = v_res_207_;
}
LEAN_EXPORT lean_object* l_Int_instDecidableEq___boxed(lean_object* v_a_208_, lean_object* v_b_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_Int_instDecidableEq(v_a_208_, v_b_209_);
lean_dec(v_b_209_);
lean_dec(v_a_208_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT void l_Int_decNonneg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_212_ = stack[0].m_obj;
uint8_t v_res_213_;
v_res_213_ = lean_int_dec_nonneg(v_m_212_);
stack->m_num = v_res_213_;
}
LEAN_EXPORT lean_object* l_Int_decNonneg___boxed(lean_object* v_m_214_){
_start:
{
uint8_t v_res_215_; lean_object* v_r_216_; 
v_res_215_ = lean_int_dec_nonneg(v_m_214_);
lean_dec(v_m_214_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT void l_Int_decLe_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_217_ = stack[0].m_obj;
lean_object* v_b_218_ = stack[1].m_obj;
uint8_t v_res_219_;
v_res_219_ = lean_int_dec_le(v_a_217_, v_b_218_);
stack->m_num = v_res_219_;
}
LEAN_EXPORT lean_object* l_Int_decLe___boxed(lean_object* v_a_220_, lean_object* v_b_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = lean_int_dec_le(v_a_220_, v_b_221_);
lean_dec(v_b_221_);
lean_dec(v_a_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT void l_Int_decLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_224_ = stack[0].m_obj;
lean_object* v_b_225_ = stack[1].m_obj;
uint8_t v_res_226_;
v_res_226_ = lean_int_dec_lt(v_a_224_, v_b_225_);
stack->m_num = v_res_226_;
}
LEAN_EXPORT lean_object* l_Int_decLt___boxed(lean_object* v_a_227_, lean_object* v_b_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = lean_int_dec_lt(v_a_227_, v_b_228_);
lean_dec(v_b_228_);
lean_dec(v_a_227_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT void l_Int_natAbs_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_231_ = stack[0].m_obj;
lean_object* v_res_232_;
v_res_232_ = lean_nat_abs(v_m_231_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l_Int_natAbs___boxed(lean_object* v_m_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = lean_nat_abs(v_m_233_);
lean_dec(v_m_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Int_ctorIdx(lean_object* v_x_235_){
_start:
{
lean_object* v_natZero_236_; lean_object* v_intZero_237_; uint8_t v_isNeg_238_; 
v_natZero_236_ = lean_unsigned_to_nat(0u);
v_intZero_237_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
v_isNeg_238_ = lean_int_dec_lt(v_x_235_, v_intZero_237_);
if (v_isNeg_238_ == 0)
{
return v_natZero_236_;
}
else
{
lean_object* v___x_239_; 
v___x_239_ = lean_unsigned_to_nat(1u);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l_Int_ctorIdx___boxed(lean_object* v_x_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Int_ctorIdx(v_x_240_);
lean_dec(v_x_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Int_ctorElim___redArg(lean_object* v_t_242_, lean_object* v_k_243_){
_start:
{
lean_object* v_intZero_244_; uint8_t v_isNeg_245_; 
v_intZero_244_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
v_isNeg_245_ = lean_int_dec_lt(v_t_242_, v_intZero_244_);
if (v_isNeg_245_ == 0)
{
lean_object* v_a_246_; lean_object* v___x_247_; 
v_a_246_ = lean_nat_abs(v_t_242_);
v___x_247_ = lean_apply_1(v_k_243_, v_a_246_);
return v___x_247_;
}
else
{
lean_object* v_abs_248_; lean_object* v_one_249_; lean_object* v_a_250_; lean_object* v___x_251_; 
v_abs_248_ = lean_nat_abs(v_t_242_);
v_one_249_ = lean_unsigned_to_nat(1u);
v_a_250_ = lean_nat_sub(v_abs_248_, v_one_249_);
lean_dec(v_abs_248_);
v___x_251_ = lean_apply_1(v_k_243_, v_a_250_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l_Int_ctorElim___redArg___boxed(lean_object* v_t_252_, lean_object* v_k_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Int_ctorElim___redArg(v_t_252_, v_k_253_);
lean_dec(v_t_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Int_ctorElim(lean_object* v_motive_255_, lean_object* v_ctorIdx_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_k_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Int_ctorElim___redArg(v_t_257_, v_k_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Int_ctorElim___boxed(lean_object* v_motive_261_, lean_object* v_ctorIdx_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_k_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Int_ctorElim(v_motive_261_, v_ctorIdx_262_, v_t_263_, v_h_264_, v_k_265_);
lean_dec(v_t_263_);
lean_dec(v_ctorIdx_262_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Int_ofNat_elim___redArg(lean_object* v_t_267_, lean_object* v_ofNat_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Int_ctorElim___redArg(v_t_267_, v_ofNat_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Int_ofNat_elim___redArg___boxed(lean_object* v_t_270_, lean_object* v_ofNat_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Int_ofNat_elim___redArg(v_t_270_, v_ofNat_271_);
lean_dec(v_t_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Int_ofNat_elim(lean_object* v_motive_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_ofNat_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Int_ctorElim___redArg(v_t_274_, v_ofNat_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Int_ofNat_elim___boxed(lean_object* v_motive_278_, lean_object* v_t_279_, lean_object* v_h_280_, lean_object* v_ofNat_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Int_ofNat_elim(v_motive_278_, v_t_279_, v_h_280_, v_ofNat_281_);
lean_dec(v_t_279_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Int_negSucc_elim___redArg(lean_object* v_t_283_, lean_object* v_negSucc_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Int_ctorElim___redArg(v_t_283_, v_negSucc_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Int_negSucc_elim___redArg___boxed(lean_object* v_t_286_, lean_object* v_negSucc_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Int_negSucc_elim___redArg(v_t_286_, v_negSucc_287_);
lean_dec(v_t_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Int_negSucc_elim(lean_object* v_motive_289_, lean_object* v_t_290_, lean_object* v_h_291_, lean_object* v_negSucc_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Int_ctorElim___redArg(v_t_290_, v_negSucc_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Int_negSucc_elim___boxed(lean_object* v_motive_294_, lean_object* v_t_295_, lean_object* v_h_296_, lean_object* v_negSucc_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Int_negSucc_elim(v_motive_294_, v_t_295_, v_h_296_, v_negSucc_297_);
lean_dec(v_t_295_);
return v_res_298_;
}
}
static lean_object* _init_l_Int_sign___closed__0(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_nat_to_int(v___x_299_);
return v___x_300_;
}
}
static lean_object* _init_l_Int_sign___closed__1(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_obj_once(&l_Int_sign___closed__0, &l_Int_sign___closed__0_once, _init_l_Int_sign___closed__0);
v___x_302_ = lean_int_neg(v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Int_sign(lean_object* v_x_303_){
_start:
{
lean_object* v_natZero_304_; lean_object* v_intZero_305_; uint8_t v_isNeg_306_; 
v_natZero_304_ = lean_unsigned_to_nat(0u);
v_intZero_305_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
v_isNeg_306_ = lean_int_dec_lt(v_x_303_, v_intZero_305_);
if (v_isNeg_306_ == 0)
{
lean_object* v_a_307_; uint8_t v_isZero_308_; 
v_a_307_ = lean_nat_abs(v_x_303_);
v_isZero_308_ = lean_nat_dec_eq(v_a_307_, v_natZero_304_);
lean_dec(v_a_307_);
if (v_isZero_308_ == 1)
{
return v_intZero_305_;
}
else
{
lean_object* v___x_309_; 
v___x_309_ = lean_obj_once(&l_Int_sign___closed__0, &l_Int_sign___closed__0_once, _init_l_Int_sign___closed__0);
return v___x_309_;
}
}
else
{
lean_object* v___x_310_; 
v___x_310_ = lean_obj_once(&l_Int_sign___closed__1, &l_Int_sign___closed__1_once, _init_l_Int_sign___closed__1);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Int_sign___boxed(lean_object* v_x_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Int_sign(v_x_311_);
lean_dec(v_x_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Int_toNat(lean_object* v_x_313_){
_start:
{
lean_object* v_natZero_314_; lean_object* v_intZero_315_; uint8_t v_isNeg_316_; 
v_natZero_314_ = lean_unsigned_to_nat(0u);
v_intZero_315_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
v_isNeg_316_ = lean_int_dec_lt(v_x_313_, v_intZero_315_);
if (v_isNeg_316_ == 0)
{
lean_object* v_a_317_; 
v_a_317_ = lean_nat_abs(v_x_313_);
return v_a_317_;
}
else
{
return v_natZero_314_;
}
}
}
LEAN_EXPORT lean_object* l_Int_toNat___boxed(lean_object* v_x_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Int_toNat(v_x_318_);
lean_dec(v_x_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Int_toNat_x3f(lean_object* v_x_320_){
_start:
{
lean_object* v_intZero_321_; uint8_t v_isNeg_322_; 
v_intZero_321_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
v_isNeg_322_ = lean_int_dec_lt(v_x_320_, v_intZero_321_);
if (v_isNeg_322_ == 0)
{
lean_object* v_a_323_; lean_object* v___x_324_; 
v_a_323_ = lean_nat_abs(v_x_320_);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v_a_323_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; 
v___x_325_ = lean_box(0);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l_Int_toNat_x3f___boxed(lean_object* v_x_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Int_toNat_x3f(v_x_326_);
lean_dec(v_x_326_);
return v_res_327_;
}
}
static lean_object* _init_l_Int_instDvd(void){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_box(0);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Int_pow(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
lean_object* v_natZero_331_; lean_object* v_intZero_332_; uint8_t v_isNeg_333_; 
v_natZero_331_ = lean_unsigned_to_nat(0u);
v_intZero_332_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
v_isNeg_333_ = lean_int_dec_lt(v_x_329_, v_intZero_332_);
if (v_isNeg_333_ == 0)
{
lean_object* v_a_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_a_334_ = lean_nat_abs(v_x_329_);
v___x_335_ = lean_nat_pow(v_a_334_, v_x_330_);
lean_dec(v_a_334_);
v___x_336_ = lean_nat_to_int(v___x_335_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_337_ = lean_unsigned_to_nat(2u);
v___x_338_ = lean_nat_mod(v_x_330_, v___x_337_);
v___x_339_ = lean_nat_dec_eq(v___x_338_, v_natZero_331_);
lean_dec(v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_340_ = lean_nat_abs(v_x_329_);
v___x_341_ = lean_nat_pow(v___x_340_, v_x_330_);
lean_dec(v___x_340_);
v___x_342_ = lean_nat_to_int(v___x_341_);
v___x_343_ = lean_int_neg(v___x_342_);
lean_dec(v___x_342_);
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_nat_abs(v_x_329_);
v___x_345_ = lean_nat_pow(v___x_344_, v_x_330_);
lean_dec(v___x_344_);
v___x_346_ = lean_nat_to_int(v___x_345_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_pow___boxed(lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Int_pow(v_x_347_, v_x_348_);
lean_dec(v_x_348_);
lean_dec(v_x_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Int_instMin___lam__0(lean_object* v_x_352_, lean_object* v_y_353_){
_start:
{
uint8_t v___x_354_; 
v___x_354_ = lean_int_dec_le(v_x_352_, v_y_353_);
if (v___x_354_ == 0)
{
lean_inc(v_y_353_);
return v_y_353_;
}
else
{
lean_inc(v_x_352_);
return v_x_352_;
}
}
}
LEAN_EXPORT lean_object* l_Int_instMin___lam__0___boxed(lean_object* v_x_355_, lean_object* v_y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Int_instMin___lam__0(v_x_355_, v_y_356_);
lean_dec(v_y_356_);
lean_dec(v_x_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Int_instMax___lam__0(lean_object* v_x_360_, lean_object* v_y_361_){
_start:
{
uint8_t v___x_362_; 
v___x_362_ = lean_int_dec_le(v_x_360_, v_y_361_);
if (v___x_362_ == 0)
{
lean_inc(v_x_360_);
return v_x_360_;
}
else
{
lean_inc(v_y_361_);
return v_y_361_;
}
}
}
LEAN_EXPORT lean_object* l_Int_instMax___lam__0___boxed(lean_object* v_x_363_, lean_object* v_y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Int_instMax___lam__0(v_x_363_, v_y_364_);
lean_dec(v_y_364_);
lean_dec(v_x_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_instIntCastInt___lam__0(lean_object* v_n_368_){
_start:
{
lean_inc(v_n_368_);
return v_n_368_;
}
}
LEAN_EXPORT lean_object* l_instIntCastInt___lam__0___boxed(lean_object* v_n_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_instIntCastInt___lam__0(v_n_369_);
lean_dec(v_n_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___redArg(lean_object* v_inst_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = lean_apply_1(v_inst_373_, v_a_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Int_cast(lean_object* v_R_376_, lean_object* v_inst_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = lean_apply_1(v_inst_377_, v_a_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_instCoeTailIntOfIntCast___redArg(lean_object* v_inst_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_alloc_closure((void*)(l_Int_cast), 3, 2);
lean_closure_set(v___x_381_, 0, lean_box(0));
lean_closure_set(v___x_381_, 1, v_inst_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_instCoeTailIntOfIntCast(lean_object* v_R_382_, lean_object* v_inst_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = lean_alloc_closure((void*)(l_Int_cast), 3, 2);
lean_closure_set(v___x_384_, 0, lean_box(0));
lean_closure_set(v___x_384_, 1, v_inst_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_instCoeHTCTIntOfIntCast___redArg(lean_object* v_inst_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lean_alloc_closure((void*)(l_Int_cast), 3, 2);
lean_closure_set(v___x_386_, 0, lean_box(0));
lean_closure_set(v___x_386_, 1, v_inst_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_instCoeHTCTIntOfIntCast(lean_object* v_R_387_, lean_object* v_inst_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = lean_alloc_closure((void*)(l_Int_cast), 3, 2);
lean_closure_set(v___x_389_, 0, lean_box(0));
lean_closure_set(v___x_389_, 1, v_inst_388_);
return v___x_389_;
}
}
lean_object* runtime_initialize_Init_Data_Cast(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Cast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_instInhabited = _init_l_Int_instInhabited();
lean_mark_persistent(l_Int_instInhabited);
l_Int_instLEInt = _init_l_Int_instLEInt();
lean_mark_persistent(l_Int_instLEInt);
l_Int_instLTInt = _init_l_Int_instLTInt();
lean_mark_persistent(l_Int_instLTInt);
l_Int_instDvd = _init_l_Int_instDvd();
lean_mark_persistent(l_Int_instDvd);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Int_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Int_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
