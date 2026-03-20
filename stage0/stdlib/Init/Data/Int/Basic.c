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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Int_ofNat___boxed(lean_object* v_a_00___x40___internal___hyg_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lean_nat_to_int(v_a_00___x40___internal___hyg_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Int_negSucc___boxed(lean_object* v_a_00___x40___internal___hyg_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lean_int_neg_succ_of_nat(v_a_00___x40___internal___hyg_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_instOfNat(lean_object* v_n_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_nat_to_int(v_n_8_);
return v___x_9_;
}
}
static lean_object* _init_l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5));
v___x_54_ = l_String_toRawSubstring_x27(v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1(lean_object* v_x_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = ((lean_object*)(l_Int_term_x2d_x5b___x2b1_x5d___closed__2));
lean_inc(v_x_74_);
v___x_78_ = l_Lean_Syntax_isOfKind(v_x_74_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; 
lean_dec_ref(v_a_75_);
lean_dec(v_x_74_);
v___x_79_ = lean_box(1);
v___x_80_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v_a_76_);
return v___x_80_;
}
else
{
lean_object* v_quotContext_81_; lean_object* v_currMacroScope_82_; lean_object* v_ref_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_quotContext_81_ = lean_ctor_get(v_a_75_, 1);
lean_inc(v_quotContext_81_);
v_currMacroScope_82_ = lean_ctor_get(v_a_75_, 2);
lean_inc(v_currMacroScope_82_);
v_ref_83_ = lean_ctor_get(v_a_75_, 5);
lean_inc(v_ref_83_);
lean_dec_ref(v_a_75_);
v___x_84_ = lean_unsigned_to_nat(1u);
v___x_85_ = l_Lean_Syntax_getArg(v_x_74_, v___x_84_);
lean_dec(v_x_74_);
v___x_86_ = 0;
v___x_87_ = l_Lean_SourceInfo_fromRef(v_ref_83_, v___x_86_);
lean_dec(v_ref_83_);
v___x_88_ = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4));
v___x_89_ = lean_obj_once(&l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6, &l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6_once, _init_l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6);
v___x_90_ = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__7));
v___x_91_ = l_Lean_addMacroScope(v_quotContext_81_, v___x_90_, v_currMacroScope_82_);
v___x_92_ = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__12));
lean_inc(v___x_87_);
v___x_93_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_93_, 0, v___x_87_);
lean_ctor_set(v___x_93_, 1, v___x_89_);
lean_ctor_set(v___x_93_, 2, v___x_91_);
lean_ctor_set(v___x_93_, 3, v___x_92_);
v___x_94_ = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__14));
lean_inc(v___x_87_);
v___x_95_ = l_Lean_Syntax_node1(v___x_87_, v___x_94_, v___x_85_);
v___x_96_ = l_Lean_Syntax_node2(v___x_87_, v___x_88_, v___x_93_, v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_a_76_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1(lean_object* v_x_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4));
lean_inc(v_x_101_);
v___x_105_ = l_Lean_Syntax_isOfKind(v_x_101_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec(v_x_101_);
v___x_106_ = lean_box(0);
v___x_107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v_a_103_);
return v___x_107_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = l_Lean_Syntax_getArg(v_x_101_, v___x_108_);
v___x_110_ = ((lean_object*)(l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__1));
lean_inc(v___x_109_);
v___x_111_ = l_Lean_Syntax_isOfKind(v___x_109_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v___x_109_);
lean_dec(v_x_101_);
v___x_112_ = lean_box(0);
v___x_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v_a_103_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = l_Lean_Syntax_getArg(v_x_101_, v___x_114_);
lean_dec(v_x_101_);
lean_inc(v___x_115_);
v___x_116_ = l_Lean_Syntax_matchesNull(v___x_115_, v___x_114_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec(v___x_115_);
lean_dec(v___x_109_);
v___x_117_ = lean_box(0);
v___x_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v_a_103_);
return v___x_118_;
}
else
{
lean_object* v___x_119_; lean_object* v_ref_120_; uint8_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_119_ = l_Lean_Syntax_getArg(v___x_115_, v___x_108_);
lean_dec(v___x_115_);
v_ref_120_ = l_Lean_replaceRef(v___x_109_, v_a_102_);
lean_dec(v___x_109_);
v___x_121_ = 0;
v___x_122_ = l_Lean_SourceInfo_fromRef(v_ref_120_, v___x_121_);
lean_dec(v_ref_120_);
v___x_123_ = ((lean_object*)(l_Int_term_x2d_x5b___x2b1_x5d___closed__2));
v___x_124_ = ((lean_object*)(l_Int_term_x2d_x5b___x2b1_x5d___closed__5));
lean_inc(v___x_122_);
v___x_125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_122_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = ((lean_object*)(l_Int_term_x2d_x5b___x2b1_x5d___closed__11));
lean_inc(v___x_122_);
v___x_127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_122_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = l_Lean_Syntax_node3(v___x_122_, v___x_123_, v___x_125_, v___x_119_, v___x_127_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v_a_103_);
return v___x_129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___boxed(lean_object* v_x_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1(v_x_130_, v_a_131_, v_a_132_);
lean_dec(v_a_131_);
return v_res_133_;
}
}
static lean_object* _init_l_Int_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_nat_to_int(v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l_Int_instInhabited(void){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Int_negOfNat(lean_object* v_x_137_){
_start:
{
lean_object* v_zero_138_; uint8_t v_isZero_139_; 
v_zero_138_ = lean_unsigned_to_nat(0u);
v_isZero_139_ = lean_nat_dec_eq(v_x_137_, v_zero_138_);
if (v_isZero_139_ == 1)
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
return v___x_140_;
}
else
{
lean_object* v_one_141_; lean_object* v_n_142_; lean_object* v___x_143_; 
v_one_141_ = lean_unsigned_to_nat(1u);
v_n_142_ = lean_nat_sub(v_x_137_, v_one_141_);
v___x_143_ = lean_int_neg_succ_of_nat(v_n_142_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l_Int_negOfNat___boxed(lean_object* v_x_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Int_negOfNat(v_x_144_);
lean_dec(v_x_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Int_neg___boxed(lean_object* v_n_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = lean_int_neg(v_n_147_);
lean_dec(v_n_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Int_subNatNat(lean_object* v_m_151_, lean_object* v_n_152_){
_start:
{
lean_object* v___x_153_; lean_object* v_zero_154_; uint8_t v_isZero_155_; 
v___x_153_ = lean_nat_sub(v_n_152_, v_m_151_);
v_zero_154_ = lean_unsigned_to_nat(0u);
v_isZero_155_ = lean_nat_dec_eq(v___x_153_, v_zero_154_);
if (v_isZero_155_ == 1)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v___x_153_);
v___x_156_ = lean_nat_sub(v_m_151_, v_n_152_);
v___x_157_ = lean_nat_to_int(v___x_156_);
return v___x_157_;
}
else
{
lean_object* v_one_158_; lean_object* v_n_159_; lean_object* v___x_160_; 
v_one_158_ = lean_unsigned_to_nat(1u);
v_n_159_ = lean_nat_sub(v___x_153_, v_one_158_);
lean_dec(v___x_153_);
v___x_160_ = lean_int_neg_succ_of_nat(v_n_159_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l_Int_subNatNat___boxed(lean_object* v_m_161_, lean_object* v_n_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Int_subNatNat(v_m_161_, v_n_162_);
lean_dec(v_n_162_);
lean_dec(v_m_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Int_add___boxed(lean_object* v_m_166_, lean_object* v_n_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = lean_int_add(v_m_166_, v_n_167_);
lean_dec(v_n_167_);
lean_dec(v_m_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Int_mul___boxed(lean_object* v_m_173_, lean_object* v_n_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = lean_int_mul(v_m_173_, v_n_174_);
lean_dec(v_n_174_);
lean_dec(v_m_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Int_sub___boxed(lean_object* v_m_180_, lean_object* v_n_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = lean_int_sub(v_m_180_, v_n_181_);
lean_dec(v_n_181_);
lean_dec(v_m_180_);
return v_res_182_;
}
}
static lean_object* _init_l_Int_instLEInt(void){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_box(0);
return v___x_185_;
}
}
static lean_object* _init_l_Int_instLTInt(void){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_box(0);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Int_decEq___boxed(lean_object* v_a_189_, lean_object* v_b_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = lean_int_dec_eq(v_a_189_, v_b_190_);
lean_dec(v_b_190_);
lean_dec(v_a_189_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT uint8_t l_Int_instDecidableEq(lean_object* v_a_193_, lean_object* v_b_194_){
_start:
{
uint8_t v___x_195_; 
v___x_195_ = lean_int_dec_eq(v_a_193_, v_b_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Int_instDecidableEq___boxed(lean_object* v_a_196_, lean_object* v_b_197_){
_start:
{
uint8_t v_res_198_; lean_object* v_r_199_; 
v_res_198_ = l_Int_instDecidableEq(v_a_196_, v_b_197_);
lean_dec(v_b_197_);
lean_dec(v_a_196_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT lean_object* l_Int_decNonneg___boxed(lean_object* v_m_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = lean_int_dec_nonneg(v_m_201_);
lean_dec(v_m_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT lean_object* l_Int_decLe___boxed(lean_object* v_a_206_, lean_object* v_b_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = lean_int_dec_le(v_a_206_, v_b_207_);
lean_dec(v_b_207_);
lean_dec(v_a_206_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT lean_object* l_Int_decLt___boxed(lean_object* v_a_212_, lean_object* v_b_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = lean_int_dec_lt(v_a_212_, v_b_213_);
lean_dec(v_b_213_);
lean_dec(v_a_212_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT lean_object* l_Int_natAbs___boxed(lean_object* v_m_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = lean_nat_abs(v_m_217_);
lean_dec(v_m_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Int_ctorIdx(lean_object* v_x_219_){
_start:
{
lean_object* v_natZero_220_; lean_object* v_intZero_221_; uint8_t v_isNeg_222_; 
v_natZero_220_ = lean_unsigned_to_nat(0u);
v_intZero_221_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
v_isNeg_222_ = lean_int_dec_lt(v_x_219_, v_intZero_221_);
if (v_isNeg_222_ == 0)
{
return v_natZero_220_;
}
else
{
lean_object* v___x_223_; 
v___x_223_ = lean_unsigned_to_nat(1u);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Int_ctorIdx___boxed(lean_object* v_x_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Int_ctorIdx(v_x_224_);
lean_dec(v_x_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Int_ctorElim___redArg(lean_object* v_t_226_, lean_object* v_k_227_){
_start:
{
lean_object* v_intZero_228_; uint8_t v_isNeg_229_; 
v_intZero_228_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
v_isNeg_229_ = lean_int_dec_lt(v_t_226_, v_intZero_228_);
if (v_isNeg_229_ == 0)
{
lean_object* v_a_230_; lean_object* v___x_231_; 
v_a_230_ = lean_nat_abs(v_t_226_);
v___x_231_ = lean_apply_1(v_k_227_, v_a_230_);
return v___x_231_;
}
else
{
lean_object* v_abs_232_; lean_object* v_one_233_; lean_object* v_a_234_; lean_object* v___x_235_; 
v_abs_232_ = lean_nat_abs(v_t_226_);
v_one_233_ = lean_unsigned_to_nat(1u);
v_a_234_ = lean_nat_sub(v_abs_232_, v_one_233_);
lean_dec(v_abs_232_);
v___x_235_ = lean_apply_1(v_k_227_, v_a_234_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Int_ctorElim___redArg___boxed(lean_object* v_t_236_, lean_object* v_k_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Int_ctorElim___redArg(v_t_236_, v_k_237_);
lean_dec(v_t_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Int_ctorElim(lean_object* v_motive_239_, lean_object* v_ctorIdx_240_, lean_object* v_t_241_, lean_object* v_h_242_, lean_object* v_k_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Int_ctorElim___redArg(v_t_241_, v_k_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Int_ctorElim___boxed(lean_object* v_motive_245_, lean_object* v_ctorIdx_246_, lean_object* v_t_247_, lean_object* v_h_248_, lean_object* v_k_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Int_ctorElim(v_motive_245_, v_ctorIdx_246_, v_t_247_, v_h_248_, v_k_249_);
lean_dec(v_t_247_);
lean_dec(v_ctorIdx_246_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Int_ofNat_elim___redArg(lean_object* v_t_251_, lean_object* v_ofNat_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Int_ctorElim___redArg(v_t_251_, v_ofNat_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Int_ofNat_elim___redArg___boxed(lean_object* v_t_254_, lean_object* v_ofNat_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Int_ofNat_elim___redArg(v_t_254_, v_ofNat_255_);
lean_dec(v_t_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Int_ofNat_elim(lean_object* v_motive_257_, lean_object* v_t_258_, lean_object* v_h_259_, lean_object* v_ofNat_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Int_ctorElim___redArg(v_t_258_, v_ofNat_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Int_ofNat_elim___boxed(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_ofNat_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Int_ofNat_elim(v_motive_262_, v_t_263_, v_h_264_, v_ofNat_265_);
lean_dec(v_t_263_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Int_negSucc_elim___redArg(lean_object* v_t_267_, lean_object* v_negSucc_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Int_ctorElim___redArg(v_t_267_, v_negSucc_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Int_negSucc_elim___redArg___boxed(lean_object* v_t_270_, lean_object* v_negSucc_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Int_negSucc_elim___redArg(v_t_270_, v_negSucc_271_);
lean_dec(v_t_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Int_negSucc_elim(lean_object* v_motive_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_negSucc_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Int_ctorElim___redArg(v_t_274_, v_negSucc_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Int_negSucc_elim___boxed(lean_object* v_motive_278_, lean_object* v_t_279_, lean_object* v_h_280_, lean_object* v_negSucc_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Int_negSucc_elim(v_motive_278_, v_t_279_, v_h_280_, v_negSucc_281_);
lean_dec(v_t_279_);
return v_res_282_;
}
}
static lean_object* _init_l_Int_sign___closed__0(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(1u);
v___x_284_ = lean_nat_to_int(v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l_Int_sign___closed__1(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_obj_once(&l_Int_sign___closed__0, &l_Int_sign___closed__0_once, _init_l_Int_sign___closed__0);
v___x_286_ = lean_int_neg(v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Int_sign(lean_object* v_x_287_){
_start:
{
lean_object* v_natZero_288_; lean_object* v_intZero_289_; uint8_t v_isNeg_290_; 
v_natZero_288_ = lean_unsigned_to_nat(0u);
v_intZero_289_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
v_isNeg_290_ = lean_int_dec_lt(v_x_287_, v_intZero_289_);
if (v_isNeg_290_ == 0)
{
lean_object* v_a_291_; uint8_t v_isZero_292_; 
v_a_291_ = lean_nat_abs(v_x_287_);
v_isZero_292_ = lean_nat_dec_eq(v_a_291_, v_natZero_288_);
lean_dec(v_a_291_);
if (v_isZero_292_ == 1)
{
return v_intZero_289_;
}
else
{
lean_object* v___x_293_; 
v___x_293_ = lean_obj_once(&l_Int_sign___closed__0, &l_Int_sign___closed__0_once, _init_l_Int_sign___closed__0);
return v___x_293_;
}
}
else
{
lean_object* v___x_294_; 
v___x_294_ = lean_obj_once(&l_Int_sign___closed__1, &l_Int_sign___closed__1_once, _init_l_Int_sign___closed__1);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Int_sign___boxed(lean_object* v_x_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Int_sign(v_x_295_);
lean_dec(v_x_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Int_toNat(lean_object* v_x_297_){
_start:
{
lean_object* v_natZero_298_; lean_object* v_intZero_299_; uint8_t v_isNeg_300_; 
v_natZero_298_ = lean_unsigned_to_nat(0u);
v_intZero_299_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
v_isNeg_300_ = lean_int_dec_lt(v_x_297_, v_intZero_299_);
if (v_isNeg_300_ == 0)
{
lean_object* v_a_301_; 
v_a_301_ = lean_nat_abs(v_x_297_);
return v_a_301_;
}
else
{
return v_natZero_298_;
}
}
}
LEAN_EXPORT lean_object* l_Int_toNat___boxed(lean_object* v_x_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Int_toNat(v_x_302_);
lean_dec(v_x_302_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Int_toNat_x3f(lean_object* v_x_304_){
_start:
{
lean_object* v_intZero_305_; uint8_t v_isNeg_306_; 
v_intZero_305_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
v_isNeg_306_ = lean_int_dec_lt(v_x_304_, v_intZero_305_);
if (v_isNeg_306_ == 0)
{
lean_object* v_a_307_; lean_object* v___x_308_; 
v_a_307_ = lean_nat_abs(v_x_304_);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v_a_307_);
return v___x_308_;
}
else
{
lean_object* v___x_309_; 
v___x_309_ = lean_box(0);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l_Int_toNat_x3f___boxed(lean_object* v_x_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Int_toNat_x3f(v_x_310_);
lean_dec(v_x_310_);
return v_res_311_;
}
}
static lean_object* _init_l_Int_instDvd(void){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = lean_box(0);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Int_pow(lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
lean_object* v_natZero_315_; lean_object* v_intZero_316_; uint8_t v_isNeg_317_; 
v_natZero_315_ = lean_unsigned_to_nat(0u);
v_intZero_316_ = lean_obj_once(&l_Int_instInhabited___closed__0, &l_Int_instInhabited___closed__0_once, _init_l_Int_instInhabited___closed__0);
v_isNeg_317_ = lean_int_dec_lt(v_x_313_, v_intZero_316_);
if (v_isNeg_317_ == 0)
{
lean_object* v_a_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_a_318_ = lean_nat_abs(v_x_313_);
v___x_319_ = lean_nat_pow(v_a_318_, v_x_314_);
lean_dec(v_a_318_);
v___x_320_ = lean_nat_to_int(v___x_319_);
return v___x_320_;
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_321_ = lean_unsigned_to_nat(2u);
v___x_322_ = lean_nat_mod(v_x_314_, v___x_321_);
v___x_323_ = lean_nat_dec_eq(v___x_322_, v_natZero_315_);
lean_dec(v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_324_ = lean_nat_abs(v_x_313_);
v___x_325_ = lean_nat_pow(v___x_324_, v_x_314_);
lean_dec(v___x_324_);
v___x_326_ = lean_nat_to_int(v___x_325_);
v___x_327_ = lean_int_neg(v___x_326_);
lean_dec(v___x_326_);
return v___x_327_;
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_nat_abs(v_x_313_);
v___x_329_ = lean_nat_pow(v___x_328_, v_x_314_);
lean_dec(v___x_328_);
v___x_330_ = lean_nat_to_int(v___x_329_);
return v___x_330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_pow___boxed(lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Int_pow(v_x_331_, v_x_332_);
lean_dec(v_x_332_);
lean_dec(v_x_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Int_instMin___lam__0(lean_object* v_x_336_, lean_object* v_y_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_int_dec_le(v_x_336_, v_y_337_);
if (v___x_338_ == 0)
{
lean_inc(v_y_337_);
return v_y_337_;
}
else
{
lean_inc(v_x_336_);
return v_x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Int_instMin___lam__0___boxed(lean_object* v_x_339_, lean_object* v_y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Int_instMin___lam__0(v_x_339_, v_y_340_);
lean_dec(v_y_340_);
lean_dec(v_x_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Int_instMax___lam__0(lean_object* v_x_344_, lean_object* v_y_345_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = lean_int_dec_le(v_x_344_, v_y_345_);
if (v___x_346_ == 0)
{
lean_inc(v_x_344_);
return v_x_344_;
}
else
{
lean_inc(v_y_345_);
return v_y_345_;
}
}
}
LEAN_EXPORT lean_object* l_Int_instMax___lam__0___boxed(lean_object* v_x_347_, lean_object* v_y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Int_instMax___lam__0(v_x_347_, v_y_348_);
lean_dec(v_y_348_);
lean_dec(v_x_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_instIntCastInt___lam__0(lean_object* v_n_352_){
_start:
{
lean_inc(v_n_352_);
return v_n_352_;
}
}
LEAN_EXPORT lean_object* l_instIntCastInt___lam__0___boxed(lean_object* v_n_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_instIntCastInt___lam__0(v_n_353_);
lean_dec(v_n_353_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___redArg(lean_object* v_inst_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lean_apply_1(v_inst_357_, v_a_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Int_cast(lean_object* v_R_360_, lean_object* v_inst_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_apply_1(v_inst_361_, v_a_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_instCoeTailIntOfIntCast___redArg(lean_object* v_inst_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_alloc_closure((void*)(l_Int_cast), 3, 2);
lean_closure_set(v___x_365_, 0, lean_box(0));
lean_closure_set(v___x_365_, 1, v_inst_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_instCoeTailIntOfIntCast(lean_object* v_R_366_, lean_object* v_inst_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_alloc_closure((void*)(l_Int_cast), 3, 2);
lean_closure_set(v___x_368_, 0, lean_box(0));
lean_closure_set(v___x_368_, 1, v_inst_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_instCoeHTCTIntOfIntCast___redArg(lean_object* v_inst_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = lean_alloc_closure((void*)(l_Int_cast), 3, 2);
lean_closure_set(v___x_370_, 0, lean_box(0));
lean_closure_set(v___x_370_, 1, v_inst_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_instCoeHTCTIntOfIntCast(lean_object* v_R_371_, lean_object* v_inst_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_alloc_closure((void*)(l_Int_cast), 3, 2);
lean_closure_set(v___x_373_, 0, lean_box(0));
lean_closure_set(v___x_373_, 1, v_inst_372_);
return v___x_373_;
}
}
lean_object* runtime_initialize_Init_Data_Cast(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
