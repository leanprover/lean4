// Lean compiler output
// Module: Init.Data.Array.Basic
// Imports: public import Init.Control.Do public import Init.GetElem public import Init.Data.List.ToArrayImpl import all Init.Data.List.ToArrayImpl public import Init.Data.Array.Set import all Init.Data.Array.Set public import Init.WF meta import Init.MetaTypes import Init.WFTactics
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_appendCore___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_repr(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static const lean_string_object l_term_x23_x5b___x2c_x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term#[_,]"};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__0 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__0_value;
static const lean_ctor_object l_term_x23_x5b___x2c_x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 119, 178, 128, 145, 112, 206, 247)}};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__1 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__1_value;
static const lean_string_object l_term_x23_x5b___x2c_x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__2 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__2_value;
static const lean_ctor_object l_term_x23_x5b___x2c_x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__3 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__3_value;
static const lean_string_object l_term_x23_x5b___x2c_x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__4 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__4_value;
static const lean_ctor_object l_term_x23_x5b___x2c_x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__4_value)}};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__5 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__5_value;
static const lean_string_object l_term_x23_x5b___x2c_x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__6 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__6_value;
static const lean_ctor_object l_term_x23_x5b___x2c_x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__6_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__7 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__7_value;
static const lean_string_object l_term_x23_x5b___x2c_x5d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__8 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__8_value;
static const lean_ctor_object l_term_x23_x5b___x2c_x5d___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__9 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__9_value;
static const lean_ctor_object l_term_x23_x5b___x2c_x5d___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__10 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__10_value;
static const lean_string_object l_term_x23_x5b___x2c_x5d___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__11 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__11_value;
static const lean_string_object l_term_x23_x5b___x2c_x5d___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__12 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__12_value;
static const lean_ctor_object l_term_x23_x5b___x2c_x5d___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__12_value)}};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__13 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__13_value;
static const lean_ctor_object l_term_x23_x5b___x2c_x5d___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__10_value),((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__11_value),((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__13_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__14 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__14_value;
static const lean_ctor_object l_term_x23_x5b___x2c_x5d___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__7_value),((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__14_value)}};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__15 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__15_value;
static const lean_ctor_object l_term_x23_x5b___x2c_x5d___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__3_value),((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__5_value),((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__15_value)}};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__16 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__16_value;
static const lean_string_object l_term_x23_x5b___x2c_x5d___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__17 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__17_value;
static const lean_ctor_object l_term_x23_x5b___x2c_x5d___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__17_value)}};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__18 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__18_value;
static const lean_ctor_object l_term_x23_x5b___x2c_x5d___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__3_value),((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__16_value),((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__18_value)}};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__19 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__19_value;
static const lean_ctor_object l_term_x23_x5b___x2c_x5d___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__19_value)}};
static const lean_object* l_term_x23_x5b___x2c_x5d___closed__20 = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__20_value;
LEAN_EXPORT const lean_object* l_term_x23_x5b___x2c_x5d = (const lean_object*)&l_term_x23_x5b___x2c_x5d___closed__20_value;
static const lean_string_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__0 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__0_value;
static const lean_string_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1_value;
static const lean_string_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2_value;
static const lean_string_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__3 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__3_value;
static const lean_ctor_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value_aux_1),((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value_aux_2),((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4_value;
static const lean_string_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "List.toArray"};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__5 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__5_value;
static lean_once_cell_t l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6;
static const lean_string_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__7 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__7_value;
static const lean_string_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__8 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__8_value;
static const lean_ctor_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9_value_aux_0),((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9_value;
static const lean_ctor_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__10 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__10_value;
static const lean_ctor_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__11 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__11_value;
static const lean_string_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__12 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__12_value;
static const lean_ctor_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13_value;
static const lean_string_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term[_]"};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__14 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__14_value;
static const lean_ctor_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(86, 147, 168, 74, 195, 98, 232, 161)}};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__15 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__15_value;
static const lean_string_object l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__16 = (const lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__16_value;
static lean_once_cell_t l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17;
LEAN_EXPORT lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instMembership(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_usize___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_uget___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_ugetBorrowed___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_uset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Array_pop___boxed(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_replicate___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_swap___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Array_swap___auto__1___closed__0 = (const lean_object*)&l_Array_swap___auto__1___closed__0_value;
static const lean_string_object l_Array_swap___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Array_swap___auto__1___closed__1 = (const lean_object*)&l_Array_swap___auto__1___closed__1_value;
static const lean_ctor_object l_Array_swap___auto__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_swap___auto__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_swap___auto__1___closed__2_value_aux_0),((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_swap___auto__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_swap___auto__1___closed__2_value_aux_1),((lean_object*)&l_Array_swap___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_swap___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_swap___auto__1___closed__2_value_aux_2),((lean_object*)&l_Array_swap___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Array_swap___auto__1___closed__2 = (const lean_object*)&l_Array_swap___auto__1___closed__2_value;
static const lean_array_object l_Array_swap___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_swap___auto__1___closed__3 = (const lean_object*)&l_Array_swap___auto__1___closed__3_value;
static const lean_string_object l_Array_swap___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Array_swap___auto__1___closed__4 = (const lean_object*)&l_Array_swap___auto__1___closed__4_value;
static const lean_ctor_object l_Array_swap___auto__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_swap___auto__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_swap___auto__1___closed__5_value_aux_0),((lean_object*)&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_swap___auto__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_swap___auto__1___closed__5_value_aux_1),((lean_object*)&l_Array_swap___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_swap___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_swap___auto__1___closed__5_value_aux_2),((lean_object*)&l_Array_swap___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Array_swap___auto__1___closed__5 = (const lean_object*)&l_Array_swap___auto__1___closed__5_value;
static const lean_string_object l_Array_swap___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticGet_elem_tactic"};
static const lean_object* l_Array_swap___auto__1___closed__6 = (const lean_object*)&l_Array_swap___auto__1___closed__6_value;
static const lean_ctor_object l_Array_swap___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_swap___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(141, 31, 109, 153, 11, 229, 201, 51)}};
static const lean_object* l_Array_swap___auto__1___closed__7 = (const lean_object*)&l_Array_swap___auto__1___closed__7_value;
static const lean_string_object l_Array_swap___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "get_elem_tactic"};
static const lean_object* l_Array_swap___auto__1___closed__8 = (const lean_object*)&l_Array_swap___auto__1___closed__8_value;
static lean_once_cell_t l_Array_swap___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_swap___auto__1___closed__9;
static lean_once_cell_t l_Array_swap___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_swap___auto__1___closed__10;
static lean_once_cell_t l_Array_swap___auto__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_swap___auto__1___closed__11;
static lean_once_cell_t l_Array_swap___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_swap___auto__1___closed__12;
static lean_once_cell_t l_Array_swap___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_swap___auto__1___closed__13;
static lean_once_cell_t l_Array_swap___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_swap___auto__1___closed__14;
static lean_once_cell_t l_Array_swap___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_swap___auto__1___closed__15;
static lean_once_cell_t l_Array_swap___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_swap___auto__1___closed__16;
static lean_once_cell_t l_Array_swap___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_swap___auto__1___closed__17;
LEAN_EXPORT lean_object* l_Array_swap___auto__1;
LEAN_EXPORT lean_object* l_Array_swap___auto__3;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_swap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_swapIfInBounds___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___lam__0(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_instGetElemUSizeLtNatToNatSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instGetElemUSizeLtNatToNatSize___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_instGetElemUSizeLtNatToNatSize___closed__0 = (const lean_object*)&l_Array_instGetElemUSizeLtNatToNatSize___closed__0_value;
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize(lean_object*);
static const lean_array_object l_Array_instEmptyCollection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_instEmptyCollection___closed__0 = (const lean_object*)&l_Array_instEmptyCollection___closed__0_value;
LEAN_EXPORT lean_object* l_Array_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Array_instInhabited(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqv___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqv(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instBEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instBEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instBEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instBEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_range___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_range___lam__0___boxed(lean_object*);
static const lean_closure_object l_Array_range___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_range___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_range___closed__0 = (const lean_object*)&l_Array_range___closed__0_value;
LEAN_EXPORT lean_object* l_Array_range(lean_object*);
LEAN_EXPORT lean_object* l_Array_range_x27___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_range_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_range_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_singleton___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_singleton(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_back_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_back_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_back_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_back___auto__1;
LEAN_EXPORT lean_object* l_Array_back___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_back___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_back(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_back___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_back_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_back_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_back_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_back_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_swapAt___auto__1;
LEAN_EXPORT lean_object* l_Array_swapAt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_swapAt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_swapAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_swapAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_swapAt_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Init.Data.Array.Basic"};
static const lean_object* l_Array_swapAt_x21___redArg___closed__0 = (const lean_object*)&l_Array_swapAt_x21___redArg___closed__0_value;
static const lean_string_object l_Array_swapAt_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Array.swapAt!"};
static const lean_object* l_Array_swapAt_x21___redArg___closed__1 = (const lean_object*)&l_Array_swapAt_x21___redArg___closed__1_value;
static const lean_string_object l_Array_swapAt_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "index "};
static const lean_object* l_Array_swapAt_x21___redArg___closed__2 = (const lean_object*)&l_Array_swapAt_x21___redArg___closed__2_value;
static const lean_string_object l_Array_swapAt_x21___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " out of bounds"};
static const lean_object* l_Array_swapAt_x21___redArg___closed__3 = (const lean_object*)&l_Array_swapAt_x21___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Array_swapAt_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_swapAt_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_shrink_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_shrink___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_shrink(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_shrink___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_take___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_take___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_take(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_take___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_drop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_drop___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_drop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_drop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modify___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modify___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modify(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modify___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modifyOp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modifyOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(lean_object*, size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlM_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrM_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrM_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxMUnsafe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxMUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_firstM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_firstM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__2(lean_object*, lean_object*);
static const lean_ctor_object l_Array_findSomeM_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array_findSomeM_x3f___redArg___closed__0 = (const lean_object*)&l_Array_findSomeM_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__2(lean_object*, lean_object*);
static const lean_ctor_object l_Array_findIdxM_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array_findIdxM_x3f___redArg___closed__0 = (const lean_object*)&l_Array_findIdxM_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_anyM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_allM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_allM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_allM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findRevM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instForMOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forRevM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forRevM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forRevM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_foldl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_foldl___redArg___closed__0 = (const lean_object*)&l_Array_foldl___redArg___closed__0_value;
static const lean_closure_object l_Array_foldl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_foldl___redArg___closed__1 = (const lean_object*)&l_Array_foldl___redArg___closed__1_value;
static const lean_closure_object l_Array_foldl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_foldl___redArg___closed__2 = (const lean_object*)&l_Array_foldl___redArg___closed__2_value;
static const lean_closure_object l_Array_foldl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_foldl___redArg___closed__3 = (const lean_object*)&l_Array_foldl___redArg___closed__3_value;
static const lean_closure_object l_Array_foldl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_foldl___redArg___closed__4 = (const lean_object*)&l_Array_foldl___redArg___closed__4_value;
static const lean_closure_object l_Array_foldl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_foldl___redArg___closed__5 = (const lean_object*)&l_Array_foldl___redArg___closed__5_value;
static const lean_closure_object l_Array_foldl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_foldl___redArg___closed__6 = (const lean_object*)&l_Array_foldl___redArg___closed__6_value;
static const lean_ctor_object l_Array_foldl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_foldl___redArg___closed__0_value),((lean_object*)&l_Array_foldl___redArg___closed__1_value)}};
static const lean_object* l_Array_foldl___redArg___closed__7 = (const lean_object*)&l_Array_foldl___redArg___closed__7_value;
static const lean_ctor_object l_Array_foldl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_foldl___redArg___closed__7_value),((lean_object*)&l_Array_foldl___redArg___closed__2_value),((lean_object*)&l_Array_foldl___redArg___closed__3_value),((lean_object*)&l_Array_foldl___redArg___closed__4_value),((lean_object*)&l_Array_foldl___redArg___closed__5_value)}};
static const lean_object* l_Array_foldl___redArg___closed__8 = (const lean_object*)&l_Array_foldl___redArg___closed__8_value;
static const lean_ctor_object l_Array_foldl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_foldl___redArg___closed__8_value),((lean_object*)&l_Array_foldl___redArg___closed__6_value)}};
static const lean_object* l_Array_foldl___redArg___closed__9 = (const lean_object*)&l_Array_foldl___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Array_foldl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sum___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sum(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_prod___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_prod(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_countP___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_countP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_count___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_count(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_map(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_instFunctor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instFunctor___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_instFunctor___closed__0 = (const lean_object*)&l_Array_instFunctor___closed__0_value;
static const lean_closure_object l_Array_instFunctor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_map, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_instFunctor___closed__1 = (const lean_object*)&l_Array_instFunctor___closed__1_value;
static const lean_ctor_object l_Array_instFunctor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_instFunctor___closed__1_value),((lean_object*)&l_Array_instFunctor___closed__0_value)}};
static const lean_object* l_Array_instFunctor___closed__2 = (const lean_object*)&l_Array_instFunctor___closed__2_value;
LEAN_EXPORT const lean_object* l_Array_instFunctor = (const lean_object*)&l_Array_instFunctor___closed__2_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_find_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_findSome_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Array.findSome!"};
static const lean_object* l_Array_findSome_x21___redArg___closed__0 = (const lean_object*)&l_Array_findSome_x21___redArg___closed__0_value;
static const lean_string_object l_Array_findSome_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "failed to find element"};
static const lean_object* l_Array_findSome_x21___redArg___closed__1 = (const lean_object*)&l_Array_findSome_x21___redArg___closed__1_value;
static lean_once_cell_t l_Array_findSome_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_findSome_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSome_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSome_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findRev_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_idxOf___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_any___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_any___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_any___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_any___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_all___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_all___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_all___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_all___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_elem___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_elem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_elem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_array_to_list_impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Array_toListAppend___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_toListAppend___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toListAppend___redArg___closed__0 = (const lean_object*)&l_Array_toListAppend___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toListAppend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_append___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_append___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_append___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_instAppend___closed__0 = (const lean_object*)&l_Array_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Array_instAppend(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_appendList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_appendList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_instHAppendList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_appendList, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_instHAppendList___closed__0 = (const lean_object*)&l_Array_instHAppendList___closed__0_value;
LEAN_EXPORT lean_object* l_Array_instHAppendList(lean_object*);
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_flatMapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_flatMap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_flatMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_flatMap(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_flatten___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_append___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_flatten___redArg___closed__0 = (const lean_object*)&l_Array_flatten___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_flatten___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_flatten(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reverse_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reverse_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_reverse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filter___redArg___closed__0 = (const lean_object*)&l_Array_filter___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_filterRevM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_reverse, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_filterRevM___redArg___closed__0 = (const lean_object*)&l_Array_filterRevM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterRevM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterRevM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getMax_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_partition___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Array_partition___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_filter___redArg___closed__0_value),((lean_object*)&l_Array_filter___redArg___closed__0_value)}};
static const lean_object* l_Array_partition___redArg___closed__0 = (const lean_object*)&l_Array_partition___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_partition___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_partition(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_popWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_popWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_takeWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_takeWhile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseIdx___auto__1;
LEAN_EXPORT lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_eraseIdx_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Array.eraseIdx!"};
static const lean_object* l_Array_eraseIdx_x21___redArg___closed__0 = (const lean_object*)&l_Array_eraseIdx_x21___redArg___closed__0_value;
static const lean_string_object l_Array_eraseIdx_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invalid index"};
static const lean_object* l_Array_eraseIdx_x21___redArg___closed__1 = (const lean_object*)&l_Array_eraseIdx_x21___redArg___closed__1_value;
static lean_once_cell_t l_Array_eraseIdx_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_eraseIdx_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_erase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseP___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx___auto__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_insertIdx_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Array.insertIdx!"};
static const lean_object* l_Array_insertIdx_x21___redArg___closed__0 = (const lean_object*)&l_Array_insertIdx_x21___redArg___closed__0_value;
static lean_once_cell_t l_Array_insertIdx_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_insertIdx_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isPrefixOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isPrefixOf___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isPrefixOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isPrefixOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWith___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_zip___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_zip___redArg___closed__0 = (const lean_object*)&l_Array_zip___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zip___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zip(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zip___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_unzip___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_unzip___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_unzip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_unzip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instLT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_leftpad___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_leftpad___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_leftpad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_leftpad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_rightpad___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_rightpad___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_rightpad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_rightpad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Array_reduceOption___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_reduceOption___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_reduceOption___redArg___closed__0 = (const lean_object*)&l_Array_reduceOption___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseReps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_allDiff___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_allDiff___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_allDiff(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_allDiff___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_getEvenElems(lean_object*, lean_object*);
static const lean_ctor_object l_Array_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__11_value)}};
static const lean_object* l_Array_repr___redArg___closed__0 = (const lean_object*)&l_Array_repr___redArg___closed__0_value;
static const lean_ctor_object l_Array_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___redArg___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___redArg___closed__1 = (const lean_object*)&l_Array_repr___redArg___closed__1_value;
static lean_once_cell_t l_Array_repr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___redArg___closed__2;
static lean_once_cell_t l_Array_repr___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___redArg___closed__3;
static const lean_ctor_object l_Array_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__4_value)}};
static const lean_object* l_Array_repr___redArg___closed__4 = (const lean_object*)&l_Array_repr___redArg___closed__4_value;
static const lean_ctor_object l_Array_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_term_x23_x5b___x2c_x5d___closed__17_value)}};
static const lean_object* l_Array_repr___redArg___closed__5 = (const lean_object*)&l_Array_repr___redArg___closed__5_value;
static const lean_string_object l_Array_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___redArg___closed__6 = (const lean_object*)&l_Array_repr___redArg___closed__6_value;
static const lean_ctor_object l_Array_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___redArg___closed__6_value)}};
static const lean_object* l_Array_repr___redArg___closed__7 = (const lean_object*)&l_Array_repr___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instRepr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instRepr(lean_object*, lean_object*);
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__5));
v___x_58_ = l_String_toRawSubstring_x27(v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Array_mkArray0(lean_box(0));
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1(lean_object* v_x_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = ((lean_object*)(l_term_x23_x5b___x2c_x5d___closed__1));
lean_inc(v_x_78_);
v___x_82_ = l_Lean_Syntax_isOfKind(v_x_78_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v_x_78_);
v___x_83_ = lean_box(1);
v___x_84_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v_a_80_);
return v___x_84_;
}
else
{
lean_object* v_quotContext_85_; lean_object* v_currMacroScope_86_; lean_object* v_ref_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_quotContext_85_ = lean_ctor_get(v_a_79_, 1);
v_currMacroScope_86_ = lean_ctor_get(v_a_79_, 2);
v_ref_87_ = lean_ctor_get(v_a_79_, 5);
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = l_Lean_Syntax_getArg(v_x_78_, v___x_88_);
lean_dec(v_x_78_);
v___x_90_ = l_Lean_Syntax_getArgs(v___x_89_);
lean_dec(v___x_89_);
v___x_91_ = 0;
v___x_92_ = l_Lean_SourceInfo_fromRef(v_ref_87_, v___x_91_);
v___x_93_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4));
v___x_94_ = lean_obj_once(&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6, &l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6_once, _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6);
v___x_95_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9));
lean_inc(v_currMacroScope_86_);
lean_inc(v_quotContext_85_);
v___x_96_ = l_Lean_addMacroScope(v_quotContext_85_, v___x_95_, v_currMacroScope_86_);
v___x_97_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__11));
lean_inc_n(v___x_92_, 6);
v___x_98_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_98_, 0, v___x_92_);
lean_ctor_set(v___x_98_, 1, v___x_94_);
lean_ctor_set(v___x_98_, 2, v___x_96_);
lean_ctor_set(v___x_98_, 3, v___x_97_);
v___x_99_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13));
v___x_100_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__15));
v___x_101_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__16));
v___x_102_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_92_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = lean_obj_once(&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17, &l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17_once, _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17);
v___x_104_ = l_Array_appendCore___redArg(v___x_103_, v___x_90_);
lean_dec_ref(v___x_90_);
v___x_105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_105_, 0, v___x_92_);
lean_ctor_set(v___x_105_, 1, v___x_99_);
lean_ctor_set(v___x_105_, 2, v___x_104_);
v___x_106_ = ((lean_object*)(l_term_x23_x5b___x2c_x5d___closed__17));
v___x_107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_92_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = l_Lean_Syntax_node3(v___x_92_, v___x_100_, v___x_102_, v___x_105_, v___x_107_);
v___x_109_ = l_Lean_Syntax_node1(v___x_92_, v___x_99_, v___x_108_);
v___x_110_ = l_Lean_Syntax_node2(v___x_92_, v___x_93_, v___x_98_, v___x_109_);
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_a_80_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___boxed(lean_object* v_x_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1(v_x_112_, v_a_113_, v_a_114_);
lean_dec_ref(v_a_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter___redArg(lean_object* v_x_116_, lean_object* v_x_117_, lean_object* v_h__1_118_, lean_object* v_h__2_119_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
lean_object* v___x_120_; 
lean_dec(v_h__2_119_);
v___x_120_ = lean_apply_1(v_h__1_118_, v_x_117_);
return v___x_120_;
}
else
{
lean_object* v_head_121_; lean_object* v_tail_122_; lean_object* v___x_123_; 
lean_dec(v_h__1_118_);
v_head_121_ = lean_ctor_get(v_x_116_, 0);
lean_inc(v_head_121_);
v_tail_122_ = lean_ctor_get(v_x_116_, 1);
lean_inc(v_tail_122_);
lean_dec_ref_known(v_x_116_, 2);
v___x_123_ = lean_apply_3(v_h__2_119_, v_head_121_, v_tail_122_, v_x_117_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter(lean_object* v_00_u03b1_124_, lean_object* v_motive_125_, lean_object* v_x_126_, lean_object* v_x_127_, lean_object* v_h__1_128_, lean_object* v_h__2_129_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
lean_object* v___x_130_; 
lean_dec(v_h__2_129_);
v___x_130_ = lean_apply_1(v_h__1_128_, v_x_127_);
return v___x_130_;
}
else
{
lean_object* v_head_131_; lean_object* v_tail_132_; lean_object* v___x_133_; 
lean_dec(v_h__1_128_);
v_head_131_ = lean_ctor_get(v_x_126_, 0);
lean_inc(v_head_131_);
v_tail_132_ = lean_ctor_get(v_x_126_, 1);
lean_inc(v_tail_132_);
lean_dec_ref_known(v_x_126_, 2);
v___x_133_ = lean_apply_3(v_h__2_129_, v_head_131_, v_tail_132_, v_x_127_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instMembership(lean_object* v_00_u03b1_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_box(0);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter___redArg(lean_object* v_x_136_, lean_object* v_h__1_137_, lean_object* v_h__2_138_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec(v_h__1_137_);
v___x_139_ = lean_box(0);
v___x_140_ = lean_apply_1(v_h__2_138_, v___x_139_);
return v___x_140_;
}
else
{
lean_object* v_val_141_; lean_object* v___x_142_; 
lean_dec(v_h__2_138_);
v_val_141_ = lean_ctor_get(v_x_136_, 0);
lean_inc(v_val_141_);
lean_dec_ref_known(v_x_136_, 1);
v___x_142_ = lean_apply_1(v_h__1_137_, v_val_141_);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_143_, lean_object* v_motive_144_, lean_object* v_x_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v_h__1_146_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_apply_1(v_h__2_147_, v___x_148_);
return v___x_149_;
}
else
{
lean_object* v_val_150_; lean_object* v___x_151_; 
lean_dec(v_h__2_147_);
v_val_150_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_val_150_);
lean_dec_ref_known(v_x_145_, 1);
v___x_151_ = lean_apply_1(v_h__1_146_, v_val_150_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Array_usize___boxed(lean_object* v_00_u03b1_154_, lean_object* v_xs_155_){
_start:
{
size_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = lean_array_size(v_xs_155_);
lean_dec_ref(v_xs_155_);
v_r_157_ = lean_box_usize(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_Array_uget___boxed(lean_object* v_00_u03b1_162_, lean_object* v_xs_163_, lean_object* v_i_164_, lean_object* v_h_165_){
_start:
{
size_t v_i_boxed_166_; lean_object* v_res_167_; 
v_i_boxed_166_ = lean_unbox_usize(v_i_164_);
lean_dec(v_i_164_);
v_res_167_ = lean_array_uget(v_xs_163_, v_i_boxed_166_);
lean_dec_ref(v_xs_163_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Array_ugetBorrowed___boxed(lean_object* v_00_u03b1_172_, lean_object* v_xs_173_, lean_object* v_i_174_, lean_object* v_h_175_){
_start:
{
size_t v_i_boxed_176_; lean_object* v_res_177_; 
v_i_boxed_176_ = lean_unbox_usize(v_i_174_);
lean_dec(v_i_174_);
v_res_177_ = lean_array_uget_borrowed(v_xs_173_, v_i_boxed_176_);
lean_dec_ref(v_xs_173_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Array_uset___boxed(lean_object* v_00_u03b1_183_, lean_object* v_xs_184_, lean_object* v_i_185_, lean_object* v_v_186_, lean_object* v_h_187_){
_start:
{
size_t v_i_boxed_188_; lean_object* v_res_189_; 
v_i_boxed_188_ = lean_unbox_usize(v_i_185_);
lean_dec(v_i_185_);
v_res_189_ = lean_array_uset(v_xs_184_, v_i_boxed_188_, v_v_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Array_pop___boxed(lean_object* v_00_u03b1_192_, lean_object* v_xs_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = lean_array_pop(v_xs_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Array_replicate___boxed(lean_object* v_00_u03b1_198_, lean_object* v_n_199_, lean_object* v_v_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = lean_mk_array(v_n_199_, v_v_200_);
return v_res_201_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__9(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = ((lean_object*)(l_Array_swap___auto__1___closed__8));
v___x_222_ = l_Lean_mkAtom(v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__10(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_223_ = lean_obj_once(&l_Array_swap___auto__1___closed__9, &l_Array_swap___auto__1___closed__9_once, _init_l_Array_swap___auto__1___closed__9);
v___x_224_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_225_ = lean_array_push(v___x_224_, v___x_223_);
return v___x_225_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__11(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_226_ = lean_obj_once(&l_Array_swap___auto__1___closed__10, &l_Array_swap___auto__1___closed__10_once, _init_l_Array_swap___auto__1___closed__10);
v___x_227_ = ((lean_object*)(l_Array_swap___auto__1___closed__7));
v___x_228_ = lean_box(2);
v___x_229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___x_227_);
lean_ctor_set(v___x_229_, 2, v___x_226_);
return v___x_229_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__12(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_obj_once(&l_Array_swap___auto__1___closed__11, &l_Array_swap___auto__1___closed__11_once, _init_l_Array_swap___auto__1___closed__11);
v___x_231_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_232_ = lean_array_push(v___x_231_, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__13(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_233_ = lean_obj_once(&l_Array_swap___auto__1___closed__12, &l_Array_swap___auto__1___closed__12_once, _init_l_Array_swap___auto__1___closed__12);
v___x_234_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13));
v___x_235_ = lean_box(2);
v___x_236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___x_234_);
lean_ctor_set(v___x_236_, 2, v___x_233_);
return v___x_236_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__14(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_obj_once(&l_Array_swap___auto__1___closed__13, &l_Array_swap___auto__1___closed__13_once, _init_l_Array_swap___auto__1___closed__13);
v___x_238_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_239_ = lean_array_push(v___x_238_, v___x_237_);
return v___x_239_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__15(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_240_ = lean_obj_once(&l_Array_swap___auto__1___closed__14, &l_Array_swap___auto__1___closed__14_once, _init_l_Array_swap___auto__1___closed__14);
v___x_241_ = ((lean_object*)(l_Array_swap___auto__1___closed__5));
v___x_242_ = lean_box(2);
v___x_243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
lean_ctor_set(v___x_243_, 2, v___x_240_);
return v___x_243_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__16(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_Array_swap___auto__1___closed__15, &l_Array_swap___auto__1___closed__15_once, _init_l_Array_swap___auto__1___closed__15);
v___x_245_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_246_ = lean_array_push(v___x_245_, v___x_244_);
return v___x_246_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__17(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_247_ = lean_obj_once(&l_Array_swap___auto__1___closed__16, &l_Array_swap___auto__1___closed__16_once, _init_l_Array_swap___auto__1___closed__16);
v___x_248_ = ((lean_object*)(l_Array_swap___auto__1___closed__2));
v___x_249_ = lean_box(2);
v___x_250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_248_);
lean_ctor_set(v___x_250_, 2, v___x_247_);
return v___x_250_;
}
}
static lean_object* _init_l_Array_swap___auto__1(void){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_251_;
}
}
static lean_object* _init_l_Array_swap___auto__3(void){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Array_swap___boxed(lean_object* v_00_u03b1_259_, lean_object* v_xs_260_, lean_object* v_i_261_, lean_object* v_j_262_, lean_object* v_hi_263_, lean_object* v_hj_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = lean_array_fswap(v_xs_260_, v_i_261_, v_j_262_);
lean_dec(v_j_262_);
lean_dec(v_i_261_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Array_swapIfInBounds___boxed(lean_object* v_00_u03b1_270_, lean_object* v_xs_271_, lean_object* v_i_272_, lean_object* v_j_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = lean_array_swap(v_xs_271_, v_i_272_, v_j_273_);
lean_dec(v_j_273_);
lean_dec(v_i_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___lam__0(lean_object* v_xs_275_, size_t v_i_276_, lean_object* v_h_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_array_uget_borrowed(v_xs_275_, v_i_276_);
lean_inc(v___x_278_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___lam__0___boxed(lean_object* v_xs_279_, lean_object* v_i_280_, lean_object* v_h_281_){
_start:
{
size_t v_i_boxed_282_; lean_object* v_res_283_; 
v_i_boxed_282_ = lean_unbox_usize(v_i_280_);
lean_dec(v_i_280_);
v_res_283_ = l_Array_instGetElemUSizeLtNatToNatSize___lam__0(v_xs_279_, v_i_boxed_282_, v_h_281_);
lean_dec_ref(v_xs_279_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize(lean_object* v_00_u03b1_285_){
_start:
{
lean_object* v___f_286_; 
v___f_286_ = ((lean_object*)(l_Array_instGetElemUSizeLtNatToNatSize___closed__0));
return v___f_286_;
}
}
LEAN_EXPORT lean_object* l_Array_instEmptyCollection(lean_object* v_00_u03b1_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Array_instInhabited(lean_object* v_00_u03b1_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
return v___x_292_;
}
}
LEAN_EXPORT uint8_t l_Array_isEmpty___redArg(lean_object* v_xs_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_294_ = lean_array_get_size(v_xs_293_);
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = lean_nat_dec_eq(v___x_294_, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Array_isEmpty___redArg___boxed(lean_object* v_xs_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = l_Array_isEmpty___redArg(v_xs_297_);
lean_dec_ref(v_xs_297_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT uint8_t l_Array_isEmpty(lean_object* v_00_u03b1_300_, lean_object* v_xs_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_302_ = lean_array_get_size(v_xs_301_);
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = lean_nat_dec_eq(v___x_302_, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Array_isEmpty___boxed(lean_object* v_00_u03b1_305_, lean_object* v_xs_306_){
_start:
{
uint8_t v_res_307_; lean_object* v_r_308_; 
v_res_307_ = l_Array_isEmpty(v_00_u03b1_305_, v_xs_306_);
lean_dec_ref(v_xs_306_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___redArg(lean_object* v_xs_309_, lean_object* v_ys_310_, lean_object* v_p_311_, lean_object* v_x_312_){
_start:
{
lean_object* v_zero_313_; uint8_t v_isZero_314_; 
v_zero_313_ = lean_unsigned_to_nat(0u);
v_isZero_314_ = lean_nat_dec_eq(v_x_312_, v_zero_313_);
if (v_isZero_314_ == 1)
{
lean_dec(v_x_312_);
lean_dec_ref(v_p_311_);
return v_isZero_314_;
}
else
{
lean_object* v_one_315_; lean_object* v_n_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_one_315_ = lean_unsigned_to_nat(1u);
v_n_316_ = lean_nat_sub(v_x_312_, v_one_315_);
lean_dec(v_x_312_);
v___x_317_ = lean_array_fget_borrowed(v_xs_309_, v_n_316_);
v___x_318_ = lean_array_fget_borrowed(v_ys_310_, v_n_316_);
lean_inc_ref(v_p_311_);
lean_inc(v___x_318_);
lean_inc(v___x_317_);
v___x_319_ = lean_apply_2(v_p_311_, v___x_317_, v___x_318_);
v___x_320_ = lean_unbox(v___x_319_);
if (v___x_320_ == 0)
{
uint8_t v___x_321_; 
lean_dec(v_n_316_);
lean_dec_ref(v_p_311_);
v___x_321_ = lean_unbox(v___x_319_);
return v___x_321_;
}
else
{
v_x_312_ = v_n_316_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___redArg___boxed(lean_object* v_xs_323_, lean_object* v_ys_324_, lean_object* v_p_325_, lean_object* v_x_326_){
_start:
{
uint8_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_Array_isEqvAux___redArg(v_xs_323_, v_ys_324_, v_p_325_, v_x_326_);
lean_dec_ref(v_ys_324_);
lean_dec_ref(v_xs_323_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux(lean_object* v_00_u03b1_329_, lean_object* v_xs_330_, lean_object* v_ys_331_, lean_object* v_hsz_332_, lean_object* v_p_333_, lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
uint8_t v___x_336_; 
v___x_336_ = l_Array_isEqvAux___redArg(v_xs_330_, v_ys_331_, v_p_333_, v_x_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___boxed(lean_object* v_00_u03b1_337_, lean_object* v_xs_338_, lean_object* v_ys_339_, lean_object* v_hsz_340_, lean_object* v_p_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_Array_isEqvAux(v_00_u03b1_337_, v_xs_338_, v_ys_339_, v_hsz_340_, v_p_341_, v_x_342_, v_x_343_);
lean_dec_ref(v_ys_339_);
lean_dec_ref(v_xs_338_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqv___redArg(lean_object* v_xs_346_, lean_object* v_ys_347_, lean_object* v_p_348_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_349_ = lean_array_get_size(v_xs_346_);
v___x_350_ = lean_array_get_size(v_ys_347_);
v___x_351_ = lean_nat_dec_eq(v___x_349_, v___x_350_);
if (v___x_351_ == 0)
{
lean_dec_ref(v_p_348_);
return v___x_351_;
}
else
{
uint8_t v___x_352_; 
v___x_352_ = l_Array_isEqvAux___redArg(v_xs_346_, v_ys_347_, v_p_348_, v___x_349_);
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqv___redArg___boxed(lean_object* v_xs_353_, lean_object* v_ys_354_, lean_object* v_p_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_Array_isEqv___redArg(v_xs_353_, v_ys_354_, v_p_355_);
lean_dec_ref(v_ys_354_);
lean_dec_ref(v_xs_353_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqv(lean_object* v_00_u03b1_358_, lean_object* v_xs_359_, lean_object* v_ys_360_, lean_object* v_p_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_362_ = lean_array_get_size(v_xs_359_);
v___x_363_ = lean_array_get_size(v_ys_360_);
v___x_364_ = lean_nat_dec_eq(v___x_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_dec_ref(v_p_361_);
return v___x_364_;
}
else
{
uint8_t v___x_365_; 
v___x_365_ = l_Array_isEqvAux___redArg(v_xs_359_, v_ys_360_, v_p_361_, v___x_362_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqv___boxed(lean_object* v_00_u03b1_366_, lean_object* v_xs_367_, lean_object* v_ys_368_, lean_object* v_p_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l_Array_isEqv(v_00_u03b1_366_, v_xs_367_, v_ys_368_, v_p_369_);
lean_dec_ref(v_ys_368_);
lean_dec_ref(v_xs_367_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT uint8_t l_Array_instBEq___redArg___lam__0(lean_object* v_inst_372_, lean_object* v_xs_373_, lean_object* v_ys_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_375_ = lean_array_get_size(v_xs_373_);
v___x_376_ = lean_array_get_size(v_ys_374_);
v___x_377_ = lean_nat_dec_eq(v___x_375_, v___x_376_);
if (v___x_377_ == 0)
{
lean_dec_ref(v_inst_372_);
return v___x_377_;
}
else
{
uint8_t v___x_378_; 
v___x_378_ = l_Array_isEqvAux___redArg(v_xs_373_, v_ys_374_, v_inst_372_, v___x_375_);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instBEq___redArg___lam__0___boxed(lean_object* v_inst_379_, lean_object* v_xs_380_, lean_object* v_ys_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = l_Array_instBEq___redArg___lam__0(v_inst_379_, v_xs_380_, v_ys_381_);
lean_dec_ref(v_ys_381_);
lean_dec_ref(v_xs_380_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT lean_object* l_Array_instBEq___redArg(lean_object* v_inst_384_){
_start:
{
lean_object* v___f_385_; 
v___f_385_ = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_385_, 0, v_inst_384_);
return v___f_385_;
}
}
LEAN_EXPORT lean_object* l_Array_instBEq(lean_object* v_00_u03b1_386_, lean_object* v_inst_387_){
_start:
{
lean_object* v___f_388_; 
v___f_388_ = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_388_, 0, v_inst_387_);
return v___f_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(lean_object* v_n_389_, lean_object* v_f_390_, lean_object* v_acc_391_, lean_object* v_i_392_){
_start:
{
lean_object* v_zero_393_; uint8_t v_isZero_394_; 
v_zero_393_ = lean_unsigned_to_nat(0u);
v_isZero_394_ = lean_nat_dec_eq(v_i_392_, v_zero_393_);
if (v_isZero_394_ == 1)
{
lean_dec(v_i_392_);
lean_dec(v_f_390_);
return v_acc_391_;
}
else
{
lean_object* v_one_395_; lean_object* v_n_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_one_395_ = lean_unsigned_to_nat(1u);
v_n_396_ = lean_nat_sub(v_i_392_, v_one_395_);
lean_dec(v_i_392_);
v___x_397_ = lean_nat_sub(v_n_389_, v_n_396_);
v___x_398_ = lean_nat_sub(v___x_397_, v_one_395_);
lean_dec(v___x_397_);
lean_inc(v_f_390_);
v___x_399_ = lean_apply_1(v_f_390_, v___x_398_);
v___x_400_ = lean_array_push(v_acc_391_, v___x_399_);
v_acc_391_ = v___x_400_;
v_i_392_ = v_n_396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg___boxed(lean_object* v_n_402_, lean_object* v_f_403_, lean_object* v_acc_404_, lean_object* v_i_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(v_n_402_, v_f_403_, v_acc_404_, v_i_405_);
lean_dec(v_n_402_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go(lean_object* v_00_u03b1_407_, lean_object* v_n_408_, lean_object* v_f_409_, lean_object* v_acc_410_, lean_object* v_i_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(v_n_408_, v_f_409_, v_acc_410_, v_i_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go___boxed(lean_object* v_00_u03b1_414_, lean_object* v_n_415_, lean_object* v_f_416_, lean_object* v_acc_417_, lean_object* v_i_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go(v_00_u03b1_414_, v_n_415_, v_f_416_, v_acc_417_, v_i_418_, v_a_419_);
lean_dec(v_n_415_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn___redArg(lean_object* v_n_421_, lean_object* v_f_422_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_mk_empty_array_with_capacity(v_n_421_);
lean_inc(v_n_421_);
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(v_n_421_, v_f_422_, v___x_423_, v_n_421_);
lean_dec(v_n_421_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn(lean_object* v_00_u03b1_425_, lean_object* v_n_426_, lean_object* v_f_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Array_ofFn___redArg(v_n_426_, v_f_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Array_range___lam__0(lean_object* v_i_429_){
_start:
{
lean_inc(v_i_429_);
return v_i_429_;
}
}
LEAN_EXPORT lean_object* l_Array_range___lam__0___boxed(lean_object* v_i_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Array_range___lam__0(v_i_430_);
lean_dec(v_i_430_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Array_range(lean_object* v_n_433_){
_start:
{
lean_object* v___f_434_; lean_object* v___x_435_; 
v___f_434_ = ((lean_object*)(l_Array_range___closed__0));
v___x_435_ = l_Array_ofFn___redArg(v_n_433_, v___f_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27___lam__0(lean_object* v_step_436_, lean_object* v_start_437_, lean_object* v_i_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_nat_mul(v_step_436_, v_i_438_);
v___x_440_ = lean_nat_add(v_start_437_, v___x_439_);
lean_dec(v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27___lam__0___boxed(lean_object* v_step_441_, lean_object* v_start_442_, lean_object* v_i_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Array_range_x27___lam__0(v_step_441_, v_start_442_, v_i_443_);
lean_dec(v_i_443_);
lean_dec(v_start_442_);
lean_dec(v_step_441_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27(lean_object* v_start_445_, lean_object* v_size_446_, lean_object* v_step_447_){
_start:
{
lean_object* v___f_448_; lean_object* v___x_449_; 
v___f_448_ = lean_alloc_closure((void*)(l_Array_range_x27___lam__0___boxed), 3, 2);
lean_closure_set(v___f_448_, 0, v_step_447_);
lean_closure_set(v___f_448_, 1, v_start_445_);
v___x_449_ = l_Array_ofFn___redArg(v_size_446_, v___f_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Array_singleton___redArg(lean_object* v_v_450_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_mk_empty_array_with_capacity(v___x_451_);
v___x_453_ = lean_array_push(v___x_452_, v_v_450_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Array_singleton(lean_object* v_00_u03b1_454_, lean_object* v_v_455_){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = lean_mk_empty_array_with_capacity(v___x_456_);
v___x_458_ = lean_array_push(v___x_457_, v_v_455_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___redArg(lean_object* v_inst_459_, lean_object* v_xs_460_){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_461_ = lean_array_get_size(v_xs_460_);
v___x_462_ = lean_unsigned_to_nat(1u);
v___x_463_ = lean_nat_sub(v___x_461_, v___x_462_);
v___x_464_ = lean_array_get_borrowed(v_inst_459_, v_xs_460_, v___x_463_);
lean_dec(v___x_463_);
lean_inc(v___x_464_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___redArg___boxed(lean_object* v_inst_465_, lean_object* v_xs_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Array_back_x21___redArg(v_inst_465_, v_xs_466_);
lean_dec_ref(v_xs_466_);
lean_dec(v_inst_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21(lean_object* v_00_u03b1_468_, lean_object* v_inst_469_, lean_object* v_xs_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_471_ = lean_array_get_size(v_xs_470_);
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = lean_nat_sub(v___x_471_, v___x_472_);
v___x_474_ = lean_array_get_borrowed(v_inst_469_, v_xs_470_, v___x_473_);
lean_dec(v___x_473_);
lean_inc(v___x_474_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___boxed(lean_object* v_00_u03b1_475_, lean_object* v_inst_476_, lean_object* v_xs_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Array_back_x21(v_00_u03b1_475_, v_inst_476_, v_xs_477_);
lean_dec_ref(v_xs_477_);
lean_dec(v_inst_476_);
return v_res_478_;
}
}
static lean_object* _init_l_Array_back___auto__1(void){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Array_back___redArg(lean_object* v_xs_480_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_481_ = lean_array_get_size(v_xs_480_);
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_nat_sub(v___x_481_, v___x_482_);
v___x_484_ = lean_array_fget_borrowed(v_xs_480_, v___x_483_);
lean_dec(v___x_483_);
lean_inc(v___x_484_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Array_back___redArg___boxed(lean_object* v_xs_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Array_back___redArg(v_xs_485_);
lean_dec_ref(v_xs_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Array_back(lean_object* v_00_u03b1_487_, lean_object* v_xs_488_, lean_object* v_h_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_490_ = lean_array_get_size(v_xs_488_);
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_nat_sub(v___x_490_, v___x_491_);
v___x_493_ = lean_array_fget_borrowed(v_xs_488_, v___x_492_);
lean_dec(v___x_492_);
lean_inc(v___x_493_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Array_back___boxed(lean_object* v_00_u03b1_494_, lean_object* v_xs_495_, lean_object* v_h_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Array_back(v_00_u03b1_494_, v_xs_495_, v_h_496_);
lean_dec_ref(v_xs_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___redArg(lean_object* v_xs_498_){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_499_ = lean_array_get_size(v_xs_498_);
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_nat_sub(v___x_499_, v___x_500_);
v___x_502_ = lean_nat_dec_lt(v___x_501_, v___x_499_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
lean_dec(v___x_501_);
v___x_503_ = lean_box(0);
return v___x_503_;
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_array_fget_borrowed(v_xs_498_, v___x_501_);
lean_dec(v___x_501_);
lean_inc(v___x_504_);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___redArg___boxed(lean_object* v_xs_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Array_back_x3f___redArg(v_xs_506_);
lean_dec_ref(v_xs_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f(lean_object* v_00_u03b1_508_, lean_object* v_xs_509_){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_510_ = lean_array_get_size(v_xs_509_);
v___x_511_ = lean_unsigned_to_nat(1u);
v___x_512_ = lean_nat_sub(v___x_510_, v___x_511_);
v___x_513_ = lean_nat_dec_lt(v___x_512_, v___x_510_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_dec(v___x_512_);
v___x_514_ = lean_box(0);
return v___x_514_;
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_array_fget_borrowed(v_xs_509_, v___x_512_);
lean_dec(v___x_512_);
lean_inc(v___x_515_);
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___boxed(lean_object* v_00_u03b1_517_, lean_object* v_xs_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Array_back_x3f(v_00_u03b1_517_, v_xs_518_);
lean_dec_ref(v_xs_518_);
return v_res_519_;
}
}
static lean_object* _init_l_Array_swapAt___auto__1(void){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___redArg(lean_object* v_xs_521_, lean_object* v_i_522_, lean_object* v_v_523_){
_start:
{
lean_object* v_e_524_; lean_object* v_xs_x27_525_; lean_object* v___x_526_; 
v_e_524_ = lean_array_fget(v_xs_521_, v_i_522_);
v_xs_x27_525_ = lean_array_fset(v_xs_521_, v_i_522_, v_v_523_);
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v_e_524_);
lean_ctor_set(v___x_526_, 1, v_xs_x27_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___redArg___boxed(lean_object* v_xs_527_, lean_object* v_i_528_, lean_object* v_v_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Array_swapAt___redArg(v_xs_527_, v_i_528_, v_v_529_);
lean_dec(v_i_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt(lean_object* v_00_u03b1_531_, lean_object* v_xs_532_, lean_object* v_i_533_, lean_object* v_v_534_, lean_object* v_hi_535_){
_start:
{
lean_object* v_e_536_; lean_object* v_xs_x27_537_; lean_object* v___x_538_; 
v_e_536_ = lean_array_fget(v_xs_532_, v_i_533_);
v_xs_x27_537_ = lean_array_fset(v_xs_532_, v_i_533_, v_v_534_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v_e_536_);
lean_ctor_set(v___x_538_, 1, v_xs_x27_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___boxed(lean_object* v_00_u03b1_539_, lean_object* v_xs_540_, lean_object* v_i_541_, lean_object* v_v_542_, lean_object* v_hi_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Array_swapAt(v_00_u03b1_539_, v_xs_540_, v_i_541_, v_v_542_, v_hi_543_);
lean_dec(v_i_541_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt_x21___redArg(lean_object* v_xs_549_, lean_object* v_i_550_, lean_object* v_v_551_){
_start:
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = lean_array_get_size(v_xs_549_);
v___x_553_ = lean_nat_dec_lt(v_i_550_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v_this_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_this_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_554_, 0, v_v_551_);
lean_ctor_set(v_this_554_, 1, v_xs_549_);
v___x_555_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_556_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__1));
v___x_557_ = lean_unsigned_to_nat(438u);
v___x_558_ = lean_unsigned_to_nat(4u);
v___x_559_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__2));
v___x_560_ = l_Nat_reprFast(v_i_550_);
v___x_561_ = lean_string_append(v___x_559_, v___x_560_);
lean_dec_ref(v___x_560_);
v___x_562_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__3));
v___x_563_ = lean_string_append(v___x_561_, v___x_562_);
v___x_564_ = l_mkPanicMessageWithDecl(v___x_555_, v___x_556_, v___x_557_, v___x_558_, v___x_563_);
lean_dec_ref(v___x_563_);
v___x_565_ = l_panic___redArg(v_this_554_, v___x_564_);
lean_dec_ref_known(v_this_554_, 2);
return v___x_565_;
}
else
{
lean_object* v_e_566_; lean_object* v_xs_x27_567_; lean_object* v___x_568_; 
v_e_566_ = lean_array_fget(v_xs_549_, v_i_550_);
v_xs_x27_567_ = lean_array_fset(v_xs_549_, v_i_550_, v_v_551_);
lean_dec(v_i_550_);
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v_e_566_);
lean_ctor_set(v___x_568_, 1, v_xs_x27_567_);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l_Array_swapAt_x21(lean_object* v_00_u03b1_569_, lean_object* v_xs_570_, lean_object* v_i_571_, lean_object* v_v_572_){
_start:
{
lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_573_ = lean_array_get_size(v_xs_570_);
v___x_574_ = lean_nat_dec_lt(v_i_571_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v_this_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_this_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_575_, 0, v_v_572_);
lean_ctor_set(v_this_575_, 1, v_xs_570_);
v___x_576_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_577_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__1));
v___x_578_ = lean_unsigned_to_nat(438u);
v___x_579_ = lean_unsigned_to_nat(4u);
v___x_580_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__2));
v___x_581_ = l_Nat_reprFast(v_i_571_);
v___x_582_ = lean_string_append(v___x_580_, v___x_581_);
lean_dec_ref(v___x_581_);
v___x_583_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__3));
v___x_584_ = lean_string_append(v___x_582_, v___x_583_);
v___x_585_ = l_mkPanicMessageWithDecl(v___x_576_, v___x_577_, v___x_578_, v___x_579_, v___x_584_);
lean_dec_ref(v___x_584_);
v___x_586_ = l_panic___redArg(v_this_575_, v___x_585_);
lean_dec_ref_known(v_this_575_, 2);
return v___x_586_;
}
else
{
lean_object* v_e_587_; lean_object* v_xs_x27_588_; lean_object* v___x_589_; 
v_e_587_ = lean_array_fget(v_xs_570_, v_i_571_);
v_xs_x27_588_ = lean_array_fset(v_xs_570_, v_i_571_, v_v_572_);
lean_dec(v_i_571_);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v_e_587_);
lean_ctor_set(v___x_589_, 1, v_xs_x27_588_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
lean_object* v_zero_592_; uint8_t v_isZero_593_; 
v_zero_592_ = lean_unsigned_to_nat(0u);
v_isZero_593_ = lean_nat_dec_eq(v_x_590_, v_zero_592_);
if (v_isZero_593_ == 1)
{
lean_dec(v_x_590_);
return v_x_591_;
}
else
{
lean_object* v_one_594_; lean_object* v_n_595_; lean_object* v___x_596_; 
v_one_594_ = lean_unsigned_to_nat(1u);
v_n_595_ = lean_nat_sub(v_x_590_, v_one_594_);
lean_dec(v_x_590_);
v___x_596_ = lean_array_pop(v_x_591_);
v_x_590_ = v_n_595_;
v_x_591_ = v___x_596_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_shrink_loop(lean_object* v_00_u03b1_598_, lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(v_x_599_, v_x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___redArg(lean_object* v_xs_602_, lean_object* v_n_603_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_array_get_size(v_xs_602_);
v___x_605_ = lean_nat_sub(v___x_604_, v_n_603_);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(v___x_605_, v_xs_602_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___redArg___boxed(lean_object* v_xs_607_, lean_object* v_n_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Array_shrink___redArg(v_xs_607_, v_n_608_);
lean_dec(v_n_608_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink(lean_object* v_00_u03b1_610_, lean_object* v_xs_611_, lean_object* v_n_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Array_shrink___redArg(v_xs_611_, v_n_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___boxed(lean_object* v_00_u03b1_614_, lean_object* v_xs_615_, lean_object* v_n_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Array_shrink(v_00_u03b1_614_, v_xs_615_, v_n_616_);
lean_dec(v_n_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Array_take___redArg(lean_object* v_xs_618_, lean_object* v_i_619_){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = l_Array_extract___redArg(v_xs_618_, v___x_620_, v_i_619_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Array_take___redArg___boxed(lean_object* v_xs_622_, lean_object* v_i_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Array_take___redArg(v_xs_622_, v_i_623_);
lean_dec_ref(v_xs_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Array_take(lean_object* v_00_u03b1_625_, lean_object* v_xs_626_, lean_object* v_i_627_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = l_Array_extract___redArg(v_xs_626_, v___x_628_, v_i_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Array_take___boxed(lean_object* v_00_u03b1_630_, lean_object* v_xs_631_, lean_object* v_i_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Array_take(v_00_u03b1_630_, v_xs_631_, v_i_632_);
lean_dec_ref(v_xs_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___redArg(lean_object* v_xs_634_, lean_object* v_i_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_array_get_size(v_xs_634_);
v___x_637_ = l_Array_extract___redArg(v_xs_634_, v_i_635_, v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___redArg___boxed(lean_object* v_xs_638_, lean_object* v_i_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Array_drop___redArg(v_xs_638_, v_i_639_);
lean_dec_ref(v_xs_638_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Array_drop(lean_object* v_00_u03b1_641_, lean_object* v_xs_642_, lean_object* v_i_643_){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_array_get_size(v_xs_642_);
v___x_645_ = l_Array_extract___redArg(v_xs_642_, v_i_643_, v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___boxed(lean_object* v_00_u03b1_646_, lean_object* v_xs_647_, lean_object* v_i_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Array_drop(v_00_u03b1_646_, v_xs_647_, v_i_648_);
lean_dec_ref(v_xs_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0(lean_object* v_toApplicative_650_, lean_object* v_xs_x27_651_, lean_object* v_i_652_, lean_object* v_v_653_){
_start:
{
lean_object* v_toPure_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_toPure_654_ = lean_ctor_get(v_toApplicative_650_, 1);
lean_inc(v_toPure_654_);
lean_dec_ref(v_toApplicative_650_);
v___x_655_ = lean_array_fset(v_xs_x27_651_, v_i_652_, v_v_653_);
v___x_656_ = lean_apply_2(v_toPure_654_, lean_box(0), v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0___boxed(lean_object* v_toApplicative_657_, lean_object* v_xs_x27_658_, lean_object* v_i_659_, lean_object* v_v_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Array_modifyMUnsafe___redArg___lam__0(v_toApplicative_657_, v_xs_x27_658_, v_i_659_, v_v_660_);
lean_dec(v_i_659_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg(lean_object* v_inst_662_, lean_object* v_xs_663_, lean_object* v_i_664_, lean_object* v_f_665_){
_start:
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_array_get_size(v_xs_663_);
v___x_667_ = lean_nat_dec_lt(v_i_664_, v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v_toApplicative_668_; lean_object* v_toPure_669_; lean_object* v___x_670_; 
lean_dec(v_f_665_);
lean_dec(v_i_664_);
v_toApplicative_668_ = lean_ctor_get(v_inst_662_, 0);
lean_inc_ref(v_toApplicative_668_);
lean_dec_ref(v_inst_662_);
v_toPure_669_ = lean_ctor_get(v_toApplicative_668_, 1);
lean_inc(v_toPure_669_);
lean_dec_ref(v_toApplicative_668_);
v___x_670_ = lean_apply_2(v_toPure_669_, lean_box(0), v_xs_663_);
return v___x_670_;
}
else
{
lean_object* v_toApplicative_671_; lean_object* v_toBind_672_; lean_object* v_v_673_; lean_object* v___x_674_; lean_object* v_xs_x27_675_; lean_object* v___f_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_toApplicative_671_ = lean_ctor_get(v_inst_662_, 0);
lean_inc_ref(v_toApplicative_671_);
v_toBind_672_ = lean_ctor_get(v_inst_662_, 1);
lean_inc(v_toBind_672_);
lean_dec_ref(v_inst_662_);
v_v_673_ = lean_array_fget(v_xs_663_, v_i_664_);
v___x_674_ = lean_box(0);
v_xs_x27_675_ = lean_array_fset(v_xs_663_, v_i_664_, v___x_674_);
v___f_676_ = lean_alloc_closure((void*)(l_Array_modifyMUnsafe___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_676_, 0, v_toApplicative_671_);
lean_closure_set(v___f_676_, 1, v_xs_x27_675_);
lean_closure_set(v___f_676_, 2, v_i_664_);
v___x_677_ = lean_apply_1(v_f_665_, v_v_673_);
v___x_678_ = lean_apply_4(v_toBind_672_, lean_box(0), lean_box(0), v___x_677_, v___f_676_);
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe(lean_object* v_00_u03b1_679_, lean_object* v_m_680_, lean_object* v_inst_681_, lean_object* v_xs_682_, lean_object* v_i_683_, lean_object* v_f_684_){
_start:
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = lean_array_get_size(v_xs_682_);
v___x_686_ = lean_nat_dec_lt(v_i_683_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v_toApplicative_687_; lean_object* v_toPure_688_; lean_object* v___x_689_; 
lean_dec(v_f_684_);
lean_dec(v_i_683_);
v_toApplicative_687_ = lean_ctor_get(v_inst_681_, 0);
lean_inc_ref(v_toApplicative_687_);
lean_dec_ref(v_inst_681_);
v_toPure_688_ = lean_ctor_get(v_toApplicative_687_, 1);
lean_inc(v_toPure_688_);
lean_dec_ref(v_toApplicative_687_);
v___x_689_ = lean_apply_2(v_toPure_688_, lean_box(0), v_xs_682_);
return v___x_689_;
}
else
{
lean_object* v_toApplicative_690_; lean_object* v_toBind_691_; lean_object* v_v_692_; lean_object* v___x_693_; lean_object* v_xs_x27_694_; lean_object* v___f_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_toApplicative_690_ = lean_ctor_get(v_inst_681_, 0);
lean_inc_ref(v_toApplicative_690_);
v_toBind_691_ = lean_ctor_get(v_inst_681_, 1);
lean_inc(v_toBind_691_);
lean_dec_ref(v_inst_681_);
v_v_692_ = lean_array_fget(v_xs_682_, v_i_683_);
v___x_693_ = lean_box(0);
v_xs_x27_694_ = lean_array_fset(v_xs_682_, v_i_683_, v___x_693_);
v___f_695_ = lean_alloc_closure((void*)(l_Array_modifyMUnsafe___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_695_, 0, v_toApplicative_690_);
lean_closure_set(v___f_695_, 1, v_xs_x27_694_);
lean_closure_set(v___f_695_, 2, v_i_683_);
v___x_696_ = lean_apply_1(v_f_684_, v_v_692_);
v___x_697_ = lean_apply_4(v_toBind_691_, lean_box(0), lean_box(0), v___x_696_, v___f_695_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___redArg(lean_object* v_xs_698_, lean_object* v_i_699_, lean_object* v_f_700_){
_start:
{
lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = lean_array_get_size(v_xs_698_);
v___x_702_ = lean_nat_dec_lt(v_i_699_, v___x_701_);
if (v___x_702_ == 0)
{
lean_dec(v_f_700_);
return v_xs_698_;
}
else
{
lean_object* v_v_703_; lean_object* v___x_704_; lean_object* v_xs_x27_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_v_703_ = lean_array_fget(v_xs_698_, v_i_699_);
v___x_704_ = lean_box(0);
v_xs_x27_705_ = lean_array_fset(v_xs_698_, v_i_699_, v___x_704_);
v___x_706_ = lean_apply_1(v_f_700_, v_v_703_);
v___x_707_ = lean_array_fset(v_xs_x27_705_, v_i_699_, v___x_706_);
return v___x_707_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___redArg___boxed(lean_object* v_xs_708_, lean_object* v_i_709_, lean_object* v_f_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Array_modify___redArg(v_xs_708_, v_i_709_, v_f_710_);
lean_dec(v_i_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Array_modify(lean_object* v_00_u03b1_712_, lean_object* v_xs_713_, lean_object* v_i_714_, lean_object* v_f_715_){
_start:
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_array_get_size(v_xs_713_);
v___x_717_ = lean_nat_dec_lt(v_i_714_, v___x_716_);
if (v___x_717_ == 0)
{
lean_dec(v_f_715_);
return v_xs_713_;
}
else
{
lean_object* v_v_718_; lean_object* v___x_719_; lean_object* v_xs_x27_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_v_718_ = lean_array_fget(v_xs_713_, v_i_714_);
v___x_719_ = lean_box(0);
v_xs_x27_720_ = lean_array_fset(v_xs_713_, v_i_714_, v___x_719_);
v___x_721_ = lean_apply_1(v_f_715_, v_v_718_);
v___x_722_ = lean_array_fset(v_xs_x27_720_, v_i_714_, v___x_721_);
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___boxed(lean_object* v_00_u03b1_723_, lean_object* v_xs_724_, lean_object* v_i_725_, lean_object* v_f_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Array_modify(v_00_u03b1_723_, v_xs_724_, v_i_725_, v_f_726_);
lean_dec(v_i_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg(lean_object* v_xs_728_, lean_object* v_idx_729_, lean_object* v_f_730_){
_start:
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = lean_array_get_size(v_xs_728_);
v___x_732_ = lean_nat_dec_lt(v_idx_729_, v___x_731_);
if (v___x_732_ == 0)
{
lean_dec(v_f_730_);
return v_xs_728_;
}
else
{
lean_object* v_v_733_; lean_object* v___x_734_; lean_object* v_xs_x27_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_v_733_ = lean_array_fget(v_xs_728_, v_idx_729_);
v___x_734_ = lean_box(0);
v_xs_x27_735_ = lean_array_fset(v_xs_728_, v_idx_729_, v___x_734_);
v___x_736_ = lean_apply_1(v_f_730_, v_v_733_);
v___x_737_ = lean_array_fset(v_xs_x27_735_, v_idx_729_, v___x_736_);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg___boxed(lean_object* v_xs_738_, lean_object* v_idx_739_, lean_object* v_f_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Array_modifyOp___redArg(v_xs_738_, v_idx_739_, v_f_740_);
lean_dec(v_idx_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp(lean_object* v_00_u03b1_742_, lean_object* v_xs_743_, lean_object* v_idx_744_, lean_object* v_f_745_){
_start:
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_array_get_size(v_xs_743_);
v___x_747_ = lean_nat_dec_lt(v_idx_744_, v___x_746_);
if (v___x_747_ == 0)
{
lean_dec(v_f_745_);
return v_xs_743_;
}
else
{
lean_object* v_v_748_; lean_object* v___x_749_; lean_object* v_xs_x27_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_v_748_ = lean_array_fget(v_xs_743_, v_idx_744_);
v___x_749_ = lean_box(0);
v_xs_x27_750_ = lean_array_fset(v_xs_743_, v_idx_744_, v___x_749_);
v___x_751_ = lean_apply_1(v_f_745_, v_v_748_);
v___x_752_ = lean_array_fset(v_xs_x27_750_, v_idx_744_, v___x_751_);
return v___x_752_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___boxed(lean_object* v_00_u03b1_753_, lean_object* v_xs_754_, lean_object* v_idx_755_, lean_object* v_f_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Array_modifyOp(v_00_u03b1_753_, v_xs_754_, v_idx_755_, v_f_756_);
lean_dec(v_idx_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed(lean_object* v_toApplicative_758_, lean_object* v_i_759_, lean_object* v_inst_760_, lean_object* v_as_761_, lean_object* v_f_762_, lean_object* v_sz_763_, lean_object* v_____do__lift_764_){
_start:
{
size_t v_i_boxed_765_; size_t v_sz_boxed_766_; lean_object* v_res_767_; 
v_i_boxed_765_ = lean_unbox_usize(v_i_759_);
lean_dec(v_i_759_);
v_sz_boxed_766_ = lean_unbox_usize(v_sz_763_);
lean_dec(v_sz_763_);
v_res_767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(v_toApplicative_758_, v_i_boxed_765_, v_inst_760_, v_as_761_, v_f_762_, v_sz_boxed_766_, v_____do__lift_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(lean_object* v_inst_768_, lean_object* v_as_769_, lean_object* v_f_770_, size_t v_sz_771_, size_t v_i_772_, lean_object* v_b_773_){
_start:
{
uint8_t v___x_774_; 
v___x_774_ = lean_usize_dec_lt(v_i_772_, v_sz_771_);
if (v___x_774_ == 0)
{
lean_object* v_toApplicative_775_; lean_object* v_toPure_776_; lean_object* v___x_777_; 
lean_dec(v_f_770_);
lean_dec_ref(v_as_769_);
v_toApplicative_775_ = lean_ctor_get(v_inst_768_, 0);
lean_inc_ref(v_toApplicative_775_);
lean_dec_ref(v_inst_768_);
v_toPure_776_ = lean_ctor_get(v_toApplicative_775_, 1);
lean_inc(v_toPure_776_);
lean_dec_ref(v_toApplicative_775_);
v___x_777_ = lean_apply_2(v_toPure_776_, lean_box(0), v_b_773_);
return v___x_777_;
}
else
{
lean_object* v_toApplicative_778_; lean_object* v_toBind_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___f_782_; lean_object* v_a_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_toApplicative_778_ = lean_ctor_get(v_inst_768_, 0);
lean_inc_ref(v_toApplicative_778_);
v_toBind_779_ = lean_ctor_get(v_inst_768_, 1);
lean_inc(v_toBind_779_);
v___x_780_ = lean_box_usize(v_i_772_);
v___x_781_ = lean_box_usize(v_sz_771_);
lean_inc(v_f_770_);
lean_inc_ref(v_as_769_);
v___f_782_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_782_, 0, v_toApplicative_778_);
lean_closure_set(v___f_782_, 1, v___x_780_);
lean_closure_set(v___f_782_, 2, v_inst_768_);
lean_closure_set(v___f_782_, 3, v_as_769_);
lean_closure_set(v___f_782_, 4, v_f_770_);
lean_closure_set(v___f_782_, 5, v___x_781_);
v_a_783_ = lean_array_uget(v_as_769_, v_i_772_);
lean_dec_ref(v_as_769_);
v___x_784_ = lean_apply_3(v_f_770_, v_a_783_, lean_box(0), v_b_773_);
v___x_785_ = lean_apply_4(v_toBind_779_, lean_box(0), lean_box(0), v___x_784_, v___f_782_);
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(lean_object* v_toApplicative_786_, size_t v_i_787_, lean_object* v_inst_788_, lean_object* v_as_789_, lean_object* v_f_790_, size_t v_sz_791_, lean_object* v_____do__lift_792_){
_start:
{
if (lean_obj_tag(v_____do__lift_792_) == 0)
{
lean_object* v_a_793_; lean_object* v_toPure_794_; lean_object* v___x_795_; 
lean_dec(v_f_790_);
lean_dec_ref(v_as_789_);
lean_dec_ref(v_inst_788_);
v_a_793_ = lean_ctor_get(v_____do__lift_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v_____do__lift_792_, 1);
v_toPure_794_ = lean_ctor_get(v_toApplicative_786_, 1);
lean_inc(v_toPure_794_);
lean_dec_ref(v_toApplicative_786_);
v___x_795_ = lean_apply_2(v_toPure_794_, lean_box(0), v_a_793_);
return v___x_795_;
}
else
{
lean_object* v_a_796_; size_t v___x_797_; size_t v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v_toApplicative_786_);
v_a_796_ = lean_ctor_get(v_____do__lift_792_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v_____do__lift_792_, 1);
v___x_797_ = ((size_t)1ULL);
v___x_798_ = lean_usize_add(v_i_787_, v___x_797_);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_788_, v_as_789_, v_f_790_, v_sz_791_, v___x_798_, v_a_796_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___boxed(lean_object* v_inst_800_, lean_object* v_as_801_, lean_object* v_f_802_, lean_object* v_sz_803_, lean_object* v_i_804_, lean_object* v_b_805_){
_start:
{
size_t v_sz_boxed_806_; size_t v_i_boxed_807_; lean_object* v_res_808_; 
v_sz_boxed_806_ = lean_unbox_usize(v_sz_803_);
lean_dec(v_sz_803_);
v_i_boxed_807_ = lean_unbox_usize(v_i_804_);
lean_dec(v_i_804_);
v_res_808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_800_, v_as_801_, v_f_802_, v_sz_boxed_806_, v_i_boxed_807_, v_b_805_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object* v_00_u03b1_809_, lean_object* v_00_u03b2_810_, lean_object* v_m_811_, lean_object* v_inst_812_, lean_object* v_as_813_, lean_object* v_f_814_, size_t v_sz_815_, size_t v_i_816_, lean_object* v_b_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_812_, v_as_813_, v_f_814_, v_sz_815_, v_i_816_, v_b_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___boxed(lean_object* v_00_u03b1_819_, lean_object* v_00_u03b2_820_, lean_object* v_m_821_, lean_object* v_inst_822_, lean_object* v_as_823_, lean_object* v_f_824_, lean_object* v_sz_825_, lean_object* v_i_826_, lean_object* v_b_827_){
_start:
{
size_t v_sz_boxed_828_; size_t v_i_boxed_829_; lean_object* v_res_830_; 
v_sz_boxed_828_ = lean_unbox_usize(v_sz_825_);
lean_dec(v_sz_825_);
v_i_boxed_829_ = lean_unbox_usize(v_i_826_);
lean_dec(v_i_826_);
v_res_830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(v_00_u03b1_819_, v_00_u03b2_820_, v_m_821_, v_inst_822_, v_as_823_, v_f_824_, v_sz_boxed_828_, v_i_boxed_829_, v_b_827_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe___redArg(lean_object* v_inst_831_, lean_object* v_as_832_, lean_object* v_b_833_, lean_object* v_f_834_){
_start:
{
size_t v_sz_835_; size_t v___x_836_; lean_object* v___x_837_; 
v_sz_835_ = lean_array_size(v_as_832_);
v___x_836_ = ((size_t)0ULL);
v___x_837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_831_, v_as_832_, v_f_834_, v_sz_835_, v___x_836_, v_b_833_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe(lean_object* v_00_u03b1_838_, lean_object* v_00_u03b2_839_, lean_object* v_m_840_, lean_object* v_inst_841_, lean_object* v_as_842_, lean_object* v_b_843_, lean_object* v_f_844_){
_start:
{
size_t v_sz_845_; size_t v___x_846_; lean_object* v___x_847_; 
v_sz_845_ = lean_array_size(v_as_842_);
v___x_846_ = ((size_t)0ULL);
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_841_, v_as_842_, v_f_844_, v_sz_845_, v___x_846_, v_b_843_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0___boxed(lean_object* v_toPure_848_, lean_object* v_inst_849_, lean_object* v_as_850_, lean_object* v_f_851_, lean_object* v_n_852_, lean_object* v_____do__lift_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Array_forIn_x27_loop___redArg___lam__0(v_toPure_848_, v_inst_849_, v_as_850_, v_f_851_, v_n_852_, v_____do__lift_853_);
lean_dec(v_n_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg(lean_object* v_inst_855_, lean_object* v_as_856_, lean_object* v_f_857_, lean_object* v_i_858_, lean_object* v_b_859_){
_start:
{
lean_object* v_toApplicative_860_; lean_object* v_toBind_861_; lean_object* v_toPure_862_; lean_object* v_zero_863_; uint8_t v_isZero_864_; 
v_toApplicative_860_ = lean_ctor_get(v_inst_855_, 0);
v_toBind_861_ = lean_ctor_get(v_inst_855_, 1);
lean_inc(v_toBind_861_);
v_toPure_862_ = lean_ctor_get(v_toApplicative_860_, 1);
lean_inc(v_toPure_862_);
v_zero_863_ = lean_unsigned_to_nat(0u);
v_isZero_864_ = lean_nat_dec_eq(v_i_858_, v_zero_863_);
if (v_isZero_864_ == 1)
{
lean_object* v___x_865_; 
lean_dec(v_toBind_861_);
lean_dec(v_f_857_);
lean_dec_ref(v_as_856_);
lean_dec_ref(v_inst_855_);
v___x_865_ = lean_apply_2(v_toPure_862_, lean_box(0), v_b_859_);
return v___x_865_;
}
else
{
lean_object* v_one_866_; lean_object* v_n_867_; lean_object* v___f_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_one_866_ = lean_unsigned_to_nat(1u);
v_n_867_ = lean_nat_sub(v_i_858_, v_one_866_);
lean_inc(v_n_867_);
lean_inc(v_f_857_);
lean_inc_ref(v_as_856_);
v___f_868_ = lean_alloc_closure((void*)(l_Array_forIn_x27_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_868_, 0, v_toPure_862_);
lean_closure_set(v___f_868_, 1, v_inst_855_);
lean_closure_set(v___f_868_, 2, v_as_856_);
lean_closure_set(v___f_868_, 3, v_f_857_);
lean_closure_set(v___f_868_, 4, v_n_867_);
v___x_869_ = lean_array_get_size(v_as_856_);
v___x_870_ = lean_nat_sub(v___x_869_, v_one_866_);
v___x_871_ = lean_nat_sub(v___x_870_, v_n_867_);
lean_dec(v_n_867_);
lean_dec(v___x_870_);
v___x_872_ = lean_array_fget(v_as_856_, v___x_871_);
lean_dec(v___x_871_);
lean_dec_ref(v_as_856_);
v___x_873_ = lean_apply_3(v_f_857_, v___x_872_, lean_box(0), v_b_859_);
v___x_874_ = lean_apply_4(v_toBind_861_, lean_box(0), lean_box(0), v___x_873_, v___f_868_);
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0(lean_object* v_toPure_875_, lean_object* v_inst_876_, lean_object* v_as_877_, lean_object* v_f_878_, lean_object* v_n_879_, lean_object* v_____do__lift_880_){
_start:
{
if (lean_obj_tag(v_____do__lift_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_882_; 
lean_dec(v_f_878_);
lean_dec_ref(v_as_877_);
lean_dec_ref(v_inst_876_);
v_a_881_ = lean_ctor_get(v_____do__lift_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v_____do__lift_880_, 1);
v___x_882_ = lean_apply_2(v_toPure_875_, lean_box(0), v_a_881_);
return v___x_882_;
}
else
{
lean_object* v_a_883_; lean_object* v___x_884_; 
lean_dec(v_toPure_875_);
v_a_883_ = lean_ctor_get(v_____do__lift_880_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v_____do__lift_880_, 1);
v___x_884_ = l_Array_forIn_x27_loop___redArg(v_inst_876_, v_as_877_, v_f_878_, v_n_879_, v_a_883_);
return v___x_884_;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___boxed(lean_object* v_inst_885_, lean_object* v_as_886_, lean_object* v_f_887_, lean_object* v_i_888_, lean_object* v_b_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Array_forIn_x27_loop___redArg(v_inst_885_, v_as_886_, v_f_887_, v_i_888_, v_b_889_);
lean_dec(v_i_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop(lean_object* v_00_u03b1_891_, lean_object* v_00_u03b2_892_, lean_object* v_m_893_, lean_object* v_inst_894_, lean_object* v_as_895_, lean_object* v_f_896_, lean_object* v_i_897_, lean_object* v_h_898_, lean_object* v_b_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Array_forIn_x27_loop___redArg(v_inst_894_, v_as_895_, v_f_896_, v_i_897_, v_b_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___boxed(lean_object* v_00_u03b1_901_, lean_object* v_00_u03b2_902_, lean_object* v_m_903_, lean_object* v_inst_904_, lean_object* v_as_905_, lean_object* v_f_906_, lean_object* v_i_907_, lean_object* v_h_908_, lean_object* v_b_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Array_forIn_x27_loop(v_00_u03b1_901_, v_00_u03b2_902_, v_m_903_, v_inst_904_, v_as_905_, v_f_906_, v_i_907_, v_h_908_, v_b_909_);
lean_dec(v_i_907_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_inst_911_, lean_object* v_00_u03b2_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
size_t v_sz_916_; size_t v___x_917_; lean_object* v___x_918_; 
v_sz_916_ = lean_array_size(v___y_913_);
v___x_917_ = ((size_t)0ULL);
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_911_, v___y_913_, v___y_915_, v_sz_916_, v___x_917_, v___y_914_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_919_){
_start:
{
lean_object* v___f_920_; 
v___f_920_ = lean_alloc_closure((void*)(l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_920_, 0, v_inst_919_);
return v___f_920_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_00_u03b1_921_, lean_object* v_m_922_, lean_object* v_inst_923_){
_start:
{
lean_object* v___f_924_; 
v___f_924_ = lean_alloc_closure((void*)(l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_924_, 0, v_inst_923_);
return v___f_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_925_, lean_object* v_inst_926_, lean_object* v_f_927_, lean_object* v_as_928_, lean_object* v_stop_929_, lean_object* v_____do__lift_930_){
_start:
{
size_t v_i_boxed_931_; size_t v_stop_boxed_932_; lean_object* v_res_933_; 
v_i_boxed_931_ = lean_unbox_usize(v_i_925_);
lean_dec(v_i_925_);
v_stop_boxed_932_ = lean_unbox_usize(v_stop_929_);
lean_dec(v_stop_929_);
v_res_933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_931_, v_inst_926_, v_f_927_, v_as_928_, v_stop_boxed_932_, v_____do__lift_930_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(lean_object* v_inst_934_, lean_object* v_f_935_, lean_object* v_as_936_, size_t v_i_937_, size_t v_stop_938_, lean_object* v_b_939_){
_start:
{
uint8_t v___x_940_; 
v___x_940_ = lean_usize_dec_eq(v_i_937_, v_stop_938_);
if (v___x_940_ == 0)
{
lean_object* v_toBind_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___f_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_toBind_941_ = lean_ctor_get(v_inst_934_, 1);
lean_inc(v_toBind_941_);
v___x_942_ = lean_box_usize(v_i_937_);
v___x_943_ = lean_box_usize(v_stop_938_);
lean_inc_ref(v_as_936_);
lean_inc(v_f_935_);
v___f_944_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_944_, 0, v___x_942_);
lean_closure_set(v___f_944_, 1, v_inst_934_);
lean_closure_set(v___f_944_, 2, v_f_935_);
lean_closure_set(v___f_944_, 3, v_as_936_);
lean_closure_set(v___f_944_, 4, v___x_943_);
v___x_945_ = lean_array_uget(v_as_936_, v_i_937_);
lean_dec_ref(v_as_936_);
v___x_946_ = lean_apply_2(v_f_935_, v_b_939_, v___x_945_);
v___x_947_ = lean_apply_4(v_toBind_941_, lean_box(0), lean_box(0), v___x_946_, v___f_944_);
return v___x_947_;
}
else
{
lean_object* v_toApplicative_948_; lean_object* v_toPure_949_; lean_object* v___x_950_; 
lean_dec_ref(v_as_936_);
lean_dec(v_f_935_);
v_toApplicative_948_ = lean_ctor_get(v_inst_934_, 0);
lean_inc_ref(v_toApplicative_948_);
lean_dec_ref(v_inst_934_);
v_toPure_949_ = lean_ctor_get(v_toApplicative_948_, 1);
lean_inc(v_toPure_949_);
lean_dec_ref(v_toApplicative_948_);
v___x_950_ = lean_apply_2(v_toPure_949_, lean_box(0), v_b_939_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_951_, lean_object* v_inst_952_, lean_object* v_f_953_, lean_object* v_as_954_, size_t v_stop_955_, lean_object* v_____do__lift_956_){
_start:
{
size_t v___x_957_; size_t v___x_958_; lean_object* v___x_959_; 
v___x_957_ = ((size_t)1ULL);
v___x_958_ = lean_usize_add(v_i_951_, v___x_957_);
v___x_959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_952_, v_f_953_, v_as_954_, v___x_958_, v_stop_955_, v_____do__lift_956_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_960_, lean_object* v_f_961_, lean_object* v_as_962_, lean_object* v_i_963_, lean_object* v_stop_964_, lean_object* v_b_965_){
_start:
{
size_t v_i_boxed_966_; size_t v_stop_boxed_967_; lean_object* v_res_968_; 
v_i_boxed_966_ = lean_unbox_usize(v_i_963_);
lean_dec(v_i_963_);
v_stop_boxed_967_ = lean_unbox_usize(v_stop_964_);
lean_dec(v_stop_964_);
v_res_968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_960_, v_f_961_, v_as_962_, v_i_boxed_966_, v_stop_boxed_967_, v_b_965_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object* v_00_u03b1_969_, lean_object* v_00_u03b2_970_, lean_object* v_m_971_, lean_object* v_inst_972_, lean_object* v_f_973_, lean_object* v_as_974_, size_t v_i_975_, size_t v_stop_976_, lean_object* v_b_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_972_, v_f_973_, v_as_974_, v_i_975_, v_stop_976_, v_b_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b1_979_, lean_object* v_00_u03b2_980_, lean_object* v_m_981_, lean_object* v_inst_982_, lean_object* v_f_983_, lean_object* v_as_984_, lean_object* v_i_985_, lean_object* v_stop_986_, lean_object* v_b_987_){
_start:
{
size_t v_i_boxed_988_; size_t v_stop_boxed_989_; lean_object* v_res_990_; 
v_i_boxed_988_ = lean_unbox_usize(v_i_985_);
lean_dec(v_i_985_);
v_stop_boxed_989_ = lean_unbox_usize(v_stop_986_);
lean_dec(v_stop_986_);
v_res_990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(v_00_u03b1_979_, v_00_u03b2_980_, v_m_981_, v_inst_982_, v_f_983_, v_as_984_, v_i_boxed_988_, v_stop_boxed_989_, v_b_987_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg(lean_object* v_inst_991_, lean_object* v_f_992_, lean_object* v_init_993_, lean_object* v_as_994_, lean_object* v_start_995_, lean_object* v_stop_996_){
_start:
{
uint8_t v___x_997_; 
v___x_997_ = lean_nat_dec_lt(v_start_995_, v_stop_996_);
if (v___x_997_ == 0)
{
lean_object* v_toApplicative_998_; lean_object* v_toPure_999_; lean_object* v___x_1000_; 
lean_dec_ref(v_as_994_);
lean_dec(v_f_992_);
v_toApplicative_998_ = lean_ctor_get(v_inst_991_, 0);
lean_inc_ref(v_toApplicative_998_);
lean_dec_ref(v_inst_991_);
v_toPure_999_ = lean_ctor_get(v_toApplicative_998_, 1);
lean_inc(v_toPure_999_);
lean_dec_ref(v_toApplicative_998_);
v___x_1000_ = lean_apply_2(v_toPure_999_, lean_box(0), v_init_993_);
return v___x_1000_;
}
else
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = lean_array_get_size(v_as_994_);
v___x_1002_ = lean_nat_dec_le(v_stop_996_, v___x_1001_);
if (v___x_1002_ == 0)
{
uint8_t v___x_1003_; 
v___x_1003_ = lean_nat_dec_lt(v_start_995_, v___x_1001_);
if (v___x_1003_ == 0)
{
lean_object* v_toApplicative_1004_; lean_object* v_toPure_1005_; lean_object* v___x_1006_; 
lean_dec_ref(v_as_994_);
lean_dec(v_f_992_);
v_toApplicative_1004_ = lean_ctor_get(v_inst_991_, 0);
lean_inc_ref(v_toApplicative_1004_);
lean_dec_ref(v_inst_991_);
v_toPure_1005_ = lean_ctor_get(v_toApplicative_1004_, 1);
lean_inc(v_toPure_1005_);
lean_dec_ref(v_toApplicative_1004_);
v___x_1006_ = lean_apply_2(v_toPure_1005_, lean_box(0), v_init_993_);
return v___x_1006_;
}
else
{
size_t v___x_1007_; size_t v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = lean_usize_of_nat(v_start_995_);
v___x_1008_ = lean_usize_of_nat(v___x_1001_);
v___x_1009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_991_, v_f_992_, v_as_994_, v___x_1007_, v___x_1008_, v_init_993_);
return v___x_1009_;
}
}
else
{
size_t v___x_1010_; size_t v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_usize_of_nat(v_start_995_);
v___x_1011_ = lean_usize_of_nat(v_stop_996_);
v___x_1012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_991_, v_f_992_, v_as_994_, v___x_1010_, v___x_1011_, v_init_993_);
return v___x_1012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg___boxed(lean_object* v_inst_1013_, lean_object* v_f_1014_, lean_object* v_init_1015_, lean_object* v_as_1016_, lean_object* v_start_1017_, lean_object* v_stop_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Array_foldlMUnsafe___redArg(v_inst_1013_, v_f_1014_, v_init_1015_, v_as_1016_, v_start_1017_, v_stop_1018_);
lean_dec(v_stop_1018_);
lean_dec(v_start_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe(lean_object* v_00_u03b1_1020_, lean_object* v_00_u03b2_1021_, lean_object* v_m_1022_, lean_object* v_inst_1023_, lean_object* v_f_1024_, lean_object* v_init_1025_, lean_object* v_as_1026_, lean_object* v_start_1027_, lean_object* v_stop_1028_){
_start:
{
uint8_t v___x_1029_; 
v___x_1029_ = lean_nat_dec_lt(v_start_1027_, v_stop_1028_);
if (v___x_1029_ == 0)
{
lean_object* v_toApplicative_1030_; lean_object* v_toPure_1031_; lean_object* v___x_1032_; 
lean_dec_ref(v_as_1026_);
lean_dec(v_f_1024_);
v_toApplicative_1030_ = lean_ctor_get(v_inst_1023_, 0);
lean_inc_ref(v_toApplicative_1030_);
lean_dec_ref(v_inst_1023_);
v_toPure_1031_ = lean_ctor_get(v_toApplicative_1030_, 1);
lean_inc(v_toPure_1031_);
lean_dec_ref(v_toApplicative_1030_);
v___x_1032_ = lean_apply_2(v_toPure_1031_, lean_box(0), v_init_1025_);
return v___x_1032_;
}
else
{
lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1033_ = lean_array_get_size(v_as_1026_);
v___x_1034_ = lean_nat_dec_le(v_stop_1028_, v___x_1033_);
if (v___x_1034_ == 0)
{
uint8_t v___x_1035_; 
v___x_1035_ = lean_nat_dec_lt(v_start_1027_, v___x_1033_);
if (v___x_1035_ == 0)
{
lean_object* v_toApplicative_1036_; lean_object* v_toPure_1037_; lean_object* v___x_1038_; 
lean_dec_ref(v_as_1026_);
lean_dec(v_f_1024_);
v_toApplicative_1036_ = lean_ctor_get(v_inst_1023_, 0);
lean_inc_ref(v_toApplicative_1036_);
lean_dec_ref(v_inst_1023_);
v_toPure_1037_ = lean_ctor_get(v_toApplicative_1036_, 1);
lean_inc(v_toPure_1037_);
lean_dec_ref(v_toApplicative_1036_);
v___x_1038_ = lean_apply_2(v_toPure_1037_, lean_box(0), v_init_1025_);
return v___x_1038_;
}
else
{
size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = lean_usize_of_nat(v_start_1027_);
v___x_1040_ = lean_usize_of_nat(v___x_1033_);
v___x_1041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1023_, v_f_1024_, v_as_1026_, v___x_1039_, v___x_1040_, v_init_1025_);
return v___x_1041_;
}
}
else
{
size_t v___x_1042_; size_t v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = lean_usize_of_nat(v_start_1027_);
v___x_1043_ = lean_usize_of_nat(v_stop_1028_);
v___x_1044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1023_, v_f_1024_, v_as_1026_, v___x_1042_, v___x_1043_, v_init_1025_);
return v___x_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___boxed(lean_object* v_00_u03b1_1045_, lean_object* v_00_u03b2_1046_, lean_object* v_m_1047_, lean_object* v_inst_1048_, lean_object* v_f_1049_, lean_object* v_init_1050_, lean_object* v_as_1051_, lean_object* v_start_1052_, lean_object* v_stop_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Array_foldlMUnsafe(v_00_u03b1_1045_, v_00_u03b2_1046_, v_m_1047_, v_inst_1048_, v_f_1049_, v_init_1050_, v_as_1051_, v_start_1052_, v_stop_1053_);
lean_dec(v_stop_1053_);
lean_dec(v_start_1052_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_1055_, lean_object* v_inst_1056_, lean_object* v_f_1057_, lean_object* v_as_1058_, lean_object* v_stop_1059_, lean_object* v_n_1060_, lean_object* v_____do__lift_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Array_foldlM_loop___redArg___lam__0(v_j_1055_, v_inst_1056_, v_f_1057_, v_as_1058_, v_stop_1059_, v_n_1060_, v_____do__lift_1061_);
lean_dec(v_n_1060_);
lean_dec(v_j_1055_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg(lean_object* v_inst_1063_, lean_object* v_f_1064_, lean_object* v_as_1065_, lean_object* v_stop_1066_, lean_object* v_i_1067_, lean_object* v_j_1068_, lean_object* v_b_1069_){
_start:
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_nat_dec_lt(v_j_1068_, v_stop_1066_);
if (v___x_1070_ == 0)
{
lean_object* v_toApplicative_1071_; lean_object* v_toPure_1072_; lean_object* v___x_1073_; 
lean_dec(v_j_1068_);
lean_dec(v_stop_1066_);
lean_dec_ref(v_as_1065_);
lean_dec(v_f_1064_);
v_toApplicative_1071_ = lean_ctor_get(v_inst_1063_, 0);
lean_inc_ref(v_toApplicative_1071_);
lean_dec_ref(v_inst_1063_);
v_toPure_1072_ = lean_ctor_get(v_toApplicative_1071_, 1);
lean_inc(v_toPure_1072_);
lean_dec_ref(v_toApplicative_1071_);
v___x_1073_ = lean_apply_2(v_toPure_1072_, lean_box(0), v_b_1069_);
return v___x_1073_;
}
else
{
lean_object* v_zero_1074_; uint8_t v_isZero_1075_; 
v_zero_1074_ = lean_unsigned_to_nat(0u);
v_isZero_1075_ = lean_nat_dec_eq(v_i_1067_, v_zero_1074_);
if (v_isZero_1075_ == 1)
{
lean_object* v_toApplicative_1076_; lean_object* v_toPure_1077_; lean_object* v___x_1078_; 
lean_dec(v_j_1068_);
lean_dec(v_stop_1066_);
lean_dec_ref(v_as_1065_);
lean_dec(v_f_1064_);
v_toApplicative_1076_ = lean_ctor_get(v_inst_1063_, 0);
lean_inc_ref(v_toApplicative_1076_);
lean_dec_ref(v_inst_1063_);
v_toPure_1077_ = lean_ctor_get(v_toApplicative_1076_, 1);
lean_inc(v_toPure_1077_);
lean_dec_ref(v_toApplicative_1076_);
v___x_1078_ = lean_apply_2(v_toPure_1077_, lean_box(0), v_b_1069_);
return v___x_1078_;
}
else
{
lean_object* v_toBind_1079_; lean_object* v_one_1080_; lean_object* v_n_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_toBind_1079_ = lean_ctor_get(v_inst_1063_, 1);
lean_inc(v_toBind_1079_);
v_one_1080_ = lean_unsigned_to_nat(1u);
v_n_1081_ = lean_nat_sub(v_i_1067_, v_one_1080_);
lean_inc_ref(v_as_1065_);
lean_inc(v_f_1064_);
lean_inc(v_j_1068_);
v___f_1082_ = lean_alloc_closure((void*)(l_Array_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1082_, 0, v_j_1068_);
lean_closure_set(v___f_1082_, 1, v_inst_1063_);
lean_closure_set(v___f_1082_, 2, v_f_1064_);
lean_closure_set(v___f_1082_, 3, v_as_1065_);
lean_closure_set(v___f_1082_, 4, v_stop_1066_);
lean_closure_set(v___f_1082_, 5, v_n_1081_);
v___x_1083_ = lean_array_fget(v_as_1065_, v_j_1068_);
lean_dec(v_j_1068_);
lean_dec_ref(v_as_1065_);
v___x_1084_ = lean_apply_2(v_f_1064_, v_b_1069_, v___x_1083_);
v___x_1085_ = lean_apply_4(v_toBind_1079_, lean_box(0), lean_box(0), v___x_1084_, v___f_1082_);
return v___x_1085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0(lean_object* v_j_1086_, lean_object* v_inst_1087_, lean_object* v_f_1088_, lean_object* v_as_1089_, lean_object* v_stop_1090_, lean_object* v_n_1091_, lean_object* v_____do__lift_1092_){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_add(v_j_1086_, v___x_1093_);
v___x_1095_ = l_Array_foldlM_loop___redArg(v_inst_1087_, v_f_1088_, v_as_1089_, v_stop_1090_, v_n_1091_, v___x_1094_, v_____do__lift_1092_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___boxed(lean_object* v_inst_1096_, lean_object* v_f_1097_, lean_object* v_as_1098_, lean_object* v_stop_1099_, lean_object* v_i_1100_, lean_object* v_j_1101_, lean_object* v_b_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Array_foldlM_loop___redArg(v_inst_1096_, v_f_1097_, v_as_1098_, v_stop_1099_, v_i_1100_, v_j_1101_, v_b_1102_);
lean_dec(v_i_1100_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_m_1106_, lean_object* v_inst_1107_, lean_object* v_f_1108_, lean_object* v_as_1109_, lean_object* v_stop_1110_, lean_object* v_h_1111_, lean_object* v_i_1112_, lean_object* v_j_1113_, lean_object* v_b_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Array_foldlM_loop___redArg(v_inst_1107_, v_f_1108_, v_as_1109_, v_stop_1110_, v_i_1112_, v_j_1113_, v_b_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___boxed(lean_object* v_00_u03b1_1116_, lean_object* v_00_u03b2_1117_, lean_object* v_m_1118_, lean_object* v_inst_1119_, lean_object* v_f_1120_, lean_object* v_as_1121_, lean_object* v_stop_1122_, lean_object* v_h_1123_, lean_object* v_i_1124_, lean_object* v_j_1125_, lean_object* v_b_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Array_foldlM_loop(v_00_u03b1_1116_, v_00_u03b2_1117_, v_m_1118_, v_inst_1119_, v_f_1120_, v_as_1121_, v_stop_1122_, v_h_1123_, v_i_1124_, v_j_1125_, v_b_1126_);
lean_dec(v_i_1124_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_inst_1128_, lean_object* v_f_1129_, lean_object* v_as_1130_, lean_object* v___x_1131_, lean_object* v_stop_1132_, lean_object* v_____do__lift_1133_){
_start:
{
size_t v___x_94__boxed_1134_; size_t v_stop_boxed_1135_; lean_object* v_res_1136_; 
v___x_94__boxed_1134_ = lean_unbox_usize(v___x_1131_);
lean_dec(v___x_1131_);
v_stop_boxed_1135_ = lean_unbox_usize(v_stop_1132_);
lean_dec(v_stop_1132_);
v_res_1136_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(v_inst_1128_, v_f_1129_, v_as_1130_, v___x_94__boxed_1134_, v_stop_boxed_1135_, v_____do__lift_1133_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(lean_object* v_inst_1137_, lean_object* v_f_1138_, lean_object* v_as_1139_, size_t v_i_1140_, size_t v_stop_1141_, lean_object* v_b_1142_){
_start:
{
uint8_t v___x_1143_; 
v___x_1143_ = lean_usize_dec_eq(v_i_1140_, v_stop_1141_);
if (v___x_1143_ == 0)
{
lean_object* v_toBind_1144_; size_t v___x_1145_; size_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___f_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_toBind_1144_ = lean_ctor_get(v_inst_1137_, 1);
lean_inc(v_toBind_1144_);
v___x_1145_ = ((size_t)1ULL);
v___x_1146_ = lean_usize_sub(v_i_1140_, v___x_1145_);
v___x_1147_ = lean_box_usize(v___x_1146_);
v___x_1148_ = lean_box_usize(v_stop_1141_);
lean_inc_ref(v_as_1139_);
lean_inc(v_f_1138_);
v___f_1149_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1149_, 0, v_inst_1137_);
lean_closure_set(v___f_1149_, 1, v_f_1138_);
lean_closure_set(v___f_1149_, 2, v_as_1139_);
lean_closure_set(v___f_1149_, 3, v___x_1147_);
lean_closure_set(v___f_1149_, 4, v___x_1148_);
v___x_1150_ = lean_array_uget(v_as_1139_, v___x_1146_);
lean_dec_ref(v_as_1139_);
v___x_1151_ = lean_apply_2(v_f_1138_, v___x_1150_, v_b_1142_);
v___x_1152_ = lean_apply_4(v_toBind_1144_, lean_box(0), lean_box(0), v___x_1151_, v___f_1149_);
return v___x_1152_;
}
else
{
lean_object* v_toApplicative_1153_; lean_object* v_toPure_1154_; lean_object* v___x_1155_; 
lean_dec_ref(v_as_1139_);
lean_dec(v_f_1138_);
v_toApplicative_1153_ = lean_ctor_get(v_inst_1137_, 0);
lean_inc_ref(v_toApplicative_1153_);
lean_dec_ref(v_inst_1137_);
v_toPure_1154_ = lean_ctor_get(v_toApplicative_1153_, 1);
lean_inc(v_toPure_1154_);
lean_dec_ref(v_toApplicative_1153_);
v___x_1155_ = lean_apply_2(v_toPure_1154_, lean_box(0), v_b_1142_);
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(lean_object* v_inst_1156_, lean_object* v_f_1157_, lean_object* v_as_1158_, size_t v___x_1159_, size_t v_stop_1160_, lean_object* v_____do__lift_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1156_, v_f_1157_, v_as_1158_, v___x_1159_, v_stop_1160_, v_____do__lift_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___boxed(lean_object* v_inst_1163_, lean_object* v_f_1164_, lean_object* v_as_1165_, lean_object* v_i_1166_, lean_object* v_stop_1167_, lean_object* v_b_1168_){
_start:
{
size_t v_i_boxed_1169_; size_t v_stop_boxed_1170_; lean_object* v_res_1171_; 
v_i_boxed_1169_ = lean_unbox_usize(v_i_1166_);
lean_dec(v_i_1166_);
v_stop_boxed_1170_ = lean_unbox_usize(v_stop_1167_);
lean_dec(v_stop_1167_);
v_res_1171_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1163_, v_f_1164_, v_as_1165_, v_i_boxed_1169_, v_stop_boxed_1170_, v_b_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object* v_00_u03b1_1172_, lean_object* v_00_u03b2_1173_, lean_object* v_m_1174_, lean_object* v_inst_1175_, lean_object* v_f_1176_, lean_object* v_as_1177_, size_t v_i_1178_, size_t v_stop_1179_, lean_object* v_b_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1175_, v_f_1176_, v_as_1177_, v_i_1178_, v_stop_1179_, v_b_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___boxed(lean_object* v_00_u03b1_1182_, lean_object* v_00_u03b2_1183_, lean_object* v_m_1184_, lean_object* v_inst_1185_, lean_object* v_f_1186_, lean_object* v_as_1187_, lean_object* v_i_1188_, lean_object* v_stop_1189_, lean_object* v_b_1190_){
_start:
{
size_t v_i_boxed_1191_; size_t v_stop_boxed_1192_; lean_object* v_res_1193_; 
v_i_boxed_1191_ = lean_unbox_usize(v_i_1188_);
lean_dec(v_i_1188_);
v_stop_boxed_1192_ = lean_unbox_usize(v_stop_1189_);
lean_dec(v_stop_1189_);
v_res_1193_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(v_00_u03b1_1182_, v_00_u03b2_1183_, v_m_1184_, v_inst_1185_, v_f_1186_, v_as_1187_, v_i_boxed_1191_, v_stop_boxed_1192_, v_b_1190_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg(lean_object* v_inst_1194_, lean_object* v_f_1195_, lean_object* v_init_1196_, lean_object* v_as_1197_, lean_object* v_start_1198_, lean_object* v_stop_1199_){
_start:
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = lean_array_get_size(v_as_1197_);
v___x_1201_ = lean_nat_dec_le(v_start_1198_, v___x_1200_);
if (v___x_1201_ == 0)
{
uint8_t v___x_1202_; 
v___x_1202_ = lean_nat_dec_lt(v_stop_1199_, v___x_1200_);
if (v___x_1202_ == 0)
{
lean_object* v_toApplicative_1203_; lean_object* v_toPure_1204_; lean_object* v___x_1205_; 
lean_dec_ref(v_as_1197_);
lean_dec(v_f_1195_);
v_toApplicative_1203_ = lean_ctor_get(v_inst_1194_, 0);
lean_inc_ref(v_toApplicative_1203_);
lean_dec_ref(v_inst_1194_);
v_toPure_1204_ = lean_ctor_get(v_toApplicative_1203_, 1);
lean_inc(v_toPure_1204_);
lean_dec_ref(v_toApplicative_1203_);
v___x_1205_ = lean_apply_2(v_toPure_1204_, lean_box(0), v_init_1196_);
return v___x_1205_;
}
else
{
size_t v___x_1206_; size_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_usize_of_nat(v___x_1200_);
v___x_1207_ = lean_usize_of_nat(v_stop_1199_);
v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1194_, v_f_1195_, v_as_1197_, v___x_1206_, v___x_1207_, v_init_1196_);
return v___x_1208_;
}
}
else
{
uint8_t v___x_1209_; 
v___x_1209_ = lean_nat_dec_lt(v_stop_1199_, v_start_1198_);
if (v___x_1209_ == 0)
{
lean_object* v_toApplicative_1210_; lean_object* v_toPure_1211_; lean_object* v___x_1212_; 
lean_dec_ref(v_as_1197_);
lean_dec(v_f_1195_);
v_toApplicative_1210_ = lean_ctor_get(v_inst_1194_, 0);
lean_inc_ref(v_toApplicative_1210_);
lean_dec_ref(v_inst_1194_);
v_toPure_1211_ = lean_ctor_get(v_toApplicative_1210_, 1);
lean_inc(v_toPure_1211_);
lean_dec_ref(v_toApplicative_1210_);
v___x_1212_ = lean_apply_2(v_toPure_1211_, lean_box(0), v_init_1196_);
return v___x_1212_;
}
else
{
size_t v___x_1213_; size_t v___x_1214_; lean_object* v___x_1215_; 
v___x_1213_ = lean_usize_of_nat(v_start_1198_);
v___x_1214_ = lean_usize_of_nat(v_stop_1199_);
v___x_1215_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1194_, v_f_1195_, v_as_1197_, v___x_1213_, v___x_1214_, v_init_1196_);
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg___boxed(lean_object* v_inst_1216_, lean_object* v_f_1217_, lean_object* v_init_1218_, lean_object* v_as_1219_, lean_object* v_start_1220_, lean_object* v_stop_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Array_foldrMUnsafe___redArg(v_inst_1216_, v_f_1217_, v_init_1218_, v_as_1219_, v_start_1220_, v_stop_1221_);
lean_dec(v_stop_1221_);
lean_dec(v_start_1220_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe(lean_object* v_00_u03b1_1223_, lean_object* v_00_u03b2_1224_, lean_object* v_m_1225_, lean_object* v_inst_1226_, lean_object* v_f_1227_, lean_object* v_init_1228_, lean_object* v_as_1229_, lean_object* v_start_1230_, lean_object* v_stop_1231_){
_start:
{
lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = lean_array_get_size(v_as_1229_);
v___x_1233_ = lean_nat_dec_le(v_start_1230_, v___x_1232_);
if (v___x_1233_ == 0)
{
uint8_t v___x_1234_; 
v___x_1234_ = lean_nat_dec_lt(v_stop_1231_, v___x_1232_);
if (v___x_1234_ == 0)
{
lean_object* v_toApplicative_1235_; lean_object* v_toPure_1236_; lean_object* v___x_1237_; 
lean_dec_ref(v_as_1229_);
lean_dec(v_f_1227_);
v_toApplicative_1235_ = lean_ctor_get(v_inst_1226_, 0);
lean_inc_ref(v_toApplicative_1235_);
lean_dec_ref(v_inst_1226_);
v_toPure_1236_ = lean_ctor_get(v_toApplicative_1235_, 1);
lean_inc(v_toPure_1236_);
lean_dec_ref(v_toApplicative_1235_);
v___x_1237_ = lean_apply_2(v_toPure_1236_, lean_box(0), v_init_1228_);
return v___x_1237_;
}
else
{
size_t v___x_1238_; size_t v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_usize_of_nat(v___x_1232_);
v___x_1239_ = lean_usize_of_nat(v_stop_1231_);
v___x_1240_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1226_, v_f_1227_, v_as_1229_, v___x_1238_, v___x_1239_, v_init_1228_);
return v___x_1240_;
}
}
else
{
uint8_t v___x_1241_; 
v___x_1241_ = lean_nat_dec_lt(v_stop_1231_, v_start_1230_);
if (v___x_1241_ == 0)
{
lean_object* v_toApplicative_1242_; lean_object* v_toPure_1243_; lean_object* v___x_1244_; 
lean_dec_ref(v_as_1229_);
lean_dec(v_f_1227_);
v_toApplicative_1242_ = lean_ctor_get(v_inst_1226_, 0);
lean_inc_ref(v_toApplicative_1242_);
lean_dec_ref(v_inst_1226_);
v_toPure_1243_ = lean_ctor_get(v_toApplicative_1242_, 1);
lean_inc(v_toPure_1243_);
lean_dec_ref(v_toApplicative_1242_);
v___x_1244_ = lean_apply_2(v_toPure_1243_, lean_box(0), v_init_1228_);
return v___x_1244_;
}
else
{
size_t v___x_1245_; size_t v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_usize_of_nat(v_start_1230_);
v___x_1246_ = lean_usize_of_nat(v_stop_1231_);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1226_, v_f_1227_, v_as_1229_, v___x_1245_, v___x_1246_, v_init_1228_);
return v___x_1247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___boxed(lean_object* v_00_u03b1_1248_, lean_object* v_00_u03b2_1249_, lean_object* v_m_1250_, lean_object* v_inst_1251_, lean_object* v_f_1252_, lean_object* v_init_1253_, lean_object* v_as_1254_, lean_object* v_start_1255_, lean_object* v_stop_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Array_foldrMUnsafe(v_00_u03b1_1248_, v_00_u03b2_1249_, v_m_1250_, v_inst_1251_, v_f_1252_, v_init_1253_, v_as_1254_, v_start_1255_, v_stop_1256_);
lean_dec(v_stop_1256_);
lean_dec(v_start_1255_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0___boxed(lean_object* v_inst_1258_, lean_object* v_f_1259_, lean_object* v_as_1260_, lean_object* v_stop_1261_, lean_object* v_n_1262_, lean_object* v_____do__lift_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Array_foldrM_fold___redArg___lam__0(v_inst_1258_, v_f_1259_, v_as_1260_, v_stop_1261_, v_n_1262_, v_____do__lift_1263_);
lean_dec(v_n_1262_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg(lean_object* v_inst_1265_, lean_object* v_f_1266_, lean_object* v_as_1267_, lean_object* v_stop_1268_, lean_object* v_i_1269_, lean_object* v_b_1270_){
_start:
{
uint8_t v___x_1271_; 
v___x_1271_ = lean_nat_dec_eq(v_i_1269_, v_stop_1268_);
if (v___x_1271_ == 0)
{
lean_object* v_zero_1272_; uint8_t v_isZero_1273_; 
v_zero_1272_ = lean_unsigned_to_nat(0u);
v_isZero_1273_ = lean_nat_dec_eq(v_i_1269_, v_zero_1272_);
if (v_isZero_1273_ == 1)
{
lean_object* v_toApplicative_1274_; lean_object* v_toPure_1275_; lean_object* v___x_1276_; 
lean_dec(v_stop_1268_);
lean_dec_ref(v_as_1267_);
lean_dec(v_f_1266_);
v_toApplicative_1274_ = lean_ctor_get(v_inst_1265_, 0);
lean_inc_ref(v_toApplicative_1274_);
lean_dec_ref(v_inst_1265_);
v_toPure_1275_ = lean_ctor_get(v_toApplicative_1274_, 1);
lean_inc(v_toPure_1275_);
lean_dec_ref(v_toApplicative_1274_);
v___x_1276_ = lean_apply_2(v_toPure_1275_, lean_box(0), v_b_1270_);
return v___x_1276_;
}
else
{
lean_object* v_toBind_1277_; lean_object* v_one_1278_; lean_object* v_n_1279_; lean_object* v___f_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_toBind_1277_ = lean_ctor_get(v_inst_1265_, 1);
lean_inc(v_toBind_1277_);
v_one_1278_ = lean_unsigned_to_nat(1u);
v_n_1279_ = lean_nat_sub(v_i_1269_, v_one_1278_);
lean_inc(v_n_1279_);
lean_inc_ref(v_as_1267_);
lean_inc(v_f_1266_);
v___f_1280_ = lean_alloc_closure((void*)(l_Array_foldrM_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1280_, 0, v_inst_1265_);
lean_closure_set(v___f_1280_, 1, v_f_1266_);
lean_closure_set(v___f_1280_, 2, v_as_1267_);
lean_closure_set(v___f_1280_, 3, v_stop_1268_);
lean_closure_set(v___f_1280_, 4, v_n_1279_);
v___x_1281_ = lean_array_fget(v_as_1267_, v_n_1279_);
lean_dec(v_n_1279_);
lean_dec_ref(v_as_1267_);
v___x_1282_ = lean_apply_2(v_f_1266_, v___x_1281_, v_b_1270_);
v___x_1283_ = lean_apply_4(v_toBind_1277_, lean_box(0), lean_box(0), v___x_1282_, v___f_1280_);
return v___x_1283_;
}
}
else
{
lean_object* v_toApplicative_1284_; lean_object* v_toPure_1285_; lean_object* v___x_1286_; 
lean_dec(v_stop_1268_);
lean_dec_ref(v_as_1267_);
lean_dec(v_f_1266_);
v_toApplicative_1284_ = lean_ctor_get(v_inst_1265_, 0);
lean_inc_ref(v_toApplicative_1284_);
lean_dec_ref(v_inst_1265_);
v_toPure_1285_ = lean_ctor_get(v_toApplicative_1284_, 1);
lean_inc(v_toPure_1285_);
lean_dec_ref(v_toApplicative_1284_);
v___x_1286_ = lean_apply_2(v_toPure_1285_, lean_box(0), v_b_1270_);
return v___x_1286_;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0(lean_object* v_inst_1287_, lean_object* v_f_1288_, lean_object* v_as_1289_, lean_object* v_stop_1290_, lean_object* v_n_1291_, lean_object* v_____do__lift_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Array_foldrM_fold___redArg(v_inst_1287_, v_f_1288_, v_as_1289_, v_stop_1290_, v_n_1291_, v_____do__lift_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___boxed(lean_object* v_inst_1294_, lean_object* v_f_1295_, lean_object* v_as_1296_, lean_object* v_stop_1297_, lean_object* v_i_1298_, lean_object* v_b_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Array_foldrM_fold___redArg(v_inst_1294_, v_f_1295_, v_as_1296_, v_stop_1297_, v_i_1298_, v_b_1299_);
lean_dec(v_i_1298_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold(lean_object* v_00_u03b1_1301_, lean_object* v_00_u03b2_1302_, lean_object* v_m_1303_, lean_object* v_inst_1304_, lean_object* v_f_1305_, lean_object* v_as_1306_, lean_object* v_stop_1307_, lean_object* v_i_1308_, lean_object* v_h_1309_, lean_object* v_b_1310_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Array_foldrM_fold___redArg(v_inst_1304_, v_f_1305_, v_as_1306_, v_stop_1307_, v_i_1308_, v_b_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___boxed(lean_object* v_00_u03b1_1312_, lean_object* v_00_u03b2_1313_, lean_object* v_m_1314_, lean_object* v_inst_1315_, lean_object* v_f_1316_, lean_object* v_as_1317_, lean_object* v_stop_1318_, lean_object* v_i_1319_, lean_object* v_h_1320_, lean_object* v_b_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Array_foldrM_fold(v_00_u03b1_1312_, v_00_u03b2_1313_, v_m_1314_, v_inst_1315_, v_f_1316_, v_as_1317_, v_stop_1318_, v_i_1319_, v_h_1320_, v_b_1321_);
lean_dec(v_i_1319_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed(lean_object* v_i_1323_, lean_object* v_bs_x27_1324_, lean_object* v_inst_1325_, lean_object* v_f_1326_, lean_object* v_sz_1327_, lean_object* v_vNew_1328_){
_start:
{
size_t v_i_boxed_1329_; size_t v_sz_boxed_1330_; lean_object* v_res_1331_; 
v_i_boxed_1329_ = lean_unbox_usize(v_i_1323_);
lean_dec(v_i_1323_);
v_sz_boxed_1330_ = lean_unbox_usize(v_sz_1327_);
lean_dec(v_sz_1327_);
v_res_1331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(v_i_boxed_1329_, v_bs_x27_1324_, v_inst_1325_, v_f_1326_, v_sz_boxed_1330_, v_vNew_1328_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(lean_object* v_inst_1332_, lean_object* v_f_1333_, size_t v_sz_1334_, size_t v_i_1335_, lean_object* v_bs_1336_){
_start:
{
uint8_t v___x_1337_; 
v___x_1337_ = lean_usize_dec_lt(v_i_1335_, v_sz_1334_);
if (v___x_1337_ == 0)
{
lean_object* v_toApplicative_1338_; lean_object* v_toPure_1339_; lean_object* v___x_1340_; 
lean_dec(v_f_1333_);
v_toApplicative_1338_ = lean_ctor_get(v_inst_1332_, 0);
lean_inc_ref(v_toApplicative_1338_);
lean_dec_ref(v_inst_1332_);
v_toPure_1339_ = lean_ctor_get(v_toApplicative_1338_, 1);
lean_inc(v_toPure_1339_);
lean_dec_ref(v_toApplicative_1338_);
v___x_1340_ = lean_apply_2(v_toPure_1339_, lean_box(0), v_bs_1336_);
return v___x_1340_;
}
else
{
lean_object* v_toBind_1341_; lean_object* v_v_1342_; lean_object* v___x_1343_; lean_object* v_bs_x27_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___f_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_toBind_1341_ = lean_ctor_get(v_inst_1332_, 1);
lean_inc(v_toBind_1341_);
v_v_1342_ = lean_array_uget(v_bs_1336_, v_i_1335_);
v___x_1343_ = lean_unsigned_to_nat(0u);
v_bs_x27_1344_ = lean_array_uset(v_bs_1336_, v_i_1335_, v___x_1343_);
v___x_1345_ = lean_box_usize(v_i_1335_);
v___x_1346_ = lean_box_usize(v_sz_1334_);
lean_inc(v_f_1333_);
v___f_1347_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1347_, 0, v___x_1345_);
lean_closure_set(v___f_1347_, 1, v_bs_x27_1344_);
lean_closure_set(v___f_1347_, 2, v_inst_1332_);
lean_closure_set(v___f_1347_, 3, v_f_1333_);
lean_closure_set(v___f_1347_, 4, v___x_1346_);
v___x_1348_ = lean_apply_1(v_f_1333_, v_v_1342_);
v___x_1349_ = lean_apply_4(v_toBind_1341_, lean_box(0), lean_box(0), v___x_1348_, v___f_1347_);
return v___x_1349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(size_t v_i_1350_, lean_object* v_bs_x27_1351_, lean_object* v_inst_1352_, lean_object* v_f_1353_, size_t v_sz_1354_, lean_object* v_vNew_1355_){
_start:
{
size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1356_ = ((size_t)1ULL);
v___x_1357_ = lean_usize_add(v_i_1350_, v___x_1356_);
v___x_1358_ = lean_array_uset(v_bs_x27_1351_, v_i_1350_, v_vNew_1355_);
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1352_, v_f_1353_, v_sz_1354_, v___x_1357_, v___x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___boxed(lean_object* v_inst_1360_, lean_object* v_f_1361_, lean_object* v_sz_1362_, lean_object* v_i_1363_, lean_object* v_bs_1364_){
_start:
{
size_t v_sz_boxed_1365_; size_t v_i_boxed_1366_; lean_object* v_res_1367_; 
v_sz_boxed_1365_ = lean_unbox_usize(v_sz_1362_);
lean_dec(v_sz_1362_);
v_i_boxed_1366_ = lean_unbox_usize(v_i_1363_);
lean_dec(v_i_1363_);
v_res_1367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1360_, v_f_1361_, v_sz_boxed_1365_, v_i_boxed_1366_, v_bs_1364_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object* v_00_u03b1_1368_, lean_object* v_00_u03b2_1369_, lean_object* v_m_1370_, lean_object* v_inst_1371_, lean_object* v_f_1372_, size_t v_sz_1373_, size_t v_i_1374_, lean_object* v_bs_1375_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1371_, v_f_1372_, v_sz_1373_, v_i_1374_, v_bs_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___boxed(lean_object* v_00_u03b1_1377_, lean_object* v_00_u03b2_1378_, lean_object* v_m_1379_, lean_object* v_inst_1380_, lean_object* v_f_1381_, lean_object* v_sz_1382_, lean_object* v_i_1383_, lean_object* v_bs_1384_){
_start:
{
size_t v_sz_boxed_1385_; size_t v_i_boxed_1386_; lean_object* v_res_1387_; 
v_sz_boxed_1385_ = lean_unbox_usize(v_sz_1382_);
lean_dec(v_sz_1382_);
v_i_boxed_1386_ = lean_unbox_usize(v_i_1383_);
lean_dec(v_i_1383_);
v_res_1387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(v_00_u03b1_1377_, v_00_u03b2_1378_, v_m_1379_, v_inst_1380_, v_f_1381_, v_sz_boxed_1385_, v_i_boxed_1386_, v_bs_1384_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe___redArg(lean_object* v_inst_1388_, lean_object* v_f_1389_, lean_object* v_as_1390_){
_start:
{
size_t v_sz_1391_; size_t v___x_1392_; lean_object* v___x_1393_; 
v_sz_1391_ = lean_array_size(v_as_1390_);
v___x_1392_ = ((size_t)0ULL);
v___x_1393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1388_, v_f_1389_, v_sz_1391_, v___x_1392_, v_as_1390_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe(lean_object* v_00_u03b1_1394_, lean_object* v_00_u03b2_1395_, lean_object* v_m_1396_, lean_object* v_inst_1397_, lean_object* v_f_1398_, lean_object* v_as_1399_){
_start:
{
size_t v_sz_1400_; size_t v___x_1401_; lean_object* v___x_1402_; 
v_sz_1400_ = lean_array_size(v_as_1399_);
v___x_1401_ = ((size_t)0ULL);
v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1397_, v_f_1398_, v_sz_1400_, v___x_1401_, v_as_1399_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0___boxed(lean_object* v_i_1403_, lean_object* v_bs_1404_, lean_object* v_inst_1405_, lean_object* v_f_1406_, lean_object* v_as_1407_, lean_object* v_____do__lift_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0(v_i_1403_, v_bs_1404_, v_inst_1405_, v_f_1406_, v_as_1407_, v_____do__lift_1408_);
lean_dec(v_i_1403_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(lean_object* v_inst_1410_, lean_object* v_f_1411_, lean_object* v_as_1412_, lean_object* v_i_1413_, lean_object* v_bs_1414_){
_start:
{
lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = lean_array_get_size(v_as_1412_);
v___x_1416_ = lean_nat_dec_lt(v_i_1413_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v_toApplicative_1417_; lean_object* v_toPure_1418_; lean_object* v___x_1419_; 
lean_dec(v_i_1413_);
lean_dec_ref(v_as_1412_);
lean_dec(v_f_1411_);
v_toApplicative_1417_ = lean_ctor_get(v_inst_1410_, 0);
lean_inc_ref(v_toApplicative_1417_);
lean_dec_ref(v_inst_1410_);
v_toPure_1418_ = lean_ctor_get(v_toApplicative_1417_, 1);
lean_inc(v_toPure_1418_);
lean_dec_ref(v_toApplicative_1417_);
v___x_1419_ = lean_apply_2(v_toPure_1418_, lean_box(0), v_bs_1414_);
return v___x_1419_;
}
else
{
lean_object* v_toBind_1420_; lean_object* v___f_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_toBind_1420_ = lean_ctor_get(v_inst_1410_, 1);
lean_inc(v_toBind_1420_);
lean_inc_ref(v_as_1412_);
lean_inc(v_f_1411_);
lean_inc(v_i_1413_);
v___f_1421_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1421_, 0, v_i_1413_);
lean_closure_set(v___f_1421_, 1, v_bs_1414_);
lean_closure_set(v___f_1421_, 2, v_inst_1410_);
lean_closure_set(v___f_1421_, 3, v_f_1411_);
lean_closure_set(v___f_1421_, 4, v_as_1412_);
v___x_1422_ = lean_array_fget(v_as_1412_, v_i_1413_);
lean_dec(v_i_1413_);
lean_dec_ref(v_as_1412_);
v___x_1423_ = lean_apply_1(v_f_1411_, v___x_1422_);
v___x_1424_ = lean_apply_4(v_toBind_1420_, lean_box(0), lean_box(0), v___x_1423_, v___f_1421_);
return v___x_1424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0(lean_object* v_i_1425_, lean_object* v_bs_1426_, lean_object* v_inst_1427_, lean_object* v_f_1428_, lean_object* v_as_1429_, lean_object* v_____do__lift_1430_){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1431_ = lean_unsigned_to_nat(1u);
v___x_1432_ = lean_nat_add(v_i_1425_, v___x_1431_);
v___x_1433_ = lean_array_push(v_bs_1426_, v_____do__lift_1430_);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(v_inst_1427_, v_f_1428_, v_as_1429_, v___x_1432_, v___x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map(lean_object* v_00_u03b1_1435_, lean_object* v_00_u03b2_1436_, lean_object* v_m_1437_, lean_object* v_inst_1438_, lean_object* v_f_1439_, lean_object* v_as_1440_, lean_object* v_i_1441_, lean_object* v_bs_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(v_inst_1438_, v_f_1439_, v_as_1440_, v_i_1441_, v_bs_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0___boxed(lean_object* v_i_1444_, lean_object* v_bs_x27_1445_, lean_object* v_inst_1446_, lean_object* v_f_1447_, lean_object* v_sz_1448_, lean_object* v_vNew_1449_){
_start:
{
size_t v_i_boxed_1450_; size_t v_sz_boxed_1451_; lean_object* v_res_1452_; 
v_i_boxed_1450_ = lean_unbox_usize(v_i_1444_);
lean_dec(v_i_1444_);
v_sz_boxed_1451_ = lean_unbox_usize(v_sz_1448_);
lean_dec(v_sz_1448_);
v_res_1452_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0(v_i_boxed_1450_, v_bs_x27_1445_, v_inst_1446_, v_f_1447_, v_sz_boxed_1451_, v_vNew_1449_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(lean_object* v_inst_1453_, lean_object* v_f_1454_, size_t v_sz_1455_, size_t v_i_1456_, lean_object* v_bs_1457_){
_start:
{
uint8_t v___x_1458_; 
v___x_1458_ = lean_usize_dec_lt(v_i_1456_, v_sz_1455_);
if (v___x_1458_ == 0)
{
lean_object* v_toApplicative_1459_; lean_object* v_toPure_1460_; lean_object* v___x_1461_; 
lean_dec(v_f_1454_);
v_toApplicative_1459_ = lean_ctor_get(v_inst_1453_, 0);
lean_inc_ref(v_toApplicative_1459_);
lean_dec_ref(v_inst_1453_);
v_toPure_1460_ = lean_ctor_get(v_toApplicative_1459_, 1);
lean_inc(v_toPure_1460_);
lean_dec_ref(v_toApplicative_1459_);
v___x_1461_ = lean_apply_2(v_toPure_1460_, lean_box(0), v_bs_1457_);
return v___x_1461_;
}
else
{
lean_object* v_toBind_1462_; lean_object* v_v_1463_; lean_object* v___x_1464_; lean_object* v_bs_x27_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___f_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_toBind_1462_ = lean_ctor_get(v_inst_1453_, 1);
lean_inc(v_toBind_1462_);
v_v_1463_ = lean_array_uget(v_bs_1457_, v_i_1456_);
v___x_1464_ = lean_unsigned_to_nat(0u);
v_bs_x27_1465_ = lean_array_uset(v_bs_1457_, v_i_1456_, v___x_1464_);
v___x_1466_ = lean_box_usize(v_i_1456_);
v___x_1467_ = lean_box_usize(v_sz_1455_);
lean_inc(v_f_1454_);
v___f_1468_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1468_, 0, v___x_1466_);
lean_closure_set(v___f_1468_, 1, v_bs_x27_1465_);
lean_closure_set(v___f_1468_, 2, v_inst_1453_);
lean_closure_set(v___f_1468_, 3, v_f_1454_);
lean_closure_set(v___f_1468_, 4, v___x_1467_);
v___x_1469_ = lean_usize_to_nat(v_i_1456_);
v___x_1470_ = lean_apply_3(v_f_1454_, v___x_1469_, v_v_1463_, lean_box(0));
v___x_1471_ = lean_apply_4(v_toBind_1462_, lean_box(0), lean_box(0), v___x_1470_, v___f_1468_);
return v___x_1471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0(size_t v_i_1472_, lean_object* v_bs_x27_1473_, lean_object* v_inst_1474_, lean_object* v_f_1475_, size_t v_sz_1476_, lean_object* v_vNew_1477_){
_start:
{
size_t v___x_1478_; size_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1478_ = ((size_t)1ULL);
v___x_1479_ = lean_usize_add(v_i_1472_, v___x_1478_);
v___x_1480_ = lean_array_uset(v_bs_x27_1473_, v_i_1472_, v_vNew_1477_);
v___x_1481_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1474_, v_f_1475_, v_sz_1476_, v___x_1479_, v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___boxed(lean_object* v_inst_1482_, lean_object* v_f_1483_, lean_object* v_sz_1484_, lean_object* v_i_1485_, lean_object* v_bs_1486_){
_start:
{
size_t v_sz_boxed_1487_; size_t v_i_boxed_1488_; lean_object* v_res_1489_; 
v_sz_boxed_1487_ = lean_unbox_usize(v_sz_1484_);
lean_dec(v_sz_1484_);
v_i_boxed_1488_ = lean_unbox_usize(v_i_1485_);
lean_dec(v_i_1485_);
v_res_1489_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1482_, v_f_1483_, v_sz_boxed_1487_, v_i_boxed_1488_, v_bs_1486_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object* v_00_u03b1_1490_, lean_object* v_00_u03b2_1491_, lean_object* v_m_1492_, lean_object* v_inst_1493_, lean_object* v_as_1494_, lean_object* v_f_1495_, size_t v_sz_1496_, size_t v_i_1497_, lean_object* v_bs_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1493_, v_f_1495_, v_sz_1496_, v_i_1497_, v_bs_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___boxed(lean_object* v_00_u03b1_1500_, lean_object* v_00_u03b2_1501_, lean_object* v_m_1502_, lean_object* v_inst_1503_, lean_object* v_as_1504_, lean_object* v_f_1505_, lean_object* v_sz_1506_, lean_object* v_i_1507_, lean_object* v_bs_1508_){
_start:
{
size_t v_sz_boxed_1509_; size_t v_i_boxed_1510_; lean_object* v_res_1511_; 
v_sz_boxed_1509_ = lean_unbox_usize(v_sz_1506_);
lean_dec(v_sz_1506_);
v_i_boxed_1510_ = lean_unbox_usize(v_i_1507_);
lean_dec(v_i_1507_);
v_res_1511_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(v_00_u03b1_1500_, v_00_u03b2_1501_, v_m_1502_, v_inst_1503_, v_as_1504_, v_f_1505_, v_sz_boxed_1509_, v_i_boxed_1510_, v_bs_1508_);
lean_dec_ref(v_as_1504_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxMUnsafe___redArg(lean_object* v_inst_1512_, lean_object* v_as_1513_, lean_object* v_f_1514_){
_start:
{
size_t v_sz_1515_; size_t v___x_1516_; lean_object* v___x_1517_; 
v_sz_1515_ = lean_array_size(v_as_1513_);
v___x_1516_ = ((size_t)0ULL);
v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1512_, v_f_1514_, v_sz_1515_, v___x_1516_, v_as_1513_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxMUnsafe(lean_object* v_00_u03b1_1518_, lean_object* v_00_u03b2_1519_, lean_object* v_m_1520_, lean_object* v_inst_1521_, lean_object* v_as_1522_, lean_object* v_f_1523_){
_start:
{
size_t v_sz_1524_; size_t v___x_1525_; lean_object* v___x_1526_; 
v_sz_1524_ = lean_array_size(v_as_1522_);
v___x_1525_ = ((size_t)0ULL);
v___x_1526_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1521_, v_f_1523_, v_sz_1524_, v___x_1525_, v_as_1522_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1527_, lean_object* v_bs_1528_, lean_object* v_inst_1529_, lean_object* v_as_1530_, lean_object* v_f_1531_, lean_object* v_n_1532_, lean_object* v_____do__lift_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Array_mapFinIdxM_map___redArg___lam__0(v_j_1527_, v_bs_1528_, v_inst_1529_, v_as_1530_, v_f_1531_, v_n_1532_, v_____do__lift_1533_);
lean_dec(v_n_1532_);
lean_dec(v_j_1527_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg(lean_object* v_inst_1535_, lean_object* v_as_1536_, lean_object* v_f_1537_, lean_object* v_i_1538_, lean_object* v_j_1539_, lean_object* v_bs_1540_){
_start:
{
lean_object* v_toApplicative_1541_; lean_object* v_toBind_1542_; lean_object* v_toPure_1543_; lean_object* v_zero_1544_; uint8_t v_isZero_1545_; 
v_toApplicative_1541_ = lean_ctor_get(v_inst_1535_, 0);
v_toBind_1542_ = lean_ctor_get(v_inst_1535_, 1);
lean_inc(v_toBind_1542_);
v_toPure_1543_ = lean_ctor_get(v_toApplicative_1541_, 1);
v_zero_1544_ = lean_unsigned_to_nat(0u);
v_isZero_1545_ = lean_nat_dec_eq(v_i_1538_, v_zero_1544_);
if (v_isZero_1545_ == 1)
{
lean_object* v___x_1546_; 
lean_inc(v_toPure_1543_);
lean_dec(v_toBind_1542_);
lean_dec(v_j_1539_);
lean_dec(v_f_1537_);
lean_dec_ref(v_as_1536_);
lean_dec_ref(v_inst_1535_);
v___x_1546_ = lean_apply_2(v_toPure_1543_, lean_box(0), v_bs_1540_);
return v___x_1546_;
}
else
{
lean_object* v_one_1547_; lean_object* v_n_1548_; lean_object* v___f_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_one_1547_ = lean_unsigned_to_nat(1u);
v_n_1548_ = lean_nat_sub(v_i_1538_, v_one_1547_);
lean_inc(v_f_1537_);
lean_inc_ref(v_as_1536_);
lean_inc(v_j_1539_);
v___f_1549_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1549_, 0, v_j_1539_);
lean_closure_set(v___f_1549_, 1, v_bs_1540_);
lean_closure_set(v___f_1549_, 2, v_inst_1535_);
lean_closure_set(v___f_1549_, 3, v_as_1536_);
lean_closure_set(v___f_1549_, 4, v_f_1537_);
lean_closure_set(v___f_1549_, 5, v_n_1548_);
v___x_1550_ = lean_array_fget(v_as_1536_, v_j_1539_);
lean_dec_ref(v_as_1536_);
v___x_1551_ = lean_apply_3(v_f_1537_, v_j_1539_, v___x_1550_, lean_box(0));
v___x_1552_ = lean_apply_4(v_toBind_1542_, lean_box(0), lean_box(0), v___x_1551_, v___f_1549_);
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1553_, lean_object* v_bs_1554_, lean_object* v_inst_1555_, lean_object* v_as_1556_, lean_object* v_f_1557_, lean_object* v_n_1558_, lean_object* v_____do__lift_1559_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1560_ = lean_unsigned_to_nat(1u);
v___x_1561_ = lean_nat_add(v_j_1553_, v___x_1560_);
v___x_1562_ = lean_array_push(v_bs_1554_, v_____do__lift_1559_);
v___x_1563_ = l_Array_mapFinIdxM_map___redArg(v_inst_1555_, v_as_1556_, v_f_1557_, v_n_1558_, v___x_1561_, v___x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1564_, lean_object* v_as_1565_, lean_object* v_f_1566_, lean_object* v_i_1567_, lean_object* v_j_1568_, lean_object* v_bs_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Array_mapFinIdxM_map___redArg(v_inst_1564_, v_as_1565_, v_f_1566_, v_i_1567_, v_j_1568_, v_bs_1569_);
lean_dec(v_i_1567_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map(lean_object* v_00_u03b1_1571_, lean_object* v_00_u03b2_1572_, lean_object* v_m_1573_, lean_object* v_inst_1574_, lean_object* v_as_1575_, lean_object* v_f_1576_, lean_object* v_i_1577_, lean_object* v_j_1578_, lean_object* v_inv_1579_, lean_object* v_bs_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Array_mapFinIdxM_map___redArg(v_inst_1574_, v_as_1575_, v_f_1576_, v_i_1577_, v_j_1578_, v_bs_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___boxed(lean_object* v_00_u03b1_1582_, lean_object* v_00_u03b2_1583_, lean_object* v_m_1584_, lean_object* v_inst_1585_, lean_object* v_as_1586_, lean_object* v_f_1587_, lean_object* v_i_1588_, lean_object* v_j_1589_, lean_object* v_inv_1590_, lean_object* v_bs_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Array_mapFinIdxM_map(v_00_u03b1_1582_, v_00_u03b2_1583_, v_m_1584_, v_inst_1585_, v_as_1586_, v_f_1587_, v_i_1588_, v_j_1589_, v_inv_1590_, v_bs_1591_);
lean_dec(v_i_1588_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg___lam__0(lean_object* v_f_1593_, lean_object* v_i_1594_, lean_object* v_a_1595_, lean_object* v_x_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_apply_2(v_f_1593_, v_i_1594_, v_a_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg(lean_object* v_inst_1598_, lean_object* v_f_1599_, lean_object* v_as_1600_){
_start:
{
lean_object* v___f_1601_; size_t v_sz_1602_; size_t v___x_1603_; lean_object* v___x_1604_; 
v___f_1601_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1601_, 0, v_f_1599_);
v_sz_1602_ = lean_array_size(v_as_1600_);
v___x_1603_ = ((size_t)0ULL);
v___x_1604_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1598_, v___f_1601_, v_sz_1602_, v___x_1603_, v_as_1600_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM(lean_object* v_00_u03b1_1605_, lean_object* v_00_u03b2_1606_, lean_object* v_m_1607_, lean_object* v_inst_1608_, lean_object* v_f_1609_, lean_object* v_as_1610_){
_start:
{
lean_object* v___f_1611_; size_t v_sz_1612_; size_t v___x_1613_; lean_object* v___x_1614_; 
v___f_1611_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1611_, 0, v_f_1609_);
v_sz_1612_ = lean_array_size(v_as_1610_);
v___x_1613_ = ((size_t)0ULL);
v___x_1614_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1608_, v___f_1611_, v_sz_1612_, v___x_1613_, v_as_1610_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed(lean_object* v_i_1615_, lean_object* v_inst_1616_, lean_object* v_f_1617_, lean_object* v_as_1618_, lean_object* v_x_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(v_i_1615_, v_inst_1616_, v_f_1617_, v_as_1618_, v_x_1619_);
lean_dec(v_i_1615_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(lean_object* v_inst_1621_, lean_object* v_f_1622_, lean_object* v_as_1623_, lean_object* v_i_1624_){
_start:
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = lean_array_get_size(v_as_1623_);
v___x_1626_ = lean_nat_dec_lt(v_i_1624_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v_failure_1627_; lean_object* v___x_1628_; 
lean_dec(v_i_1624_);
lean_dec_ref(v_as_1623_);
lean_dec(v_f_1622_);
v_failure_1627_ = lean_ctor_get(v_inst_1621_, 1);
lean_inc(v_failure_1627_);
lean_dec_ref(v_inst_1621_);
v___x_1628_ = lean_apply_1(v_failure_1627_, lean_box(0));
return v___x_1628_;
}
else
{
lean_object* v_orElse_1629_; lean_object* v___f_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_orElse_1629_ = lean_ctor_get(v_inst_1621_, 2);
lean_inc(v_orElse_1629_);
lean_inc_ref(v_as_1623_);
lean_inc(v_f_1622_);
lean_inc(v_i_1624_);
v___f_1630_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1630_, 0, v_i_1624_);
lean_closure_set(v___f_1630_, 1, v_inst_1621_);
lean_closure_set(v___f_1630_, 2, v_f_1622_);
lean_closure_set(v___f_1630_, 3, v_as_1623_);
v___x_1631_ = lean_array_fget(v_as_1623_, v_i_1624_);
lean_dec(v_i_1624_);
lean_dec_ref(v_as_1623_);
v___x_1632_ = lean_apply_1(v_f_1622_, v___x_1631_);
v___x_1633_ = lean_apply_3(v_orElse_1629_, lean_box(0), v___x_1632_, v___f_1630_);
return v___x_1633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(lean_object* v_i_1634_, lean_object* v_inst_1635_, lean_object* v_f_1636_, lean_object* v_as_1637_, lean_object* v_x_1638_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1639_ = lean_unsigned_to_nat(1u);
v___x_1640_ = lean_nat_add(v_i_1634_, v___x_1639_);
v___x_1641_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1635_, v_f_1636_, v_as_1637_, v___x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_object* v_00_u03b2_1642_, lean_object* v_00_u03b1_1643_, lean_object* v_m_1644_, lean_object* v_inst_1645_, lean_object* v_f_1646_, lean_object* v_as_1647_, lean_object* v_i_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1645_, v_f_1646_, v_as_1647_, v_i_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM___redArg(lean_object* v_inst_1650_, lean_object* v_f_1651_, lean_object* v_as_1652_){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_unsigned_to_nat(0u);
v___x_1654_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1650_, v_f_1651_, v_as_1652_, v___x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM(lean_object* v_00_u03b2_1655_, lean_object* v_00_u03b1_1656_, lean_object* v_m_1657_, lean_object* v_inst_1658_, lean_object* v_f_1659_, lean_object* v_as_1660_){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_unsigned_to_nat(0u);
v___x_1662_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1658_, v_f_1659_, v_as_1660_, v___x_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__0(lean_object* v___x_1663_, lean_object* v_toPure_1664_, lean_object* v___x_1665_, lean_object* v_____do__lift_1666_){
_start:
{
if (lean_obj_tag(v_____do__lift_1666_) == 1)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec_ref(v___x_1665_);
v___x_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1667_, 0, v_____do__lift_1666_);
v___x_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v___x_1663_);
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
v___x_1670_ = lean_apply_2(v_toPure_1664_, lean_box(0), v___x_1669_);
return v___x_1670_;
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_dec(v_____do__lift_1666_);
v___x_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1665_);
v___x_1672_ = lean_apply_2(v_toPure_1664_, lean_box(0), v___x_1671_);
return v___x_1672_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1(lean_object* v_f_1673_, lean_object* v_toBind_1674_, lean_object* v___f_1675_, lean_object* v_a_1676_, lean_object* v_x_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_apply_1(v_f_1673_, v_a_1676_);
v___x_1680_ = lean_apply_4(v_toBind_1674_, lean_box(0), lean_box(0), v___x_1679_, v___f_1675_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1___boxed(lean_object* v_f_1681_, lean_object* v_toBind_1682_, lean_object* v___f_1683_, lean_object* v_a_1684_, lean_object* v_x_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Array_findSomeM_x3f___redArg___lam__1(v_f_1681_, v_toBind_1682_, v___f_1683_, v_a_1684_, v_x_1685_, v___y_1686_);
lean_dec_ref(v___y_1686_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__2(lean_object* v_toPure_1688_, lean_object* v_____s_1689_){
_start:
{
lean_object* v_fst_1690_; 
v_fst_1690_ = lean_ctor_get(v_____s_1689_, 0);
lean_inc(v_fst_1690_);
lean_dec_ref(v_____s_1689_);
if (lean_obj_tag(v_fst_1690_) == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_box(0);
v___x_1692_ = lean_apply_2(v_toPure_1688_, lean_box(0), v___x_1691_);
return v___x_1692_;
}
else
{
lean_object* v_val_1693_; lean_object* v___x_1694_; 
v_val_1693_ = lean_ctor_get(v_fst_1690_, 0);
lean_inc(v_val_1693_);
lean_dec_ref_known(v_fst_1690_, 1);
v___x_1694_ = lean_apply_2(v_toPure_1688_, lean_box(0), v_val_1693_);
return v___x_1694_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg(lean_object* v_inst_1698_, lean_object* v_f_1699_, lean_object* v_as_1700_){
_start:
{
lean_object* v_toApplicative_1701_; lean_object* v_toBind_1702_; lean_object* v_toPure_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___f_1706_; lean_object* v___f_1707_; lean_object* v___f_1708_; size_t v_sz_1709_; size_t v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_toApplicative_1701_ = lean_ctor_get(v_inst_1698_, 0);
v_toBind_1702_ = lean_ctor_get(v_inst_1698_, 1);
lean_inc_n(v_toBind_1702_, 2);
v_toPure_1703_ = lean_ctor_get(v_toApplicative_1701_, 1);
v___x_1704_ = lean_box(0);
v___x_1705_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1703_, 2);
v___f_1706_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1706_, 0, v___x_1704_);
lean_closure_set(v___f_1706_, 1, v_toPure_1703_);
lean_closure_set(v___f_1706_, 2, v___x_1705_);
v___f_1707_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1707_, 0, v_f_1699_);
lean_closure_set(v___f_1707_, 1, v_toBind_1702_);
lean_closure_set(v___f_1707_, 2, v___f_1706_);
v___f_1708_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1708_, 0, v_toPure_1703_);
v_sz_1709_ = lean_array_size(v_as_1700_);
v___x_1710_ = ((size_t)0ULL);
v___x_1711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1698_, v_as_1700_, v___f_1707_, v_sz_1709_, v___x_1710_, v___x_1705_);
v___x_1712_ = lean_apply_4(v_toBind_1702_, lean_box(0), lean_box(0), v___x_1711_, v___f_1708_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f(lean_object* v_00_u03b1_1713_, lean_object* v_00_u03b2_1714_, lean_object* v_m_1715_, lean_object* v_inst_1716_, lean_object* v_f_1717_, lean_object* v_as_1718_){
_start:
{
lean_object* v_toApplicative_1719_; lean_object* v_toBind_1720_; lean_object* v_toPure_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___f_1724_; lean_object* v___f_1725_; lean_object* v___f_1726_; size_t v_sz_1727_; size_t v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_toApplicative_1719_ = lean_ctor_get(v_inst_1716_, 0);
v_toBind_1720_ = lean_ctor_get(v_inst_1716_, 1);
lean_inc_n(v_toBind_1720_, 2);
v_toPure_1721_ = lean_ctor_get(v_toApplicative_1719_, 1);
v___x_1722_ = lean_box(0);
v___x_1723_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1721_, 2);
v___f_1724_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1724_, 0, v___x_1722_);
lean_closure_set(v___f_1724_, 1, v_toPure_1721_);
lean_closure_set(v___f_1724_, 2, v___x_1723_);
v___f_1725_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1725_, 0, v_f_1717_);
lean_closure_set(v___f_1725_, 1, v_toBind_1720_);
lean_closure_set(v___f_1725_, 2, v___f_1724_);
v___f_1726_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1726_, 0, v_toPure_1721_);
v_sz_1727_ = lean_array_size(v_as_1718_);
v___x_1728_ = ((size_t)0ULL);
v___x_1729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1716_, v_as_1718_, v___f_1725_, v_sz_1727_, v___x_1728_, v___x_1723_);
v___x_1730_ = lean_apply_4(v_toBind_1720_, lean_box(0), lean_box(0), v___x_1729_, v___f_1726_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0(lean_object* v___x_1731_, lean_object* v_toPure_1732_, lean_object* v_a_1733_, lean_object* v___x_1734_, uint8_t v_____do__lift_1735_){
_start:
{
if (v_____do__lift_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec(v_a_1733_);
v___x_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1731_);
v___x_1737_ = lean_apply_2(v_toPure_1732_, lean_box(0), v___x_1736_);
return v___x_1737_;
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_dec_ref(v___x_1731_);
v___x_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_a_1733_);
v___x_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
v___x_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
lean_ctor_set(v___x_1740_, 1, v___x_1734_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
v___x_1742_ = lean_apply_2(v_toPure_1732_, lean_box(0), v___x_1741_);
return v___x_1742_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0___boxed(lean_object* v___x_1743_, lean_object* v_toPure_1744_, lean_object* v_a_1745_, lean_object* v___x_1746_, lean_object* v_____do__lift_1747_){
_start:
{
uint8_t v_____do__lift_214__boxed_1748_; lean_object* v_res_1749_; 
v_____do__lift_214__boxed_1748_ = lean_unbox(v_____do__lift_1747_);
v_res_1749_ = l_Array_findM_x3f___redArg___lam__0(v___x_1743_, v_toPure_1744_, v_a_1745_, v___x_1746_, v_____do__lift_214__boxed_1748_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1(lean_object* v___x_1750_, lean_object* v_toPure_1751_, lean_object* v___x_1752_, lean_object* v_p_1753_, lean_object* v_toBind_1754_, lean_object* v_a_1755_, lean_object* v_x_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v___f_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_inc(v_a_1755_);
v___f_1758_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1758_, 0, v___x_1750_);
lean_closure_set(v___f_1758_, 1, v_toPure_1751_);
lean_closure_set(v___f_1758_, 2, v_a_1755_);
lean_closure_set(v___f_1758_, 3, v___x_1752_);
v___x_1759_ = lean_apply_1(v_p_1753_, v_a_1755_);
v___x_1760_ = lean_apply_4(v_toBind_1754_, lean_box(0), lean_box(0), v___x_1759_, v___f_1758_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_1761_, lean_object* v_toPure_1762_, lean_object* v___x_1763_, lean_object* v_p_1764_, lean_object* v_toBind_1765_, lean_object* v_a_1766_, lean_object* v_x_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Array_findM_x3f___redArg___lam__1(v___x_1761_, v_toPure_1762_, v___x_1763_, v_p_1764_, v_toBind_1765_, v_a_1766_, v_x_1767_, v___y_1768_);
lean_dec_ref(v___y_1768_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg(lean_object* v_inst_1770_, lean_object* v_p_1771_, lean_object* v_as_1772_){
_start:
{
lean_object* v_toApplicative_1773_; lean_object* v_toBind_1774_; lean_object* v_toPure_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___f_1778_; lean_object* v___f_1779_; size_t v_sz_1780_; size_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_toApplicative_1773_ = lean_ctor_get(v_inst_1770_, 0);
v_toBind_1774_ = lean_ctor_get(v_inst_1770_, 1);
lean_inc_n(v_toBind_1774_, 2);
v_toPure_1775_ = lean_ctor_get(v_toApplicative_1773_, 1);
v___x_1776_ = lean_box(0);
v___x_1777_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1775_, 2);
v___f_1778_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1778_, 0, v___x_1777_);
lean_closure_set(v___f_1778_, 1, v_toPure_1775_);
lean_closure_set(v___f_1778_, 2, v___x_1776_);
lean_closure_set(v___f_1778_, 3, v_p_1771_);
lean_closure_set(v___f_1778_, 4, v_toBind_1774_);
v___f_1779_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1779_, 0, v_toPure_1775_);
v_sz_1780_ = lean_array_size(v_as_1772_);
v___x_1781_ = ((size_t)0ULL);
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1770_, v_as_1772_, v___f_1778_, v_sz_1780_, v___x_1781_, v___x_1777_);
v___x_1783_ = lean_apply_4(v_toBind_1774_, lean_box(0), lean_box(0), v___x_1782_, v___f_1779_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f(lean_object* v_m_1784_, lean_object* v_00_u03b1_1785_, lean_object* v_inst_1786_, lean_object* v_p_1787_, lean_object* v_as_1788_){
_start:
{
lean_object* v_toApplicative_1789_; lean_object* v_toBind_1790_; lean_object* v_toPure_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___f_1794_; lean_object* v___f_1795_; size_t v_sz_1796_; size_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_toApplicative_1789_ = lean_ctor_get(v_inst_1786_, 0);
v_toBind_1790_ = lean_ctor_get(v_inst_1786_, 1);
lean_inc_n(v_toBind_1790_, 2);
v_toPure_1791_ = lean_ctor_get(v_toApplicative_1789_, 1);
v___x_1792_ = lean_box(0);
v___x_1793_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1791_, 2);
v___f_1794_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1794_, 0, v___x_1793_);
lean_closure_set(v___f_1794_, 1, v_toPure_1791_);
lean_closure_set(v___f_1794_, 2, v___x_1792_);
lean_closure_set(v___f_1794_, 3, v_p_1787_);
lean_closure_set(v___f_1794_, 4, v_toBind_1790_);
v___f_1795_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1795_, 0, v_toPure_1791_);
v_sz_1796_ = lean_array_size(v_as_1788_);
v___x_1797_ = ((size_t)0ULL);
v___x_1798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1786_, v_as_1788_, v___f_1794_, v_sz_1796_, v___x_1797_, v___x_1793_);
v___x_1799_ = lean_apply_4(v_toBind_1790_, lean_box(0), lean_box(0), v___x_1798_, v___f_1795_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0(lean_object* v_snd_1800_, lean_object* v___x_1801_, lean_object* v_toPure_1802_, uint8_t v_____do__lift_1803_){
_start:
{
if (v_____do__lift_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1804_ = lean_unsigned_to_nat(1u);
v___x_1805_ = lean_nat_add(v_snd_1800_, v___x_1804_);
lean_dec(v_snd_1800_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1801_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
v___x_1808_ = lean_apply_2(v_toPure_1802_, lean_box(0), v___x_1807_);
return v___x_1808_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec(v___x_1801_);
lean_inc(v_snd_1800_);
v___x_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1809_, 0, v_snd_1800_);
v___x_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
lean_ctor_set(v___x_1811_, 1, v_snd_1800_);
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
v___x_1813_ = lean_apply_2(v_toPure_1802_, lean_box(0), v___x_1812_);
return v___x_1813_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0___boxed(lean_object* v_snd_1814_, lean_object* v___x_1815_, lean_object* v_toPure_1816_, lean_object* v_____do__lift_1817_){
_start:
{
uint8_t v_____do__lift_249__boxed_1818_; lean_object* v_res_1819_; 
v_____do__lift_249__boxed_1818_ = lean_unbox(v_____do__lift_1817_);
v_res_1819_ = l_Array_findIdxM_x3f___redArg___lam__0(v_snd_1814_, v___x_1815_, v_toPure_1816_, v_____do__lift_249__boxed_1818_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__1(lean_object* v___x_1820_, lean_object* v_toPure_1821_, lean_object* v_p_1822_, lean_object* v_toBind_1823_, lean_object* v_a_1824_, lean_object* v_x_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_snd_1827_; lean_object* v___f_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v_snd_1827_ = lean_ctor_get(v___y_1826_, 1);
lean_inc(v_snd_1827_);
lean_dec_ref(v___y_1826_);
v___f_1828_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1828_, 0, v_snd_1827_);
lean_closure_set(v___f_1828_, 1, v___x_1820_);
lean_closure_set(v___f_1828_, 2, v_toPure_1821_);
v___x_1829_ = lean_apply_1(v_p_1822_, v_a_1824_);
v___x_1830_ = lean_apply_4(v_toBind_1823_, lean_box(0), lean_box(0), v___x_1829_, v___f_1828_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__2(lean_object* v_toPure_1831_, lean_object* v_____s_1832_){
_start:
{
lean_object* v_fst_1833_; 
v_fst_1833_ = lean_ctor_get(v_____s_1832_, 0);
lean_inc(v_fst_1833_);
lean_dec_ref(v_____s_1832_);
if (lean_obj_tag(v_fst_1833_) == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = lean_box(0);
v___x_1835_ = lean_apply_2(v_toPure_1831_, lean_box(0), v___x_1834_);
return v___x_1835_;
}
else
{
lean_object* v_val_1836_; lean_object* v___x_1837_; 
v_val_1836_ = lean_ctor_get(v_fst_1833_, 0);
lean_inc(v_val_1836_);
lean_dec_ref_known(v_fst_1833_, 1);
v___x_1837_ = lean_apply_2(v_toPure_1831_, lean_box(0), v_val_1836_);
return v___x_1837_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg(lean_object* v_inst_1841_, lean_object* v_p_1842_, lean_object* v_as_1843_){
_start:
{
lean_object* v_toApplicative_1844_; lean_object* v_toBind_1845_; lean_object* v_toPure_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___f_1849_; lean_object* v___f_1850_; size_t v_sz_1851_; size_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v_toApplicative_1844_ = lean_ctor_get(v_inst_1841_, 0);
v_toBind_1845_ = lean_ctor_get(v_inst_1841_, 1);
lean_inc_n(v_toBind_1845_, 2);
v_toPure_1846_ = lean_ctor_get(v_toApplicative_1844_, 1);
v___x_1847_ = lean_box(0);
v___x_1848_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1846_, 2);
v___f_1849_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1849_, 0, v___x_1847_);
lean_closure_set(v___f_1849_, 1, v_toPure_1846_);
lean_closure_set(v___f_1849_, 2, v_p_1842_);
lean_closure_set(v___f_1849_, 3, v_toBind_1845_);
v___f_1850_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1850_, 0, v_toPure_1846_);
v_sz_1851_ = lean_array_size(v_as_1843_);
v___x_1852_ = ((size_t)0ULL);
v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1841_, v_as_1843_, v___f_1849_, v_sz_1851_, v___x_1852_, v___x_1848_);
v___x_1854_ = lean_apply_4(v_toBind_1845_, lean_box(0), lean_box(0), v___x_1853_, v___f_1850_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f(lean_object* v_00_u03b1_1855_, lean_object* v_m_1856_, lean_object* v_inst_1857_, lean_object* v_p_1858_, lean_object* v_as_1859_){
_start:
{
lean_object* v_toApplicative_1860_; lean_object* v_toBind_1861_; lean_object* v_toPure_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___f_1865_; lean_object* v___f_1866_; size_t v_sz_1867_; size_t v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_toApplicative_1860_ = lean_ctor_get(v_inst_1857_, 0);
v_toBind_1861_ = lean_ctor_get(v_inst_1857_, 1);
lean_inc_n(v_toBind_1861_, 2);
v_toPure_1862_ = lean_ctor_get(v_toApplicative_1860_, 1);
v___x_1863_ = lean_box(0);
v___x_1864_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1862_, 2);
v___f_1865_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1865_, 0, v___x_1863_);
lean_closure_set(v___f_1865_, 1, v_toPure_1862_);
lean_closure_set(v___f_1865_, 2, v_p_1858_);
lean_closure_set(v___f_1865_, 3, v_toBind_1861_);
v___f_1866_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1866_, 0, v_toPure_1862_);
v_sz_1867_ = lean_array_size(v_as_1859_);
v___x_1868_ = ((size_t)0ULL);
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1857_, v_as_1859_, v___f_1865_, v_sz_1867_, v___x_1868_, v___x_1864_);
v___x_1870_ = lean_apply_4(v_toBind_1861_, lean_box(0), lean_box(0), v___x_1869_, v___f_1866_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed(lean_object* v_i_1871_, lean_object* v_inst_1872_, lean_object* v_p_1873_, lean_object* v_as_1874_, lean_object* v_stop_1875_, lean_object* v_toApplicative_1876_, lean_object* v___x_1877_, lean_object* v_____do__lift_1878_){
_start:
{
size_t v_i_boxed_1879_; size_t v_stop_boxed_1880_; uint8_t v___x_153__boxed_1881_; uint8_t v_____do__lift_154__boxed_1882_; lean_object* v_res_1883_; 
v_i_boxed_1879_ = lean_unbox_usize(v_i_1871_);
lean_dec(v_i_1871_);
v_stop_boxed_1880_ = lean_unbox_usize(v_stop_1875_);
lean_dec(v_stop_1875_);
v___x_153__boxed_1881_ = lean_unbox(v___x_1877_);
v_____do__lift_154__boxed_1882_ = lean_unbox(v_____do__lift_1878_);
v_res_1883_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(v_i_boxed_1879_, v_inst_1872_, v_p_1873_, v_as_1874_, v_stop_boxed_1880_, v_toApplicative_1876_, v___x_153__boxed_1881_, v_____do__lift_154__boxed_1882_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(lean_object* v_inst_1884_, lean_object* v_p_1885_, lean_object* v_as_1886_, size_t v_i_1887_, size_t v_stop_1888_){
_start:
{
uint8_t v___x_1889_; 
v___x_1889_ = lean_usize_dec_eq(v_i_1887_, v_stop_1888_);
if (v___x_1889_ == 0)
{
lean_object* v_toApplicative_1890_; lean_object* v_toBind_1891_; uint8_t v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___f_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v_toApplicative_1890_ = lean_ctor_get(v_inst_1884_, 0);
lean_inc_ref(v_toApplicative_1890_);
v_toBind_1891_ = lean_ctor_get(v_inst_1884_, 1);
lean_inc(v_toBind_1891_);
v___x_1892_ = 1;
v___x_1893_ = lean_box_usize(v_i_1887_);
v___x_1894_ = lean_box_usize(v_stop_1888_);
v___x_1895_ = lean_box(v___x_1892_);
lean_inc_ref(v_as_1886_);
lean_inc(v_p_1885_);
v___f_1896_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1896_, 0, v___x_1893_);
lean_closure_set(v___f_1896_, 1, v_inst_1884_);
lean_closure_set(v___f_1896_, 2, v_p_1885_);
lean_closure_set(v___f_1896_, 3, v_as_1886_);
lean_closure_set(v___f_1896_, 4, v___x_1894_);
lean_closure_set(v___f_1896_, 5, v_toApplicative_1890_);
lean_closure_set(v___f_1896_, 6, v___x_1895_);
v___x_1897_ = lean_array_uget(v_as_1886_, v_i_1887_);
lean_dec_ref(v_as_1886_);
v___x_1898_ = lean_apply_1(v_p_1885_, v___x_1897_);
v___x_1899_ = lean_apply_4(v_toBind_1891_, lean_box(0), lean_box(0), v___x_1898_, v___f_1896_);
return v___x_1899_;
}
else
{
lean_object* v_toApplicative_1900_; lean_object* v_toPure_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_dec_ref(v_as_1886_);
lean_dec(v_p_1885_);
v_toApplicative_1900_ = lean_ctor_get(v_inst_1884_, 0);
lean_inc_ref(v_toApplicative_1900_);
lean_dec_ref(v_inst_1884_);
v_toPure_1901_ = lean_ctor_get(v_toApplicative_1900_, 1);
lean_inc(v_toPure_1901_);
lean_dec_ref(v_toApplicative_1900_);
v___x_1902_ = 0;
v___x_1903_ = lean_box(v___x_1902_);
v___x_1904_ = lean_apply_2(v_toPure_1901_, lean_box(0), v___x_1903_);
return v___x_1904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(size_t v_i_1905_, lean_object* v_inst_1906_, lean_object* v_p_1907_, lean_object* v_as_1908_, size_t v_stop_1909_, lean_object* v_toApplicative_1910_, uint8_t v___x_1911_, uint8_t v_____do__lift_1912_){
_start:
{
if (v_____do__lift_1912_ == 0)
{
size_t v___x_1913_; size_t v___x_1914_; lean_object* v___x_1915_; 
lean_dec_ref(v_toApplicative_1910_);
v___x_1913_ = ((size_t)1ULL);
v___x_1914_ = lean_usize_add(v_i_1905_, v___x_1913_);
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1906_, v_p_1907_, v_as_1908_, v___x_1914_, v_stop_1909_);
return v___x_1915_;
}
else
{
lean_object* v_toPure_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_dec_ref(v_as_1908_);
lean_dec(v_p_1907_);
lean_dec_ref(v_inst_1906_);
v_toPure_1916_ = lean_ctor_get(v_toApplicative_1910_, 1);
lean_inc(v_toPure_1916_);
lean_dec_ref(v_toApplicative_1910_);
v___x_1917_ = lean_box(v___x_1911_);
v___x_1918_ = lean_apply_2(v_toPure_1916_, lean_box(0), v___x_1917_);
return v___x_1918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___boxed(lean_object* v_inst_1919_, lean_object* v_p_1920_, lean_object* v_as_1921_, lean_object* v_i_1922_, lean_object* v_stop_1923_){
_start:
{
size_t v_i_boxed_1924_; size_t v_stop_boxed_1925_; lean_object* v_res_1926_; 
v_i_boxed_1924_ = lean_unbox_usize(v_i_1922_);
lean_dec(v_i_1922_);
v_stop_boxed_1925_ = lean_unbox_usize(v_stop_1923_);
lean_dec(v_stop_1923_);
v_res_1926_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1919_, v_p_1920_, v_as_1921_, v_i_boxed_1924_, v_stop_boxed_1925_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object* v_00_u03b1_1927_, lean_object* v_m_1928_, lean_object* v_inst_1929_, lean_object* v_p_1930_, lean_object* v_as_1931_, size_t v_i_1932_, size_t v_stop_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1929_, v_p_1930_, v_as_1931_, v_i_1932_, v_stop_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___boxed(lean_object* v_00_u03b1_1935_, lean_object* v_m_1936_, lean_object* v_inst_1937_, lean_object* v_p_1938_, lean_object* v_as_1939_, lean_object* v_i_1940_, lean_object* v_stop_1941_){
_start:
{
size_t v_i_boxed_1942_; size_t v_stop_boxed_1943_; lean_object* v_res_1944_; 
v_i_boxed_1942_ = lean_unbox_usize(v_i_1940_);
lean_dec(v_i_1940_);
v_stop_boxed_1943_ = lean_unbox_usize(v_stop_1941_);
lean_dec(v_stop_1941_);
v_res_1944_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(v_00_u03b1_1935_, v_m_1936_, v_inst_1937_, v_p_1938_, v_as_1939_, v_i_boxed_1942_, v_stop_boxed_1943_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg(lean_object* v_inst_1945_, lean_object* v_p_1946_, lean_object* v_as_1947_, lean_object* v_start_1948_, lean_object* v_stop_1949_){
_start:
{
lean_object* v___y_1951_; uint8_t v___x_1960_; 
v___x_1960_ = lean_nat_dec_lt(v_start_1948_, v_stop_1949_);
if (v___x_1960_ == 0)
{
lean_object* v_toApplicative_1961_; lean_object* v_toPure_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec(v_stop_1949_);
lean_dec_ref(v_as_1947_);
lean_dec(v_p_1946_);
v_toApplicative_1961_ = lean_ctor_get(v_inst_1945_, 0);
lean_inc_ref(v_toApplicative_1961_);
lean_dec_ref(v_inst_1945_);
v_toPure_1962_ = lean_ctor_get(v_toApplicative_1961_, 1);
lean_inc(v_toPure_1962_);
lean_dec_ref(v_toApplicative_1961_);
v___x_1963_ = lean_box(v___x_1960_);
v___x_1964_ = lean_apply_2(v_toPure_1962_, lean_box(0), v___x_1963_);
return v___x_1964_;
}
else
{
lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1965_ = lean_array_get_size(v_as_1947_);
v___x_1966_ = lean_nat_dec_le(v_stop_1949_, v___x_1965_);
if (v___x_1966_ == 0)
{
lean_dec(v_stop_1949_);
v___y_1951_ = v___x_1965_;
goto v___jp_1950_;
}
else
{
v___y_1951_ = v_stop_1949_;
goto v___jp_1950_;
}
}
v___jp_1950_:
{
uint8_t v___x_1952_; 
v___x_1952_ = lean_nat_dec_lt(v_start_1948_, v___y_1951_);
if (v___x_1952_ == 0)
{
lean_object* v_toApplicative_1953_; lean_object* v_toPure_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_dec(v___y_1951_);
lean_dec_ref(v_as_1947_);
lean_dec(v_p_1946_);
v_toApplicative_1953_ = lean_ctor_get(v_inst_1945_, 0);
lean_inc_ref(v_toApplicative_1953_);
lean_dec_ref(v_inst_1945_);
v_toPure_1954_ = lean_ctor_get(v_toApplicative_1953_, 1);
lean_inc(v_toPure_1954_);
lean_dec_ref(v_toApplicative_1953_);
v___x_1955_ = lean_box(v___x_1952_);
v___x_1956_ = lean_apply_2(v_toPure_1954_, lean_box(0), v___x_1955_);
return v___x_1956_;
}
else
{
size_t v___x_1957_; size_t v___x_1958_; lean_object* v___x_1959_; 
v___x_1957_ = lean_usize_of_nat(v_start_1948_);
v___x_1958_ = lean_usize_of_nat(v___y_1951_);
lean_dec(v___y_1951_);
v___x_1959_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1945_, v_p_1946_, v_as_1947_, v___x_1957_, v___x_1958_);
return v___x_1959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg___boxed(lean_object* v_inst_1967_, lean_object* v_p_1968_, lean_object* v_as_1969_, lean_object* v_start_1970_, lean_object* v_stop_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Array_anyMUnsafe___redArg(v_inst_1967_, v_p_1968_, v_as_1969_, v_start_1970_, v_stop_1971_);
lean_dec(v_start_1970_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe(lean_object* v_00_u03b1_1973_, lean_object* v_m_1974_, lean_object* v_inst_1975_, lean_object* v_p_1976_, lean_object* v_as_1977_, lean_object* v_start_1978_, lean_object* v_stop_1979_){
_start:
{
lean_object* v___y_1981_; uint8_t v___x_1990_; 
v___x_1990_ = lean_nat_dec_lt(v_start_1978_, v_stop_1979_);
if (v___x_1990_ == 0)
{
lean_object* v_toApplicative_1991_; lean_object* v_toPure_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_dec(v_stop_1979_);
lean_dec_ref(v_as_1977_);
lean_dec(v_p_1976_);
v_toApplicative_1991_ = lean_ctor_get(v_inst_1975_, 0);
lean_inc_ref(v_toApplicative_1991_);
lean_dec_ref(v_inst_1975_);
v_toPure_1992_ = lean_ctor_get(v_toApplicative_1991_, 1);
lean_inc(v_toPure_1992_);
lean_dec_ref(v_toApplicative_1991_);
v___x_1993_ = lean_box(v___x_1990_);
v___x_1994_ = lean_apply_2(v_toPure_1992_, lean_box(0), v___x_1993_);
return v___x_1994_;
}
else
{
lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = lean_array_get_size(v_as_1977_);
v___x_1996_ = lean_nat_dec_le(v_stop_1979_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_dec(v_stop_1979_);
v___y_1981_ = v___x_1995_;
goto v___jp_1980_;
}
else
{
v___y_1981_ = v_stop_1979_;
goto v___jp_1980_;
}
}
v___jp_1980_:
{
uint8_t v___x_1982_; 
v___x_1982_ = lean_nat_dec_lt(v_start_1978_, v___y_1981_);
if (v___x_1982_ == 0)
{
lean_object* v_toApplicative_1983_; lean_object* v_toPure_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
lean_dec(v___y_1981_);
lean_dec_ref(v_as_1977_);
lean_dec(v_p_1976_);
v_toApplicative_1983_ = lean_ctor_get(v_inst_1975_, 0);
lean_inc_ref(v_toApplicative_1983_);
lean_dec_ref(v_inst_1975_);
v_toPure_1984_ = lean_ctor_get(v_toApplicative_1983_, 1);
lean_inc(v_toPure_1984_);
lean_dec_ref(v_toApplicative_1983_);
v___x_1985_ = lean_box(v___x_1982_);
v___x_1986_ = lean_apply_2(v_toPure_1984_, lean_box(0), v___x_1985_);
return v___x_1986_;
}
else
{
size_t v___x_1987_; size_t v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = lean_usize_of_nat(v_start_1978_);
v___x_1988_ = lean_usize_of_nat(v___y_1981_);
lean_dec(v___y_1981_);
v___x_1989_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1975_, v_p_1976_, v_as_1977_, v___x_1987_, v___x_1988_);
return v___x_1989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___boxed(lean_object* v_00_u03b1_1997_, lean_object* v_m_1998_, lean_object* v_inst_1999_, lean_object* v_p_2000_, lean_object* v_as_2001_, lean_object* v_start_2002_, lean_object* v_stop_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Array_anyMUnsafe(v_00_u03b1_1997_, v_m_1998_, v_inst_1999_, v_p_2000_, v_as_2001_, v_start_2002_, v_stop_2003_);
lean_dec(v_start_2002_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0___boxed(lean_object* v_j_2005_, lean_object* v_inst_2006_, lean_object* v_p_2007_, lean_object* v_as_2008_, lean_object* v_stop_2009_, lean_object* v_toApplicative_2010_, lean_object* v_____do__lift_2011_){
_start:
{
uint8_t v_____do__lift_82__boxed_2012_; lean_object* v_res_2013_; 
v_____do__lift_82__boxed_2012_ = lean_unbox(v_____do__lift_2011_);
v_res_2013_ = l_Array_anyM_loop___redArg___lam__0(v_j_2005_, v_inst_2006_, v_p_2007_, v_as_2008_, v_stop_2009_, v_toApplicative_2010_, v_____do__lift_82__boxed_2012_);
lean_dec(v_j_2005_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg(lean_object* v_inst_2014_, lean_object* v_p_2015_, lean_object* v_as_2016_, lean_object* v_stop_2017_, lean_object* v_j_2018_){
_start:
{
uint8_t v___x_2019_; 
v___x_2019_ = lean_nat_dec_lt(v_j_2018_, v_stop_2017_);
if (v___x_2019_ == 0)
{
lean_object* v_toApplicative_2020_; lean_object* v_toPure_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec(v_j_2018_);
lean_dec(v_stop_2017_);
lean_dec_ref(v_as_2016_);
lean_dec(v_p_2015_);
v_toApplicative_2020_ = lean_ctor_get(v_inst_2014_, 0);
lean_inc_ref(v_toApplicative_2020_);
lean_dec_ref(v_inst_2014_);
v_toPure_2021_ = lean_ctor_get(v_toApplicative_2020_, 1);
lean_inc(v_toPure_2021_);
lean_dec_ref(v_toApplicative_2020_);
v___x_2022_ = lean_box(v___x_2019_);
v___x_2023_ = lean_apply_2(v_toPure_2021_, lean_box(0), v___x_2022_);
return v___x_2023_;
}
else
{
lean_object* v_toApplicative_2024_; lean_object* v_toBind_2025_; lean_object* v___f_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v_toApplicative_2024_ = lean_ctor_get(v_inst_2014_, 0);
lean_inc_ref(v_toApplicative_2024_);
v_toBind_2025_ = lean_ctor_get(v_inst_2014_, 1);
lean_inc(v_toBind_2025_);
lean_inc_ref(v_as_2016_);
lean_inc(v_p_2015_);
lean_inc(v_j_2018_);
v___f_2026_ = lean_alloc_closure((void*)(l_Array_anyM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_2026_, 0, v_j_2018_);
lean_closure_set(v___f_2026_, 1, v_inst_2014_);
lean_closure_set(v___f_2026_, 2, v_p_2015_);
lean_closure_set(v___f_2026_, 3, v_as_2016_);
lean_closure_set(v___f_2026_, 4, v_stop_2017_);
lean_closure_set(v___f_2026_, 5, v_toApplicative_2024_);
v___x_2027_ = lean_array_fget(v_as_2016_, v_j_2018_);
lean_dec(v_j_2018_);
lean_dec_ref(v_as_2016_);
v___x_2028_ = lean_apply_1(v_p_2015_, v___x_2027_);
v___x_2029_ = lean_apply_4(v_toBind_2025_, lean_box(0), lean_box(0), v___x_2028_, v___f_2026_);
return v___x_2029_;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0(lean_object* v_j_2030_, lean_object* v_inst_2031_, lean_object* v_p_2032_, lean_object* v_as_2033_, lean_object* v_stop_2034_, lean_object* v_toApplicative_2035_, uint8_t v_____do__lift_2036_){
_start:
{
if (v_____do__lift_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec_ref(v_toApplicative_2035_);
v___x_2037_ = lean_unsigned_to_nat(1u);
v___x_2038_ = lean_nat_add(v_j_2030_, v___x_2037_);
v___x_2039_ = l_Array_anyM_loop___redArg(v_inst_2031_, v_p_2032_, v_as_2033_, v_stop_2034_, v___x_2038_);
return v___x_2039_;
}
else
{
lean_object* v_toPure_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
lean_dec(v_stop_2034_);
lean_dec_ref(v_as_2033_);
lean_dec(v_p_2032_);
lean_dec_ref(v_inst_2031_);
v_toPure_2040_ = lean_ctor_get(v_toApplicative_2035_, 1);
lean_inc(v_toPure_2040_);
lean_dec_ref(v_toApplicative_2035_);
v___x_2041_ = lean_box(v_____do__lift_2036_);
v___x_2042_ = lean_apply_2(v_toPure_2040_, lean_box(0), v___x_2041_);
return v___x_2042_;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop(lean_object* v_00_u03b1_2043_, lean_object* v_m_2044_, lean_object* v_inst_2045_, lean_object* v_p_2046_, lean_object* v_as_2047_, lean_object* v_stop_2048_, lean_object* v_h_2049_, lean_object* v_j_2050_){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Array_anyM_loop___redArg(v_inst_2045_, v_p_2046_, v_as_2047_, v_stop_2048_, v_j_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0(lean_object* v_toPure_2052_, uint8_t v_____do__lift_2053_){
_start:
{
uint8_t v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = lean_bool_not(v_____do__lift_2053_);
v___x_2055_ = lean_box(v___x_2054_);
v___x_2056_ = lean_apply_2(v_toPure_2052_, lean_box(0), v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0___boxed(lean_object* v_toPure_2057_, lean_object* v_____do__lift_2058_){
_start:
{
uint8_t v_____do__lift_99__boxed_2059_; lean_object* v_res_2060_; 
v_____do__lift_99__boxed_2059_ = lean_unbox(v_____do__lift_2058_);
v_res_2060_ = l_Array_allM___redArg___lam__0(v_toPure_2057_, v_____do__lift_99__boxed_2059_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__2(lean_object* v_p_2061_, lean_object* v_toBind_2062_, lean_object* v___f_2063_, lean_object* v_v_2064_){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = lean_apply_1(v_p_2061_, v_v_2064_);
v___x_2066_ = lean_apply_4(v_toBind_2062_, lean_box(0), lean_box(0), v___x_2065_, v___f_2063_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg(lean_object* v_inst_2067_, lean_object* v_p_2068_, lean_object* v_as_2069_, lean_object* v_start_2070_, lean_object* v_stop_2071_){
_start:
{
lean_object* v_toApplicative_2072_; lean_object* v_toBind_2073_; lean_object* v_toPure_2074_; lean_object* v___f_2075_; uint8_t v___x_2076_; 
v_toApplicative_2072_ = lean_ctor_get(v_inst_2067_, 0);
v_toBind_2073_ = lean_ctor_get(v_inst_2067_, 1);
lean_inc(v_toBind_2073_);
v_toPure_2074_ = lean_ctor_get(v_toApplicative_2072_, 1);
lean_inc(v_toPure_2074_);
v___f_2075_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2075_, 0, v_toPure_2074_);
v___x_2076_ = lean_nat_dec_lt(v_start_2070_, v_stop_2071_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
lean_inc(v_toPure_2074_);
lean_dec(v_stop_2071_);
lean_dec_ref(v_as_2069_);
lean_dec(v_p_2068_);
lean_dec_ref(v_inst_2067_);
v___x_2077_ = lean_box(v___x_2076_);
v___x_2078_ = lean_apply_2(v_toPure_2074_, lean_box(0), v___x_2077_);
v___x_2079_ = lean_apply_4(v_toBind_2073_, lean_box(0), lean_box(0), v___x_2078_, v___f_2075_);
return v___x_2079_;
}
else
{
lean_object* v___f_2080_; lean_object* v___y_2082_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
lean_inc_ref(v___f_2075_);
lean_inc(v_toBind_2073_);
v___f_2080_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2080_, 0, v_p_2068_);
lean_closure_set(v___f_2080_, 1, v_toBind_2073_);
lean_closure_set(v___f_2080_, 2, v___f_2075_);
v___x_2091_ = lean_array_get_size(v_as_2069_);
v___x_2092_ = lean_nat_dec_le(v_stop_2071_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_dec(v_stop_2071_);
v___y_2082_ = v___x_2091_;
goto v___jp_2081_;
}
else
{
v___y_2082_ = v_stop_2071_;
goto v___jp_2081_;
}
v___jp_2081_:
{
uint8_t v___x_2083_; 
v___x_2083_ = lean_nat_dec_lt(v_start_2070_, v___y_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_inc(v_toPure_2074_);
lean_dec(v___y_2082_);
lean_dec_ref(v___f_2080_);
lean_dec_ref(v_as_2069_);
lean_dec_ref(v_inst_2067_);
v___x_2084_ = lean_box(v___x_2083_);
v___x_2085_ = lean_apply_2(v_toPure_2074_, lean_box(0), v___x_2084_);
v___x_2086_ = lean_apply_4(v_toBind_2073_, lean_box(0), lean_box(0), v___x_2085_, v___f_2075_);
return v___x_2086_;
}
else
{
size_t v___x_2087_; size_t v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2087_ = lean_usize_of_nat(v_start_2070_);
v___x_2088_ = lean_usize_of_nat(v___y_2082_);
lean_dec(v___y_2082_);
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2067_, v___f_2080_, v_as_2069_, v___x_2087_, v___x_2088_);
v___x_2090_ = lean_apply_4(v_toBind_2073_, lean_box(0), lean_box(0), v___x_2089_, v___f_2075_);
return v___x_2090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___boxed(lean_object* v_inst_2093_, lean_object* v_p_2094_, lean_object* v_as_2095_, lean_object* v_start_2096_, lean_object* v_stop_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Array_allM___redArg(v_inst_2093_, v_p_2094_, v_as_2095_, v_start_2096_, v_stop_2097_);
lean_dec(v_start_2096_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Array_allM(lean_object* v_00_u03b1_2099_, lean_object* v_m_2100_, lean_object* v_inst_2101_, lean_object* v_p_2102_, lean_object* v_as_2103_, lean_object* v_start_2104_, lean_object* v_stop_2105_){
_start:
{
lean_object* v_toApplicative_2106_; lean_object* v_toBind_2107_; lean_object* v_toPure_2108_; lean_object* v___f_2109_; uint8_t v___x_2110_; 
v_toApplicative_2106_ = lean_ctor_get(v_inst_2101_, 0);
v_toBind_2107_ = lean_ctor_get(v_inst_2101_, 1);
lean_inc(v_toBind_2107_);
v_toPure_2108_ = lean_ctor_get(v_toApplicative_2106_, 1);
lean_inc(v_toPure_2108_);
v___f_2109_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2109_, 0, v_toPure_2108_);
v___x_2110_ = lean_nat_dec_lt(v_start_2104_, v_stop_2105_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_inc(v_toPure_2108_);
lean_dec(v_stop_2105_);
lean_dec_ref(v_as_2103_);
lean_dec(v_p_2102_);
lean_dec_ref(v_inst_2101_);
v___x_2111_ = lean_box(v___x_2110_);
v___x_2112_ = lean_apply_2(v_toPure_2108_, lean_box(0), v___x_2111_);
v___x_2113_ = lean_apply_4(v_toBind_2107_, lean_box(0), lean_box(0), v___x_2112_, v___f_2109_);
return v___x_2113_;
}
else
{
lean_object* v___f_2114_; lean_object* v___y_2116_; lean_object* v___x_2125_; uint8_t v___x_2126_; 
lean_inc_ref(v___f_2109_);
lean_inc(v_toBind_2107_);
v___f_2114_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2114_, 0, v_p_2102_);
lean_closure_set(v___f_2114_, 1, v_toBind_2107_);
lean_closure_set(v___f_2114_, 2, v___f_2109_);
v___x_2125_ = lean_array_get_size(v_as_2103_);
v___x_2126_ = lean_nat_dec_le(v_stop_2105_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_dec(v_stop_2105_);
v___y_2116_ = v___x_2125_;
goto v___jp_2115_;
}
else
{
v___y_2116_ = v_stop_2105_;
goto v___jp_2115_;
}
v___jp_2115_:
{
uint8_t v___x_2117_; 
v___x_2117_ = lean_nat_dec_lt(v_start_2104_, v___y_2116_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_inc(v_toPure_2108_);
lean_dec(v___y_2116_);
lean_dec_ref(v___f_2114_);
lean_dec_ref(v_as_2103_);
lean_dec_ref(v_inst_2101_);
v___x_2118_ = lean_box(v___x_2117_);
v___x_2119_ = lean_apply_2(v_toPure_2108_, lean_box(0), v___x_2118_);
v___x_2120_ = lean_apply_4(v_toBind_2107_, lean_box(0), lean_box(0), v___x_2119_, v___f_2109_);
return v___x_2120_;
}
else
{
size_t v___x_2121_; size_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2121_ = lean_usize_of_nat(v_start_2104_);
v___x_2122_ = lean_usize_of_nat(v___y_2116_);
lean_dec(v___y_2116_);
v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2101_, v___f_2114_, v_as_2103_, v___x_2121_, v___x_2122_);
v___x_2124_ = lean_apply_4(v_toBind_2107_, lean_box(0), lean_box(0), v___x_2123_, v___f_2109_);
return v___x_2124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___boxed(lean_object* v_00_u03b1_2127_, lean_object* v_m_2128_, lean_object* v_inst_2129_, lean_object* v_p_2130_, lean_object* v_as_2131_, lean_object* v_start_2132_, lean_object* v_stop_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Array_allM(v_00_u03b1_2127_, v_m_2128_, v_inst_2129_, v_p_2130_, v_as_2131_, v_start_2132_, v_stop_2133_);
lean_dec(v_start_2132_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed(lean_object* v_inst_2135_, lean_object* v_f_2136_, lean_object* v_as_2137_, lean_object* v_n_2138_, lean_object* v_toPure_2139_, lean_object* v_r_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(v_inst_2135_, v_f_2136_, v_as_2137_, v_n_2138_, v_toPure_2139_, v_r_2140_);
lean_dec(v_n_2138_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(lean_object* v_inst_2142_, lean_object* v_f_2143_, lean_object* v_as_2144_, lean_object* v_i_2145_){
_start:
{
lean_object* v_toApplicative_2146_; lean_object* v_toBind_2147_; lean_object* v_toPure_2148_; lean_object* v_zero_2149_; uint8_t v_isZero_2150_; 
v_toApplicative_2146_ = lean_ctor_get(v_inst_2142_, 0);
v_toBind_2147_ = lean_ctor_get(v_inst_2142_, 1);
lean_inc(v_toBind_2147_);
v_toPure_2148_ = lean_ctor_get(v_toApplicative_2146_, 1);
lean_inc(v_toPure_2148_);
v_zero_2149_ = lean_unsigned_to_nat(0u);
v_isZero_2150_ = lean_nat_dec_eq(v_i_2145_, v_zero_2149_);
if (v_isZero_2150_ == 1)
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
lean_dec(v_toBind_2147_);
lean_dec_ref(v_as_2144_);
lean_dec(v_f_2143_);
lean_dec_ref(v_inst_2142_);
v___x_2151_ = lean_box(0);
v___x_2152_ = lean_apply_2(v_toPure_2148_, lean_box(0), v___x_2151_);
return v___x_2152_;
}
else
{
lean_object* v_one_2153_; lean_object* v_n_2154_; lean_object* v___f_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v_one_2153_ = lean_unsigned_to_nat(1u);
v_n_2154_ = lean_nat_sub(v_i_2145_, v_one_2153_);
lean_inc(v_n_2154_);
lean_inc_ref(v_as_2144_);
lean_inc(v_f_2143_);
v___f_2155_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2155_, 0, v_inst_2142_);
lean_closure_set(v___f_2155_, 1, v_f_2143_);
lean_closure_set(v___f_2155_, 2, v_as_2144_);
lean_closure_set(v___f_2155_, 3, v_n_2154_);
lean_closure_set(v___f_2155_, 4, v_toPure_2148_);
v___x_2156_ = lean_array_fget(v_as_2144_, v_n_2154_);
lean_dec(v_n_2154_);
lean_dec_ref(v_as_2144_);
v___x_2157_ = lean_apply_1(v_f_2143_, v___x_2156_);
v___x_2158_ = lean_apply_4(v_toBind_2147_, lean_box(0), lean_box(0), v___x_2157_, v___f_2155_);
return v___x_2158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(lean_object* v_inst_2159_, lean_object* v_f_2160_, lean_object* v_as_2161_, lean_object* v_n_2162_, lean_object* v_toPure_2163_, lean_object* v_r_2164_){
_start:
{
if (lean_obj_tag(v_r_2164_) == 0)
{
lean_object* v___x_2165_; 
lean_dec(v_toPure_2163_);
v___x_2165_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2159_, v_f_2160_, v_as_2161_, v_n_2162_);
return v___x_2165_;
}
else
{
lean_object* v___x_2166_; 
lean_dec_ref(v_as_2161_);
lean_dec(v_f_2160_);
lean_dec_ref(v_inst_2159_);
v___x_2166_ = lean_apply_2(v_toPure_2163_, lean_box(0), v_r_2164_);
return v___x_2166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___boxed(lean_object* v_inst_2167_, lean_object* v_f_2168_, lean_object* v_as_2169_, lean_object* v_i_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2167_, v_f_2168_, v_as_2169_, v_i_2170_);
lean_dec(v_i_2170_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_object* v_00_u03b1_2172_, lean_object* v_00_u03b2_2173_, lean_object* v_m_2174_, lean_object* v_inst_2175_, lean_object* v_f_2176_, lean_object* v_as_2177_, lean_object* v_i_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2175_, v_f_2176_, v_as_2177_, v_i_2178_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___boxed(lean_object* v_00_u03b1_2181_, lean_object* v_00_u03b2_2182_, lean_object* v_m_2183_, lean_object* v_inst_2184_, lean_object* v_f_2185_, lean_object* v_as_2186_, lean_object* v_i_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(v_00_u03b1_2181_, v_00_u03b2_2182_, v_m_2183_, v_inst_2184_, v_f_2185_, v_as_2186_, v_i_2187_, v_a_2188_);
lean_dec(v_i_2187_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f___redArg(lean_object* v_inst_2190_, lean_object* v_f_2191_, lean_object* v_as_2192_){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = lean_array_get_size(v_as_2192_);
v___x_2194_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2190_, v_f_2191_, v_as_2192_, v___x_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f(lean_object* v_00_u03b1_2195_, lean_object* v_00_u03b2_2196_, lean_object* v_m_2197_, lean_object* v_inst_2198_, lean_object* v_f_2199_, lean_object* v_as_2200_){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = lean_array_get_size(v_as_2200_);
v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2198_, v_f_2199_, v_as_2200_, v___x_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2203_, lean_object* v_a_2204_, uint8_t v_____do__lift_2205_){
_start:
{
if (v_____do__lift_2205_ == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec(v_a_2204_);
v___x_2206_ = lean_box(0);
v___x_2207_ = lean_apply_2(v_toPure_2203_, lean_box(0), v___x_2206_);
return v___x_2207_;
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_a_2204_);
v___x_2209_ = lean_apply_2(v_toPure_2203_, lean_box(0), v___x_2208_);
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2210_, lean_object* v_a_2211_, lean_object* v_____do__lift_2212_){
_start:
{
uint8_t v_____do__lift_74__boxed_2213_; lean_object* v_res_2214_; 
v_____do__lift_74__boxed_2213_ = lean_unbox(v_____do__lift_2212_);
v_res_2214_ = l_Array_findRevM_x3f___redArg___lam__0(v_toPure_2210_, v_a_2211_, v_____do__lift_74__boxed_2213_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2215_, lean_object* v_p_2216_, lean_object* v_toBind_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v___f_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_inc(v_a_2218_);
v___f_2219_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2219_, 0, v_toPure_2215_);
lean_closure_set(v___f_2219_, 1, v_a_2218_);
v___x_2220_ = lean_apply_1(v_p_2216_, v_a_2218_);
v___x_2221_ = lean_apply_4(v_toBind_2217_, lean_box(0), lean_box(0), v___x_2220_, v___f_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg(lean_object* v_inst_2222_, lean_object* v_p_2223_, lean_object* v_as_2224_){
_start:
{
lean_object* v_toApplicative_2225_; lean_object* v_toBind_2226_; lean_object* v_toPure_2227_; lean_object* v___f_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v_toApplicative_2225_ = lean_ctor_get(v_inst_2222_, 0);
v_toBind_2226_ = lean_ctor_get(v_inst_2222_, 1);
v_toPure_2227_ = lean_ctor_get(v_toApplicative_2225_, 1);
lean_inc(v_toBind_2226_);
lean_inc(v_toPure_2227_);
v___f_2228_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2228_, 0, v_toPure_2227_);
lean_closure_set(v___f_2228_, 1, v_p_2223_);
lean_closure_set(v___f_2228_, 2, v_toBind_2226_);
v___x_2229_ = lean_array_get_size(v_as_2224_);
v___x_2230_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2222_, v___f_2228_, v_as_2224_, v___x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f(lean_object* v_00_u03b1_2231_, lean_object* v_m_2232_, lean_object* v_inst_2233_, lean_object* v_p_2234_, lean_object* v_as_2235_){
_start:
{
lean_object* v_toApplicative_2236_; lean_object* v_toBind_2237_; lean_object* v_toPure_2238_; lean_object* v___f_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v_toApplicative_2236_ = lean_ctor_get(v_inst_2233_, 0);
v_toBind_2237_ = lean_ctor_get(v_inst_2233_, 1);
v_toPure_2238_ = lean_ctor_get(v_toApplicative_2236_, 1);
lean_inc(v_toBind_2237_);
lean_inc(v_toPure_2238_);
v___f_2239_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2239_, 0, v_toPure_2238_);
lean_closure_set(v___f_2239_, 1, v_p_2234_);
lean_closure_set(v___f_2239_, 2, v_toBind_2237_);
v___x_2240_ = lean_array_get_size(v_as_2235_);
v___x_2241_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2233_, v___f_2239_, v_as_2235_, v___x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___lam__0(lean_object* v_f_2242_, lean_object* v_x_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_apply_1(v_f_2242_, v___y_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg(lean_object* v_inst_2246_, lean_object* v_f_2247_, lean_object* v_as_2248_, lean_object* v_start_2249_, lean_object* v_stop_2250_){
_start:
{
lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_nat_dec_lt(v_start_2249_, v_stop_2250_);
if (v___x_2252_ == 0)
{
lean_object* v_toApplicative_2253_; lean_object* v_toPure_2254_; lean_object* v___x_2255_; 
lean_dec_ref(v_as_2248_);
lean_dec(v_f_2247_);
v_toApplicative_2253_ = lean_ctor_get(v_inst_2246_, 0);
lean_inc_ref(v_toApplicative_2253_);
lean_dec_ref(v_inst_2246_);
v_toPure_2254_ = lean_ctor_get(v_toApplicative_2253_, 1);
lean_inc(v_toPure_2254_);
lean_dec_ref(v_toApplicative_2253_);
v___x_2255_ = lean_apply_2(v_toPure_2254_, lean_box(0), v___x_2251_);
return v___x_2255_;
}
else
{
lean_object* v___f_2256_; lean_object* v___x_2257_; uint8_t v___x_2258_; 
v___f_2256_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2256_, 0, v_f_2247_);
v___x_2257_ = lean_array_get_size(v_as_2248_);
v___x_2258_ = lean_nat_dec_le(v_stop_2250_, v___x_2257_);
if (v___x_2258_ == 0)
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_nat_dec_lt(v_start_2249_, v___x_2257_);
if (v___x_2259_ == 0)
{
lean_object* v_toApplicative_2260_; lean_object* v_toPure_2261_; lean_object* v___x_2262_; 
lean_dec_ref(v___f_2256_);
lean_dec_ref(v_as_2248_);
v_toApplicative_2260_ = lean_ctor_get(v_inst_2246_, 0);
lean_inc_ref(v_toApplicative_2260_);
lean_dec_ref(v_inst_2246_);
v_toPure_2261_ = lean_ctor_get(v_toApplicative_2260_, 1);
lean_inc(v_toPure_2261_);
lean_dec_ref(v_toApplicative_2260_);
v___x_2262_ = lean_apply_2(v_toPure_2261_, lean_box(0), v___x_2251_);
return v___x_2262_;
}
else
{
size_t v___x_2263_; size_t v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = lean_usize_of_nat(v_start_2249_);
v___x_2264_ = lean_usize_of_nat(v___x_2257_);
v___x_2265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2246_, v___f_2256_, v_as_2248_, v___x_2263_, v___x_2264_, v___x_2251_);
return v___x_2265_;
}
}
else
{
size_t v___x_2266_; size_t v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = lean_usize_of_nat(v_start_2249_);
v___x_2267_ = lean_usize_of_nat(v_stop_2250_);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2246_, v___f_2256_, v_as_2248_, v___x_2266_, v___x_2267_, v___x_2251_);
return v___x_2268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___boxed(lean_object* v_inst_2269_, lean_object* v_f_2270_, lean_object* v_as_2271_, lean_object* v_start_2272_, lean_object* v_stop_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Array_forM___redArg(v_inst_2269_, v_f_2270_, v_as_2271_, v_start_2272_, v_stop_2273_);
lean_dec(v_stop_2273_);
lean_dec(v_start_2272_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Array_forM(lean_object* v_00_u03b1_2275_, lean_object* v_m_2276_, lean_object* v_inst_2277_, lean_object* v_f_2278_, lean_object* v_as_2279_, lean_object* v_start_2280_, lean_object* v_stop_2281_){
_start:
{
lean_object* v___x_2282_; uint8_t v___x_2283_; 
v___x_2282_ = lean_box(0);
v___x_2283_ = lean_nat_dec_lt(v_start_2280_, v_stop_2281_);
if (v___x_2283_ == 0)
{
lean_object* v_toApplicative_2284_; lean_object* v_toPure_2285_; lean_object* v___x_2286_; 
lean_dec_ref(v_as_2279_);
lean_dec(v_f_2278_);
v_toApplicative_2284_ = lean_ctor_get(v_inst_2277_, 0);
lean_inc_ref(v_toApplicative_2284_);
lean_dec_ref(v_inst_2277_);
v_toPure_2285_ = lean_ctor_get(v_toApplicative_2284_, 1);
lean_inc(v_toPure_2285_);
lean_dec_ref(v_toApplicative_2284_);
v___x_2286_ = lean_apply_2(v_toPure_2285_, lean_box(0), v___x_2282_);
return v___x_2286_;
}
else
{
lean_object* v___f_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___f_2287_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2287_, 0, v_f_2278_);
v___x_2288_ = lean_array_get_size(v_as_2279_);
v___x_2289_ = lean_nat_dec_le(v_stop_2281_, v___x_2288_);
if (v___x_2289_ == 0)
{
uint8_t v___x_2290_; 
v___x_2290_ = lean_nat_dec_lt(v_start_2280_, v___x_2288_);
if (v___x_2290_ == 0)
{
lean_object* v_toApplicative_2291_; lean_object* v_toPure_2292_; lean_object* v___x_2293_; 
lean_dec_ref(v___f_2287_);
lean_dec_ref(v_as_2279_);
v_toApplicative_2291_ = lean_ctor_get(v_inst_2277_, 0);
lean_inc_ref(v_toApplicative_2291_);
lean_dec_ref(v_inst_2277_);
v_toPure_2292_ = lean_ctor_get(v_toApplicative_2291_, 1);
lean_inc(v_toPure_2292_);
lean_dec_ref(v_toApplicative_2291_);
v___x_2293_ = lean_apply_2(v_toPure_2292_, lean_box(0), v___x_2282_);
return v___x_2293_;
}
else
{
size_t v___x_2294_; size_t v___x_2295_; lean_object* v___x_2296_; 
v___x_2294_ = lean_usize_of_nat(v_start_2280_);
v___x_2295_ = lean_usize_of_nat(v___x_2288_);
v___x_2296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2277_, v___f_2287_, v_as_2279_, v___x_2294_, v___x_2295_, v___x_2282_);
return v___x_2296_;
}
}
else
{
size_t v___x_2297_; size_t v___x_2298_; lean_object* v___x_2299_; 
v___x_2297_ = lean_usize_of_nat(v_start_2280_);
v___x_2298_ = lean_usize_of_nat(v_stop_2281_);
v___x_2299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2277_, v___f_2287_, v_as_2279_, v___x_2297_, v___x_2298_, v___x_2282_);
return v___x_2299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___boxed(lean_object* v_00_u03b1_2300_, lean_object* v_m_2301_, lean_object* v_inst_2302_, lean_object* v_f_2303_, lean_object* v_as_2304_, lean_object* v_start_2305_, lean_object* v_stop_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Array_forM(v_00_u03b1_2300_, v_m_2301_, v_inst_2302_, v_f_2303_, v_as_2304_, v_start_2305_, v_stop_2306_);
lean_dec(v_stop_2306_);
lean_dec(v_start_2305_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg___lam__1(lean_object* v_inst_2308_, lean_object* v_xs_2309_, lean_object* v_f_2310_){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2311_ = lean_unsigned_to_nat(0u);
v___x_2312_ = lean_array_get_size(v_xs_2309_);
v___x_2313_ = lean_box(0);
v___x_2314_ = lean_nat_dec_lt(v___x_2311_, v___x_2312_);
if (v___x_2314_ == 0)
{
lean_object* v_toApplicative_2315_; lean_object* v_toPure_2316_; lean_object* v___x_2317_; 
lean_dec(v_f_2310_);
lean_dec_ref(v_xs_2309_);
v_toApplicative_2315_ = lean_ctor_get(v_inst_2308_, 0);
lean_inc_ref(v_toApplicative_2315_);
lean_dec_ref(v_inst_2308_);
v_toPure_2316_ = lean_ctor_get(v_toApplicative_2315_, 1);
lean_inc(v_toPure_2316_);
lean_dec_ref(v_toApplicative_2315_);
v___x_2317_ = lean_apply_2(v_toPure_2316_, lean_box(0), v___x_2313_);
return v___x_2317_;
}
else
{
lean_object* v___f_2318_; uint8_t v___x_2319_; 
v___f_2318_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2318_, 0, v_f_2310_);
v___x_2319_ = lean_nat_dec_le(v___x_2312_, v___x_2312_);
if (v___x_2319_ == 0)
{
if (v___x_2314_ == 0)
{
lean_object* v_toApplicative_2320_; lean_object* v_toPure_2321_; lean_object* v___x_2322_; 
lean_dec_ref(v___f_2318_);
lean_dec_ref(v_xs_2309_);
v_toApplicative_2320_ = lean_ctor_get(v_inst_2308_, 0);
lean_inc_ref(v_toApplicative_2320_);
lean_dec_ref(v_inst_2308_);
v_toPure_2321_ = lean_ctor_get(v_toApplicative_2320_, 1);
lean_inc(v_toPure_2321_);
lean_dec_ref(v_toApplicative_2320_);
v___x_2322_ = lean_apply_2(v_toPure_2321_, lean_box(0), v___x_2313_);
return v___x_2322_;
}
else
{
size_t v___x_2323_; size_t v___x_2324_; lean_object* v___x_2325_; 
v___x_2323_ = ((size_t)0ULL);
v___x_2324_ = lean_usize_of_nat(v___x_2312_);
v___x_2325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2308_, v___f_2318_, v_xs_2309_, v___x_2323_, v___x_2324_, v___x_2313_);
return v___x_2325_;
}
}
else
{
size_t v___x_2326_; size_t v___x_2327_; lean_object* v___x_2328_; 
v___x_2326_ = ((size_t)0ULL);
v___x_2327_ = lean_usize_of_nat(v___x_2312_);
v___x_2328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2308_, v___f_2318_, v_xs_2309_, v___x_2326_, v___x_2327_, v___x_2313_);
return v___x_2328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg(lean_object* v_inst_2329_){
_start:
{
lean_object* v___f_2330_; 
v___f_2330_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2330_, 0, v_inst_2329_);
return v___f_2330_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad(lean_object* v_00_u03b1_2331_, lean_object* v_m_2332_, lean_object* v_inst_2333_){
_start:
{
lean_object* v___f_2334_; 
v___f_2334_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2334_, 0, v_inst_2333_);
return v___f_2334_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___lam__0(lean_object* v_f_2335_, lean_object* v_a_2336_, lean_object* v_x_2337_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_apply_1(v_f_2335_, v_a_2336_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg(lean_object* v_inst_2339_, lean_object* v_f_2340_, lean_object* v_as_2341_, lean_object* v_start_2342_, lean_object* v_stop_2343_){
_start:
{
lean_object* v___f_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___f_2344_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2344_, 0, v_f_2340_);
v___x_2345_ = lean_box(0);
v___x_2346_ = lean_array_get_size(v_as_2341_);
v___x_2347_ = lean_nat_dec_le(v_start_2342_, v___x_2346_);
if (v___x_2347_ == 0)
{
uint8_t v___x_2348_; 
v___x_2348_ = lean_nat_dec_lt(v_stop_2343_, v___x_2346_);
if (v___x_2348_ == 0)
{
lean_object* v_toApplicative_2349_; lean_object* v_toPure_2350_; lean_object* v___x_2351_; 
lean_dec_ref(v___f_2344_);
lean_dec_ref(v_as_2341_);
v_toApplicative_2349_ = lean_ctor_get(v_inst_2339_, 0);
lean_inc_ref(v_toApplicative_2349_);
lean_dec_ref(v_inst_2339_);
v_toPure_2350_ = lean_ctor_get(v_toApplicative_2349_, 1);
lean_inc(v_toPure_2350_);
lean_dec_ref(v_toApplicative_2349_);
v___x_2351_ = lean_apply_2(v_toPure_2350_, lean_box(0), v___x_2345_);
return v___x_2351_;
}
else
{
size_t v___x_2352_; size_t v___x_2353_; lean_object* v___x_2354_; 
v___x_2352_ = lean_usize_of_nat(v___x_2346_);
v___x_2353_ = lean_usize_of_nat(v_stop_2343_);
v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2339_, v___f_2344_, v_as_2341_, v___x_2352_, v___x_2353_, v___x_2345_);
return v___x_2354_;
}
}
else
{
uint8_t v___x_2355_; 
v___x_2355_ = lean_nat_dec_lt(v_stop_2343_, v_start_2342_);
if (v___x_2355_ == 0)
{
lean_object* v_toApplicative_2356_; lean_object* v_toPure_2357_; lean_object* v___x_2358_; 
lean_dec_ref(v___f_2344_);
lean_dec_ref(v_as_2341_);
v_toApplicative_2356_ = lean_ctor_get(v_inst_2339_, 0);
lean_inc_ref(v_toApplicative_2356_);
lean_dec_ref(v_inst_2339_);
v_toPure_2357_ = lean_ctor_get(v_toApplicative_2356_, 1);
lean_inc(v_toPure_2357_);
lean_dec_ref(v_toApplicative_2356_);
v___x_2358_ = lean_apply_2(v_toPure_2357_, lean_box(0), v___x_2345_);
return v___x_2358_;
}
else
{
size_t v___x_2359_; size_t v___x_2360_; lean_object* v___x_2361_; 
v___x_2359_ = lean_usize_of_nat(v_start_2342_);
v___x_2360_ = lean_usize_of_nat(v_stop_2343_);
v___x_2361_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2339_, v___f_2344_, v_as_2341_, v___x_2359_, v___x_2360_, v___x_2345_);
return v___x_2361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___boxed(lean_object* v_inst_2362_, lean_object* v_f_2363_, lean_object* v_as_2364_, lean_object* v_start_2365_, lean_object* v_stop_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Array_forRevM___redArg(v_inst_2362_, v_f_2363_, v_as_2364_, v_start_2365_, v_stop_2366_);
lean_dec(v_stop_2366_);
lean_dec(v_start_2365_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM(lean_object* v_00_u03b1_2368_, lean_object* v_m_2369_, lean_object* v_inst_2370_, lean_object* v_f_2371_, lean_object* v_as_2372_, lean_object* v_start_2373_, lean_object* v_stop_2374_){
_start:
{
lean_object* v___f_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___f_2375_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2375_, 0, v_f_2371_);
v___x_2376_ = lean_box(0);
v___x_2377_ = lean_array_get_size(v_as_2372_);
v___x_2378_ = lean_nat_dec_le(v_start_2373_, v___x_2377_);
if (v___x_2378_ == 0)
{
uint8_t v___x_2379_; 
v___x_2379_ = lean_nat_dec_lt(v_stop_2374_, v___x_2377_);
if (v___x_2379_ == 0)
{
lean_object* v_toApplicative_2380_; lean_object* v_toPure_2381_; lean_object* v___x_2382_; 
lean_dec_ref(v___f_2375_);
lean_dec_ref(v_as_2372_);
v_toApplicative_2380_ = lean_ctor_get(v_inst_2370_, 0);
lean_inc_ref(v_toApplicative_2380_);
lean_dec_ref(v_inst_2370_);
v_toPure_2381_ = lean_ctor_get(v_toApplicative_2380_, 1);
lean_inc(v_toPure_2381_);
lean_dec_ref(v_toApplicative_2380_);
v___x_2382_ = lean_apply_2(v_toPure_2381_, lean_box(0), v___x_2376_);
return v___x_2382_;
}
else
{
size_t v___x_2383_; size_t v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = lean_usize_of_nat(v___x_2377_);
v___x_2384_ = lean_usize_of_nat(v_stop_2374_);
v___x_2385_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2370_, v___f_2375_, v_as_2372_, v___x_2383_, v___x_2384_, v___x_2376_);
return v___x_2385_;
}
}
else
{
uint8_t v___x_2386_; 
v___x_2386_ = lean_nat_dec_lt(v_stop_2374_, v_start_2373_);
if (v___x_2386_ == 0)
{
lean_object* v_toApplicative_2387_; lean_object* v_toPure_2388_; lean_object* v___x_2389_; 
lean_dec_ref(v___f_2375_);
lean_dec_ref(v_as_2372_);
v_toApplicative_2387_ = lean_ctor_get(v_inst_2370_, 0);
lean_inc_ref(v_toApplicative_2387_);
lean_dec_ref(v_inst_2370_);
v_toPure_2388_ = lean_ctor_get(v_toApplicative_2387_, 1);
lean_inc(v_toPure_2388_);
lean_dec_ref(v_toApplicative_2387_);
v___x_2389_ = lean_apply_2(v_toPure_2388_, lean_box(0), v___x_2376_);
return v___x_2389_;
}
else
{
size_t v___x_2390_; size_t v___x_2391_; lean_object* v___x_2392_; 
v___x_2390_ = lean_usize_of_nat(v_start_2373_);
v___x_2391_ = lean_usize_of_nat(v_stop_2374_);
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2370_, v___f_2375_, v_as_2372_, v___x_2390_, v___x_2391_, v___x_2376_);
return v___x_2392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___boxed(lean_object* v_00_u03b1_2393_, lean_object* v_m_2394_, lean_object* v_inst_2395_, lean_object* v_f_2396_, lean_object* v_as_2397_, lean_object* v_start_2398_, lean_object* v_stop_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Array_forRevM(v_00_u03b1_2393_, v_m_2394_, v_inst_2395_, v_f_2396_, v_as_2397_, v_start_2398_, v_stop_2399_);
lean_dec(v_stop_2399_);
lean_dec(v_start_2398_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___lam__0(lean_object* v_f_2401_, lean_object* v_x1_2402_, lean_object* v_x2_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_apply_2(v_f_2401_, v_x1_2402_, v_x2_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg(lean_object* v_f_2424_, lean_object* v_init_2425_, lean_object* v_as_2426_, lean_object* v_start_2427_, lean_object* v_stop_2428_){
_start:
{
lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2429_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2430_ = lean_nat_dec_lt(v_start_2427_, v_stop_2428_);
if (v___x_2430_ == 0)
{
lean_dec_ref(v_as_2426_);
lean_dec(v_f_2424_);
return v_init_2425_;
}
else
{
lean_object* v___f_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___f_2431_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2431_, 0, v_f_2424_);
v___x_2432_ = lean_array_get_size(v_as_2426_);
v___x_2433_ = lean_nat_dec_le(v_stop_2428_, v___x_2432_);
if (v___x_2433_ == 0)
{
uint8_t v___x_2434_; 
v___x_2434_ = lean_nat_dec_lt(v_start_2427_, v___x_2432_);
if (v___x_2434_ == 0)
{
lean_dec_ref(v___f_2431_);
lean_dec_ref(v_as_2426_);
return v_init_2425_;
}
else
{
size_t v___x_2435_; size_t v___x_2436_; lean_object* v___x_2437_; 
v___x_2435_ = lean_usize_of_nat(v_start_2427_);
v___x_2436_ = lean_usize_of_nat(v___x_2432_);
v___x_2437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2429_, v___f_2431_, v_as_2426_, v___x_2435_, v___x_2436_, v_init_2425_);
return v___x_2437_;
}
}
else
{
size_t v___x_2438_; size_t v___x_2439_; lean_object* v___x_2440_; 
v___x_2438_ = lean_usize_of_nat(v_start_2427_);
v___x_2439_ = lean_usize_of_nat(v_stop_2428_);
v___x_2440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2429_, v___f_2431_, v_as_2426_, v___x_2438_, v___x_2439_, v_init_2425_);
return v___x_2440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___boxed(lean_object* v_f_2441_, lean_object* v_init_2442_, lean_object* v_as_2443_, lean_object* v_start_2444_, lean_object* v_stop_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Array_foldl___redArg(v_f_2441_, v_init_2442_, v_as_2443_, v_start_2444_, v_stop_2445_);
lean_dec(v_stop_2445_);
lean_dec(v_start_2444_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl(lean_object* v_00_u03b1_2447_, lean_object* v_00_u03b2_2448_, lean_object* v_f_2449_, lean_object* v_init_2450_, lean_object* v_as_2451_, lean_object* v_start_2452_, lean_object* v_stop_2453_){
_start:
{
lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___x_2454_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2455_ = lean_nat_dec_lt(v_start_2452_, v_stop_2453_);
if (v___x_2455_ == 0)
{
lean_dec_ref(v_as_2451_);
lean_dec(v_f_2449_);
return v_init_2450_;
}
else
{
lean_object* v___f_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___f_2456_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2456_, 0, v_f_2449_);
v___x_2457_ = lean_array_get_size(v_as_2451_);
v___x_2458_ = lean_nat_dec_le(v_stop_2453_, v___x_2457_);
if (v___x_2458_ == 0)
{
uint8_t v___x_2459_; 
v___x_2459_ = lean_nat_dec_lt(v_start_2452_, v___x_2457_);
if (v___x_2459_ == 0)
{
lean_dec_ref(v___f_2456_);
lean_dec_ref(v_as_2451_);
return v_init_2450_;
}
else
{
size_t v___x_2460_; size_t v___x_2461_; lean_object* v___x_2462_; 
v___x_2460_ = lean_usize_of_nat(v_start_2452_);
v___x_2461_ = lean_usize_of_nat(v___x_2457_);
v___x_2462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2454_, v___f_2456_, v_as_2451_, v___x_2460_, v___x_2461_, v_init_2450_);
return v___x_2462_;
}
}
else
{
size_t v___x_2463_; size_t v___x_2464_; lean_object* v___x_2465_; 
v___x_2463_ = lean_usize_of_nat(v_start_2452_);
v___x_2464_ = lean_usize_of_nat(v_stop_2453_);
v___x_2465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2454_, v___f_2456_, v_as_2451_, v___x_2463_, v___x_2464_, v_init_2450_);
return v___x_2465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___boxed(lean_object* v_00_u03b1_2466_, lean_object* v_00_u03b2_2467_, lean_object* v_f_2468_, lean_object* v_init_2469_, lean_object* v_as_2470_, lean_object* v_start_2471_, lean_object* v_stop_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Array_foldl(v_00_u03b1_2466_, v_00_u03b2_2467_, v_f_2468_, v_init_2469_, v_as_2470_, v_start_2471_, v_stop_2472_);
lean_dec(v_stop_2472_);
lean_dec(v_start_2471_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg(lean_object* v_f_2474_, lean_object* v_init_2475_, lean_object* v_as_2476_, lean_object* v_start_2477_, lean_object* v_stop_2478_){
_start:
{
lean_object* v___f_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v___f_2479_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2479_, 0, v_f_2474_);
v___x_2480_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2481_ = lean_array_get_size(v_as_2476_);
v___x_2482_ = lean_nat_dec_le(v_start_2477_, v___x_2481_);
if (v___x_2482_ == 0)
{
uint8_t v___x_2483_; 
v___x_2483_ = lean_nat_dec_lt(v_stop_2478_, v___x_2481_);
if (v___x_2483_ == 0)
{
lean_dec_ref(v___f_2479_);
lean_dec_ref(v_as_2476_);
return v_init_2475_;
}
else
{
size_t v___x_2484_; size_t v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = lean_usize_of_nat(v___x_2481_);
v___x_2485_ = lean_usize_of_nat(v_stop_2478_);
v___x_2486_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2480_, v___f_2479_, v_as_2476_, v___x_2484_, v___x_2485_, v_init_2475_);
return v___x_2486_;
}
}
else
{
uint8_t v___x_2487_; 
v___x_2487_ = lean_nat_dec_lt(v_stop_2478_, v_start_2477_);
if (v___x_2487_ == 0)
{
lean_dec_ref(v___f_2479_);
lean_dec_ref(v_as_2476_);
return v_init_2475_;
}
else
{
size_t v___x_2488_; size_t v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = lean_usize_of_nat(v_start_2477_);
v___x_2489_ = lean_usize_of_nat(v_stop_2478_);
v___x_2490_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2480_, v___f_2479_, v_as_2476_, v___x_2488_, v___x_2489_, v_init_2475_);
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg___boxed(lean_object* v_f_2491_, lean_object* v_init_2492_, lean_object* v_as_2493_, lean_object* v_start_2494_, lean_object* v_stop_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Array_foldr___redArg(v_f_2491_, v_init_2492_, v_as_2493_, v_start_2494_, v_stop_2495_);
lean_dec(v_stop_2495_);
lean_dec(v_start_2494_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr(lean_object* v_00_u03b1_2497_, lean_object* v_00_u03b2_2498_, lean_object* v_f_2499_, lean_object* v_init_2500_, lean_object* v_as_2501_, lean_object* v_start_2502_, lean_object* v_stop_2503_){
_start:
{
lean_object* v___f_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
v___f_2504_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2504_, 0, v_f_2499_);
v___x_2505_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2506_ = lean_array_get_size(v_as_2501_);
v___x_2507_ = lean_nat_dec_le(v_start_2502_, v___x_2506_);
if (v___x_2507_ == 0)
{
uint8_t v___x_2508_; 
v___x_2508_ = lean_nat_dec_lt(v_stop_2503_, v___x_2506_);
if (v___x_2508_ == 0)
{
lean_dec_ref(v___f_2504_);
lean_dec_ref(v_as_2501_);
return v_init_2500_;
}
else
{
size_t v___x_2509_; size_t v___x_2510_; lean_object* v___x_2511_; 
v___x_2509_ = lean_usize_of_nat(v___x_2506_);
v___x_2510_ = lean_usize_of_nat(v_stop_2503_);
v___x_2511_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2505_, v___f_2504_, v_as_2501_, v___x_2509_, v___x_2510_, v_init_2500_);
return v___x_2511_;
}
}
else
{
uint8_t v___x_2512_; 
v___x_2512_ = lean_nat_dec_lt(v_stop_2503_, v_start_2502_);
if (v___x_2512_ == 0)
{
lean_dec_ref(v___f_2504_);
lean_dec_ref(v_as_2501_);
return v_init_2500_;
}
else
{
size_t v___x_2513_; size_t v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = lean_usize_of_nat(v_start_2502_);
v___x_2514_ = lean_usize_of_nat(v_stop_2503_);
v___x_2515_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2505_, v___f_2504_, v_as_2501_, v___x_2513_, v___x_2514_, v_init_2500_);
return v___x_2515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___boxed(lean_object* v_00_u03b1_2516_, lean_object* v_00_u03b2_2517_, lean_object* v_f_2518_, lean_object* v_init_2519_, lean_object* v_as_2520_, lean_object* v_start_2521_, lean_object* v_stop_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Array_foldr(v_00_u03b1_2516_, v_00_u03b2_2517_, v_f_2518_, v_init_2519_, v_as_2520_, v_start_2521_, v_stop_2522_);
lean_dec(v_stop_2522_);
lean_dec(v_start_2521_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg___lam__0(lean_object* v_inst_2524_, lean_object* v_x1_2525_, lean_object* v_x2_2526_){
_start:
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_apply_2(v_inst_2524_, v_x1_2525_, v_x2_2526_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg(lean_object* v_inst_2528_, lean_object* v_inst_2529_, lean_object* v_as_2530_){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2531_ = lean_array_get_size(v_as_2530_);
v___x_2532_ = lean_unsigned_to_nat(0u);
v___x_2533_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2534_ = lean_nat_dec_lt(v___x_2532_, v___x_2531_);
if (v___x_2534_ == 0)
{
lean_dec_ref(v_as_2530_);
lean_dec(v_inst_2528_);
return v_inst_2529_;
}
else
{
lean_object* v___f_2535_; size_t v___x_2536_; size_t v___x_2537_; lean_object* v___x_2538_; 
v___f_2535_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2535_, 0, v_inst_2528_);
v___x_2536_ = lean_usize_of_nat(v___x_2531_);
v___x_2537_ = ((size_t)0ULL);
v___x_2538_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2533_, v___f_2535_, v_as_2530_, v___x_2536_, v___x_2537_, v_inst_2529_);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l_Array_sum(lean_object* v_00_u03b1_2539_, lean_object* v_inst_2540_, lean_object* v_inst_2541_, lean_object* v_as_2542_){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2543_ = lean_array_get_size(v_as_2542_);
v___x_2544_ = lean_unsigned_to_nat(0u);
v___x_2545_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2546_ = lean_nat_dec_lt(v___x_2544_, v___x_2543_);
if (v___x_2546_ == 0)
{
lean_dec_ref(v_as_2542_);
lean_dec(v_inst_2540_);
return v_inst_2541_;
}
else
{
lean_object* v___f_2547_; size_t v___x_2548_; size_t v___x_2549_; lean_object* v___x_2550_; 
v___f_2547_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2547_, 0, v_inst_2540_);
v___x_2548_ = lean_usize_of_nat(v___x_2543_);
v___x_2549_ = ((size_t)0ULL);
v___x_2550_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2545_, v___f_2547_, v_as_2542_, v___x_2548_, v___x_2549_, v_inst_2541_);
return v___x_2550_;
}
}
}
LEAN_EXPORT lean_object* l_Array_prod___redArg(lean_object* v_inst_2551_, lean_object* v_inst_2552_, lean_object* v_as_2553_){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___x_2554_ = lean_array_get_size(v_as_2553_);
v___x_2555_ = lean_unsigned_to_nat(0u);
v___x_2556_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2557_ = lean_nat_dec_lt(v___x_2555_, v___x_2554_);
if (v___x_2557_ == 0)
{
lean_dec_ref(v_as_2553_);
lean_dec(v_inst_2551_);
return v_inst_2552_;
}
else
{
lean_object* v___f_2558_; size_t v___x_2559_; size_t v___x_2560_; lean_object* v___x_2561_; 
v___f_2558_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2558_, 0, v_inst_2551_);
v___x_2559_ = lean_usize_of_nat(v___x_2554_);
v___x_2560_ = ((size_t)0ULL);
v___x_2561_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2556_, v___f_2558_, v_as_2553_, v___x_2559_, v___x_2560_, v_inst_2552_);
return v___x_2561_;
}
}
}
LEAN_EXPORT lean_object* l_Array_prod(lean_object* v_00_u03b1_2562_, lean_object* v_inst_2563_, lean_object* v_inst_2564_, lean_object* v_as_2565_){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2566_ = lean_array_get_size(v_as_2565_);
v___x_2567_ = lean_unsigned_to_nat(0u);
v___x_2568_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2569_ = lean_nat_dec_lt(v___x_2567_, v___x_2566_);
if (v___x_2569_ == 0)
{
lean_dec_ref(v_as_2565_);
lean_dec(v_inst_2563_);
return v_inst_2564_;
}
else
{
lean_object* v___f_2570_; size_t v___x_2571_; size_t v___x_2572_; lean_object* v___x_2573_; 
v___f_2570_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2570_, 0, v_inst_2563_);
v___x_2571_ = lean_usize_of_nat(v___x_2566_);
v___x_2572_ = ((size_t)0ULL);
v___x_2573_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2568_, v___f_2570_, v_as_2565_, v___x_2571_, v___x_2572_, v_inst_2564_);
return v___x_2573_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0(lean_object* v_p_2574_, lean_object* v_x1_2575_, lean_object* v_x2_2576_){
_start:
{
lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2577_ = lean_apply_1(v_p_2574_, v_x1_2575_);
v___x_2578_ = lean_unbox(v___x_2577_);
if (v___x_2578_ == 0)
{
lean_inc(v_x2_2576_);
return v_x2_2576_;
}
else
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = lean_unsigned_to_nat(1u);
v___x_2580_ = lean_nat_add(v_x2_2576_, v___x_2579_);
return v___x_2580_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0___boxed(lean_object* v_p_2581_, lean_object* v_x1_2582_, lean_object* v_x2_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Array_countP___redArg___lam__0(v_p_2581_, v_x1_2582_, v_x2_2583_);
lean_dec(v_x2_2583_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg(lean_object* v_p_2585_, lean_object* v_as_2586_){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2587_ = lean_unsigned_to_nat(0u);
v___x_2588_ = lean_array_get_size(v_as_2586_);
v___x_2589_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2590_ = lean_nat_dec_lt(v___x_2587_, v___x_2588_);
if (v___x_2590_ == 0)
{
lean_dec_ref(v_as_2586_);
lean_dec_ref(v_p_2585_);
return v___x_2587_;
}
else
{
lean_object* v___f_2591_; size_t v___x_2592_; size_t v___x_2593_; lean_object* v___x_2594_; 
v___f_2591_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2591_, 0, v_p_2585_);
v___x_2592_ = lean_usize_of_nat(v___x_2588_);
v___x_2593_ = ((size_t)0ULL);
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2589_, v___f_2591_, v_as_2586_, v___x_2592_, v___x_2593_, v___x_2587_);
return v___x_2594_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP(lean_object* v_00_u03b1_2595_, lean_object* v_p_2596_, lean_object* v_as_2597_){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v___x_2598_ = lean_unsigned_to_nat(0u);
v___x_2599_ = lean_array_get_size(v_as_2597_);
v___x_2600_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2601_ = lean_nat_dec_lt(v___x_2598_, v___x_2599_);
if (v___x_2601_ == 0)
{
lean_dec_ref(v_as_2597_);
lean_dec_ref(v_p_2596_);
return v___x_2598_;
}
else
{
lean_object* v___f_2602_; size_t v___x_2603_; size_t v___x_2604_; lean_object* v___x_2605_; 
v___f_2602_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2602_, 0, v_p_2596_);
v___x_2603_ = lean_usize_of_nat(v___x_2599_);
v___x_2604_ = ((size_t)0ULL);
v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2600_, v___f_2602_, v_as_2597_, v___x_2603_, v___x_2604_, v___x_2598_);
return v___x_2605_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0(lean_object* v_inst_2606_, lean_object* v_a_2607_, lean_object* v_x1_2608_, lean_object* v_x2_2609_){
_start:
{
lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2610_ = lean_apply_2(v_inst_2606_, v_x1_2608_, v_a_2607_);
v___x_2611_ = lean_unbox(v___x_2610_);
if (v___x_2611_ == 0)
{
lean_inc(v_x2_2609_);
return v_x2_2609_;
}
else
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_unsigned_to_nat(1u);
v___x_2613_ = lean_nat_add(v_x2_2609_, v___x_2612_);
return v___x_2613_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0___boxed(lean_object* v_inst_2614_, lean_object* v_a_2615_, lean_object* v_x1_2616_, lean_object* v_x2_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Array_count___redArg___lam__0(v_inst_2614_, v_a_2615_, v_x1_2616_, v_x2_2617_);
lean_dec(v_x2_2617_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg(lean_object* v_inst_2619_, lean_object* v_a_2620_, lean_object* v_as_2621_){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2622_ = lean_unsigned_to_nat(0u);
v___x_2623_ = lean_array_get_size(v_as_2621_);
v___x_2624_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2625_ = lean_nat_dec_lt(v___x_2622_, v___x_2623_);
if (v___x_2625_ == 0)
{
lean_dec_ref(v_as_2621_);
lean_dec(v_a_2620_);
lean_dec_ref(v_inst_2619_);
return v___x_2622_;
}
else
{
lean_object* v___f_2626_; size_t v___x_2627_; size_t v___x_2628_; lean_object* v___x_2629_; 
v___f_2626_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2626_, 0, v_inst_2619_);
lean_closure_set(v___f_2626_, 1, v_a_2620_);
v___x_2627_ = lean_usize_of_nat(v___x_2623_);
v___x_2628_ = ((size_t)0ULL);
v___x_2629_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2624_, v___f_2626_, v_as_2621_, v___x_2627_, v___x_2628_, v___x_2622_);
return v___x_2629_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count(lean_object* v_00_u03b1_2630_, lean_object* v_inst_2631_, lean_object* v_a_2632_, lean_object* v_as_2633_){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2634_ = lean_unsigned_to_nat(0u);
v___x_2635_ = lean_array_get_size(v_as_2633_);
v___x_2636_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2637_ = lean_nat_dec_lt(v___x_2634_, v___x_2635_);
if (v___x_2637_ == 0)
{
lean_dec_ref(v_as_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_inst_2631_);
return v___x_2634_;
}
else
{
lean_object* v___f_2638_; size_t v___x_2639_; size_t v___x_2640_; lean_object* v___x_2641_; 
v___f_2638_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2638_, 0, v_inst_2631_);
lean_closure_set(v___f_2638_, 1, v_a_2632_);
v___x_2639_ = lean_usize_of_nat(v___x_2635_);
v___x_2640_ = ((size_t)0ULL);
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2636_, v___f_2638_, v_as_2633_, v___x_2639_, v___x_2640_, v___x_2634_);
return v___x_2641_;
}
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg___lam__0(lean_object* v_f_2642_, lean_object* v_x_2643_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = lean_apply_1(v_f_2642_, v_x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg(lean_object* v_f_2645_, lean_object* v_as_2646_){
_start:
{
lean_object* v___f_2647_; lean_object* v___x_2648_; size_t v_sz_2649_; size_t v___x_2650_; lean_object* v___x_2651_; 
v___f_2647_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2647_, 0, v_f_2645_);
v___x_2648_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2649_ = lean_array_size(v_as_2646_);
v___x_2650_ = ((size_t)0ULL);
v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2648_, v___f_2647_, v_sz_2649_, v___x_2650_, v_as_2646_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Array_map(lean_object* v_00_u03b1_2652_, lean_object* v_00_u03b2_2653_, lean_object* v_f_2654_, lean_object* v_as_2655_){
_start:
{
lean_object* v___f_2656_; lean_object* v___x_2657_; size_t v_sz_2658_; size_t v___x_2659_; lean_object* v___x_2660_; 
v___f_2656_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2656_, 0, v_f_2654_);
v___x_2657_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2658_ = lean_array_size(v_as_2655_);
v___x_2659_ = ((size_t)0ULL);
v___x_2660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2657_, v___f_2656_, v_sz_2658_, v___x_2659_, v_as_2655_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0(lean_object* v___y_2661_, lean_object* v_x_2662_){
_start:
{
lean_inc(v___y_2661_);
return v___y_2661_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0___boxed(lean_object* v___y_2663_, lean_object* v_x_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Array_instFunctor___lam__0(v___y_2663_, v_x_2664_);
lean_dec(v_x_2664_);
lean_dec(v___y_2663_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__1(lean_object* v_00_u03b1_2666_, lean_object* v_00_u03b2_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___f_2670_; lean_object* v___x_2671_; size_t v_sz_2672_; size_t v___x_2673_; lean_object* v___x_2674_; 
v___f_2670_ = lean_alloc_closure((void*)(l_Array_instFunctor___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2670_, 0, v___y_2668_);
v___x_2671_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2672_ = lean_array_size(v___y_2669_);
v___x_2673_ = ((size_t)0ULL);
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2671_, v___f_2670_, v_sz_2672_, v___x_2673_, v___y_2669_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg___lam__0(lean_object* v_f_2681_, lean_object* v_x1_2682_, lean_object* v_x2_2683_, lean_object* v_x3_2684_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = lean_apply_3(v_f_2681_, v_x1_2682_, v_x2_2683_, lean_box(0));
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg(lean_object* v_as_2686_, lean_object* v_f_2687_){
_start:
{
lean_object* v___f_2688_; lean_object* v___x_2689_; size_t v_sz_2690_; size_t v___x_2691_; lean_object* v___x_2692_; 
v___f_2688_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2688_, 0, v_f_2687_);
v___x_2689_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2690_ = lean_array_size(v_as_2686_);
v___x_2691_ = ((size_t)0ULL);
v___x_2692_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2689_, v___f_2688_, v_sz_2690_, v___x_2691_, v_as_2686_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx(lean_object* v_00_u03b1_2693_, lean_object* v_00_u03b2_2694_, lean_object* v_as_2695_, lean_object* v_f_2696_){
_start:
{
lean_object* v___f_2697_; lean_object* v___x_2698_; size_t v_sz_2699_; size_t v___x_2700_; lean_object* v___x_2701_; 
v___f_2697_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2697_, 0, v_f_2696_);
v___x_2698_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2699_ = lean_array_size(v_as_2695_);
v___x_2700_ = ((size_t)0ULL);
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2698_, v___f_2697_, v_sz_2699_, v___x_2700_, v_as_2695_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx___redArg(lean_object* v_f_2702_, lean_object* v_as_2703_){
_start:
{
lean_object* v___f_2704_; lean_object* v___x_2705_; size_t v_sz_2706_; size_t v___x_2707_; lean_object* v___x_2708_; 
v___f_2704_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2704_, 0, v_f_2702_);
v___x_2705_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2706_ = lean_array_size(v_as_2703_);
v___x_2707_ = ((size_t)0ULL);
v___x_2708_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2705_, v___f_2704_, v_sz_2706_, v___x_2707_, v_as_2703_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx(lean_object* v_00_u03b1_2709_, lean_object* v_00_u03b2_2710_, lean_object* v_f_2711_, lean_object* v_as_2712_){
_start:
{
lean_object* v___f_2713_; lean_object* v___x_2714_; size_t v_sz_2715_; size_t v___x_2716_; lean_object* v___x_2717_; 
v___f_2713_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2713_, 0, v_f_2711_);
v___x_2714_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2715_ = lean_array_size(v_as_2712_);
v___x_2716_ = ((size_t)0ULL);
v___x_2717_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2714_, v___f_2713_, v_sz_2715_, v___x_2716_, v_as_2712_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(lean_object* v_start_2718_, size_t v_sz_2719_, size_t v_i_2720_, lean_object* v_bs_2721_){
_start:
{
uint8_t v___x_2722_; 
v___x_2722_ = lean_usize_dec_lt(v_i_2720_, v_sz_2719_);
if (v___x_2722_ == 0)
{
return v_bs_2721_;
}
else
{
lean_object* v_v_2723_; lean_object* v___x_2724_; lean_object* v_bs_x27_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; size_t v___x_2729_; size_t v___x_2730_; lean_object* v___x_2731_; 
v_v_2723_ = lean_array_uget(v_bs_2721_, v_i_2720_);
v___x_2724_ = lean_unsigned_to_nat(0u);
v_bs_x27_2725_ = lean_array_uset(v_bs_2721_, v_i_2720_, v___x_2724_);
v___x_2726_ = lean_usize_to_nat(v_i_2720_);
v___x_2727_ = lean_nat_add(v_start_2718_, v___x_2726_);
lean_dec(v___x_2726_);
v___x_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2728_, 0, v_v_2723_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = ((size_t)1ULL);
v___x_2730_ = lean_usize_add(v_i_2720_, v___x_2729_);
v___x_2731_ = lean_array_uset(v_bs_x27_2725_, v_i_2720_, v___x_2728_);
v_i_2720_ = v___x_2730_;
v_bs_2721_ = v___x_2731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg___boxed(lean_object* v_start_2733_, lean_object* v_sz_2734_, lean_object* v_i_2735_, lean_object* v_bs_2736_){
_start:
{
size_t v_sz_boxed_2737_; size_t v_i_boxed_2738_; lean_object* v_res_2739_; 
v_sz_boxed_2737_ = lean_unbox_usize(v_sz_2734_);
lean_dec(v_sz_2734_);
v_i_boxed_2738_ = lean_unbox_usize(v_i_2735_);
lean_dec(v_i_2735_);
v_res_2739_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2733_, v_sz_boxed_2737_, v_i_boxed_2738_, v_bs_2736_);
lean_dec(v_start_2733_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg(lean_object* v_xs_2740_, lean_object* v_start_2741_){
_start:
{
size_t v_sz_2742_; size_t v___x_2743_; lean_object* v___x_2744_; 
v_sz_2742_ = lean_array_size(v_xs_2740_);
v___x_2743_ = ((size_t)0ULL);
v___x_2744_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2741_, v_sz_2742_, v___x_2743_, v_xs_2740_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg___boxed(lean_object* v_xs_2745_, lean_object* v_start_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Array_zipIdx___redArg(v_xs_2745_, v_start_2746_);
lean_dec(v_start_2746_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx(lean_object* v_00_u03b1_2748_, lean_object* v_xs_2749_, lean_object* v_start_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Array_zipIdx___redArg(v_xs_2749_, v_start_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___boxed(lean_object* v_00_u03b1_2752_, lean_object* v_xs_2753_, lean_object* v_start_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Array_zipIdx(v_00_u03b1_2752_, v_xs_2753_, v_start_2754_);
lean_dec(v_start_2754_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(lean_object* v_00_u03b1_2756_, lean_object* v_start_2757_, lean_object* v_as_2758_, size_t v_sz_2759_, size_t v_i_2760_, lean_object* v_bs_2761_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2757_, v_sz_2759_, v_i_2760_, v_bs_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___boxed(lean_object* v_00_u03b1_2763_, lean_object* v_start_2764_, lean_object* v_as_2765_, lean_object* v_sz_2766_, lean_object* v_i_2767_, lean_object* v_bs_2768_){
_start:
{
size_t v_sz_boxed_2769_; size_t v_i_boxed_2770_; lean_object* v_res_2771_; 
v_sz_boxed_2769_ = lean_unbox_usize(v_sz_2766_);
lean_dec(v_sz_2766_);
v_i_boxed_2770_ = lean_unbox_usize(v_i_2767_);
lean_dec(v_i_2767_);
v_res_2771_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(v_00_u03b1_2763_, v_start_2764_, v_as_2765_, v_sz_boxed_2769_, v_i_boxed_2770_, v_bs_2768_);
lean_dec_ref(v_as_2765_);
lean_dec(v_start_2764_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0(lean_object* v_p_2772_, lean_object* v___x_2773_, lean_object* v___x_2774_, lean_object* v_a_2775_, lean_object* v_x_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v___x_2778_; uint8_t v___x_2779_; 
lean_inc(v_a_2775_);
v___x_2778_ = lean_apply_1(v_p_2772_, v_a_2775_);
v___x_2779_ = lean_unbox(v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; 
lean_dec(v_a_2775_);
v___x_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2773_);
return v___x_2780_;
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_dec_ref(v___x_2773_);
v___x_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2781_, 0, v_a_2775_);
v___x_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
v___x_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
lean_ctor_set(v___x_2783_, 1, v___x_2774_);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
return v___x_2784_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0___boxed(lean_object* v_p_2785_, lean_object* v___x_2786_, lean_object* v___x_2787_, lean_object* v_a_2788_, lean_object* v_x_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Array_find_x3f___redArg___lam__0(v_p_2785_, v___x_2786_, v___x_2787_, v_a_2788_, v_x_2789_, v___y_2790_);
lean_dec_ref(v___y_2790_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg(lean_object* v_p_2792_, lean_object* v_as_2793_){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___f_2798_; size_t v_sz_2799_; size_t v___x_2800_; lean_object* v___x_2801_; lean_object* v_fst_2802_; 
v___x_2794_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2795_ = lean_box(0);
v___x_2796_ = lean_box(0);
v___x_2797_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2798_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2798_, 0, v_p_2792_);
lean_closure_set(v___f_2798_, 1, v___x_2797_);
lean_closure_set(v___f_2798_, 2, v___x_2796_);
v_sz_2799_ = lean_array_size(v_as_2793_);
v___x_2800_ = ((size_t)0ULL);
v___x_2801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2794_, v_as_2793_, v___f_2798_, v_sz_2799_, v___x_2800_, v___x_2797_);
v_fst_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_fst_2802_);
lean_dec(v___x_2801_);
if (lean_obj_tag(v_fst_2802_) == 0)
{
return v___x_2795_;
}
else
{
lean_object* v_val_2803_; 
v_val_2803_ = lean_ctor_get(v_fst_2802_, 0);
lean_inc(v_val_2803_);
lean_dec_ref_known(v_fst_2802_, 1);
return v_val_2803_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f(lean_object* v_00_u03b1_2804_, lean_object* v_p_2805_, lean_object* v_as_2806_){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___f_2811_; size_t v_sz_2812_; size_t v___x_2813_; lean_object* v___x_2814_; lean_object* v_fst_2815_; 
v___x_2807_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2808_ = lean_box(0);
v___x_2809_ = lean_box(0);
v___x_2810_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2811_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2811_, 0, v_p_2805_);
lean_closure_set(v___f_2811_, 1, v___x_2810_);
lean_closure_set(v___f_2811_, 2, v___x_2809_);
v_sz_2812_ = lean_array_size(v_as_2806_);
v___x_2813_ = ((size_t)0ULL);
v___x_2814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2807_, v_as_2806_, v___f_2811_, v_sz_2812_, v___x_2813_, v___x_2810_);
v_fst_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_fst_2815_);
lean_dec(v___x_2814_);
if (lean_obj_tag(v_fst_2815_) == 0)
{
return v___x_2808_;
}
else
{
lean_object* v_val_2816_; 
v_val_2816_ = lean_ctor_get(v_fst_2815_, 0);
lean_inc(v_val_2816_);
lean_dec_ref_known(v_fst_2815_, 1);
return v_val_2816_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0(lean_object* v_f_2817_, lean_object* v___x_2818_, lean_object* v___x_2819_, lean_object* v_a_2820_, lean_object* v_x_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = lean_apply_1(v_f_2817_, v_a_2820_);
if (lean_obj_tag(v___x_2823_) == 1)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
lean_dec_ref(v___x_2819_);
v___x_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
v___x_2825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
lean_ctor_set(v___x_2825_, 1, v___x_2818_);
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
return v___x_2826_;
}
else
{
lean_object* v___x_2827_; 
lean_dec(v___x_2823_);
v___x_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2819_);
return v___x_2827_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2828_, lean_object* v___x_2829_, lean_object* v___x_2830_, lean_object* v_a_2831_, lean_object* v_x_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Array_findSome_x3f___redArg___lam__0(v_f_2828_, v___x_2829_, v___x_2830_, v_a_2831_, v_x_2832_, v___y_2833_);
lean_dec_ref(v___y_2833_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg(lean_object* v_f_2835_, lean_object* v_as_2836_){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___f_2841_; size_t v_sz_2842_; size_t v___x_2843_; lean_object* v___x_2844_; lean_object* v_fst_2845_; 
v___x_2837_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2838_ = lean_box(0);
v___x_2839_ = lean_box(0);
v___x_2840_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2841_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2841_, 0, v_f_2835_);
lean_closure_set(v___f_2841_, 1, v___x_2839_);
lean_closure_set(v___f_2841_, 2, v___x_2840_);
v_sz_2842_ = lean_array_size(v_as_2836_);
v___x_2843_ = ((size_t)0ULL);
v___x_2844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2837_, v_as_2836_, v___f_2841_, v_sz_2842_, v___x_2843_, v___x_2840_);
v_fst_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_fst_2845_);
lean_dec(v___x_2844_);
if (lean_obj_tag(v_fst_2845_) == 0)
{
return v___x_2838_;
}
else
{
lean_object* v_val_2846_; 
v_val_2846_ = lean_ctor_get(v_fst_2845_, 0);
lean_inc(v_val_2846_);
lean_dec_ref_known(v_fst_2845_, 1);
return v_val_2846_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f(lean_object* v_00_u03b1_2847_, lean_object* v_00_u03b2_2848_, lean_object* v_f_2849_, lean_object* v_as_2850_){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___f_2855_; size_t v_sz_2856_; size_t v___x_2857_; lean_object* v___x_2858_; lean_object* v_fst_2859_; 
v___x_2851_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_box(0);
v___x_2854_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2855_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2855_, 0, v_f_2849_);
lean_closure_set(v___f_2855_, 1, v___x_2853_);
lean_closure_set(v___f_2855_, 2, v___x_2854_);
v_sz_2856_ = lean_array_size(v_as_2850_);
v___x_2857_ = ((size_t)0ULL);
v___x_2858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2851_, v_as_2850_, v___f_2855_, v_sz_2856_, v___x_2857_, v___x_2854_);
v_fst_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_fst_2859_);
lean_dec(v___x_2858_);
if (lean_obj_tag(v_fst_2859_) == 0)
{
return v___x_2852_;
}
else
{
lean_object* v_val_2860_; 
v_val_2860_ = lean_ctor_get(v_fst_2859_, 0);
lean_inc(v_val_2860_);
lean_dec_ref_known(v_fst_2859_, 1);
return v_val_2860_;
}
}
}
static lean_object* _init_l_Array_findSome_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2863_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__1));
v___x_2864_ = lean_unsigned_to_nat(14u);
v___x_2865_ = lean_unsigned_to_nat(1254u);
v___x_2866_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__0));
v___x_2867_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_2868_ = l_mkPanicMessageWithDecl(v___x_2867_, v___x_2866_, v___x_2865_, v___x_2864_, v___x_2863_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg(lean_object* v_inst_2869_, lean_object* v_f_2870_, lean_object* v_xs_2871_){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___f_2878_; size_t v_sz_2879_; size_t v___x_2880_; lean_object* v___x_2881_; lean_object* v_fst_2882_; 
v___x_2875_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2876_ = lean_box(0);
v___x_2877_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2878_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2878_, 0, v_f_2870_);
lean_closure_set(v___f_2878_, 1, v___x_2876_);
lean_closure_set(v___f_2878_, 2, v___x_2877_);
v_sz_2879_ = lean_array_size(v_xs_2871_);
v___x_2880_ = ((size_t)0ULL);
v___x_2881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2875_, v_xs_2871_, v___f_2878_, v_sz_2879_, v___x_2880_, v___x_2877_);
v_fst_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_fst_2882_);
lean_dec(v___x_2881_);
if (lean_obj_tag(v_fst_2882_) == 0)
{
goto v___jp_2872_;
}
else
{
lean_object* v_val_2883_; 
v_val_2883_ = lean_ctor_get(v_fst_2882_, 0);
lean_inc(v_val_2883_);
lean_dec_ref_known(v_fst_2882_, 1);
if (lean_obj_tag(v_val_2883_) == 0)
{
goto v___jp_2872_;
}
else
{
lean_object* v_val_2884_; 
v_val_2884_ = lean_ctor_get(v_val_2883_, 0);
lean_inc(v_val_2884_);
lean_dec_ref_known(v_val_2883_, 1);
return v_val_2884_;
}
}
v___jp_2872_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2874_ = l_panic___redArg(v_inst_2869_, v___x_2873_);
return v___x_2874_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg___boxed(lean_object* v_inst_2885_, lean_object* v_f_2886_, lean_object* v_xs_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Array_findSome_x21___redArg(v_inst_2885_, v_f_2886_, v_xs_2887_);
lean_dec(v_inst_2885_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21(lean_object* v_00_u03b1_2889_, lean_object* v_00_u03b2_2890_, lean_object* v_inst_2891_, lean_object* v_f_2892_, lean_object* v_xs_2893_){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___f_2900_; size_t v_sz_2901_; size_t v___x_2902_; lean_object* v___x_2903_; lean_object* v_fst_2904_; 
v___x_2897_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2898_ = lean_box(0);
v___x_2899_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2900_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2900_, 0, v_f_2892_);
lean_closure_set(v___f_2900_, 1, v___x_2898_);
lean_closure_set(v___f_2900_, 2, v___x_2899_);
v_sz_2901_ = lean_array_size(v_xs_2893_);
v___x_2902_ = ((size_t)0ULL);
v___x_2903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2897_, v_xs_2893_, v___f_2900_, v_sz_2901_, v___x_2902_, v___x_2899_);
v_fst_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_fst_2904_);
lean_dec(v___x_2903_);
if (lean_obj_tag(v_fst_2904_) == 0)
{
goto v___jp_2894_;
}
else
{
lean_object* v_val_2905_; 
v_val_2905_ = lean_ctor_get(v_fst_2904_, 0);
lean_inc(v_val_2905_);
lean_dec_ref_known(v_fst_2904_, 1);
if (lean_obj_tag(v_val_2905_) == 0)
{
goto v___jp_2894_;
}
else
{
lean_object* v_val_2906_; 
v_val_2906_ = lean_ctor_get(v_val_2905_, 0);
lean_inc(v_val_2906_);
lean_dec_ref_known(v_val_2905_, 1);
return v_val_2906_;
}
}
v___jp_2894_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2896_ = l_panic___redArg(v_inst_2891_, v___x_2895_);
return v___x_2896_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___boxed(lean_object* v_00_u03b1_2907_, lean_object* v_00_u03b2_2908_, lean_object* v_inst_2909_, lean_object* v_f_2910_, lean_object* v_xs_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Array_findSome_x21(v_00_u03b1_2907_, v_00_u03b2_2908_, v_inst_2909_, v_f_2910_, v_xs_2911_);
lean_dec(v_inst_2909_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2913_, lean_object* v_x_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = lean_apply_1(v_f_2913_, v_x_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg(lean_object* v_f_2916_, lean_object* v_as_2917_){
_start:
{
lean_object* v___f_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___f_2918_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2918_, 0, v_f_2916_);
v___x_2919_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2920_ = lean_array_get_size(v_as_2917_);
v___x_2921_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2919_, v___f_2918_, v_as_2917_, v___x_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f(lean_object* v_00_u03b1_2922_, lean_object* v_00_u03b2_2923_, lean_object* v_f_2924_, lean_object* v_as_2925_){
_start:
{
lean_object* v___f_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___f_2926_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2926_, 0, v_f_2924_);
v___x_2927_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2928_ = lean_array_get_size(v_as_2925_);
v___x_2929_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2927_, v___f_2926_, v_as_2925_, v___x_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg___lam__0(lean_object* v_p_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v___x_2932_; uint8_t v___x_2933_; 
lean_inc(v_a_2931_);
v___x_2932_ = lean_apply_1(v_p_2930_, v_a_2931_);
v___x_2933_ = lean_unbox(v___x_2932_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; 
lean_dec(v_a_2931_);
v___x_2934_ = lean_box(0);
return v___x_2934_;
}
else
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2935_, 0, v_a_2931_);
return v___x_2935_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg(lean_object* v_p_2936_, lean_object* v_as_2937_){
_start:
{
lean_object* v___f_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___f_2938_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2938_, 0, v_p_2936_);
v___x_2939_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2940_ = lean_array_get_size(v_as_2937_);
v___x_2941_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2939_, v___f_2938_, v_as_2937_, v___x_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f(lean_object* v_00_u03b1_2942_, lean_object* v_p_2943_, lean_object* v_as_2944_){
_start:
{
lean_object* v___f_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___f_2945_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2945_, 0, v_p_2943_);
v___x_2946_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2947_ = lean_array_get_size(v_as_2944_);
v___x_2948_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2946_, v___f_2945_, v_as_2944_, v___x_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object* v_p_2949_, lean_object* v_as_2950_, lean_object* v_j_2951_){
_start:
{
lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2952_ = lean_array_get_size(v_as_2950_);
v___x_2953_ = lean_nat_dec_lt(v_j_2951_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; 
lean_dec(v_j_2951_);
lean_dec_ref(v_p_2949_);
v___x_2954_ = lean_box(0);
return v___x_2954_;
}
else
{
lean_object* v___x_2955_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
v___x_2955_ = lean_array_fget_borrowed(v_as_2950_, v_j_2951_);
lean_inc_ref(v_p_2949_);
lean_inc(v___x_2955_);
v___x_2956_ = lean_apply_1(v_p_2949_, v___x_2955_);
v___x_2957_ = lean_unbox(v___x_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = lean_unsigned_to_nat(1u);
v___x_2959_ = lean_nat_add(v_j_2951_, v___x_2958_);
lean_dec(v_j_2951_);
v_j_2951_ = v___x_2959_;
goto _start;
}
else
{
lean_object* v___x_2961_; 
lean_dec_ref(v_p_2949_);
v___x_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2961_, 0, v_j_2951_);
return v___x_2961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg___boxed(lean_object* v_p_2962_, lean_object* v_as_2963_, lean_object* v_j_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Array_findIdx_x3f_loop___redArg(v_p_2962_, v_as_2963_, v_j_2964_);
lean_dec_ref(v_as_2963_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop(lean_object* v_00_u03b1_2966_, lean_object* v_p_2967_, lean_object* v_as_2968_, lean_object* v_j_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Array_findIdx_x3f_loop___redArg(v_p_2967_, v_as_2968_, v_j_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___boxed(lean_object* v_00_u03b1_2971_, lean_object* v_p_2972_, lean_object* v_as_2973_, lean_object* v_j_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Array_findIdx_x3f_loop(v_00_u03b1_2971_, v_p_2972_, v_as_2973_, v_j_2974_);
lean_dec_ref(v_as_2973_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg(lean_object* v_p_2976_, lean_object* v_as_2977_){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_unsigned_to_nat(0u);
v___x_2979_ = l_Array_findIdx_x3f_loop___redArg(v_p_2976_, v_as_2977_, v___x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg___boxed(lean_object* v_p_2980_, lean_object* v_as_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Array_findIdx_x3f___redArg(v_p_2980_, v_as_2981_);
lean_dec_ref(v_as_2981_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f(lean_object* v_00_u03b1_2983_, lean_object* v_p_2984_, lean_object* v_as_2985_){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = lean_unsigned_to_nat(0u);
v___x_2987_ = l_Array_findIdx_x3f_loop___redArg(v_p_2984_, v_as_2985_, v___x_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___boxed(lean_object* v_00_u03b1_2988_, lean_object* v_p_2989_, lean_object* v_as_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Array_findIdx_x3f(v_00_u03b1_2988_, v_p_2989_, v_as_2990_);
lean_dec_ref(v_as_2990_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(lean_object* v_p_2992_, lean_object* v_as_2993_, lean_object* v_j_2994_){
_start:
{
lean_object* v___x_2995_; uint8_t v___x_2996_; 
v___x_2995_ = lean_array_get_size(v_as_2993_);
v___x_2996_ = lean_nat_dec_lt(v_j_2994_, v___x_2995_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; 
lean_dec(v_j_2994_);
lean_dec_ref(v_p_2992_);
v___x_2997_ = lean_box(0);
return v___x_2997_;
}
else
{
lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2998_ = lean_array_fget_borrowed(v_as_2993_, v_j_2994_);
lean_inc_ref(v_p_2992_);
lean_inc(v___x_2998_);
v___x_2999_ = lean_apply_1(v_p_2992_, v___x_2998_);
v___x_3000_ = lean_unbox(v___x_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = lean_unsigned_to_nat(1u);
v___x_3002_ = lean_nat_add(v_j_2994_, v___x_3001_);
lean_dec(v_j_2994_);
v_j_2994_ = v___x_3002_;
goto _start;
}
else
{
lean_object* v___x_3004_; 
lean_dec_ref(v_p_2992_);
v___x_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3004_, 0, v_j_2994_);
return v___x_3004_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg___boxed(lean_object* v_p_3005_, lean_object* v_as_3006_, lean_object* v_j_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3005_, v_as_3006_, v_j_3007_);
lean_dec_ref(v_as_3006_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object* v_00_u03b1_3009_, lean_object* v_p_3010_, lean_object* v_as_3011_, lean_object* v_j_3012_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3010_, v_as_3011_, v_j_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___boxed(lean_object* v_00_u03b1_3014_, lean_object* v_p_3015_, lean_object* v_as_3016_, lean_object* v_j_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(v_00_u03b1_3014_, v_p_3015_, v_as_3016_, v_j_3017_);
lean_dec_ref(v_as_3016_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg(lean_object* v_p_3019_, lean_object* v_as_3020_){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = lean_unsigned_to_nat(0u);
v___x_3022_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3019_, v_as_3020_, v___x_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg___boxed(lean_object* v_p_3023_, lean_object* v_as_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Array_findFinIdx_x3f___redArg(v_p_3023_, v_as_3024_);
lean_dec_ref(v_as_3024_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f(lean_object* v_00_u03b1_3026_, lean_object* v_p_3027_, lean_object* v_as_3028_){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = lean_unsigned_to_nat(0u);
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3027_, v_as_3028_, v___x_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_3031_, lean_object* v_p_3032_, lean_object* v_as_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Array_findFinIdx_x3f(v_00_u03b1_3031_, v_p_3032_, v_as_3033_);
lean_dec_ref(v_as_3033_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg(lean_object* v_p_3035_, lean_object* v_as_3036_){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = lean_unsigned_to_nat(0u);
v___x_3038_ = l_Array_findIdx_x3f_loop___redArg(v_p_3035_, v_as_3036_, v___x_3037_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_array_get_size(v_as_3036_);
return v___x_3039_;
}
else
{
lean_object* v_val_3040_; 
v_val_3040_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_val_3040_);
lean_dec_ref_known(v___x_3038_, 1);
return v_val_3040_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg___boxed(lean_object* v_p_3041_, lean_object* v_as_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Array_findIdx___redArg(v_p_3041_, v_as_3042_);
lean_dec_ref(v_as_3042_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx(lean_object* v_00_u03b1_3044_, lean_object* v_p_3045_, lean_object* v_as_3046_){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = lean_unsigned_to_nat(0u);
v___x_3048_ = l_Array_findIdx_x3f_loop___redArg(v_p_3045_, v_as_3046_, v___x_3047_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v___x_3049_; 
v___x_3049_ = lean_array_get_size(v_as_3046_);
return v___x_3049_;
}
else
{
lean_object* v_val_3050_; 
v_val_3050_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_val_3050_);
lean_dec_ref_known(v___x_3048_, 1);
return v_val_3050_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___boxed(lean_object* v_00_u03b1_3051_, lean_object* v_p_3052_, lean_object* v_as_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Array_findIdx(v_00_u03b1_3051_, v_p_3052_, v_as_3053_);
lean_dec_ref(v_as_3053_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg(lean_object* v_inst_3055_, lean_object* v_xs_3056_, lean_object* v_v_3057_, lean_object* v_i_3058_){
_start:
{
lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3059_ = lean_array_get_size(v_xs_3056_);
v___x_3060_ = lean_nat_dec_lt(v_i_3058_, v___x_3059_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; 
lean_dec(v_i_3058_);
lean_dec(v_v_3057_);
lean_dec_ref(v_inst_3055_);
v___x_3061_ = lean_box(0);
return v___x_3061_;
}
else
{
lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; 
v___x_3062_ = lean_array_fget_borrowed(v_xs_3056_, v_i_3058_);
lean_inc_ref(v_inst_3055_);
lean_inc(v_v_3057_);
lean_inc(v___x_3062_);
v___x_3063_ = lean_apply_2(v_inst_3055_, v___x_3062_, v_v_3057_);
v___x_3064_ = lean_unbox(v___x_3063_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = lean_unsigned_to_nat(1u);
v___x_3066_ = lean_nat_add(v_i_3058_, v___x_3065_);
lean_dec(v_i_3058_);
v_i_3058_ = v___x_3066_;
goto _start;
}
else
{
lean_object* v___x_3068_; 
lean_dec(v_v_3057_);
lean_dec_ref(v_inst_3055_);
v___x_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3068_, 0, v_i_3058_);
return v___x_3068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg___boxed(lean_object* v_inst_3069_, lean_object* v_xs_3070_, lean_object* v_v_3071_, lean_object* v_i_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Array_idxOfAux___redArg(v_inst_3069_, v_xs_3070_, v_v_3071_, v_i_3072_);
lean_dec_ref(v_xs_3070_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux(lean_object* v_00_u03b1_3074_, lean_object* v_inst_3075_, lean_object* v_xs_3076_, lean_object* v_v_3077_, lean_object* v_i_3078_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = l_Array_idxOfAux___redArg(v_inst_3075_, v_xs_3076_, v_v_3077_, v_i_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___boxed(lean_object* v_00_u03b1_3080_, lean_object* v_inst_3081_, lean_object* v_xs_3082_, lean_object* v_v_3083_, lean_object* v_i_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Array_idxOfAux(v_00_u03b1_3080_, v_inst_3081_, v_xs_3082_, v_v_3083_, v_i_3084_);
lean_dec_ref(v_xs_3082_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg(lean_object* v_inst_3086_, lean_object* v_xs_3087_, lean_object* v_v_3088_){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = lean_unsigned_to_nat(0u);
v___x_3090_ = l_Array_idxOfAux___redArg(v_inst_3086_, v_xs_3087_, v_v_3088_, v___x_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_3091_, lean_object* v_xs_3092_, lean_object* v_v_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Array_finIdxOf_x3f___redArg(v_inst_3091_, v_xs_3092_, v_v_3093_);
lean_dec_ref(v_xs_3092_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f(lean_object* v_00_u03b1_3095_, lean_object* v_inst_3096_, lean_object* v_xs_3097_, lean_object* v_v_3098_){
_start:
{
lean_object* v___x_3099_; 
v___x_3099_ = l_Array_finIdxOf_x3f___redArg(v_inst_3096_, v_xs_3097_, v_v_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_3100_, lean_object* v_inst_3101_, lean_object* v_xs_3102_, lean_object* v_v_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Array_finIdxOf_x3f(v_00_u03b1_3100_, v_inst_3101_, v_xs_3102_, v_v_3103_);
lean_dec_ref(v_xs_3102_);
return v_res_3104_;
}
}
LEAN_EXPORT uint8_t l_Array_idxOf___redArg___lam__0(lean_object* v_inst_3105_, lean_object* v_a_3106_, lean_object* v_x_3107_){
_start:
{
lean_object* v___x_3108_; uint8_t v___x_3109_; 
v___x_3108_ = lean_apply_2(v_inst_3105_, v_x_3107_, v_a_3106_);
v___x_3109_ = lean_unbox(v___x_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___lam__0___boxed(lean_object* v_inst_3110_, lean_object* v_a_3111_, lean_object* v_x_3112_){
_start:
{
uint8_t v_res_3113_; lean_object* v_r_3114_; 
v_res_3113_ = l_Array_idxOf___redArg___lam__0(v_inst_3110_, v_a_3111_, v_x_3112_);
v_r_3114_ = lean_box(v_res_3113_);
return v_r_3114_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg(lean_object* v_inst_3115_, lean_object* v_a_3116_, lean_object* v_as_3117_){
_start:
{
lean_object* v___f_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___f_3118_ = lean_alloc_closure((void*)(l_Array_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3118_, 0, v_inst_3115_);
lean_closure_set(v___f_3118_, 1, v_a_3116_);
v___x_3119_ = lean_unsigned_to_nat(0u);
v___x_3120_ = l_Array_findIdx_x3f_loop___redArg(v___f_3118_, v_as_3117_, v___x_3119_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v___x_3121_; 
v___x_3121_ = lean_array_get_size(v_as_3117_);
return v___x_3121_;
}
else
{
lean_object* v_val_3122_; 
v_val_3122_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_val_3122_);
lean_dec_ref_known(v___x_3120_, 1);
return v_val_3122_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___boxed(lean_object* v_inst_3123_, lean_object* v_a_3124_, lean_object* v_as_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Array_idxOf___redArg(v_inst_3123_, v_a_3124_, v_as_3125_);
lean_dec_ref(v_as_3125_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf(lean_object* v_00_u03b1_3127_, lean_object* v_inst_3128_, lean_object* v_a_3129_, lean_object* v_as_3130_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Array_idxOf___redArg(v_inst_3128_, v_a_3129_, v_as_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___boxed(lean_object* v_00_u03b1_3132_, lean_object* v_inst_3133_, lean_object* v_a_3134_, lean_object* v_as_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Array_idxOf(v_00_u03b1_3132_, v_inst_3133_, v_a_3134_, v_as_3135_);
lean_dec_ref(v_as_3135_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg(lean_object* v_inst_3137_, lean_object* v_xs_3138_, lean_object* v_v_3139_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Array_finIdxOf_x3f___redArg(v_inst_3137_, v_xs_3138_, v_v_3139_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v___x_3141_; 
v___x_3141_ = lean_box(0);
return v___x_3141_;
}
else
{
lean_object* v_val_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
v_val_3142_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3140_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_val_3142_);
lean_dec(v___x_3140_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_val_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg___boxed(lean_object* v_inst_3150_, lean_object* v_xs_3151_, lean_object* v_v_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Array_idxOf_x3f___redArg(v_inst_3150_, v_xs_3151_, v_v_3152_);
lean_dec_ref(v_xs_3151_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f(lean_object* v_00_u03b1_3154_, lean_object* v_inst_3155_, lean_object* v_xs_3156_, lean_object* v_v_3157_){
_start:
{
lean_object* v___x_3158_; 
v___x_3158_ = l_Array_idxOf_x3f___redArg(v_inst_3155_, v_xs_3156_, v_v_3157_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___boxed(lean_object* v_00_u03b1_3159_, lean_object* v_inst_3160_, lean_object* v_xs_3161_, lean_object* v_v_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Array_idxOf_x3f(v_00_u03b1_3159_, v_inst_3160_, v_xs_3161_, v_v_3162_);
lean_dec_ref(v_xs_3161_);
return v_res_3163_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg___lam__0(lean_object* v_p_3164_, lean_object* v_x_3165_){
_start:
{
lean_object* v___x_3166_; uint8_t v___x_3167_; 
v___x_3166_ = lean_apply_1(v_p_3164_, v_x_3165_);
v___x_3167_ = lean_unbox(v___x_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___lam__0___boxed(lean_object* v_p_3168_, lean_object* v_x_3169_){
_start:
{
uint8_t v_res_3170_; lean_object* v_r_3171_; 
v_res_3170_ = l_Array_any___redArg___lam__0(v_p_3168_, v_x_3169_);
v_r_3171_ = lean_box(v_res_3170_);
return v_r_3171_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg(lean_object* v_as_3172_, lean_object* v_p_3173_, lean_object* v_start_3174_, lean_object* v_stop_3175_){
_start:
{
lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___x_3176_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3177_ = lean_nat_dec_lt(v_start_3174_, v_stop_3175_);
if (v___x_3177_ == 0)
{
lean_dec(v_stop_3175_);
lean_dec_ref(v_p_3173_);
lean_dec_ref(v_as_3172_);
return v___x_3177_;
}
else
{
lean_object* v___f_3178_; lean_object* v___y_3180_; lean_object* v___x_3186_; uint8_t v___x_3187_; 
v___f_3178_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3178_, 0, v_p_3173_);
v___x_3186_ = lean_array_get_size(v_as_3172_);
v___x_3187_ = lean_nat_dec_le(v_stop_3175_, v___x_3186_);
if (v___x_3187_ == 0)
{
lean_dec(v_stop_3175_);
v___y_3180_ = v___x_3186_;
goto v___jp_3179_;
}
else
{
v___y_3180_ = v_stop_3175_;
goto v___jp_3179_;
}
v___jp_3179_:
{
uint8_t v___x_3181_; 
v___x_3181_ = lean_nat_dec_lt(v_start_3174_, v___y_3180_);
if (v___x_3181_ == 0)
{
lean_dec(v___y_3180_);
lean_dec_ref(v___f_3178_);
lean_dec_ref(v_as_3172_);
return v___x_3181_;
}
else
{
size_t v___x_3182_; size_t v___x_3183_; lean_object* v___x_3184_; uint8_t v___x_3185_; 
v___x_3182_ = lean_usize_of_nat(v_start_3174_);
v___x_3183_ = lean_usize_of_nat(v___y_3180_);
lean_dec(v___y_3180_);
v___x_3184_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3176_, v___f_3178_, v_as_3172_, v___x_3182_, v___x_3183_);
v___x_3185_ = lean_unbox(v___x_3184_);
lean_dec(v___x_3184_);
return v___x_3185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___boxed(lean_object* v_as_3188_, lean_object* v_p_3189_, lean_object* v_start_3190_, lean_object* v_stop_3191_){
_start:
{
uint8_t v_res_3192_; lean_object* v_r_3193_; 
v_res_3192_ = l_Array_any___redArg(v_as_3188_, v_p_3189_, v_start_3190_, v_stop_3191_);
lean_dec(v_start_3190_);
v_r_3193_ = lean_box(v_res_3192_);
return v_r_3193_;
}
}
LEAN_EXPORT uint8_t l_Array_any(lean_object* v_00_u03b1_3194_, lean_object* v_as_3195_, lean_object* v_p_3196_, lean_object* v_start_3197_, lean_object* v_stop_3198_){
_start:
{
lean_object* v___x_3199_; uint8_t v___x_3200_; 
v___x_3199_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3200_ = lean_nat_dec_lt(v_start_3197_, v_stop_3198_);
if (v___x_3200_ == 0)
{
lean_dec(v_stop_3198_);
lean_dec_ref(v_p_3196_);
lean_dec_ref(v_as_3195_);
return v___x_3200_;
}
else
{
lean_object* v___f_3201_; lean_object* v___y_3203_; lean_object* v___x_3209_; uint8_t v___x_3210_; 
v___f_3201_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3201_, 0, v_p_3196_);
v___x_3209_ = lean_array_get_size(v_as_3195_);
v___x_3210_ = lean_nat_dec_le(v_stop_3198_, v___x_3209_);
if (v___x_3210_ == 0)
{
lean_dec(v_stop_3198_);
v___y_3203_ = v___x_3209_;
goto v___jp_3202_;
}
else
{
v___y_3203_ = v_stop_3198_;
goto v___jp_3202_;
}
v___jp_3202_:
{
uint8_t v___x_3204_; 
v___x_3204_ = lean_nat_dec_lt(v_start_3197_, v___y_3203_);
if (v___x_3204_ == 0)
{
lean_dec(v___y_3203_);
lean_dec_ref(v___f_3201_);
lean_dec_ref(v_as_3195_);
return v___x_3204_;
}
else
{
size_t v___x_3205_; size_t v___x_3206_; lean_object* v___x_3207_; uint8_t v___x_3208_; 
v___x_3205_ = lean_usize_of_nat(v_start_3197_);
v___x_3206_ = lean_usize_of_nat(v___y_3203_);
lean_dec(v___y_3203_);
v___x_3207_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3199_, v___f_3201_, v_as_3195_, v___x_3205_, v___x_3206_);
v___x_3208_ = lean_unbox(v___x_3207_);
lean_dec(v___x_3207_);
return v___x_3208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___boxed(lean_object* v_00_u03b1_3211_, lean_object* v_as_3212_, lean_object* v_p_3213_, lean_object* v_start_3214_, lean_object* v_stop_3215_){
_start:
{
uint8_t v_res_3216_; lean_object* v_r_3217_; 
v_res_3216_ = l_Array_any(v_00_u03b1_3211_, v_as_3212_, v_p_3213_, v_start_3214_, v_stop_3215_);
lean_dec(v_start_3214_);
v_r_3217_ = lean_box(v_res_3216_);
return v_r_3217_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg___lam__0(lean_object* v_p_3218_, lean_object* v_v_3219_){
_start:
{
lean_object* v___x_3220_; uint8_t v___x_3221_; uint8_t v___x_3222_; 
v___x_3220_ = lean_apply_1(v_p_3218_, v_v_3219_);
v___x_3221_ = lean_unbox(v___x_3220_);
v___x_3222_ = lean_bool_not(v___x_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___lam__0___boxed(lean_object* v_p_3223_, lean_object* v_v_3224_){
_start:
{
uint8_t v_res_3225_; lean_object* v_r_3226_; 
v_res_3225_ = l_Array_all___redArg___lam__0(v_p_3223_, v_v_3224_);
v_r_3226_ = lean_box(v_res_3225_);
return v_r_3226_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg(lean_object* v_as_3227_, lean_object* v_p_3228_, lean_object* v_start_3229_, lean_object* v_stop_3230_){
_start:
{
lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3231_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3232_ = lean_nat_dec_lt(v_start_3229_, v_stop_3230_);
if (v___x_3232_ == 0)
{
uint8_t v___x_3233_; 
lean_dec(v_stop_3230_);
lean_dec_ref(v_p_3228_);
lean_dec_ref(v_as_3227_);
v___x_3233_ = lean_bool_not(v___x_3232_);
return v___x_3233_;
}
else
{
lean_object* v___f_3234_; lean_object* v___y_3236_; lean_object* v___x_3244_; uint8_t v___x_3245_; 
v___f_3234_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3234_, 0, v_p_3228_);
v___x_3244_ = lean_array_get_size(v_as_3227_);
v___x_3245_ = lean_nat_dec_le(v_stop_3230_, v___x_3244_);
if (v___x_3245_ == 0)
{
lean_dec(v_stop_3230_);
v___y_3236_ = v___x_3244_;
goto v___jp_3235_;
}
else
{
v___y_3236_ = v_stop_3230_;
goto v___jp_3235_;
}
v___jp_3235_:
{
uint8_t v___x_3237_; 
v___x_3237_ = lean_nat_dec_lt(v_start_3229_, v___y_3236_);
if (v___x_3237_ == 0)
{
uint8_t v___x_3238_; 
lean_dec(v___y_3236_);
lean_dec_ref(v___f_3234_);
lean_dec_ref(v_as_3227_);
v___x_3238_ = lean_bool_not(v___x_3237_);
return v___x_3238_;
}
else
{
size_t v___x_3239_; size_t v___x_3240_; lean_object* v___x_3241_; uint8_t v___x_3242_; uint8_t v___x_3243_; 
v___x_3239_ = lean_usize_of_nat(v_start_3229_);
v___x_3240_ = lean_usize_of_nat(v___y_3236_);
lean_dec(v___y_3236_);
v___x_3241_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3231_, v___f_3234_, v_as_3227_, v___x_3239_, v___x_3240_);
v___x_3242_ = lean_unbox(v___x_3241_);
lean_dec(v___x_3241_);
v___x_3243_ = lean_bool_not(v___x_3242_);
return v___x_3243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___boxed(lean_object* v_as_3246_, lean_object* v_p_3247_, lean_object* v_start_3248_, lean_object* v_stop_3249_){
_start:
{
uint8_t v_res_3250_; lean_object* v_r_3251_; 
v_res_3250_ = l_Array_all___redArg(v_as_3246_, v_p_3247_, v_start_3248_, v_stop_3249_);
lean_dec(v_start_3248_);
v_r_3251_ = lean_box(v_res_3250_);
return v_r_3251_;
}
}
LEAN_EXPORT uint8_t l_Array_all(lean_object* v_00_u03b1_3252_, lean_object* v_as_3253_, lean_object* v_p_3254_, lean_object* v_start_3255_, lean_object* v_stop_3256_){
_start:
{
lean_object* v___x_3257_; uint8_t v___x_3258_; 
v___x_3257_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3258_ = lean_nat_dec_lt(v_start_3255_, v_stop_3256_);
if (v___x_3258_ == 0)
{
uint8_t v___x_3259_; 
lean_dec(v_stop_3256_);
lean_dec_ref(v_p_3254_);
lean_dec_ref(v_as_3253_);
v___x_3259_ = lean_bool_not(v___x_3258_);
return v___x_3259_;
}
else
{
lean_object* v___f_3260_; lean_object* v___y_3262_; lean_object* v___x_3270_; uint8_t v___x_3271_; 
v___f_3260_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3260_, 0, v_p_3254_);
v___x_3270_ = lean_array_get_size(v_as_3253_);
v___x_3271_ = lean_nat_dec_le(v_stop_3256_, v___x_3270_);
if (v___x_3271_ == 0)
{
lean_dec(v_stop_3256_);
v___y_3262_ = v___x_3270_;
goto v___jp_3261_;
}
else
{
v___y_3262_ = v_stop_3256_;
goto v___jp_3261_;
}
v___jp_3261_:
{
uint8_t v___x_3263_; 
v___x_3263_ = lean_nat_dec_lt(v_start_3255_, v___y_3262_);
if (v___x_3263_ == 0)
{
uint8_t v___x_3264_; 
lean_dec(v___y_3262_);
lean_dec_ref(v___f_3260_);
lean_dec_ref(v_as_3253_);
v___x_3264_ = lean_bool_not(v___x_3263_);
return v___x_3264_;
}
else
{
size_t v___x_3265_; size_t v___x_3266_; lean_object* v___x_3267_; uint8_t v___x_3268_; uint8_t v___x_3269_; 
v___x_3265_ = lean_usize_of_nat(v_start_3255_);
v___x_3266_ = lean_usize_of_nat(v___y_3262_);
lean_dec(v___y_3262_);
v___x_3267_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3257_, v___f_3260_, v_as_3253_, v___x_3265_, v___x_3266_);
v___x_3268_ = lean_unbox(v___x_3267_);
lean_dec(v___x_3267_);
v___x_3269_ = lean_bool_not(v___x_3268_);
return v___x_3269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___boxed(lean_object* v_00_u03b1_3272_, lean_object* v_as_3273_, lean_object* v_p_3274_, lean_object* v_start_3275_, lean_object* v_stop_3276_){
_start:
{
uint8_t v_res_3277_; lean_object* v_r_3278_; 
v_res_3277_ = l_Array_all(v_00_u03b1_3272_, v_as_3273_, v_p_3274_, v_start_3275_, v_stop_3276_);
lean_dec(v_start_3275_);
v_r_3278_ = lean_box(v_res_3277_);
return v_r_3278_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg___lam__0(lean_object* v_inst_3279_, lean_object* v_a_3280_, lean_object* v_x_3281_){
_start:
{
lean_object* v___x_3282_; uint8_t v___x_3283_; 
v___x_3282_ = lean_apply_2(v_inst_3279_, v_a_3280_, v_x_3281_);
v___x_3283_ = lean_unbox(v___x_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___lam__0___boxed(lean_object* v_inst_3284_, lean_object* v_a_3285_, lean_object* v_x_3286_){
_start:
{
uint8_t v_res_3287_; lean_object* v_r_3288_; 
v_res_3287_ = l_Array_contains___redArg___lam__0(v_inst_3284_, v_a_3285_, v_x_3286_);
v_r_3288_ = lean_box(v_res_3287_);
return v_r_3288_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg(lean_object* v_inst_3289_, lean_object* v_as_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; uint8_t v___x_3295_; 
v___x_3292_ = lean_unsigned_to_nat(0u);
v___x_3293_ = lean_array_get_size(v_as_3290_);
v___x_3294_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3295_ = lean_nat_dec_lt(v___x_3292_, v___x_3293_);
if (v___x_3295_ == 0)
{
lean_dec(v_a_3291_);
lean_dec_ref(v_as_3290_);
lean_dec_ref(v_inst_3289_);
return v___x_3295_;
}
else
{
if (v___x_3295_ == 0)
{
lean_dec(v_a_3291_);
lean_dec_ref(v_as_3290_);
lean_dec_ref(v_inst_3289_);
return v___x_3295_;
}
else
{
lean_object* v___f_3296_; size_t v___x_3297_; size_t v___x_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___f_3296_ = lean_alloc_closure((void*)(l_Array_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3296_, 0, v_inst_3289_);
lean_closure_set(v___f_3296_, 1, v_a_3291_);
v___x_3297_ = ((size_t)0ULL);
v___x_3298_ = lean_usize_of_nat(v___x_3293_);
v___x_3299_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3294_, v___f_3296_, v_as_3290_, v___x_3297_, v___x_3298_);
v___x_3300_ = lean_unbox(v___x_3299_);
lean_dec(v___x_3299_);
return v___x_3300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___boxed(lean_object* v_inst_3301_, lean_object* v_as_3302_, lean_object* v_a_3303_){
_start:
{
uint8_t v_res_3304_; lean_object* v_r_3305_; 
v_res_3304_ = l_Array_contains___redArg(v_inst_3301_, v_as_3302_, v_a_3303_);
v_r_3305_ = lean_box(v_res_3304_);
return v_r_3305_;
}
}
LEAN_EXPORT uint8_t l_Array_contains(lean_object* v_00_u03b1_3306_, lean_object* v_inst_3307_, lean_object* v_as_3308_, lean_object* v_a_3309_){
_start:
{
uint8_t v___x_3310_; 
v___x_3310_ = l_Array_contains___redArg(v_inst_3307_, v_as_3308_, v_a_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___boxed(lean_object* v_00_u03b1_3311_, lean_object* v_inst_3312_, lean_object* v_as_3313_, lean_object* v_a_3314_){
_start:
{
uint8_t v_res_3315_; lean_object* v_r_3316_; 
v_res_3315_ = l_Array_contains(v_00_u03b1_3311_, v_inst_3312_, v_as_3313_, v_a_3314_);
v_r_3316_ = lean_box(v_res_3315_);
return v_r_3316_;
}
}
LEAN_EXPORT uint8_t l_Array_elem___redArg(lean_object* v_inst_3317_, lean_object* v_a_3318_, lean_object* v_as_3319_){
_start:
{
uint8_t v___x_3320_; 
v___x_3320_ = l_Array_contains___redArg(v_inst_3317_, v_as_3319_, v_a_3318_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___redArg___boxed(lean_object* v_inst_3321_, lean_object* v_a_3322_, lean_object* v_as_3323_){
_start:
{
uint8_t v_res_3324_; lean_object* v_r_3325_; 
v_res_3324_ = l_Array_elem___redArg(v_inst_3321_, v_a_3322_, v_as_3323_);
v_r_3325_ = lean_box(v_res_3324_);
return v_r_3325_;
}
}
LEAN_EXPORT uint8_t l_Array_elem(lean_object* v_00_u03b1_3326_, lean_object* v_inst_3327_, lean_object* v_a_3328_, lean_object* v_as_3329_){
_start:
{
uint8_t v___x_3330_; 
v___x_3330_ = l_Array_contains___redArg(v_inst_3327_, v_as_3329_, v_a_3328_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___boxed(lean_object* v_00_u03b1_3331_, lean_object* v_inst_3332_, lean_object* v_a_3333_, lean_object* v_as_3334_){
_start:
{
uint8_t v_res_3335_; lean_object* v_r_3336_; 
v_res_3335_ = l_Array_elem(v_00_u03b1_3331_, v_inst_3332_, v_a_3333_, v_as_3334_);
v_r_3336_ = lean_box(v_res_3335_);
return v_r_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(lean_object* v_as_3337_, size_t v_i_3338_, size_t v_stop_3339_, lean_object* v_b_3340_){
_start:
{
uint8_t v___x_3341_; 
v___x_3341_ = lean_usize_dec_eq(v_i_3338_, v_stop_3339_);
if (v___x_3341_ == 0)
{
size_t v___x_3342_; size_t v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3342_ = ((size_t)1ULL);
v___x_3343_ = lean_usize_sub(v_i_3338_, v___x_3342_);
v___x_3344_ = lean_array_uget_borrowed(v_as_3337_, v___x_3343_);
lean_inc(v___x_3344_);
v___x_3345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
lean_ctor_set(v___x_3345_, 1, v_b_3340_);
v_i_3338_ = v___x_3343_;
v_b_3340_ = v___x_3345_;
goto _start;
}
else
{
return v_b_3340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg___boxed(lean_object* v_as_3347_, lean_object* v_i_3348_, lean_object* v_stop_3349_, lean_object* v_b_3350_){
_start:
{
size_t v_i_boxed_3351_; size_t v_stop_boxed_3352_; lean_object* v_res_3353_; 
v_i_boxed_3351_ = lean_unbox_usize(v_i_3348_);
lean_dec(v_i_3348_);
v_stop_boxed_3352_ = lean_unbox_usize(v_stop_3349_);
lean_dec(v_stop_3349_);
v_res_3353_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3347_, v_i_boxed_3351_, v_stop_boxed_3352_, v_b_3350_);
lean_dec_ref(v_as_3347_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg(lean_object* v_as_3354_){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3355_ = lean_box(0);
v___x_3356_ = lean_array_get_size(v_as_3354_);
v___x_3357_ = lean_unsigned_to_nat(0u);
v___x_3358_ = lean_nat_dec_lt(v___x_3357_, v___x_3356_);
if (v___x_3358_ == 0)
{
return v___x_3355_;
}
else
{
size_t v___x_3359_; size_t v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = lean_usize_of_nat(v___x_3356_);
v___x_3360_ = ((size_t)0ULL);
v___x_3361_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3354_, v___x_3359_, v___x_3360_, v___x_3355_);
return v___x_3361_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg___boxed(lean_object* v_as_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l_Array_toListImpl___redArg(v_as_3362_);
lean_dec_ref(v_as_3362_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* lean_array_to_list_impl(lean_object* v_00_u03b1_3364_, lean_object* v_as_3365_){
_start:
{
lean_object* v___x_3366_; 
v___x_3366_ = l_Array_toListImpl___redArg(v_as_3365_);
lean_dec_ref(v_as_3365_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(lean_object* v_00_u03b1_3367_, lean_object* v_as_3368_, size_t v_i_3369_, size_t v_stop_3370_, lean_object* v_b_3371_){
_start:
{
lean_object* v___x_3372_; 
v___x_3372_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3368_, v_i_3369_, v_stop_3370_, v_b_3371_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___boxed(lean_object* v_00_u03b1_3373_, lean_object* v_as_3374_, lean_object* v_i_3375_, lean_object* v_stop_3376_, lean_object* v_b_3377_){
_start:
{
size_t v_i_boxed_3378_; size_t v_stop_boxed_3379_; lean_object* v_res_3380_; 
v_i_boxed_3378_ = lean_unbox_usize(v_i_3375_);
lean_dec(v_i_3375_);
v_stop_boxed_3379_ = lean_unbox_usize(v_stop_3376_);
lean_dec(v_stop_3376_);
v_res_3380_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(v_00_u03b1_3373_, v_as_3374_, v_i_boxed_3378_, v_stop_boxed_3379_, v_b_3377_);
lean_dec_ref(v_as_3374_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg___lam__0(lean_object* v_x1_3381_, lean_object* v_x2_3382_){
_start:
{
lean_object* v___x_3383_; 
v___x_3383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3383_, 0, v_x1_3381_);
lean_ctor_set(v___x_3383_, 1, v_x2_3382_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg(lean_object* v_as_3385_, lean_object* v_l_3386_){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; 
v___x_3387_ = lean_array_get_size(v_as_3385_);
v___x_3388_ = lean_unsigned_to_nat(0u);
v___x_3389_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3390_ = lean_nat_dec_lt(v___x_3388_, v___x_3387_);
if (v___x_3390_ == 0)
{
lean_dec_ref(v_as_3385_);
return v_l_3386_;
}
else
{
lean_object* v___f_3391_; size_t v___x_3392_; size_t v___x_3393_; lean_object* v___x_3394_; 
v___f_3391_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3392_ = lean_usize_of_nat(v___x_3387_);
v___x_3393_ = ((size_t)0ULL);
v___x_3394_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3389_, v___f_3391_, v_as_3385_, v___x_3392_, v___x_3393_, v_l_3386_);
return v___x_3394_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend(lean_object* v_00_u03b1_3395_, lean_object* v_as_3396_, lean_object* v_l_3397_){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v___x_3398_ = lean_array_get_size(v_as_3396_);
v___x_3399_ = lean_unsigned_to_nat(0u);
v___x_3400_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3401_ = lean_nat_dec_lt(v___x_3399_, v___x_3398_);
if (v___x_3401_ == 0)
{
lean_dec_ref(v_as_3396_);
return v_l_3397_;
}
else
{
lean_object* v___f_3402_; size_t v___x_3403_; size_t v___x_3404_; lean_object* v___x_3405_; 
v___f_3402_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3403_ = lean_usize_of_nat(v___x_3398_);
v___x_3404_ = ((size_t)0ULL);
v___x_3405_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3400_, v___f_3402_, v_as_3396_, v___x_3403_, v___x_3404_, v_l_3397_);
return v___x_3405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(lean_object* v_as_3406_, size_t v_i_3407_, size_t v_stop_3408_, lean_object* v_b_3409_){
_start:
{
uint8_t v___x_3410_; 
v___x_3410_ = lean_usize_dec_eq(v_i_3407_, v_stop_3408_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; lean_object* v___x_3412_; size_t v___x_3413_; size_t v___x_3414_; 
v___x_3411_ = lean_array_uget_borrowed(v_as_3406_, v_i_3407_);
lean_inc(v___x_3411_);
v___x_3412_ = lean_array_push(v_b_3409_, v___x_3411_);
v___x_3413_ = ((size_t)1ULL);
v___x_3414_ = lean_usize_add(v_i_3407_, v___x_3413_);
v_i_3407_ = v___x_3414_;
v_b_3409_ = v___x_3412_;
goto _start;
}
else
{
return v_b_3409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg___boxed(lean_object* v_as_3416_, lean_object* v_i_3417_, lean_object* v_stop_3418_, lean_object* v_b_3419_){
_start:
{
size_t v_i_boxed_3420_; size_t v_stop_boxed_3421_; lean_object* v_res_3422_; 
v_i_boxed_3420_ = lean_unbox_usize(v_i_3417_);
lean_dec(v_i_3417_);
v_stop_boxed_3421_ = lean_unbox_usize(v_stop_3418_);
lean_dec(v_stop_3418_);
v_res_3422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3416_, v_i_boxed_3420_, v_stop_boxed_3421_, v_b_3419_);
lean_dec_ref(v_as_3416_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg(lean_object* v_as_3423_, lean_object* v_bs_3424_){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
v___x_3425_ = lean_unsigned_to_nat(0u);
v___x_3426_ = lean_array_get_size(v_bs_3424_);
v___x_3427_ = lean_nat_dec_lt(v___x_3425_, v___x_3426_);
if (v___x_3427_ == 0)
{
return v_as_3423_;
}
else
{
uint8_t v___x_3428_; 
v___x_3428_ = lean_nat_dec_le(v___x_3426_, v___x_3426_);
if (v___x_3428_ == 0)
{
if (v___x_3427_ == 0)
{
return v_as_3423_;
}
else
{
size_t v___x_3429_; size_t v___x_3430_; lean_object* v___x_3431_; 
v___x_3429_ = ((size_t)0ULL);
v___x_3430_ = lean_usize_of_nat(v___x_3426_);
v___x_3431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3424_, v___x_3429_, v___x_3430_, v_as_3423_);
return v___x_3431_;
}
}
else
{
size_t v___x_3432_; size_t v___x_3433_; lean_object* v___x_3434_; 
v___x_3432_ = ((size_t)0ULL);
v___x_3433_ = lean_usize_of_nat(v___x_3426_);
v___x_3434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3424_, v___x_3432_, v___x_3433_, v_as_3423_);
return v___x_3434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg___boxed(lean_object* v_as_3435_, lean_object* v_bs_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Array_append___redArg(v_as_3435_, v_bs_3436_);
lean_dec_ref(v_bs_3436_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Array_append(lean_object* v_00_u03b1_3438_, lean_object* v_as_3439_, lean_object* v_bs_3440_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = l_Array_append___redArg(v_as_3439_, v_bs_3440_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Array_append___boxed(lean_object* v_00_u03b1_3442_, lean_object* v_as_3443_, lean_object* v_bs_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Array_append(v_00_u03b1_3442_, v_as_3443_, v_bs_3444_);
lean_dec_ref(v_bs_3444_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(lean_object* v_00_u03b1_3446_, lean_object* v_as_3447_, size_t v_i_3448_, size_t v_stop_3449_, lean_object* v_b_3450_){
_start:
{
lean_object* v___x_3451_; 
v___x_3451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3447_, v_i_3448_, v_stop_3449_, v_b_3450_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___boxed(lean_object* v_00_u03b1_3452_, lean_object* v_as_3453_, lean_object* v_i_3454_, lean_object* v_stop_3455_, lean_object* v_b_3456_){
_start:
{
size_t v_i_boxed_3457_; size_t v_stop_boxed_3458_; lean_object* v_res_3459_; 
v_i_boxed_3457_ = lean_unbox_usize(v_i_3454_);
lean_dec(v_i_3454_);
v_stop_boxed_3458_ = lean_unbox_usize(v_stop_3455_);
lean_dec(v_stop_3455_);
v_res_3459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(v_00_u03b1_3452_, v_as_3453_, v_i_boxed_3457_, v_stop_boxed_3458_, v_b_3456_);
lean_dec_ref(v_as_3453_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend(lean_object* v_00_u03b1_3461_){
_start:
{
lean_object* v___x_3462_; 
v___x_3462_ = ((lean_object*)(l_Array_instAppend___closed__0));
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object* v_x_3463_, lean_object* v_x_3464_){
_start:
{
if (lean_obj_tag(v_x_3464_) == 0)
{
return v_x_3463_;
}
else
{
lean_object* v_head_3465_; lean_object* v_tail_3466_; lean_object* v___x_3467_; 
v_head_3465_ = lean_ctor_get(v_x_3464_, 0);
lean_inc(v_head_3465_);
v_tail_3466_ = lean_ctor_get(v_x_3464_, 1);
lean_inc(v_tail_3466_);
lean_dec_ref_known(v_x_3464_, 2);
v___x_3467_ = lean_array_push(v_x_3463_, v_head_3465_);
v_x_3463_ = v___x_3467_;
v_x_3464_ = v_tail_3466_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_appendList___redArg(lean_object* v_as_3469_, lean_object* v_bs_3470_){
_start:
{
lean_object* v___x_3471_; 
v___x_3471_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3469_, v_bs_3470_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Array_appendList(lean_object* v_00_u03b1_3472_, lean_object* v_as_3473_, lean_object* v_bs_3474_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3473_, v_bs_3474_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0(lean_object* v_00_u03b1_3476_, lean_object* v_x_3477_, lean_object* v_x_3478_){
_start:
{
lean_object* v___x_3479_; 
v___x_3479_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_3477_, v_x_3478_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList(lean_object* v_00_u03b1_3481_){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = ((lean_object*)(l_Array_instHAppendList___closed__0));
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0(lean_object* v_bs_3483_, lean_object* v_toPure_3484_, lean_object* v_____do__lift_3485_){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = l_Array_append___redArg(v_bs_3483_, v_____do__lift_3485_);
v___x_3487_ = lean_apply_2(v_toPure_3484_, lean_box(0), v___x_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0___boxed(lean_object* v_bs_3488_, lean_object* v_toPure_3489_, lean_object* v_____do__lift_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Array_flatMapM___redArg___lam__0(v_bs_3488_, v_toPure_3489_, v_____do__lift_3490_);
lean_dec_ref(v_____do__lift_3490_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__1(lean_object* v_toPure_3492_, lean_object* v_f_3493_, lean_object* v_toBind_3494_, lean_object* v_bs_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v___f_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___f_3497_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3497_, 0, v_bs_3495_);
lean_closure_set(v___f_3497_, 1, v_toPure_3492_);
v___x_3498_ = lean_apply_1(v_f_3493_, v_a_3496_);
v___x_3499_ = lean_apply_4(v_toBind_3494_, lean_box(0), lean_box(0), v___x_3498_, v___f_3497_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg(lean_object* v_inst_3500_, lean_object* v_f_3501_, lean_object* v_as_3502_){
_start:
{
lean_object* v_toApplicative_3503_; lean_object* v_toBind_3504_; lean_object* v_toPure_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; uint8_t v___x_3509_; 
v_toApplicative_3503_ = lean_ctor_get(v_inst_3500_, 0);
v_toBind_3504_ = lean_ctor_get(v_inst_3500_, 1);
v_toPure_3505_ = lean_ctor_get(v_toApplicative_3503_, 1);
v___x_3506_ = lean_unsigned_to_nat(0u);
v___x_3507_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3508_ = lean_array_get_size(v_as_3502_);
v___x_3509_ = lean_nat_dec_lt(v___x_3506_, v___x_3508_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; 
lean_inc(v_toPure_3505_);
lean_dec_ref(v_as_3502_);
lean_dec(v_f_3501_);
lean_dec_ref(v_inst_3500_);
v___x_3510_ = lean_apply_2(v_toPure_3505_, lean_box(0), v___x_3507_);
return v___x_3510_;
}
else
{
lean_object* v___f_3511_; uint8_t v___x_3512_; 
lean_inc(v_toBind_3504_);
lean_inc(v_toPure_3505_);
v___f_3511_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3511_, 0, v_toPure_3505_);
lean_closure_set(v___f_3511_, 1, v_f_3501_);
lean_closure_set(v___f_3511_, 2, v_toBind_3504_);
v___x_3512_ = lean_nat_dec_le(v___x_3508_, v___x_3508_);
if (v___x_3512_ == 0)
{
if (v___x_3509_ == 0)
{
lean_object* v___x_3513_; 
lean_inc(v_toPure_3505_);
lean_dec_ref(v___f_3511_);
lean_dec_ref(v_as_3502_);
lean_dec_ref(v_inst_3500_);
v___x_3513_ = lean_apply_2(v_toPure_3505_, lean_box(0), v___x_3507_);
return v___x_3513_;
}
else
{
size_t v___x_3514_; size_t v___x_3515_; lean_object* v___x_3516_; 
v___x_3514_ = ((size_t)0ULL);
v___x_3515_ = lean_usize_of_nat(v___x_3508_);
v___x_3516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3500_, v___f_3511_, v_as_3502_, v___x_3514_, v___x_3515_, v___x_3507_);
return v___x_3516_;
}
}
else
{
size_t v___x_3517_; size_t v___x_3518_; lean_object* v___x_3519_; 
v___x_3517_ = ((size_t)0ULL);
v___x_3518_ = lean_usize_of_nat(v___x_3508_);
v___x_3519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3500_, v___f_3511_, v_as_3502_, v___x_3517_, v___x_3518_, v___x_3507_);
return v___x_3519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM(lean_object* v_00_u03b1_3520_, lean_object* v_m_3521_, lean_object* v_00_u03b2_3522_, lean_object* v_inst_3523_, lean_object* v_f_3524_, lean_object* v_as_3525_){
_start:
{
lean_object* v_toApplicative_3526_; lean_object* v_toBind_3527_; lean_object* v_toPure_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; uint8_t v___x_3532_; 
v_toApplicative_3526_ = lean_ctor_get(v_inst_3523_, 0);
v_toBind_3527_ = lean_ctor_get(v_inst_3523_, 1);
v_toPure_3528_ = lean_ctor_get(v_toApplicative_3526_, 1);
v___x_3529_ = lean_unsigned_to_nat(0u);
v___x_3530_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3531_ = lean_array_get_size(v_as_3525_);
v___x_3532_ = lean_nat_dec_lt(v___x_3529_, v___x_3531_);
if (v___x_3532_ == 0)
{
lean_object* v___x_3533_; 
lean_inc(v_toPure_3528_);
lean_dec_ref(v_as_3525_);
lean_dec(v_f_3524_);
lean_dec_ref(v_inst_3523_);
v___x_3533_ = lean_apply_2(v_toPure_3528_, lean_box(0), v___x_3530_);
return v___x_3533_;
}
else
{
lean_object* v___f_3534_; uint8_t v___x_3535_; 
lean_inc(v_toBind_3527_);
lean_inc(v_toPure_3528_);
v___f_3534_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3534_, 0, v_toPure_3528_);
lean_closure_set(v___f_3534_, 1, v_f_3524_);
lean_closure_set(v___f_3534_, 2, v_toBind_3527_);
v___x_3535_ = lean_nat_dec_le(v___x_3531_, v___x_3531_);
if (v___x_3535_ == 0)
{
if (v___x_3532_ == 0)
{
lean_object* v___x_3536_; 
lean_inc(v_toPure_3528_);
lean_dec_ref(v___f_3534_);
lean_dec_ref(v_as_3525_);
lean_dec_ref(v_inst_3523_);
v___x_3536_ = lean_apply_2(v_toPure_3528_, lean_box(0), v___x_3530_);
return v___x_3536_;
}
else
{
size_t v___x_3537_; size_t v___x_3538_; lean_object* v___x_3539_; 
v___x_3537_ = ((size_t)0ULL);
v___x_3538_ = lean_usize_of_nat(v___x_3531_);
v___x_3539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3523_, v___f_3534_, v_as_3525_, v___x_3537_, v___x_3538_, v___x_3530_);
return v___x_3539_;
}
}
else
{
size_t v___x_3540_; size_t v___x_3541_; lean_object* v___x_3542_; 
v___x_3540_ = ((size_t)0ULL);
v___x_3541_ = lean_usize_of_nat(v___x_3531_);
v___x_3542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3523_, v___f_3534_, v_as_3525_, v___x_3540_, v___x_3541_, v___x_3530_);
return v___x_3542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg___lam__0(lean_object* v_f_3543_, lean_object* v_x1_3544_, lean_object* v_x2_3545_){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3546_ = lean_apply_1(v_f_3543_, v_x2_3545_);
v___x_3547_ = l_Array_append___redArg(v_x1_3544_, v___x_3546_);
lean_dec_ref(v___x_3546_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg(lean_object* v_f_3548_, lean_object* v_as_3549_){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v___x_3550_ = lean_unsigned_to_nat(0u);
v___x_3551_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3552_ = lean_array_get_size(v_as_3549_);
v___x_3553_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3554_ = lean_nat_dec_lt(v___x_3550_, v___x_3552_);
if (v___x_3554_ == 0)
{
lean_dec_ref(v_as_3549_);
lean_dec_ref(v_f_3548_);
return v___x_3551_;
}
else
{
lean_object* v___f_3555_; uint8_t v___x_3556_; 
v___f_3555_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3555_, 0, v_f_3548_);
v___x_3556_ = lean_nat_dec_le(v___x_3552_, v___x_3552_);
if (v___x_3556_ == 0)
{
if (v___x_3554_ == 0)
{
lean_dec_ref(v___f_3555_);
lean_dec_ref(v_as_3549_);
return v___x_3551_;
}
else
{
size_t v___x_3557_; size_t v___x_3558_; lean_object* v___x_3559_; 
v___x_3557_ = ((size_t)0ULL);
v___x_3558_ = lean_usize_of_nat(v___x_3552_);
v___x_3559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3553_, v___f_3555_, v_as_3549_, v___x_3557_, v___x_3558_, v___x_3551_);
return v___x_3559_;
}
}
else
{
size_t v___x_3560_; size_t v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = ((size_t)0ULL);
v___x_3561_ = lean_usize_of_nat(v___x_3552_);
v___x_3562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3553_, v___f_3555_, v_as_3549_, v___x_3560_, v___x_3561_, v___x_3551_);
return v___x_3562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap(lean_object* v_00_u03b1_3563_, lean_object* v_00_u03b2_3564_, lean_object* v_f_3565_, lean_object* v_as_3566_){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v___x_3567_ = lean_unsigned_to_nat(0u);
v___x_3568_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3569_ = lean_array_get_size(v_as_3566_);
v___x_3570_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3571_ = lean_nat_dec_lt(v___x_3567_, v___x_3569_);
if (v___x_3571_ == 0)
{
lean_dec_ref(v_as_3566_);
lean_dec_ref(v_f_3565_);
return v___x_3568_;
}
else
{
lean_object* v___f_3572_; uint8_t v___x_3573_; 
v___f_3572_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3572_, 0, v_f_3565_);
v___x_3573_ = lean_nat_dec_le(v___x_3569_, v___x_3569_);
if (v___x_3573_ == 0)
{
if (v___x_3571_ == 0)
{
lean_dec_ref(v___f_3572_);
lean_dec_ref(v_as_3566_);
return v___x_3568_;
}
else
{
size_t v___x_3574_; size_t v___x_3575_; lean_object* v___x_3576_; 
v___x_3574_ = ((size_t)0ULL);
v___x_3575_ = lean_usize_of_nat(v___x_3569_);
v___x_3576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3570_, v___f_3572_, v_as_3566_, v___x_3574_, v___x_3575_, v___x_3568_);
return v___x_3576_;
}
}
else
{
size_t v___x_3577_; size_t v___x_3578_; lean_object* v___x_3579_; 
v___x_3577_ = ((size_t)0ULL);
v___x_3578_ = lean_usize_of_nat(v___x_3569_);
v___x_3579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3570_, v___f_3572_, v_as_3566_, v___x_3577_, v___x_3578_, v___x_3568_);
return v___x_3579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten___redArg(lean_object* v_xss_3581_){
_start:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; 
v___x_3582_ = lean_unsigned_to_nat(0u);
v___x_3583_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3584_ = lean_array_get_size(v_xss_3581_);
v___x_3585_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3586_ = lean_nat_dec_lt(v___x_3582_, v___x_3584_);
if (v___x_3586_ == 0)
{
lean_dec_ref(v_xss_3581_);
return v___x_3583_;
}
else
{
lean_object* v___f_3587_; uint8_t v___x_3588_; 
v___f_3587_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3588_ = lean_nat_dec_le(v___x_3584_, v___x_3584_);
if (v___x_3588_ == 0)
{
if (v___x_3586_ == 0)
{
lean_dec_ref(v_xss_3581_);
return v___x_3583_;
}
else
{
size_t v___x_3589_; size_t v___x_3590_; lean_object* v___x_3591_; 
v___x_3589_ = ((size_t)0ULL);
v___x_3590_ = lean_usize_of_nat(v___x_3584_);
v___x_3591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3585_, v___f_3587_, v_xss_3581_, v___x_3589_, v___x_3590_, v___x_3583_);
return v___x_3591_;
}
}
else
{
size_t v___x_3592_; size_t v___x_3593_; lean_object* v___x_3594_; 
v___x_3592_ = ((size_t)0ULL);
v___x_3593_ = lean_usize_of_nat(v___x_3584_);
v___x_3594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3585_, v___f_3587_, v_xss_3581_, v___x_3592_, v___x_3593_, v___x_3583_);
return v___x_3594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten(lean_object* v_00_u03b1_3595_, lean_object* v_xss_3596_){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3597_ = lean_unsigned_to_nat(0u);
v___x_3598_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3599_ = lean_array_get_size(v_xss_3596_);
v___x_3600_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3601_ = lean_nat_dec_lt(v___x_3597_, v___x_3599_);
if (v___x_3601_ == 0)
{
lean_dec_ref(v_xss_3596_);
return v___x_3598_;
}
else
{
lean_object* v___f_3602_; uint8_t v___x_3603_; 
v___f_3602_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3603_ = lean_nat_dec_le(v___x_3599_, v___x_3599_);
if (v___x_3603_ == 0)
{
if (v___x_3601_ == 0)
{
lean_dec_ref(v_xss_3596_);
return v___x_3598_;
}
else
{
size_t v___x_3604_; size_t v___x_3605_; lean_object* v___x_3606_; 
v___x_3604_ = ((size_t)0ULL);
v___x_3605_ = lean_usize_of_nat(v___x_3599_);
v___x_3606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3600_, v___f_3602_, v_xss_3596_, v___x_3604_, v___x_3605_, v___x_3598_);
return v___x_3606_;
}
}
else
{
size_t v___x_3607_; size_t v___x_3608_; lean_object* v___x_3609_; 
v___x_3607_ = ((size_t)0ULL);
v___x_3608_ = lean_usize_of_nat(v___x_3599_);
v___x_3609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3600_, v___f_3602_, v_xss_3596_, v___x_3607_, v___x_3608_, v___x_3598_);
return v___x_3609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop___redArg(lean_object* v_as_3610_, lean_object* v_i_3611_, lean_object* v_j_3612_){
_start:
{
uint8_t v___x_3613_; 
v___x_3613_ = lean_nat_dec_lt(v_i_3611_, v_j_3612_);
if (v___x_3613_ == 0)
{
lean_dec(v_j_3612_);
lean_dec(v_i_3611_);
return v_as_3610_;
}
else
{
lean_object* v_as_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v_as_3614_ = lean_array_fswap(v_as_3610_, v_i_3611_, v_j_3612_);
v___x_3615_ = lean_unsigned_to_nat(1u);
v___x_3616_ = lean_nat_add(v_i_3611_, v___x_3615_);
lean_dec(v_i_3611_);
v___x_3617_ = lean_nat_sub(v_j_3612_, v___x_3615_);
lean_dec(v_j_3612_);
v_as_3610_ = v_as_3614_;
v_i_3611_ = v___x_3616_;
v_j_3612_ = v___x_3617_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop(lean_object* v_00_u03b1_3619_, lean_object* v_as_3620_, lean_object* v_i_3621_, lean_object* v_j_3622_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l_Array_reverse_loop___redArg(v_as_3620_, v_i_3621_, v_j_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Array_reverse___redArg(lean_object* v_as_3624_){
_start:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; uint8_t v___x_3627_; 
v___x_3625_ = lean_array_get_size(v_as_3624_);
v___x_3626_ = lean_unsigned_to_nat(1u);
v___x_3627_ = lean_nat_dec_le(v___x_3625_, v___x_3626_);
if (v___x_3627_ == 0)
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3628_ = lean_unsigned_to_nat(0u);
v___x_3629_ = lean_nat_sub(v___x_3625_, v___x_3626_);
v___x_3630_ = l_Array_reverse_loop___redArg(v_as_3624_, v___x_3628_, v___x_3629_);
return v___x_3630_;
}
else
{
return v_as_3624_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse(lean_object* v_00_u03b1_3631_, lean_object* v_as_3632_){
_start:
{
lean_object* v___x_3633_; 
v___x_3633_ = l_Array_reverse___redArg(v_as_3632_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___lam__0(lean_object* v_p_3634_, lean_object* v_x1_3635_, lean_object* v_x2_3636_){
_start:
{
lean_object* v___x_3637_; uint8_t v___x_3638_; 
lean_inc(v_x2_3636_);
v___x_3637_ = lean_apply_1(v_p_3634_, v_x2_3636_);
v___x_3638_ = lean_unbox(v___x_3637_);
if (v___x_3638_ == 0)
{
lean_dec(v_x2_3636_);
return v_x1_3635_;
}
else
{
lean_object* v___x_3639_; 
v___x_3639_ = lean_array_push(v_x1_3635_, v_x2_3636_);
return v___x_3639_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg(lean_object* v_p_3642_, lean_object* v_as_3643_, lean_object* v_start_3644_, lean_object* v_stop_3645_){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3646_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3647_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3648_ = lean_nat_dec_lt(v_start_3644_, v_stop_3645_);
if (v___x_3648_ == 0)
{
lean_dec_ref(v_as_3643_);
lean_dec_ref(v_p_3642_);
return v___x_3646_;
}
else
{
lean_object* v___f_3649_; lean_object* v___x_3650_; uint8_t v___x_3651_; 
v___f_3649_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3649_, 0, v_p_3642_);
v___x_3650_ = lean_array_get_size(v_as_3643_);
v___x_3651_ = lean_nat_dec_le(v_stop_3645_, v___x_3650_);
if (v___x_3651_ == 0)
{
uint8_t v___x_3652_; 
v___x_3652_ = lean_nat_dec_lt(v_start_3644_, v___x_3650_);
if (v___x_3652_ == 0)
{
lean_dec_ref(v___f_3649_);
lean_dec_ref(v_as_3643_);
return v___x_3646_;
}
else
{
size_t v___x_3653_; size_t v___x_3654_; lean_object* v___x_3655_; 
v___x_3653_ = lean_usize_of_nat(v_start_3644_);
v___x_3654_ = lean_usize_of_nat(v___x_3650_);
v___x_3655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3647_, v___f_3649_, v_as_3643_, v___x_3653_, v___x_3654_, v___x_3646_);
return v___x_3655_;
}
}
else
{
size_t v___x_3656_; size_t v___x_3657_; lean_object* v___x_3658_; 
v___x_3656_ = lean_usize_of_nat(v_start_3644_);
v___x_3657_ = lean_usize_of_nat(v_stop_3645_);
v___x_3658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3647_, v___f_3649_, v_as_3643_, v___x_3656_, v___x_3657_, v___x_3646_);
return v___x_3658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___boxed(lean_object* v_p_3659_, lean_object* v_as_3660_, lean_object* v_start_3661_, lean_object* v_stop_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l_Array_filter___redArg(v_p_3659_, v_as_3660_, v_start_3661_, v_stop_3662_);
lean_dec(v_stop_3662_);
lean_dec(v_start_3661_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_Array_filter(lean_object* v_00_u03b1_3664_, lean_object* v_p_3665_, lean_object* v_as_3666_, lean_object* v_start_3667_, lean_object* v_stop_3668_){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; 
v___x_3669_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3670_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3671_ = lean_nat_dec_lt(v_start_3667_, v_stop_3668_);
if (v___x_3671_ == 0)
{
lean_dec_ref(v_as_3666_);
lean_dec_ref(v_p_3665_);
return v___x_3669_;
}
else
{
lean_object* v___f_3672_; lean_object* v___x_3673_; uint8_t v___x_3674_; 
v___f_3672_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3672_, 0, v_p_3665_);
v___x_3673_ = lean_array_get_size(v_as_3666_);
v___x_3674_ = lean_nat_dec_le(v_stop_3668_, v___x_3673_);
if (v___x_3674_ == 0)
{
uint8_t v___x_3675_; 
v___x_3675_ = lean_nat_dec_lt(v_start_3667_, v___x_3673_);
if (v___x_3675_ == 0)
{
lean_dec_ref(v___f_3672_);
lean_dec_ref(v_as_3666_);
return v___x_3669_;
}
else
{
size_t v___x_3676_; size_t v___x_3677_; lean_object* v___x_3678_; 
v___x_3676_ = lean_usize_of_nat(v_start_3667_);
v___x_3677_ = lean_usize_of_nat(v___x_3673_);
v___x_3678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3670_, v___f_3672_, v_as_3666_, v___x_3676_, v___x_3677_, v___x_3669_);
return v___x_3678_;
}
}
else
{
size_t v___x_3679_; size_t v___x_3680_; lean_object* v___x_3681_; 
v___x_3679_ = lean_usize_of_nat(v_start_3667_);
v___x_3680_ = lean_usize_of_nat(v_stop_3668_);
v___x_3681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3670_, v___f_3672_, v_as_3666_, v___x_3679_, v___x_3680_, v___x_3669_);
return v___x_3681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___boxed(lean_object* v_00_u03b1_3682_, lean_object* v_p_3683_, lean_object* v_as_3684_, lean_object* v_start_3685_, lean_object* v_stop_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Array_filter(v_00_u03b1_3682_, v_p_3683_, v_as_3684_, v_start_3685_, v_stop_3686_);
lean_dec(v_stop_3686_);
lean_dec(v_start_3685_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0(lean_object* v_toApplicative_3688_, lean_object* v_acc_3689_, lean_object* v_a_3690_, uint8_t v_____do__lift_3691_){
_start:
{
if (v_____do__lift_3691_ == 0)
{
lean_object* v_toPure_3692_; lean_object* v___x_3693_; 
lean_dec(v_a_3690_);
v_toPure_3692_ = lean_ctor_get(v_toApplicative_3688_, 1);
lean_inc(v_toPure_3692_);
lean_dec_ref(v_toApplicative_3688_);
v___x_3693_ = lean_apply_2(v_toPure_3692_, lean_box(0), v_acc_3689_);
return v___x_3693_;
}
else
{
lean_object* v_toPure_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v_toPure_3694_ = lean_ctor_get(v_toApplicative_3688_, 1);
lean_inc(v_toPure_3694_);
lean_dec_ref(v_toApplicative_3688_);
v___x_3695_ = lean_array_push(v_acc_3689_, v_a_3690_);
v___x_3696_ = lean_apply_2(v_toPure_3694_, lean_box(0), v___x_3695_);
return v___x_3696_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0___boxed(lean_object* v_toApplicative_3697_, lean_object* v_acc_3698_, lean_object* v_a_3699_, lean_object* v_____do__lift_3700_){
_start:
{
uint8_t v_____do__lift_119__boxed_3701_; lean_object* v_res_3702_; 
v_____do__lift_119__boxed_3701_ = lean_unbox(v_____do__lift_3700_);
v_res_3702_ = l_Array_filterM___redArg___lam__0(v_toApplicative_3697_, v_acc_3698_, v_a_3699_, v_____do__lift_119__boxed_3701_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__1(lean_object* v_toApplicative_3703_, lean_object* v_p_3704_, lean_object* v_toBind_3705_, lean_object* v_acc_3706_, lean_object* v_a_3707_){
_start:
{
lean_object* v___f_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
lean_inc(v_a_3707_);
v___f_3708_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3708_, 0, v_toApplicative_3703_);
lean_closure_set(v___f_3708_, 1, v_acc_3706_);
lean_closure_set(v___f_3708_, 2, v_a_3707_);
v___x_3709_ = lean_apply_1(v_p_3704_, v_a_3707_);
v___x_3710_ = lean_apply_4(v_toBind_3705_, lean_box(0), lean_box(0), v___x_3709_, v___f_3708_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg(lean_object* v_inst_3711_, lean_object* v_p_3712_, lean_object* v_as_3713_, lean_object* v_start_3714_, lean_object* v_stop_3715_){
_start:
{
lean_object* v_toApplicative_3716_; lean_object* v_toBind_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v_toApplicative_3716_ = lean_ctor_get(v_inst_3711_, 0);
v_toBind_3717_ = lean_ctor_get(v_inst_3711_, 1);
v___x_3718_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3719_ = lean_nat_dec_lt(v_start_3714_, v_stop_3715_);
if (v___x_3719_ == 0)
{
lean_object* v_toPure_3720_; lean_object* v___x_3721_; 
lean_inc_ref(v_toApplicative_3716_);
lean_dec_ref(v_as_3713_);
lean_dec(v_p_3712_);
lean_dec_ref(v_inst_3711_);
v_toPure_3720_ = lean_ctor_get(v_toApplicative_3716_, 1);
lean_inc(v_toPure_3720_);
lean_dec_ref(v_toApplicative_3716_);
v___x_3721_ = lean_apply_2(v_toPure_3720_, lean_box(0), v___x_3718_);
return v___x_3721_;
}
else
{
lean_object* v___f_3722_; lean_object* v___x_3723_; uint8_t v___x_3724_; 
lean_inc(v_toBind_3717_);
lean_inc_ref(v_toApplicative_3716_);
v___f_3722_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3722_, 0, v_toApplicative_3716_);
lean_closure_set(v___f_3722_, 1, v_p_3712_);
lean_closure_set(v___f_3722_, 2, v_toBind_3717_);
v___x_3723_ = lean_array_get_size(v_as_3713_);
v___x_3724_ = lean_nat_dec_le(v_stop_3715_, v___x_3723_);
if (v___x_3724_ == 0)
{
uint8_t v___x_3725_; 
v___x_3725_ = lean_nat_dec_lt(v_start_3714_, v___x_3723_);
if (v___x_3725_ == 0)
{
lean_object* v_toPure_3726_; lean_object* v___x_3727_; 
lean_inc_ref(v_toApplicative_3716_);
lean_dec_ref(v___f_3722_);
lean_dec_ref(v_as_3713_);
lean_dec_ref(v_inst_3711_);
v_toPure_3726_ = lean_ctor_get(v_toApplicative_3716_, 1);
lean_inc(v_toPure_3726_);
lean_dec_ref(v_toApplicative_3716_);
v___x_3727_ = lean_apply_2(v_toPure_3726_, lean_box(0), v___x_3718_);
return v___x_3727_;
}
else
{
size_t v___x_3728_; size_t v___x_3729_; lean_object* v___x_3730_; 
v___x_3728_ = lean_usize_of_nat(v_start_3714_);
v___x_3729_ = lean_usize_of_nat(v___x_3723_);
v___x_3730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3711_, v___f_3722_, v_as_3713_, v___x_3728_, v___x_3729_, v___x_3718_);
return v___x_3730_;
}
}
else
{
size_t v___x_3731_; size_t v___x_3732_; lean_object* v___x_3733_; 
v___x_3731_ = lean_usize_of_nat(v_start_3714_);
v___x_3732_ = lean_usize_of_nat(v_stop_3715_);
v___x_3733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3711_, v___f_3722_, v_as_3713_, v___x_3731_, v___x_3732_, v___x_3718_);
return v___x_3733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___boxed(lean_object* v_inst_3734_, lean_object* v_p_3735_, lean_object* v_as_3736_, lean_object* v_start_3737_, lean_object* v_stop_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l_Array_filterM___redArg(v_inst_3734_, v_p_3735_, v_as_3736_, v_start_3737_, v_stop_3738_);
lean_dec(v_stop_3738_);
lean_dec(v_start_3737_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM(lean_object* v_m_3740_, lean_object* v_00_u03b1_3741_, lean_object* v_inst_3742_, lean_object* v_p_3743_, lean_object* v_as_3744_, lean_object* v_start_3745_, lean_object* v_stop_3746_){
_start:
{
lean_object* v_toApplicative_3747_; lean_object* v_toBind_3748_; lean_object* v___x_3749_; uint8_t v___x_3750_; 
v_toApplicative_3747_ = lean_ctor_get(v_inst_3742_, 0);
v_toBind_3748_ = lean_ctor_get(v_inst_3742_, 1);
v___x_3749_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3750_ = lean_nat_dec_lt(v_start_3745_, v_stop_3746_);
if (v___x_3750_ == 0)
{
lean_object* v_toPure_3751_; lean_object* v___x_3752_; 
lean_inc_ref(v_toApplicative_3747_);
lean_dec_ref(v_as_3744_);
lean_dec(v_p_3743_);
lean_dec_ref(v_inst_3742_);
v_toPure_3751_ = lean_ctor_get(v_toApplicative_3747_, 1);
lean_inc(v_toPure_3751_);
lean_dec_ref(v_toApplicative_3747_);
v___x_3752_ = lean_apply_2(v_toPure_3751_, lean_box(0), v___x_3749_);
return v___x_3752_;
}
else
{
lean_object* v___f_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
lean_inc(v_toBind_3748_);
lean_inc_ref(v_toApplicative_3747_);
v___f_3753_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3753_, 0, v_toApplicative_3747_);
lean_closure_set(v___f_3753_, 1, v_p_3743_);
lean_closure_set(v___f_3753_, 2, v_toBind_3748_);
v___x_3754_ = lean_array_get_size(v_as_3744_);
v___x_3755_ = lean_nat_dec_le(v_stop_3746_, v___x_3754_);
if (v___x_3755_ == 0)
{
uint8_t v___x_3756_; 
v___x_3756_ = lean_nat_dec_lt(v_start_3745_, v___x_3754_);
if (v___x_3756_ == 0)
{
lean_object* v_toPure_3757_; lean_object* v___x_3758_; 
lean_inc_ref(v_toApplicative_3747_);
lean_dec_ref(v___f_3753_);
lean_dec_ref(v_as_3744_);
lean_dec_ref(v_inst_3742_);
v_toPure_3757_ = lean_ctor_get(v_toApplicative_3747_, 1);
lean_inc(v_toPure_3757_);
lean_dec_ref(v_toApplicative_3747_);
v___x_3758_ = lean_apply_2(v_toPure_3757_, lean_box(0), v___x_3749_);
return v___x_3758_;
}
else
{
size_t v___x_3759_; size_t v___x_3760_; lean_object* v___x_3761_; 
v___x_3759_ = lean_usize_of_nat(v_start_3745_);
v___x_3760_ = lean_usize_of_nat(v___x_3754_);
v___x_3761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3742_, v___f_3753_, v_as_3744_, v___x_3759_, v___x_3760_, v___x_3749_);
return v___x_3761_;
}
}
else
{
size_t v___x_3762_; size_t v___x_3763_; lean_object* v___x_3764_; 
v___x_3762_ = lean_usize_of_nat(v_start_3745_);
v___x_3763_ = lean_usize_of_nat(v_stop_3746_);
v___x_3764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3742_, v___f_3753_, v_as_3744_, v___x_3762_, v___x_3763_, v___x_3749_);
return v___x_3764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___boxed(lean_object* v_m_3765_, lean_object* v_00_u03b1_3766_, lean_object* v_inst_3767_, lean_object* v_p_3768_, lean_object* v_as_3769_, lean_object* v_start_3770_, lean_object* v_stop_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Array_filterM(v_m_3765_, v_00_u03b1_3766_, v_inst_3767_, v_p_3768_, v_as_3769_, v_start_3770_, v_stop_3771_);
lean_dec(v_stop_3771_);
lean_dec(v_start_3770_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__0(lean_object* v_toPure_3773_, lean_object* v_acc_3774_, lean_object* v_a_3775_, uint8_t v_____do__lift_3776_){
_start:
{
if (v_____do__lift_3776_ == 0)
{
lean_object* v___x_3777_; 
lean_dec(v_a_3775_);
v___x_3777_ = lean_apply_2(v_toPure_3773_, lean_box(0), v_acc_3774_);
return v___x_3777_;
}
else
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = lean_array_push(v_acc_3774_, v_a_3775_);
v___x_3779_ = lean_apply_2(v_toPure_3773_, lean_box(0), v___x_3778_);
return v___x_3779_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__0___boxed(lean_object* v_toPure_3780_, lean_object* v_acc_3781_, lean_object* v_a_3782_, lean_object* v_____do__lift_3783_){
_start:
{
uint8_t v_____do__lift_129__boxed_3784_; lean_object* v_res_3785_; 
v_____do__lift_129__boxed_3784_ = lean_unbox(v_____do__lift_3783_);
v_res_3785_ = l_Array_filterRevM___redArg___lam__0(v_toPure_3780_, v_acc_3781_, v_a_3782_, v_____do__lift_129__boxed_3784_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__1(lean_object* v_toPure_3786_, lean_object* v_p_3787_, lean_object* v_toBind_3788_, lean_object* v_a_3789_, lean_object* v_acc_3790_){
_start:
{
lean_object* v___f_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
lean_inc(v_a_3789_);
v___f_3791_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3791_, 0, v_toPure_3786_);
lean_closure_set(v___f_3791_, 1, v_acc_3790_);
lean_closure_set(v___f_3791_, 2, v_a_3789_);
v___x_3792_ = lean_apply_1(v_p_3787_, v_a_3789_);
v___x_3793_ = lean_apply_4(v_toBind_3788_, lean_box(0), lean_box(0), v___x_3792_, v___f_3791_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg(lean_object* v_inst_3795_, lean_object* v_p_3796_, lean_object* v_as_3797_, lean_object* v_start_3798_, lean_object* v_stop_3799_){
_start:
{
lean_object* v_toApplicative_3800_; lean_object* v_toFunctor_3801_; lean_object* v_toBind_3802_; lean_object* v_toPure_3803_; lean_object* v_map_3804_; lean_object* v___f_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; uint8_t v___x_3809_; 
v_toApplicative_3800_ = lean_ctor_get(v_inst_3795_, 0);
v_toFunctor_3801_ = lean_ctor_get(v_toApplicative_3800_, 0);
v_toBind_3802_ = lean_ctor_get(v_inst_3795_, 1);
v_toPure_3803_ = lean_ctor_get(v_toApplicative_3800_, 1);
v_map_3804_ = lean_ctor_get(v_toFunctor_3801_, 0);
lean_inc(v_map_3804_);
lean_inc(v_toBind_3802_);
lean_inc(v_toPure_3803_);
v___f_3805_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3805_, 0, v_toPure_3803_);
lean_closure_set(v___f_3805_, 1, v_p_3796_);
lean_closure_set(v___f_3805_, 2, v_toBind_3802_);
v___x_3806_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3807_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3808_ = lean_array_get_size(v_as_3797_);
v___x_3809_ = lean_nat_dec_le(v_start_3798_, v___x_3808_);
if (v___x_3809_ == 0)
{
uint8_t v___x_3810_; 
v___x_3810_ = lean_nat_dec_lt(v_stop_3799_, v___x_3808_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
lean_inc(v_toPure_3803_);
lean_dec_ref(v___f_3805_);
lean_dec_ref(v_as_3797_);
lean_dec_ref(v_inst_3795_);
v___x_3811_ = lean_apply_2(v_toPure_3803_, lean_box(0), v___x_3807_);
v___x_3812_ = lean_apply_4(v_map_3804_, lean_box(0), lean_box(0), v___x_3806_, v___x_3811_);
return v___x_3812_;
}
else
{
size_t v___x_3813_; size_t v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3813_ = lean_usize_of_nat(v___x_3808_);
v___x_3814_ = lean_usize_of_nat(v_stop_3799_);
v___x_3815_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3795_, v___f_3805_, v_as_3797_, v___x_3813_, v___x_3814_, v___x_3807_);
v___x_3816_ = lean_apply_4(v_map_3804_, lean_box(0), lean_box(0), v___x_3806_, v___x_3815_);
return v___x_3816_;
}
}
else
{
uint8_t v___x_3817_; 
v___x_3817_ = lean_nat_dec_lt(v_stop_3799_, v_start_3798_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
lean_inc(v_toPure_3803_);
lean_dec_ref(v___f_3805_);
lean_dec_ref(v_as_3797_);
lean_dec_ref(v_inst_3795_);
v___x_3818_ = lean_apply_2(v_toPure_3803_, lean_box(0), v___x_3807_);
v___x_3819_ = lean_apply_4(v_map_3804_, lean_box(0), lean_box(0), v___x_3806_, v___x_3818_);
return v___x_3819_;
}
else
{
size_t v___x_3820_; size_t v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3820_ = lean_usize_of_nat(v_start_3798_);
v___x_3821_ = lean_usize_of_nat(v_stop_3799_);
v___x_3822_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3795_, v___f_3805_, v_as_3797_, v___x_3820_, v___x_3821_, v___x_3807_);
v___x_3823_ = lean_apply_4(v_map_3804_, lean_box(0), lean_box(0), v___x_3806_, v___x_3822_);
return v___x_3823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___boxed(lean_object* v_inst_3824_, lean_object* v_p_3825_, lean_object* v_as_3826_, lean_object* v_start_3827_, lean_object* v_stop_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_Array_filterRevM___redArg(v_inst_3824_, v_p_3825_, v_as_3826_, v_start_3827_, v_stop_3828_);
lean_dec(v_stop_3828_);
lean_dec(v_start_3827_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM(lean_object* v_m_3830_, lean_object* v_00_u03b1_3831_, lean_object* v_inst_3832_, lean_object* v_p_3833_, lean_object* v_as_3834_, lean_object* v_start_3835_, lean_object* v_stop_3836_){
_start:
{
lean_object* v_toApplicative_3837_; lean_object* v_toFunctor_3838_; lean_object* v_toBind_3839_; lean_object* v_toPure_3840_; lean_object* v_map_3841_; lean_object* v___f_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; uint8_t v___x_3846_; 
v_toApplicative_3837_ = lean_ctor_get(v_inst_3832_, 0);
v_toFunctor_3838_ = lean_ctor_get(v_toApplicative_3837_, 0);
v_toBind_3839_ = lean_ctor_get(v_inst_3832_, 1);
v_toPure_3840_ = lean_ctor_get(v_toApplicative_3837_, 1);
v_map_3841_ = lean_ctor_get(v_toFunctor_3838_, 0);
lean_inc(v_map_3841_);
lean_inc(v_toBind_3839_);
lean_inc(v_toPure_3840_);
v___f_3842_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3842_, 0, v_toPure_3840_);
lean_closure_set(v___f_3842_, 1, v_p_3833_);
lean_closure_set(v___f_3842_, 2, v_toBind_3839_);
v___x_3843_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3844_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3845_ = lean_array_get_size(v_as_3834_);
v___x_3846_ = lean_nat_dec_le(v_start_3835_, v___x_3845_);
if (v___x_3846_ == 0)
{
uint8_t v___x_3847_; 
v___x_3847_ = lean_nat_dec_lt(v_stop_3836_, v___x_3845_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
lean_inc(v_toPure_3840_);
lean_dec_ref(v___f_3842_);
lean_dec_ref(v_as_3834_);
lean_dec_ref(v_inst_3832_);
v___x_3848_ = lean_apply_2(v_toPure_3840_, lean_box(0), v___x_3844_);
v___x_3849_ = lean_apply_4(v_map_3841_, lean_box(0), lean_box(0), v___x_3843_, v___x_3848_);
return v___x_3849_;
}
else
{
size_t v___x_3850_; size_t v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3850_ = lean_usize_of_nat(v___x_3845_);
v___x_3851_ = lean_usize_of_nat(v_stop_3836_);
v___x_3852_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3832_, v___f_3842_, v_as_3834_, v___x_3850_, v___x_3851_, v___x_3844_);
v___x_3853_ = lean_apply_4(v_map_3841_, lean_box(0), lean_box(0), v___x_3843_, v___x_3852_);
return v___x_3853_;
}
}
else
{
uint8_t v___x_3854_; 
v___x_3854_ = lean_nat_dec_lt(v_stop_3836_, v_start_3835_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
lean_inc(v_toPure_3840_);
lean_dec_ref(v___f_3842_);
lean_dec_ref(v_as_3834_);
lean_dec_ref(v_inst_3832_);
v___x_3855_ = lean_apply_2(v_toPure_3840_, lean_box(0), v___x_3844_);
v___x_3856_ = lean_apply_4(v_map_3841_, lean_box(0), lean_box(0), v___x_3843_, v___x_3855_);
return v___x_3856_;
}
else
{
size_t v___x_3857_; size_t v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3857_ = lean_usize_of_nat(v_start_3835_);
v___x_3858_ = lean_usize_of_nat(v_stop_3836_);
v___x_3859_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3832_, v___f_3842_, v_as_3834_, v___x_3857_, v___x_3858_, v___x_3844_);
v___x_3860_ = lean_apply_4(v_map_3841_, lean_box(0), lean_box(0), v___x_3843_, v___x_3859_);
return v___x_3860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___boxed(lean_object* v_m_3861_, lean_object* v_00_u03b1_3862_, lean_object* v_inst_3863_, lean_object* v_p_3864_, lean_object* v_as_3865_, lean_object* v_start_3866_, lean_object* v_stop_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_Array_filterRevM(v_m_3861_, v_00_u03b1_3862_, v_inst_3863_, v_p_3864_, v_as_3865_, v_start_3866_, v_stop_3867_);
lean_dec(v_stop_3867_);
lean_dec(v_start_3866_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__0(lean_object* v_toPure_3869_, lean_object* v_bs_3870_, lean_object* v_____do__lift_3871_){
_start:
{
if (lean_obj_tag(v_____do__lift_3871_) == 0)
{
lean_object* v___x_3872_; 
v___x_3872_ = lean_apply_2(v_toPure_3869_, lean_box(0), v_bs_3870_);
return v___x_3872_;
}
else
{
lean_object* v_val_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v_val_3873_ = lean_ctor_get(v_____do__lift_3871_, 0);
lean_inc(v_val_3873_);
lean_dec_ref_known(v_____do__lift_3871_, 1);
v___x_3874_ = lean_array_push(v_bs_3870_, v_val_3873_);
v___x_3875_ = lean_apply_2(v_toPure_3869_, lean_box(0), v___x_3874_);
return v___x_3875_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__1(lean_object* v_toPure_3876_, lean_object* v_f_3877_, lean_object* v_toBind_3878_, lean_object* v_bs_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v___f_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___f_3881_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3881_, 0, v_toPure_3876_);
lean_closure_set(v___f_3881_, 1, v_bs_3879_);
v___x_3882_ = lean_apply_1(v_f_3877_, v_a_3880_);
v___x_3883_ = lean_apply_4(v_toBind_3878_, lean_box(0), lean_box(0), v___x_3882_, v___f_3881_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg(lean_object* v_inst_3884_, lean_object* v_f_3885_, lean_object* v_as_3886_, lean_object* v_start_3887_, lean_object* v_stop_3888_){
_start:
{
lean_object* v_toApplicative_3889_; lean_object* v_toBind_3890_; lean_object* v_toPure_3891_; lean_object* v___x_3892_; uint8_t v___x_3893_; 
v_toApplicative_3889_ = lean_ctor_get(v_inst_3884_, 0);
v_toBind_3890_ = lean_ctor_get(v_inst_3884_, 1);
v_toPure_3891_ = lean_ctor_get(v_toApplicative_3889_, 1);
v___x_3892_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3893_ = lean_nat_dec_lt(v_start_3887_, v_stop_3888_);
if (v___x_3893_ == 0)
{
lean_object* v___x_3894_; 
lean_inc(v_toPure_3891_);
lean_dec_ref(v_as_3886_);
lean_dec(v_f_3885_);
lean_dec_ref(v_inst_3884_);
v___x_3894_ = lean_apply_2(v_toPure_3891_, lean_box(0), v___x_3892_);
return v___x_3894_;
}
else
{
lean_object* v___f_3895_; lean_object* v___x_3896_; uint8_t v___x_3897_; 
lean_inc(v_toBind_3890_);
lean_inc(v_toPure_3891_);
v___f_3895_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3895_, 0, v_toPure_3891_);
lean_closure_set(v___f_3895_, 1, v_f_3885_);
lean_closure_set(v___f_3895_, 2, v_toBind_3890_);
v___x_3896_ = lean_array_get_size(v_as_3886_);
v___x_3897_ = lean_nat_dec_le(v_stop_3888_, v___x_3896_);
if (v___x_3897_ == 0)
{
uint8_t v___x_3898_; 
v___x_3898_ = lean_nat_dec_lt(v_start_3887_, v___x_3896_);
if (v___x_3898_ == 0)
{
lean_object* v___x_3899_; 
lean_inc(v_toPure_3891_);
lean_dec_ref(v___f_3895_);
lean_dec_ref(v_as_3886_);
lean_dec_ref(v_inst_3884_);
v___x_3899_ = lean_apply_2(v_toPure_3891_, lean_box(0), v___x_3892_);
return v___x_3899_;
}
else
{
size_t v___x_3900_; size_t v___x_3901_; lean_object* v___x_3902_; 
v___x_3900_ = lean_usize_of_nat(v_start_3887_);
v___x_3901_ = lean_usize_of_nat(v___x_3896_);
v___x_3902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3884_, v___f_3895_, v_as_3886_, v___x_3900_, v___x_3901_, v___x_3892_);
return v___x_3902_;
}
}
else
{
size_t v___x_3903_; size_t v___x_3904_; lean_object* v___x_3905_; 
v___x_3903_ = lean_usize_of_nat(v_start_3887_);
v___x_3904_ = lean_usize_of_nat(v_stop_3888_);
v___x_3905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3884_, v___f_3895_, v_as_3886_, v___x_3903_, v___x_3904_, v___x_3892_);
return v___x_3905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___boxed(lean_object* v_inst_3906_, lean_object* v_f_3907_, lean_object* v_as_3908_, lean_object* v_start_3909_, lean_object* v_stop_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Array_filterMapM___redArg(v_inst_3906_, v_f_3907_, v_as_3908_, v_start_3909_, v_stop_3910_);
lean_dec(v_stop_3910_);
lean_dec(v_start_3909_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM(lean_object* v_00_u03b1_3912_, lean_object* v_m_3913_, lean_object* v_00_u03b2_3914_, lean_object* v_inst_3915_, lean_object* v_f_3916_, lean_object* v_as_3917_, lean_object* v_start_3918_, lean_object* v_stop_3919_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Array_filterMapM___redArg(v_inst_3915_, v_f_3916_, v_as_3917_, v_start_3918_, v_stop_3919_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___boxed(lean_object* v_00_u03b1_3921_, lean_object* v_m_3922_, lean_object* v_00_u03b2_3923_, lean_object* v_inst_3924_, lean_object* v_f_3925_, lean_object* v_as_3926_, lean_object* v_start_3927_, lean_object* v_stop_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Array_filterMapM(v_00_u03b1_3921_, v_m_3922_, v_00_u03b2_3923_, v_inst_3924_, v_f_3925_, v_as_3926_, v_start_3927_, v_stop_3928_);
lean_dec(v_stop_3928_);
lean_dec(v_start_3927_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg(lean_object* v_f_3930_, lean_object* v_as_3931_, lean_object* v_start_3932_, lean_object* v_stop_3933_){
_start:
{
lean_object* v___f_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___f_3934_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3934_, 0, v_f_3930_);
v___x_3935_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3936_ = l_Array_filterMapM___redArg(v___x_3935_, v___f_3934_, v_as_3931_, v_start_3932_, v_stop_3933_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg___boxed(lean_object* v_f_3937_, lean_object* v_as_3938_, lean_object* v_start_3939_, lean_object* v_stop_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l_Array_filterMap___redArg(v_f_3937_, v_as_3938_, v_start_3939_, v_stop_3940_);
lean_dec(v_stop_3940_);
lean_dec(v_start_3939_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap(lean_object* v_00_u03b1_3942_, lean_object* v_00_u03b2_3943_, lean_object* v_f_3944_, lean_object* v_as_3945_, lean_object* v_start_3946_, lean_object* v_stop_3947_){
_start:
{
lean_object* v___f_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___f_3948_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3948_, 0, v_f_3944_);
v___x_3949_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3950_ = l_Array_filterMapM___redArg(v___x_3949_, v___f_3948_, v_as_3945_, v_start_3946_, v_stop_3947_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___boxed(lean_object* v_00_u03b1_3951_, lean_object* v_00_u03b2_3952_, lean_object* v_f_3953_, lean_object* v_as_3954_, lean_object* v_start_3955_, lean_object* v_stop_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l_Array_filterMap(v_00_u03b1_3951_, v_00_u03b2_3952_, v_f_3953_, v_as_3954_, v_start_3955_, v_stop_3956_);
lean_dec(v_stop_3956_);
lean_dec(v_start_3955_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg___lam__0(lean_object* v_lt_3958_, lean_object* v_x1_3959_, lean_object* v_x2_3960_){
_start:
{
lean_object* v___x_3961_; uint8_t v___x_3962_; 
lean_inc(v_x2_3960_);
lean_inc(v_x1_3959_);
v___x_3961_ = lean_apply_2(v_lt_3958_, v_x1_3959_, v_x2_3960_);
v___x_3962_ = lean_unbox(v___x_3961_);
if (v___x_3962_ == 0)
{
lean_dec(v_x2_3960_);
return v_x1_3959_;
}
else
{
lean_dec(v_x1_3959_);
return v_x2_3960_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg(lean_object* v_as_3963_, lean_object* v_lt_3964_){
_start:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; 
v___x_3965_ = lean_unsigned_to_nat(0u);
v___x_3966_ = lean_array_get_size(v_as_3963_);
v___x_3967_ = lean_nat_dec_lt(v___x_3965_, v___x_3966_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; 
lean_dec_ref(v_lt_3964_);
lean_dec_ref(v_as_3963_);
v___x_3968_ = lean_box(0);
return v___x_3968_;
}
else
{
lean_object* v_a0_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; 
v_a0_3969_ = lean_array_fget(v_as_3963_, v___x_3965_);
v___x_3970_ = lean_unsigned_to_nat(1u);
v___x_3971_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3972_ = lean_nat_dec_lt(v___x_3970_, v___x_3966_);
if (v___x_3972_ == 0)
{
lean_object* v___x_3973_; 
lean_dec_ref(v_lt_3964_);
lean_dec_ref(v_as_3963_);
v___x_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3973_, 0, v_a0_3969_);
return v___x_3973_;
}
else
{
lean_object* v___f_3974_; uint8_t v___x_3975_; 
v___f_3974_ = lean_alloc_closure((void*)(l_Array_getMax_x3f___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3974_, 0, v_lt_3964_);
v___x_3975_ = lean_nat_dec_le(v___x_3966_, v___x_3966_);
if (v___x_3975_ == 0)
{
if (v___x_3972_ == 0)
{
lean_object* v___x_3976_; 
lean_dec_ref(v___f_3974_);
lean_dec_ref(v_as_3963_);
v___x_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3976_, 0, v_a0_3969_);
return v___x_3976_;
}
else
{
size_t v___x_3977_; size_t v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3977_ = ((size_t)1ULL);
v___x_3978_ = lean_usize_of_nat(v___x_3966_);
v___x_3979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3971_, v___f_3974_, v_as_3963_, v___x_3977_, v___x_3978_, v_a0_3969_);
v___x_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
return v___x_3980_;
}
}
else
{
size_t v___x_3981_; size_t v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3981_ = ((size_t)1ULL);
v___x_3982_ = lean_usize_of_nat(v___x_3966_);
v___x_3983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3971_, v___f_3974_, v_as_3963_, v___x_3981_, v___x_3982_, v_a0_3969_);
v___x_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3983_);
return v___x_3984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f(lean_object* v_00_u03b1_3985_, lean_object* v_as_3986_, lean_object* v_lt_3987_){
_start:
{
lean_object* v___x_3988_; 
v___x_3988_ = l_Array_getMax_x3f___redArg(v_as_3986_, v_lt_3987_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg___lam__0(lean_object* v_p_3989_, lean_object* v_a_3990_, lean_object* v_x_3991_, lean_object* v___y_3992_){
_start:
{
lean_object* v_fst_3993_; lean_object* v_snd_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4010_; 
v_fst_3993_ = lean_ctor_get(v___y_3992_, 0);
v_snd_3994_ = lean_ctor_get(v___y_3992_, 1);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___y_3992_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_3996_ = v___y_3992_;
v_isShared_3997_ = v_isSharedCheck_4010_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_snd_3994_);
lean_inc(v_fst_3993_);
lean_dec(v___y_3992_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4010_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3998_; uint8_t v___x_3999_; 
lean_inc(v_a_3990_);
v___x_3998_ = lean_apply_1(v_p_3989_, v_a_3990_);
v___x_3999_ = lean_unbox(v___x_3998_);
if (v___x_3999_ == 0)
{
lean_object* v___x_4000_; lean_object* v___x_4002_; 
v___x_4000_ = lean_array_push(v_snd_3994_, v_a_3990_);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 1, v___x_4000_);
v___x_4002_ = v___x_3996_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_fst_3993_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v___x_4000_);
v___x_4002_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
lean_object* v___x_4003_; 
v___x_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
return v___x_4003_;
}
}
else
{
lean_object* v___x_4005_; lean_object* v___x_4007_; 
v___x_4005_ = lean_array_push(v_fst_3993_, v_a_3990_);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 0, v___x_4005_);
v___x_4007_ = v___x_3996_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v___x_4005_);
lean_ctor_set(v_reuseFailAlloc_4009_, 1, v_snd_3994_);
v___x_4007_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4008_; 
v___x_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
return v___x_4008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg(lean_object* v_p_4013_, lean_object* v_as_4014_){
_start:
{
lean_object* v___f_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; size_t v_sz_4018_; size_t v___x_4019_; lean_object* v___x_4020_; lean_object* v_fst_4021_; lean_object* v_snd_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
v___f_4015_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4015_, 0, v_p_4013_);
v___x_4016_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4017_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_4018_ = lean_array_size(v_as_4014_);
v___x_4019_ = ((size_t)0ULL);
v___x_4020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_4016_, v_as_4014_, v___f_4015_, v_sz_4018_, v___x_4019_, v___x_4017_);
v_fst_4021_ = lean_ctor_get(v___x_4020_, 0);
v_snd_4022_ = lean_ctor_get(v___x_4020_, 1);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_4020_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_snd_4022_);
lean_inc(v_fst_4021_);
lean_dec(v___x_4020_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_fst_4021_);
lean_ctor_set(v_reuseFailAlloc_4028_, 1, v_snd_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition(lean_object* v_00_u03b1_4030_, lean_object* v_p_4031_, lean_object* v_as_4032_){
_start:
{
lean_object* v___f_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; size_t v_sz_4036_; size_t v___x_4037_; lean_object* v___x_4038_; lean_object* v_fst_4039_; lean_object* v_snd_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
v___f_4033_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4033_, 0, v_p_4031_);
v___x_4034_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4035_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_4036_ = lean_array_size(v_as_4032_);
v___x_4037_ = ((size_t)0ULL);
v___x_4038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_4034_, v_as_4032_, v___f_4033_, v_sz_4036_, v___x_4037_, v___x_4035_);
v_fst_4039_ = lean_ctor_get(v___x_4038_, 0);
v_snd_4040_ = lean_ctor_get(v___x_4038_, 1);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_4038_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_snd_4040_);
lean_inc(v_fst_4039_);
lean_dec(v___x_4038_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_fst_4039_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v_snd_4040_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile___redArg(lean_object* v_p_4048_, lean_object* v_as_4049_){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; uint8_t v___x_4052_; 
v___x_4050_ = lean_unsigned_to_nat(0u);
v___x_4051_ = lean_array_get_size(v_as_4049_);
v___x_4052_ = lean_nat_dec_lt(v___x_4050_, v___x_4051_);
if (v___x_4052_ == 0)
{
lean_dec_ref(v_p_4048_);
return v_as_4049_;
}
else
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; 
v___x_4053_ = lean_unsigned_to_nat(1u);
v___x_4054_ = lean_nat_sub(v___x_4051_, v___x_4053_);
v___x_4055_ = lean_array_fget_borrowed(v_as_4049_, v___x_4054_);
lean_dec(v___x_4054_);
lean_inc_ref(v_p_4048_);
lean_inc(v___x_4055_);
v___x_4056_ = lean_apply_1(v_p_4048_, v___x_4055_);
v___x_4057_ = lean_unbox(v___x_4056_);
if (v___x_4057_ == 0)
{
lean_dec_ref(v_p_4048_);
return v_as_4049_;
}
else
{
lean_object* v___x_4058_; 
v___x_4058_ = lean_array_pop(v_as_4049_);
v_as_4049_ = v___x_4058_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile(lean_object* v_00_u03b1_4060_, lean_object* v_p_4061_, lean_object* v_as_4062_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Array_popWhile___redArg(v_p_4061_, v_as_4062_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(lean_object* v_p_4064_, lean_object* v_as_4065_, lean_object* v_i_4066_, lean_object* v_acc_4067_){
_start:
{
lean_object* v___x_4068_; uint8_t v___x_4069_; 
v___x_4068_ = lean_array_get_size(v_as_4065_);
v___x_4069_ = lean_nat_dec_lt(v_i_4066_, v___x_4068_);
if (v___x_4069_ == 0)
{
lean_dec(v_i_4066_);
lean_dec_ref(v_p_4064_);
return v_acc_4067_;
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4071_; uint8_t v___x_4072_; 
v_a_4070_ = lean_array_fget_borrowed(v_as_4065_, v_i_4066_);
lean_inc_ref(v_p_4064_);
lean_inc(v_a_4070_);
v___x_4071_ = lean_apply_1(v_p_4064_, v_a_4070_);
v___x_4072_ = lean_unbox(v___x_4071_);
if (v___x_4072_ == 0)
{
lean_dec(v_i_4066_);
lean_dec_ref(v_p_4064_);
return v_acc_4067_;
}
else
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4073_ = lean_unsigned_to_nat(1u);
v___x_4074_ = lean_nat_add(v_i_4066_, v___x_4073_);
lean_dec(v_i_4066_);
lean_inc(v_a_4070_);
v___x_4075_ = lean_array_push(v_acc_4067_, v_a_4070_);
v_i_4066_ = v___x_4074_;
v_acc_4067_ = v___x_4075_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg___boxed(lean_object* v_p_4077_, lean_object* v_as_4078_, lean_object* v_i_4079_, lean_object* v_acc_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4077_, v_as_4078_, v_i_4079_, v_acc_4080_);
lean_dec_ref(v_as_4078_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(lean_object* v_00_u03b1_4082_, lean_object* v_p_4083_, lean_object* v_as_4084_, lean_object* v_i_4085_, lean_object* v_acc_4086_){
_start:
{
lean_object* v___x_4087_; 
v___x_4087_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4083_, v_as_4084_, v_i_4085_, v_acc_4086_);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___boxed(lean_object* v_00_u03b1_4088_, lean_object* v_p_4089_, lean_object* v_as_4090_, lean_object* v_i_4091_, lean_object* v_acc_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(v_00_u03b1_4088_, v_p_4089_, v_as_4090_, v_i_4091_, v_acc_4092_);
lean_dec_ref(v_as_4090_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg(lean_object* v_p_4094_, lean_object* v_as_4095_){
_start:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4096_ = lean_unsigned_to_nat(0u);
v___x_4097_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4098_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4094_, v_as_4095_, v___x_4096_, v___x_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg___boxed(lean_object* v_p_4099_, lean_object* v_as_4100_){
_start:
{
lean_object* v_res_4101_; 
v_res_4101_ = l_Array_takeWhile___redArg(v_p_4099_, v_as_4100_);
lean_dec_ref(v_as_4100_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile(lean_object* v_00_u03b1_4102_, lean_object* v_p_4103_, lean_object* v_as_4104_){
_start:
{
lean_object* v___x_4105_; 
v___x_4105_ = l_Array_takeWhile___redArg(v_p_4103_, v_as_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___boxed(lean_object* v_00_u03b1_4106_, lean_object* v_p_4107_, lean_object* v_as_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Array_takeWhile(v_00_u03b1_4106_, v_p_4107_, v_as_4108_);
lean_dec_ref(v_as_4108_);
return v_res_4109_;
}
}
static lean_object* _init_l_Array_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_4110_; 
v___x_4110_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx___redArg(lean_object* v_xs_4111_, lean_object* v_i_4112_){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; uint8_t v___x_4116_; 
v___x_4113_ = lean_unsigned_to_nat(1u);
v___x_4114_ = lean_nat_add(v_i_4112_, v___x_4113_);
v___x_4115_ = lean_array_get_size(v_xs_4111_);
v___x_4116_ = lean_nat_dec_lt(v___x_4114_, v___x_4115_);
if (v___x_4116_ == 0)
{
lean_object* v___x_4117_; 
lean_dec(v___x_4114_);
lean_dec(v_i_4112_);
v___x_4117_ = lean_array_pop(v_xs_4111_);
return v___x_4117_;
}
else
{
lean_object* v_xs_x27_4118_; 
v_xs_x27_4118_ = lean_array_fswap(v_xs_4111_, v___x_4114_, v_i_4112_);
lean_dec(v_i_4112_);
v_xs_4111_ = v_xs_x27_4118_;
v_i_4112_ = v___x_4114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx(lean_object* v_00_u03b1_4120_, lean_object* v_xs_4121_, lean_object* v_i_4122_, lean_object* v_h_4123_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_Array_eraseIdx___redArg(v_xs_4121_, v_i_4122_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds___redArg(lean_object* v_xs_4125_, lean_object* v_i_4126_){
_start:
{
lean_object* v___x_4127_; uint8_t v___x_4128_; 
v___x_4127_ = lean_array_get_size(v_xs_4125_);
v___x_4128_ = lean_nat_dec_lt(v_i_4126_, v___x_4127_);
if (v___x_4128_ == 0)
{
lean_dec(v_i_4126_);
return v_xs_4125_;
}
else
{
lean_object* v___x_4129_; 
v___x_4129_ = l_Array_eraseIdx___redArg(v_xs_4125_, v_i_4126_);
return v___x_4129_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds(lean_object* v_00_u03b1_4130_, lean_object* v_xs_4131_, lean_object* v_i_4132_){
_start:
{
lean_object* v___x_4133_; 
v___x_4133_ = l_Array_eraseIdxIfInBounds___redArg(v_xs_4131_, v_i_4132_);
return v___x_4133_;
}
}
static lean_object* _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4134_; 
v___x_4134_ = l_Array_instInhabited(lean_box(0));
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(lean_object* v_msg_4135_){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4136_ = lean_obj_once(&l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0, &l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0_once, _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0);
v___x_4137_ = lean_panic_fn_borrowed(v___x_4136_, v_msg_4135_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0(lean_object* v_00_u03b1_4138_, lean_object* v_msg_4139_){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v_msg_4139_);
return v___x_4140_;
}
}
static lean_object* _init_l_Array_eraseIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4143_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4144_ = lean_unsigned_to_nat(47u);
v___x_4145_ = lean_unsigned_to_nat(1842u);
v___x_4146_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__0));
v___x_4147_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4148_ = l_mkPanicMessageWithDecl(v___x_4147_, v___x_4146_, v___x_4145_, v___x_4144_, v___x_4143_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21___redArg(lean_object* v_xs_4149_, lean_object* v_i_4150_){
_start:
{
lean_object* v___x_4151_; uint8_t v___x_4152_; 
v___x_4151_ = lean_array_get_size(v_xs_4149_);
v___x_4152_ = lean_nat_dec_lt(v_i_4150_, v___x_4151_);
if (v___x_4152_ == 0)
{
lean_object* v___x_4153_; lean_object* v___x_4154_; 
lean_dec(v_i_4150_);
lean_dec_ref(v_xs_4149_);
v___x_4153_ = lean_obj_once(&l_Array_eraseIdx_x21___redArg___closed__2, &l_Array_eraseIdx_x21___redArg___closed__2_once, _init_l_Array_eraseIdx_x21___redArg___closed__2);
v___x_4154_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4153_);
return v___x_4154_;
}
else
{
lean_object* v___x_4155_; 
v___x_4155_ = l_Array_eraseIdx___redArg(v_xs_4149_, v_i_4150_);
return v___x_4155_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21(lean_object* v_00_u03b1_4156_, lean_object* v_xs_4157_, lean_object* v_i_4158_){
_start:
{
lean_object* v___x_4159_; 
v___x_4159_ = l_Array_eraseIdx_x21___redArg(v_xs_4157_, v_i_4158_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l_Array_erase___redArg(lean_object* v_inst_4160_, lean_object* v_as_4161_, lean_object* v_a_4162_){
_start:
{
lean_object* v___x_4163_; 
v___x_4163_ = l_Array_finIdxOf_x3f___redArg(v_inst_4160_, v_as_4161_, v_a_4162_);
if (lean_obj_tag(v___x_4163_) == 0)
{
return v_as_4161_;
}
else
{
lean_object* v_val_4164_; lean_object* v___x_4165_; 
v_val_4164_ = lean_ctor_get(v___x_4163_, 0);
lean_inc(v_val_4164_);
lean_dec_ref_known(v___x_4163_, 1);
v___x_4165_ = l_Array_eraseIdx___redArg(v_as_4161_, v_val_4164_);
return v___x_4165_;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase(lean_object* v_00_u03b1_4166_, lean_object* v_inst_4167_, lean_object* v_as_4168_, lean_object* v_a_4169_){
_start:
{
lean_object* v___x_4170_; 
v___x_4170_ = l_Array_erase___redArg(v_inst_4167_, v_as_4168_, v_a_4169_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseP___redArg(lean_object* v_as_4171_, lean_object* v_p_4172_){
_start:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = lean_unsigned_to_nat(0u);
v___x_4174_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_4172_, v_as_4171_, v___x_4173_);
if (lean_obj_tag(v___x_4174_) == 0)
{
return v_as_4171_;
}
else
{
lean_object* v_val_4175_; lean_object* v___x_4176_; 
v_val_4175_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_val_4175_);
lean_dec_ref_known(v___x_4174_, 1);
v___x_4176_ = l_Array_eraseIdx___redArg(v_as_4171_, v_val_4175_);
return v___x_4176_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseP(lean_object* v_00_u03b1_4177_, lean_object* v_as_4178_, lean_object* v_p_4179_){
_start:
{
lean_object* v___x_4180_; 
v___x_4180_ = l_Array_eraseP___redArg(v_as_4178_, v_p_4179_);
return v___x_4180_;
}
}
static lean_object* _init_l_Array_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_4181_; 
v___x_4181_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(lean_object* v_i_4182_, lean_object* v_as_4183_, lean_object* v_j_4184_){
_start:
{
uint8_t v___x_4185_; 
v___x_4185_ = lean_nat_dec_lt(v_i_4182_, v_j_4184_);
if (v___x_4185_ == 0)
{
lean_dec(v_j_4184_);
return v_as_4183_;
}
else
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v_as_4188_; 
v___x_4186_ = lean_unsigned_to_nat(1u);
v___x_4187_ = lean_nat_sub(v_j_4184_, v___x_4186_);
v_as_4188_ = lean_array_fswap(v_as_4183_, v___x_4187_, v_j_4184_);
lean_dec(v_j_4184_);
v_as_4183_ = v_as_4188_;
v_j_4184_ = v___x_4187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg___boxed(lean_object* v_i_4190_, lean_object* v_as_4191_, lean_object* v_j_4192_){
_start:
{
lean_object* v_res_4193_; 
v_res_4193_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4190_, v_as_4191_, v_j_4192_);
lean_dec(v_i_4190_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object* v_00_u03b1_4194_, lean_object* v_i_4195_, lean_object* v_as_4196_, lean_object* v_j_4197_){
_start:
{
lean_object* v___x_4198_; 
v___x_4198_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4195_, v_as_4196_, v_j_4197_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___boxed(lean_object* v_00_u03b1_4199_, lean_object* v_i_4200_, lean_object* v_as_4201_, lean_object* v_j_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(v_00_u03b1_4199_, v_i_4200_, v_as_4201_, v_j_4202_);
lean_dec(v_i_4200_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg(lean_object* v_as_4204_, lean_object* v_i_4205_, lean_object* v_a_4206_){
_start:
{
lean_object* v_j_4207_; lean_object* v_as_4208_; lean_object* v___x_4209_; 
v_j_4207_ = lean_array_get_size(v_as_4204_);
v_as_4208_ = lean_array_push(v_as_4204_, v_a_4206_);
v___x_4209_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4205_, v_as_4208_, v_j_4207_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg___boxed(lean_object* v_as_4210_, lean_object* v_i_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l_Array_insertIdx___redArg(v_as_4210_, v_i_4211_, v_a_4212_);
lean_dec(v_i_4211_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx(lean_object* v_00_u03b1_4214_, lean_object* v_as_4215_, lean_object* v_i_4216_, lean_object* v_a_4217_, lean_object* v_x_4218_){
_start:
{
lean_object* v_j_4219_; lean_object* v_as_4220_; lean_object* v___x_4221_; 
v_j_4219_ = lean_array_get_size(v_as_4215_);
v_as_4220_ = lean_array_push(v_as_4215_, v_a_4217_);
v___x_4221_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4216_, v_as_4220_, v_j_4219_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___boxed(lean_object* v_00_u03b1_4222_, lean_object* v_as_4223_, lean_object* v_i_4224_, lean_object* v_a_4225_, lean_object* v_x_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l_Array_insertIdx(v_00_u03b1_4222_, v_as_4223_, v_i_4224_, v_a_4225_, v_x_4226_);
lean_dec(v_i_4224_);
return v_res_4227_;
}
}
static lean_object* _init_l_Array_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4229_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4230_ = lean_unsigned_to_nat(7u);
v___x_4231_ = lean_unsigned_to_nat(1924u);
v___x_4232_ = ((lean_object*)(l_Array_insertIdx_x21___redArg___closed__0));
v___x_4233_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4234_ = l_mkPanicMessageWithDecl(v___x_4233_, v___x_4232_, v___x_4231_, v___x_4230_, v___x_4229_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg(lean_object* v_as_4235_, lean_object* v_i_4236_, lean_object* v_a_4237_){
_start:
{
lean_object* v___x_4238_; uint8_t v___x_4239_; 
v___x_4238_ = lean_array_get_size(v_as_4235_);
v___x_4239_ = lean_nat_dec_le(v_i_4236_, v___x_4238_);
if (v___x_4239_ == 0)
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
lean_dec(v_a_4237_);
lean_dec_ref(v_as_4235_);
v___x_4240_ = lean_obj_once(&l_Array_insertIdx_x21___redArg___closed__1, &l_Array_insertIdx_x21___redArg___closed__1_once, _init_l_Array_insertIdx_x21___redArg___closed__1);
v___x_4241_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4240_);
return v___x_4241_;
}
else
{
lean_object* v_as_4242_; lean_object* v___x_4243_; 
v_as_4242_ = lean_array_push(v_as_4235_, v_a_4237_);
v___x_4243_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4236_, v_as_4242_, v___x_4238_);
return v___x_4243_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg___boxed(lean_object* v_as_4244_, lean_object* v_i_4245_, lean_object* v_a_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Array_insertIdx_x21___redArg(v_as_4244_, v_i_4245_, v_a_4246_);
lean_dec(v_i_4245_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21(lean_object* v_00_u03b1_4248_, lean_object* v_as_4249_, lean_object* v_i_4250_, lean_object* v_a_4251_){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Array_insertIdx_x21___redArg(v_as_4249_, v_i_4250_, v_a_4251_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___boxed(lean_object* v_00_u03b1_4253_, lean_object* v_as_4254_, lean_object* v_i_4255_, lean_object* v_a_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l_Array_insertIdx_x21(v_00_u03b1_4253_, v_as_4254_, v_i_4255_, v_a_4256_);
lean_dec(v_i_4255_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg(lean_object* v_as_4258_, lean_object* v_i_4259_, lean_object* v_a_4260_){
_start:
{
lean_object* v___x_4261_; uint8_t v___x_4262_; 
v___x_4261_ = lean_array_get_size(v_as_4258_);
v___x_4262_ = lean_nat_dec_le(v_i_4259_, v___x_4261_);
if (v___x_4262_ == 0)
{
lean_dec(v_a_4260_);
return v_as_4258_;
}
else
{
lean_object* v_as_4263_; lean_object* v___x_4264_; 
v_as_4263_ = lean_array_push(v_as_4258_, v_a_4260_);
v___x_4264_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4259_, v_as_4263_, v___x_4261_);
return v___x_4264_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg___boxed(lean_object* v_as_4265_, lean_object* v_i_4266_, lean_object* v_a_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l_Array_insertIdxIfInBounds___redArg(v_as_4265_, v_i_4266_, v_a_4267_);
lean_dec(v_i_4266_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds(lean_object* v_00_u03b1_4269_, lean_object* v_as_4270_, lean_object* v_i_4271_, lean_object* v_a_4272_){
_start:
{
lean_object* v___x_4273_; 
v___x_4273_ = l_Array_insertIdxIfInBounds___redArg(v_as_4270_, v_i_4271_, v_a_4272_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___boxed(lean_object* v_00_u03b1_4274_, lean_object* v_as_4275_, lean_object* v_i_4276_, lean_object* v_a_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l_Array_insertIdxIfInBounds(v_00_u03b1_4274_, v_as_4275_, v_i_4276_, v_a_4277_);
lean_dec(v_i_4276_);
return v_res_4278_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux___redArg(lean_object* v_inst_4279_, lean_object* v_as_4280_, lean_object* v_bs_4281_, lean_object* v_i_4282_){
_start:
{
lean_object* v___x_4283_; uint8_t v___x_4284_; 
v___x_4283_ = lean_array_get_size(v_as_4280_);
v___x_4284_ = lean_nat_dec_lt(v_i_4282_, v___x_4283_);
if (v___x_4284_ == 0)
{
uint8_t v___x_4285_; 
lean_dec(v_i_4282_);
lean_dec_ref(v_inst_4279_);
v___x_4285_ = 1;
return v___x_4285_;
}
else
{
lean_object* v_a_4286_; lean_object* v_b_4287_; lean_object* v___x_4288_; uint8_t v___x_4289_; 
v_a_4286_ = lean_array_fget_borrowed(v_as_4280_, v_i_4282_);
v_b_4287_ = lean_array_fget_borrowed(v_bs_4281_, v_i_4282_);
lean_inc_ref(v_inst_4279_);
lean_inc(v_b_4287_);
lean_inc(v_a_4286_);
v___x_4288_ = lean_apply_2(v_inst_4279_, v_a_4286_, v_b_4287_);
v___x_4289_ = lean_unbox(v___x_4288_);
if (v___x_4289_ == 0)
{
uint8_t v___x_4290_; 
lean_dec(v_i_4282_);
lean_dec_ref(v_inst_4279_);
v___x_4290_ = lean_unbox(v___x_4288_);
return v___x_4290_;
}
else
{
lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4291_ = lean_unsigned_to_nat(1u);
v___x_4292_ = lean_nat_add(v_i_4282_, v___x_4291_);
lean_dec(v_i_4282_);
v_i_4282_ = v___x_4292_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___redArg___boxed(lean_object* v_inst_4294_, lean_object* v_as_4295_, lean_object* v_bs_4296_, lean_object* v_i_4297_){
_start:
{
uint8_t v_res_4298_; lean_object* v_r_4299_; 
v_res_4298_ = l_Array_isPrefixOfAux___redArg(v_inst_4294_, v_as_4295_, v_bs_4296_, v_i_4297_);
lean_dec_ref(v_bs_4296_);
lean_dec_ref(v_as_4295_);
v_r_4299_ = lean_box(v_res_4298_);
return v_r_4299_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux(lean_object* v_00_u03b1_4300_, lean_object* v_inst_4301_, lean_object* v_as_4302_, lean_object* v_bs_4303_, lean_object* v_hle_4304_, lean_object* v_i_4305_){
_start:
{
uint8_t v___x_4306_; 
v___x_4306_ = l_Array_isPrefixOfAux___redArg(v_inst_4301_, v_as_4302_, v_bs_4303_, v_i_4305_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___boxed(lean_object* v_00_u03b1_4307_, lean_object* v_inst_4308_, lean_object* v_as_4309_, lean_object* v_bs_4310_, lean_object* v_hle_4311_, lean_object* v_i_4312_){
_start:
{
uint8_t v_res_4313_; lean_object* v_r_4314_; 
v_res_4313_ = l_Array_isPrefixOfAux(v_00_u03b1_4307_, v_inst_4308_, v_as_4309_, v_bs_4310_, v_hle_4311_, v_i_4312_);
lean_dec_ref(v_bs_4310_);
lean_dec_ref(v_as_4309_);
v_r_4314_ = lean_box(v_res_4313_);
return v_r_4314_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf___redArg(lean_object* v_inst_4315_, lean_object* v_as_4316_, lean_object* v_bs_4317_){
_start:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; uint8_t v___x_4320_; 
v___x_4318_ = lean_array_get_size(v_as_4316_);
v___x_4319_ = lean_array_get_size(v_bs_4317_);
v___x_4320_ = lean_nat_dec_le(v___x_4318_, v___x_4319_);
if (v___x_4320_ == 0)
{
lean_dec_ref(v_inst_4315_);
return v___x_4320_;
}
else
{
lean_object* v___x_4321_; uint8_t v___x_4322_; 
v___x_4321_ = lean_unsigned_to_nat(0u);
v___x_4322_ = l_Array_isPrefixOfAux___redArg(v_inst_4315_, v_as_4316_, v_bs_4317_, v___x_4321_);
return v___x_4322_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___redArg___boxed(lean_object* v_inst_4323_, lean_object* v_as_4324_, lean_object* v_bs_4325_){
_start:
{
uint8_t v_res_4326_; lean_object* v_r_4327_; 
v_res_4326_ = l_Array_isPrefixOf___redArg(v_inst_4323_, v_as_4324_, v_bs_4325_);
lean_dec_ref(v_bs_4325_);
lean_dec_ref(v_as_4324_);
v_r_4327_ = lean_box(v_res_4326_);
return v_r_4327_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf(lean_object* v_00_u03b1_4328_, lean_object* v_inst_4329_, lean_object* v_as_4330_, lean_object* v_bs_4331_){
_start:
{
uint8_t v___x_4332_; 
v___x_4332_ = l_Array_isPrefixOf___redArg(v_inst_4329_, v_as_4330_, v_bs_4331_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___boxed(lean_object* v_00_u03b1_4333_, lean_object* v_inst_4334_, lean_object* v_as_4335_, lean_object* v_bs_4336_){
_start:
{
uint8_t v_res_4337_; lean_object* v_r_4338_; 
v_res_4337_ = l_Array_isPrefixOf(v_00_u03b1_4333_, v_inst_4334_, v_as_4335_, v_bs_4336_);
lean_dec_ref(v_bs_4336_);
lean_dec_ref(v_as_4335_);
v_r_4338_ = lean_box(v_res_4337_);
return v_r_4338_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0___boxed(lean_object* v_i_4339_, lean_object* v_cs_4340_, lean_object* v_inst_4341_, lean_object* v_as_4342_, lean_object* v_bs_4343_, lean_object* v_f_4344_, lean_object* v_____do__lift_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_Array_zipWithMAux___redArg___lam__0(v_i_4339_, v_cs_4340_, v_inst_4341_, v_as_4342_, v_bs_4343_, v_f_4344_, v_____do__lift_4345_);
lean_dec(v_i_4339_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg(lean_object* v_inst_4347_, lean_object* v_as_4348_, lean_object* v_bs_4349_, lean_object* v_f_4350_, lean_object* v_i_4351_, lean_object* v_cs_4352_){
_start:
{
lean_object* v___x_4353_; uint8_t v___x_4354_; 
v___x_4353_ = lean_array_get_size(v_as_4348_);
v___x_4354_ = lean_nat_dec_lt(v_i_4351_, v___x_4353_);
if (v___x_4354_ == 0)
{
lean_object* v_toApplicative_4355_; lean_object* v_toPure_4356_; lean_object* v___x_4357_; 
lean_dec(v_i_4351_);
lean_dec(v_f_4350_);
lean_dec_ref(v_bs_4349_);
lean_dec_ref(v_as_4348_);
v_toApplicative_4355_ = lean_ctor_get(v_inst_4347_, 0);
lean_inc_ref(v_toApplicative_4355_);
lean_dec_ref(v_inst_4347_);
v_toPure_4356_ = lean_ctor_get(v_toApplicative_4355_, 1);
lean_inc(v_toPure_4356_);
lean_dec_ref(v_toApplicative_4355_);
v___x_4357_ = lean_apply_2(v_toPure_4356_, lean_box(0), v_cs_4352_);
return v___x_4357_;
}
else
{
lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4358_ = lean_array_get_size(v_bs_4349_);
v___x_4359_ = lean_nat_dec_lt(v_i_4351_, v___x_4358_);
if (v___x_4359_ == 0)
{
lean_object* v_toApplicative_4360_; lean_object* v_toPure_4361_; lean_object* v___x_4362_; 
lean_dec(v_i_4351_);
lean_dec(v_f_4350_);
lean_dec_ref(v_bs_4349_);
lean_dec_ref(v_as_4348_);
v_toApplicative_4360_ = lean_ctor_get(v_inst_4347_, 0);
lean_inc_ref(v_toApplicative_4360_);
lean_dec_ref(v_inst_4347_);
v_toPure_4361_ = lean_ctor_get(v_toApplicative_4360_, 1);
lean_inc(v_toPure_4361_);
lean_dec_ref(v_toApplicative_4360_);
v___x_4362_ = lean_apply_2(v_toPure_4361_, lean_box(0), v_cs_4352_);
return v___x_4362_;
}
else
{
lean_object* v_toBind_4363_; lean_object* v___f_4364_; lean_object* v_a_4365_; lean_object* v_b_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v_toBind_4363_ = lean_ctor_get(v_inst_4347_, 1);
lean_inc(v_toBind_4363_);
lean_inc(v_f_4350_);
lean_inc_ref(v_bs_4349_);
lean_inc_ref(v_as_4348_);
lean_inc(v_i_4351_);
v___f_4364_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4364_, 0, v_i_4351_);
lean_closure_set(v___f_4364_, 1, v_cs_4352_);
lean_closure_set(v___f_4364_, 2, v_inst_4347_);
lean_closure_set(v___f_4364_, 3, v_as_4348_);
lean_closure_set(v___f_4364_, 4, v_bs_4349_);
lean_closure_set(v___f_4364_, 5, v_f_4350_);
v_a_4365_ = lean_array_fget(v_as_4348_, v_i_4351_);
lean_dec_ref(v_as_4348_);
v_b_4366_ = lean_array_fget(v_bs_4349_, v_i_4351_);
lean_dec(v_i_4351_);
lean_dec_ref(v_bs_4349_);
v___x_4367_ = lean_apply_2(v_f_4350_, v_a_4365_, v_b_4366_);
v___x_4368_ = lean_apply_4(v_toBind_4363_, lean_box(0), lean_box(0), v___x_4367_, v___f_4364_);
return v___x_4368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0(lean_object* v_i_4369_, lean_object* v_cs_4370_, lean_object* v_inst_4371_, lean_object* v_as_4372_, lean_object* v_bs_4373_, lean_object* v_f_4374_, lean_object* v_____do__lift_4375_){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4376_ = lean_unsigned_to_nat(1u);
v___x_4377_ = lean_nat_add(v_i_4369_, v___x_4376_);
v___x_4378_ = lean_array_push(v_cs_4370_, v_____do__lift_4375_);
v___x_4379_ = l_Array_zipWithMAux___redArg(v_inst_4371_, v_as_4372_, v_bs_4373_, v_f_4374_, v___x_4377_, v___x_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux(lean_object* v_00_u03b1_4380_, lean_object* v_00_u03b2_4381_, lean_object* v_00_u03b3_4382_, lean_object* v_m_4383_, lean_object* v_inst_4384_, lean_object* v_as_4385_, lean_object* v_bs_4386_, lean_object* v_f_4387_, lean_object* v_i_4388_, lean_object* v_cs_4389_){
_start:
{
lean_object* v___x_4390_; 
v___x_4390_ = l_Array_zipWithMAux___redArg(v_inst_4384_, v_as_4385_, v_bs_4386_, v_f_4387_, v_i_4388_, v_cs_4389_);
return v___x_4390_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith___redArg(lean_object* v_f_4391_, lean_object* v_as_4392_, lean_object* v_bs_4393_){
_start:
{
lean_object* v___f_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___f_4394_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4394_, 0, v_f_4391_);
v___x_4395_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4396_ = lean_unsigned_to_nat(0u);
v___x_4397_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4398_ = l_Array_zipWithMAux___redArg(v___x_4395_, v_as_4392_, v_bs_4393_, v___f_4394_, v___x_4396_, v___x_4397_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith(lean_object* v_00_u03b1_4399_, lean_object* v_00_u03b2_4400_, lean_object* v_00_u03b3_4401_, lean_object* v_f_4402_, lean_object* v_as_4403_, lean_object* v_bs_4404_){
_start:
{
lean_object* v___f_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___f_4405_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4405_, 0, v_f_4402_);
v___x_4406_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4407_ = lean_unsigned_to_nat(0u);
v___x_4408_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4409_ = l_Array_zipWithMAux___redArg(v___x_4406_, v_as_4403_, v_bs_4404_, v___f_4405_, v___x_4407_, v___x_4408_);
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(lean_object* v_as_4410_, lean_object* v_bs_4411_, lean_object* v_i_4412_, lean_object* v_cs_4413_){
_start:
{
lean_object* v___x_4414_; uint8_t v___x_4415_; 
v___x_4414_ = lean_array_get_size(v_as_4410_);
v___x_4415_ = lean_nat_dec_lt(v_i_4412_, v___x_4414_);
if (v___x_4415_ == 0)
{
lean_dec(v_i_4412_);
return v_cs_4413_;
}
else
{
lean_object* v___x_4416_; uint8_t v___x_4417_; 
v___x_4416_ = lean_array_get_size(v_bs_4411_);
v___x_4417_ = lean_nat_dec_lt(v_i_4412_, v___x_4416_);
if (v___x_4417_ == 0)
{
lean_dec(v_i_4412_);
return v_cs_4413_;
}
else
{
lean_object* v_a_4418_; lean_object* v_b_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v_a_4418_ = lean_array_fget_borrowed(v_as_4410_, v_i_4412_);
v_b_4419_ = lean_array_fget_borrowed(v_bs_4411_, v_i_4412_);
lean_inc(v_b_4419_);
lean_inc(v_a_4418_);
v___x_4420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4420_, 0, v_a_4418_);
lean_ctor_set(v___x_4420_, 1, v_b_4419_);
v___x_4421_ = lean_unsigned_to_nat(1u);
v___x_4422_ = lean_nat_add(v_i_4412_, v___x_4421_);
lean_dec(v_i_4412_);
v___x_4423_ = lean_array_push(v_cs_4413_, v___x_4420_);
v_i_4412_ = v___x_4422_;
v_cs_4413_ = v___x_4423_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg___boxed(lean_object* v_as_4425_, lean_object* v_bs_4426_, lean_object* v_i_4427_, lean_object* v_cs_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4425_, v_bs_4426_, v_i_4427_, v_cs_4428_);
lean_dec_ref(v_bs_4426_);
lean_dec_ref(v_as_4425_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg(lean_object* v_as_4432_, lean_object* v_bs_4433_){
_start:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4434_ = lean_unsigned_to_nat(0u);
v___x_4435_ = ((lean_object*)(l_Array_zip___redArg___closed__0));
v___x_4436_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4432_, v_bs_4433_, v___x_4434_, v___x_4435_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg___boxed(lean_object* v_as_4437_, lean_object* v_bs_4438_){
_start:
{
lean_object* v_res_4439_; 
v_res_4439_ = l_Array_zip___redArg(v_as_4437_, v_bs_4438_);
lean_dec_ref(v_bs_4438_);
lean_dec_ref(v_as_4437_);
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l_Array_zip(lean_object* v_00_u03b1_4440_, lean_object* v_00_u03b2_4441_, lean_object* v_as_4442_, lean_object* v_bs_4443_){
_start:
{
lean_object* v___x_4444_; 
v___x_4444_ = l_Array_zip___redArg(v_as_4442_, v_bs_4443_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___boxed(lean_object* v_00_u03b1_4445_, lean_object* v_00_u03b2_4446_, lean_object* v_as_4447_, lean_object* v_bs_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l_Array_zip(v_00_u03b1_4445_, v_00_u03b2_4446_, v_as_4447_, v_bs_4448_);
lean_dec_ref(v_bs_4448_);
lean_dec_ref(v_as_4447_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0(lean_object* v_00_u03b1_4450_, lean_object* v_00_u03b2_4451_, lean_object* v_as_4452_, lean_object* v_bs_4453_, lean_object* v_i_4454_, lean_object* v_cs_4455_){
_start:
{
lean_object* v___x_4456_; 
v___x_4456_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4452_, v_bs_4453_, v_i_4454_, v_cs_4455_);
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___boxed(lean_object* v_00_u03b1_4457_, lean_object* v_00_u03b2_4458_, lean_object* v_as_4459_, lean_object* v_bs_4460_, lean_object* v_i_4461_, lean_object* v_cs_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_Array_zipWithMAux___at___00Array_zip_spec__0(v_00_u03b1_4457_, v_00_u03b2_4458_, v_as_4459_, v_bs_4460_, v_i_4461_, v_cs_4462_);
lean_dec_ref(v_bs_4460_);
lean_dec_ref(v_as_4459_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(lean_object* v_f_4464_, lean_object* v_as_4465_, lean_object* v_bs_4466_, lean_object* v_i_4467_, lean_object* v_cs_4468_){
_start:
{
lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4478_; lean_object* v___y_4485_; lean_object* v___x_4492_; lean_object* v___x_4493_; uint8_t v___x_4494_; 
v___x_4492_ = lean_array_get_size(v_as_4465_);
v___x_4493_ = lean_array_get_size(v_bs_4466_);
v___x_4494_ = lean_nat_dec_le(v___x_4492_, v___x_4493_);
if (v___x_4494_ == 0)
{
v___y_4485_ = v___x_4492_;
goto v___jp_4484_;
}
else
{
v___y_4485_ = v___x_4493_;
goto v___jp_4484_;
}
v___jp_4469_:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4472_ = lean_unsigned_to_nat(1u);
v___x_4473_ = lean_nat_add(v_i_4467_, v___x_4472_);
lean_dec(v_i_4467_);
lean_inc(v_f_4464_);
v___x_4474_ = lean_apply_2(v_f_4464_, v___y_4470_, v___y_4471_);
v___x_4475_ = lean_array_push(v_cs_4468_, v___x_4474_);
v_i_4467_ = v___x_4473_;
v_cs_4468_ = v___x_4475_;
goto _start;
}
v___jp_4477_:
{
lean_object* v___x_4479_; uint8_t v___x_4480_; 
v___x_4479_ = lean_array_get_size(v_bs_4466_);
v___x_4480_ = lean_nat_dec_lt(v_i_4467_, v___x_4479_);
if (v___x_4480_ == 0)
{
lean_object* v___x_4481_; 
v___x_4481_ = lean_box(0);
v___y_4470_ = v___y_4478_;
v___y_4471_ = v___x_4481_;
goto v___jp_4469_;
}
else
{
lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4482_ = lean_array_fget_borrowed(v_bs_4466_, v_i_4467_);
lean_inc(v___x_4482_);
v___x_4483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4482_);
v___y_4470_ = v___y_4478_;
v___y_4471_ = v___x_4483_;
goto v___jp_4469_;
}
}
v___jp_4484_:
{
uint8_t v___x_4486_; 
v___x_4486_ = lean_nat_dec_lt(v_i_4467_, v___y_4485_);
lean_dec(v___y_4485_);
if (v___x_4486_ == 0)
{
lean_dec(v_i_4467_);
lean_dec(v_f_4464_);
return v_cs_4468_;
}
else
{
lean_object* v___x_4487_; uint8_t v___x_4488_; 
v___x_4487_ = lean_array_get_size(v_as_4465_);
v___x_4488_ = lean_nat_dec_lt(v_i_4467_, v___x_4487_);
if (v___x_4488_ == 0)
{
lean_object* v___x_4489_; 
v___x_4489_ = lean_box(0);
v___y_4478_ = v___x_4489_;
goto v___jp_4477_;
}
else
{
lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4490_ = lean_array_fget_borrowed(v_as_4465_, v_i_4467_);
lean_inc(v___x_4490_);
v___x_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4490_);
v___y_4478_ = v___x_4491_;
goto v___jp_4477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg___boxed(lean_object* v_f_4495_, lean_object* v_as_4496_, lean_object* v_bs_4497_, lean_object* v_i_4498_, lean_object* v_cs_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4495_, v_as_4496_, v_bs_4497_, v_i_4498_, v_cs_4499_);
lean_dec_ref(v_bs_4497_);
lean_dec_ref(v_as_4496_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(lean_object* v_00_u03b1_4501_, lean_object* v_00_u03b2_4502_, lean_object* v_00_u03b3_4503_, lean_object* v_f_4504_, lean_object* v_as_4505_, lean_object* v_bs_4506_, lean_object* v_i_4507_, lean_object* v_cs_4508_){
_start:
{
lean_object* v___x_4509_; 
v___x_4509_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4504_, v_as_4505_, v_bs_4506_, v_i_4507_, v_cs_4508_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___boxed(lean_object* v_00_u03b1_4510_, lean_object* v_00_u03b2_4511_, lean_object* v_00_u03b3_4512_, lean_object* v_f_4513_, lean_object* v_as_4514_, lean_object* v_bs_4515_, lean_object* v_i_4516_, lean_object* v_cs_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(v_00_u03b1_4510_, v_00_u03b2_4511_, v_00_u03b3_4512_, v_f_4513_, v_as_4514_, v_bs_4515_, v_i_4516_, v_cs_4517_);
lean_dec_ref(v_bs_4515_);
lean_dec_ref(v_as_4514_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg(lean_object* v_f_4519_, lean_object* v_as_4520_, lean_object* v_bs_4521_){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4522_ = lean_unsigned_to_nat(0u);
v___x_4523_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4524_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4519_, v_as_4520_, v_bs_4521_, v___x_4522_, v___x_4523_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg___boxed(lean_object* v_f_4525_, lean_object* v_as_4526_, lean_object* v_bs_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l_Array_zipWithAll___redArg(v_f_4525_, v_as_4526_, v_bs_4527_);
lean_dec_ref(v_bs_4527_);
lean_dec_ref(v_as_4526_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll(lean_object* v_00_u03b1_4529_, lean_object* v_00_u03b2_4530_, lean_object* v_00_u03b3_4531_, lean_object* v_f_4532_, lean_object* v_as_4533_, lean_object* v_bs_4534_){
_start:
{
lean_object* v___x_4535_; 
v___x_4535_ = l_Array_zipWithAll___redArg(v_f_4532_, v_as_4533_, v_bs_4534_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___boxed(lean_object* v_00_u03b1_4536_, lean_object* v_00_u03b2_4537_, lean_object* v_00_u03b3_4538_, lean_object* v_f_4539_, lean_object* v_as_4540_, lean_object* v_bs_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Array_zipWithAll(v_00_u03b1_4536_, v_00_u03b2_4537_, v_00_u03b3_4538_, v_f_4539_, v_as_4540_, v_bs_4541_);
lean_dec_ref(v_bs_4541_);
lean_dec_ref(v_as_4540_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM___redArg(lean_object* v_inst_4543_, lean_object* v_f_4544_, lean_object* v_as_4545_, lean_object* v_bs_4546_){
_start:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4547_ = lean_unsigned_to_nat(0u);
v___x_4548_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4549_ = l_Array_zipWithMAux___redArg(v_inst_4543_, v_as_4545_, v_bs_4546_, v_f_4544_, v___x_4547_, v___x_4548_);
return v___x_4549_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM(lean_object* v_00_u03b1_4550_, lean_object* v_00_u03b2_4551_, lean_object* v_00_u03b3_4552_, lean_object* v_m_4553_, lean_object* v_inst_4554_, lean_object* v_f_4555_, lean_object* v_as_4556_, lean_object* v_bs_4557_){
_start:
{
lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4558_ = lean_unsigned_to_nat(0u);
v___x_4559_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4560_ = l_Array_zipWithMAux___redArg(v_inst_4554_, v_as_4556_, v_bs_4557_, v_f_4555_, v___x_4558_, v___x_4559_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(lean_object* v_as_4561_, size_t v_i_4562_, size_t v_stop_4563_, lean_object* v_b_4564_){
_start:
{
uint8_t v___x_4565_; 
v___x_4565_ = lean_usize_dec_eq(v_i_4562_, v_stop_4563_);
if (v___x_4565_ == 0)
{
lean_object* v_fst_4566_; lean_object* v_snd_4567_; lean_object* v___x_4568_; lean_object* v_fst_4569_; lean_object* v_snd_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4582_; 
v_fst_4566_ = lean_ctor_get(v_b_4564_, 0);
lean_inc(v_fst_4566_);
v_snd_4567_ = lean_ctor_get(v_b_4564_, 1);
lean_inc(v_snd_4567_);
lean_dec_ref(v_b_4564_);
v___x_4568_ = lean_array_uget(v_as_4561_, v_i_4562_);
v_fst_4569_ = lean_ctor_get(v___x_4568_, 0);
v_snd_4570_ = lean_ctor_get(v___x_4568_, 1);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4568_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4572_ = v___x_4568_;
v_isShared_4573_ = v_isSharedCheck_4582_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_snd_4570_);
lean_inc(v_fst_4569_);
lean_dec(v___x_4568_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4582_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4577_; 
v___x_4574_ = lean_array_push(v_fst_4566_, v_fst_4569_);
v___x_4575_ = lean_array_push(v_snd_4567_, v_snd_4570_);
if (v_isShared_4573_ == 0)
{
lean_ctor_set(v___x_4572_, 1, v___x_4575_);
lean_ctor_set(v___x_4572_, 0, v___x_4574_);
v___x_4577_ = v___x_4572_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4574_);
lean_ctor_set(v_reuseFailAlloc_4581_, 1, v___x_4575_);
v___x_4577_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
size_t v___x_4578_; size_t v___x_4579_; 
v___x_4578_ = ((size_t)1ULL);
v___x_4579_ = lean_usize_add(v_i_4562_, v___x_4578_);
v_i_4562_ = v___x_4579_;
v_b_4564_ = v___x_4577_;
goto _start;
}
}
}
else
{
return v_b_4564_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg___boxed(lean_object* v_as_4583_, lean_object* v_i_4584_, lean_object* v_stop_4585_, lean_object* v_b_4586_){
_start:
{
size_t v_i_boxed_4587_; size_t v_stop_boxed_4588_; lean_object* v_res_4589_; 
v_i_boxed_4587_ = lean_unbox_usize(v_i_4584_);
lean_dec(v_i_4584_);
v_stop_boxed_4588_ = lean_unbox_usize(v_stop_4585_);
lean_dec(v_stop_4585_);
v_res_4589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4583_, v_i_boxed_4587_, v_stop_boxed_4588_, v_b_4586_);
lean_dec_ref(v_as_4583_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg(lean_object* v_as_4590_){
_start:
{
lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; uint8_t v___x_4594_; 
v___x_4591_ = lean_unsigned_to_nat(0u);
v___x_4592_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v___x_4593_ = lean_array_get_size(v_as_4590_);
v___x_4594_ = lean_nat_dec_lt(v___x_4591_, v___x_4593_);
if (v___x_4594_ == 0)
{
return v___x_4592_;
}
else
{
uint8_t v___x_4595_; 
v___x_4595_ = lean_nat_dec_le(v___x_4593_, v___x_4593_);
if (v___x_4595_ == 0)
{
if (v___x_4594_ == 0)
{
return v___x_4592_;
}
else
{
size_t v___x_4596_; size_t v___x_4597_; lean_object* v___x_4598_; 
v___x_4596_ = ((size_t)0ULL);
v___x_4597_ = lean_usize_of_nat(v___x_4593_);
v___x_4598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4590_, v___x_4596_, v___x_4597_, v___x_4592_);
return v___x_4598_;
}
}
else
{
size_t v___x_4599_; size_t v___x_4600_; lean_object* v___x_4601_; 
v___x_4599_ = ((size_t)0ULL);
v___x_4600_ = lean_usize_of_nat(v___x_4593_);
v___x_4601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4590_, v___x_4599_, v___x_4600_, v___x_4592_);
return v___x_4601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg___boxed(lean_object* v_as_4602_){
_start:
{
lean_object* v_res_4603_; 
v_res_4603_ = l_Array_unzip___redArg(v_as_4602_);
lean_dec_ref(v_as_4602_);
return v_res_4603_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip(lean_object* v_00_u03b1_4604_, lean_object* v_00_u03b2_4605_, lean_object* v_as_4606_){
_start:
{
lean_object* v___x_4607_; 
v___x_4607_ = l_Array_unzip___redArg(v_as_4606_);
return v___x_4607_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___boxed(lean_object* v_00_u03b1_4608_, lean_object* v_00_u03b2_4609_, lean_object* v_as_4610_){
_start:
{
lean_object* v_res_4611_; 
v_res_4611_ = l_Array_unzip(v_00_u03b1_4608_, v_00_u03b2_4609_, v_as_4610_);
lean_dec_ref(v_as_4610_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(lean_object* v_00_u03b1_4612_, lean_object* v_00_u03b2_4613_, lean_object* v_as_4614_, size_t v_i_4615_, size_t v_stop_4616_, lean_object* v_b_4617_){
_start:
{
lean_object* v___x_4618_; 
v___x_4618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4614_, v_i_4615_, v_stop_4616_, v_b_4617_);
return v___x_4618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___boxed(lean_object* v_00_u03b1_4619_, lean_object* v_00_u03b2_4620_, lean_object* v_as_4621_, lean_object* v_i_4622_, lean_object* v_stop_4623_, lean_object* v_b_4624_){
_start:
{
size_t v_i_boxed_4625_; size_t v_stop_boxed_4626_; lean_object* v_res_4627_; 
v_i_boxed_4625_ = lean_unbox_usize(v_i_4622_);
lean_dec(v_i_4622_);
v_stop_boxed_4626_ = lean_unbox_usize(v_stop_4623_);
lean_dec(v_stop_4623_);
v_res_4627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(v_00_u03b1_4619_, v_00_u03b2_4620_, v_as_4621_, v_i_boxed_4625_, v_stop_boxed_4626_, v_b_4624_);
lean_dec_ref(v_as_4621_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l_Array_replace___redArg(lean_object* v_inst_4628_, lean_object* v_xs_4629_, lean_object* v_a_4630_, lean_object* v_b_4631_){
_start:
{
lean_object* v___x_4632_; 
v___x_4632_ = l_Array_finIdxOf_x3f___redArg(v_inst_4628_, v_xs_4629_, v_a_4630_);
if (lean_obj_tag(v___x_4632_) == 0)
{
lean_dec(v_b_4631_);
return v_xs_4629_;
}
else
{
lean_object* v_val_4633_; lean_object* v___x_4634_; 
v_val_4633_ = lean_ctor_get(v___x_4632_, 0);
lean_inc(v_val_4633_);
lean_dec_ref_known(v___x_4632_, 1);
v___x_4634_ = lean_array_fset(v_xs_4629_, v_val_4633_, v_b_4631_);
lean_dec(v_val_4633_);
return v___x_4634_;
}
}
}
LEAN_EXPORT lean_object* l_Array_replace(lean_object* v_00_u03b1_4635_, lean_object* v_inst_4636_, lean_object* v_xs_4637_, lean_object* v_a_4638_, lean_object* v_b_4639_){
_start:
{
lean_object* v___x_4640_; 
v___x_4640_ = l_Array_replace___redArg(v_inst_4636_, v_xs_4637_, v_a_4638_, v_b_4639_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l_Array_instLT(lean_object* v_00_u03b1_4641_, lean_object* v_inst_4642_){
_start:
{
lean_object* v___x_4643_; 
v___x_4643_ = lean_box(0);
return v___x_4643_;
}
}
LEAN_EXPORT lean_object* l_Array_instLE(lean_object* v_00_u03b1_4644_, lean_object* v_inst_4645_){
_start:
{
lean_object* v___x_4646_; 
v___x_4646_ = lean_box(0);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg(lean_object* v_n_4647_, lean_object* v_a_4648_, lean_object* v_xs_4649_){
_start:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4650_ = lean_array_get_size(v_xs_4649_);
v___x_4651_ = lean_nat_sub(v_n_4647_, v___x_4650_);
v___x_4652_ = lean_mk_array(v___x_4651_, v_a_4648_);
v___x_4653_ = l_Array_append___redArg(v___x_4652_, v_xs_4649_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg___boxed(lean_object* v_n_4654_, lean_object* v_a_4655_, lean_object* v_xs_4656_){
_start:
{
lean_object* v_res_4657_; 
v_res_4657_ = l_Array_leftpad___redArg(v_n_4654_, v_a_4655_, v_xs_4656_);
lean_dec_ref(v_xs_4656_);
lean_dec(v_n_4654_);
return v_res_4657_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad(lean_object* v_00_u03b1_4658_, lean_object* v_n_4659_, lean_object* v_a_4660_, lean_object* v_xs_4661_){
_start:
{
lean_object* v___x_4662_; 
v___x_4662_ = l_Array_leftpad___redArg(v_n_4659_, v_a_4660_, v_xs_4661_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___boxed(lean_object* v_00_u03b1_4663_, lean_object* v_n_4664_, lean_object* v_a_4665_, lean_object* v_xs_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l_Array_leftpad(v_00_u03b1_4663_, v_n_4664_, v_a_4665_, v_xs_4666_);
lean_dec_ref(v_xs_4666_);
lean_dec(v_n_4664_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg(lean_object* v_n_4668_, lean_object* v_a_4669_, lean_object* v_xs_4670_){
_start:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4671_ = lean_array_get_size(v_xs_4670_);
v___x_4672_ = lean_nat_sub(v_n_4668_, v___x_4671_);
v___x_4673_ = lean_mk_array(v___x_4672_, v_a_4669_);
v___x_4674_ = l_Array_append___redArg(v_xs_4670_, v___x_4673_);
lean_dec_ref(v___x_4673_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg___boxed(lean_object* v_n_4675_, lean_object* v_a_4676_, lean_object* v_xs_4677_){
_start:
{
lean_object* v_res_4678_; 
v_res_4678_ = l_Array_rightpad___redArg(v_n_4675_, v_a_4676_, v_xs_4677_);
lean_dec(v_n_4675_);
return v_res_4678_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad(lean_object* v_00_u03b1_4679_, lean_object* v_n_4680_, lean_object* v_a_4681_, lean_object* v_xs_4682_){
_start:
{
lean_object* v___x_4683_; 
v___x_4683_ = l_Array_rightpad___redArg(v_n_4680_, v_a_4681_, v_xs_4682_);
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___boxed(lean_object* v_00_u03b1_4684_, lean_object* v_n_4685_, lean_object* v_a_4686_, lean_object* v_xs_4687_){
_start:
{
lean_object* v_res_4688_; 
v_res_4688_ = l_Array_rightpad(v_00_u03b1_4684_, v_n_4685_, v_a_4686_, v_xs_4687_);
lean_dec(v_n_4685_);
return v_res_4688_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0(lean_object* v_x_4689_){
_start:
{
lean_inc(v_x_4689_);
return v_x_4689_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0___boxed(lean_object* v_x_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l_Array_reduceOption___redArg___lam__0(v_x_4690_);
lean_dec(v_x_4690_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg(lean_object* v_as_4693_){
_start:
{
lean_object* v___f_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___f_4694_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4695_ = lean_unsigned_to_nat(0u);
v___x_4696_ = lean_array_get_size(v_as_4693_);
v___x_4697_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4698_ = l_Array_filterMapM___redArg(v___x_4697_, v___f_4694_, v_as_4693_, v___x_4695_, v___x_4696_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption(lean_object* v_00_u03b1_4699_, lean_object* v_as_4700_){
_start:
{
lean_object* v___f_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___f_4701_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4702_ = lean_unsigned_to_nat(0u);
v___x_4703_ = lean_array_get_size(v_as_4700_);
v___x_4704_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4705_ = l_Array_filterMapM___redArg(v___x_4704_, v___f_4701_, v_as_4700_, v___x_4702_, v___x_4703_);
return v___x_4705_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg___lam__0(lean_object* v_inst_4706_, lean_object* v_x1_4707_, lean_object* v_x2_4708_){
_start:
{
lean_object* v_fst_4709_; lean_object* v_snd_4710_; lean_object* v___x_4711_; uint8_t v___x_4712_; 
v_fst_4709_ = lean_ctor_get(v_x1_4707_, 0);
v_snd_4710_ = lean_ctor_get(v_x1_4707_, 1);
lean_inc(v_fst_4709_);
lean_inc(v_x2_4708_);
v___x_4711_ = lean_apply_2(v_inst_4706_, v_x2_4708_, v_fst_4709_);
v___x_4712_ = lean_unbox(v___x_4711_);
if (v___x_4712_ == 0)
{
lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4720_; 
lean_inc(v_snd_4710_);
lean_inc(v_fst_4709_);
v_isSharedCheck_4720_ = !lean_is_exclusive(v_x1_4707_);
if (v_isSharedCheck_4720_ == 0)
{
lean_object* v_unused_4721_; lean_object* v_unused_4722_; 
v_unused_4721_ = lean_ctor_get(v_x1_4707_, 1);
lean_dec(v_unused_4721_);
v_unused_4722_ = lean_ctor_get(v_x1_4707_, 0);
lean_dec(v_unused_4722_);
v___x_4714_ = v_x1_4707_;
v_isShared_4715_ = v_isSharedCheck_4720_;
goto v_resetjp_4713_;
}
else
{
lean_dec(v_x1_4707_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4720_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4716_; lean_object* v___x_4718_; 
v___x_4716_ = lean_array_push(v_snd_4710_, v_fst_4709_);
if (v_isShared_4715_ == 0)
{
lean_ctor_set(v___x_4714_, 1, v___x_4716_);
lean_ctor_set(v___x_4714_, 0, v_x2_4708_);
v___x_4718_ = v___x_4714_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_x2_4708_);
lean_ctor_set(v_reuseFailAlloc_4719_, 1, v___x_4716_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
else
{
lean_dec(v_x2_4708_);
return v_x1_4707_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg(lean_object* v_inst_4723_, lean_object* v_as_4724_){
_start:
{
lean_object* v___y_4726_; lean_object* v___x_4730_; lean_object* v___x_4731_; uint8_t v___x_4732_; 
v___x_4730_ = lean_unsigned_to_nat(0u);
v___x_4731_ = lean_array_get_size(v_as_4724_);
v___x_4732_ = lean_nat_dec_lt(v___x_4730_, v___x_4731_);
if (v___x_4732_ == 0)
{
lean_object* v___x_4733_; 
lean_dec_ref(v_as_4724_);
lean_dec_ref(v_inst_4723_);
v___x_4733_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
return v___x_4733_;
}
else
{
lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; 
v___x_4734_ = lean_array_fget_borrowed(v_as_4724_, v___x_4730_);
v___x_4735_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4736_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
if (v___x_4732_ == 0)
{
lean_object* v___x_4737_; 
lean_inc(v___x_4734_);
lean_dec_ref(v_as_4724_);
lean_dec_ref(v_inst_4723_);
v___x_4737_ = lean_array_push(v___x_4735_, v___x_4734_);
return v___x_4737_;
}
else
{
lean_object* v___f_4738_; lean_object* v___x_4739_; uint8_t v___x_4740_; 
v___f_4738_ = lean_alloc_closure((void*)(l_Array_eraseReps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4738_, 0, v_inst_4723_);
lean_inc(v___x_4734_);
v___x_4739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4739_, 0, v___x_4734_);
lean_ctor_set(v___x_4739_, 1, v___x_4735_);
v___x_4740_ = lean_nat_dec_le(v___x_4731_, v___x_4731_);
if (v___x_4740_ == 0)
{
if (v___x_4732_ == 0)
{
lean_object* v___x_4741_; 
lean_inc(v___x_4734_);
lean_dec_ref_known(v___x_4739_, 2);
lean_dec_ref(v___f_4738_);
lean_dec_ref(v_as_4724_);
v___x_4741_ = lean_array_push(v___x_4735_, v___x_4734_);
return v___x_4741_;
}
else
{
size_t v___x_4742_; size_t v___x_4743_; lean_object* v___x_4744_; 
v___x_4742_ = ((size_t)0ULL);
v___x_4743_ = lean_usize_of_nat(v___x_4731_);
v___x_4744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4736_, v___f_4738_, v_as_4724_, v___x_4742_, v___x_4743_, v___x_4739_);
v___y_4726_ = v___x_4744_;
goto v___jp_4725_;
}
}
else
{
size_t v___x_4745_; size_t v___x_4746_; lean_object* v___x_4747_; 
v___x_4745_ = ((size_t)0ULL);
v___x_4746_ = lean_usize_of_nat(v___x_4731_);
v___x_4747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4736_, v___f_4738_, v_as_4724_, v___x_4745_, v___x_4746_, v___x_4739_);
v___y_4726_ = v___x_4747_;
goto v___jp_4725_;
}
}
}
v___jp_4725_:
{
lean_object* v_fst_4727_; lean_object* v_snd_4728_; lean_object* v___x_4729_; 
v_fst_4727_ = lean_ctor_get(v___y_4726_, 0);
lean_inc(v_fst_4727_);
v_snd_4728_ = lean_ctor_get(v___y_4726_, 1);
lean_inc(v_snd_4728_);
lean_dec_ref(v___y_4726_);
v___x_4729_ = lean_array_push(v_snd_4728_, v_fst_4727_);
return v___x_4729_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps(lean_object* v_00_u03b1_4748_, lean_object* v_inst_4749_, lean_object* v_as_4750_){
_start:
{
lean_object* v___x_4751_; 
v___x_4751_ = l_Array_eraseReps___redArg(v_inst_4749_, v_as_4750_);
return v___x_4751_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(lean_object* v_inst_4752_, lean_object* v_as_4753_, lean_object* v_a_4754_, lean_object* v_x_4755_){
_start:
{
lean_object* v_zero_4756_; uint8_t v_isZero_4757_; 
v_zero_4756_ = lean_unsigned_to_nat(0u);
v_isZero_4757_ = lean_nat_dec_eq(v_x_4755_, v_zero_4756_);
if (v_isZero_4757_ == 1)
{
lean_dec(v_x_4755_);
lean_dec(v_a_4754_);
lean_dec_ref(v_inst_4752_);
return v_isZero_4757_;
}
else
{
lean_object* v_one_4758_; lean_object* v_n_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; uint8_t v___x_4762_; uint8_t v___x_4763_; 
v_one_4758_ = lean_unsigned_to_nat(1u);
v_n_4759_ = lean_nat_sub(v_x_4755_, v_one_4758_);
lean_dec(v_x_4755_);
v___x_4760_ = lean_array_fget_borrowed(v_as_4753_, v_n_4759_);
lean_inc_ref(v_inst_4752_);
lean_inc(v___x_4760_);
lean_inc(v_a_4754_);
v___x_4761_ = lean_apply_2(v_inst_4752_, v_a_4754_, v___x_4760_);
v___x_4762_ = lean_unbox(v___x_4761_);
v___x_4763_ = lean_bool_not(v___x_4762_);
if (v___x_4763_ == 0)
{
lean_dec(v_n_4759_);
lean_dec(v_a_4754_);
lean_dec_ref(v_inst_4752_);
return v___x_4763_;
}
else
{
v_x_4755_ = v_n_4759_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg___boxed(lean_object* v_inst_4765_, lean_object* v_as_4766_, lean_object* v_a_4767_, lean_object* v_x_4768_){
_start:
{
uint8_t v_res_4769_; lean_object* v_r_4770_; 
v_res_4769_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4765_, v_as_4766_, v_a_4767_, v_x_4768_);
lean_dec_ref(v_as_4766_);
v_r_4770_ = lean_box(v_res_4769_);
return v_r_4770_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(lean_object* v_00_u03b1_4771_, lean_object* v_inst_4772_, lean_object* v_as_4773_, lean_object* v_a_4774_, lean_object* v_x_4775_, lean_object* v_x_4776_){
_start:
{
uint8_t v___x_4777_; 
v___x_4777_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4772_, v_as_4773_, v_a_4774_, v_x_4775_);
return v___x_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___boxed(lean_object* v_00_u03b1_4778_, lean_object* v_inst_4779_, lean_object* v_as_4780_, lean_object* v_a_4781_, lean_object* v_x_4782_, lean_object* v_x_4783_){
_start:
{
uint8_t v_res_4784_; lean_object* v_r_4785_; 
v_res_4784_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(v_00_u03b1_4778_, v_inst_4779_, v_as_4780_, v_a_4781_, v_x_4782_, v_x_4783_);
lean_dec_ref(v_as_4780_);
v_r_4785_ = lean_box(v_res_4784_);
return v_r_4785_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(lean_object* v_inst_4786_, lean_object* v_as_4787_, lean_object* v_i_4788_){
_start:
{
lean_object* v___x_4789_; uint8_t v___x_4790_; 
v___x_4789_ = lean_array_get_size(v_as_4787_);
v___x_4790_ = lean_nat_dec_lt(v_i_4788_, v___x_4789_);
if (v___x_4790_ == 0)
{
uint8_t v___x_4791_; 
lean_dec(v_i_4788_);
lean_dec_ref(v_inst_4786_);
v___x_4791_ = 1;
return v___x_4791_;
}
else
{
lean_object* v___x_4792_; uint8_t v___x_4793_; 
v___x_4792_ = lean_array_fget_borrowed(v_as_4787_, v_i_4788_);
lean_inc(v_i_4788_);
lean_inc(v___x_4792_);
lean_inc_ref(v_inst_4786_);
v___x_4793_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4786_, v_as_4787_, v___x_4792_, v_i_4788_);
if (v___x_4793_ == 0)
{
lean_dec(v_i_4788_);
lean_dec_ref(v_inst_4786_);
return v___x_4793_;
}
else
{
lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4794_ = lean_unsigned_to_nat(1u);
v___x_4795_ = lean_nat_add(v_i_4788_, v___x_4794_);
lean_dec(v_i_4788_);
v_i_4788_ = v___x_4795_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg___boxed(lean_object* v_inst_4797_, lean_object* v_as_4798_, lean_object* v_i_4799_){
_start:
{
uint8_t v_res_4800_; lean_object* v_r_4801_; 
v_res_4800_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4797_, v_as_4798_, v_i_4799_);
lean_dec_ref(v_as_4798_);
v_r_4801_ = lean_box(v_res_4800_);
return v_r_4801_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux(lean_object* v_00_u03b1_4802_, lean_object* v_inst_4803_, lean_object* v_as_4804_, lean_object* v_i_4805_){
_start:
{
uint8_t v___x_4806_; 
v___x_4806_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4803_, v_as_4804_, v_i_4805_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___boxed(lean_object* v_00_u03b1_4807_, lean_object* v_inst_4808_, lean_object* v_as_4809_, lean_object* v_i_4810_){
_start:
{
uint8_t v_res_4811_; lean_object* v_r_4812_; 
v_res_4811_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux(v_00_u03b1_4807_, v_inst_4808_, v_as_4809_, v_i_4810_);
lean_dec_ref(v_as_4809_);
v_r_4812_ = lean_box(v_res_4811_);
return v_r_4812_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___redArg(lean_object* v_inst_4813_, lean_object* v_as_4814_){
_start:
{
lean_object* v___x_4815_; uint8_t v___x_4816_; 
v___x_4815_ = lean_unsigned_to_nat(0u);
v___x_4816_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4813_, v_as_4814_, v___x_4815_);
return v___x_4816_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___redArg___boxed(lean_object* v_inst_4817_, lean_object* v_as_4818_){
_start:
{
uint8_t v_res_4819_; lean_object* v_r_4820_; 
v_res_4819_ = l_Array_allDiff___redArg(v_inst_4817_, v_as_4818_);
lean_dec_ref(v_as_4818_);
v_r_4820_ = lean_box(v_res_4819_);
return v_r_4820_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff(lean_object* v_00_u03b1_4821_, lean_object* v_inst_4822_, lean_object* v_as_4823_){
_start:
{
uint8_t v___x_4824_; 
v___x_4824_ = l_Array_allDiff___redArg(v_inst_4822_, v_as_4823_);
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___boxed(lean_object* v_00_u03b1_4825_, lean_object* v_inst_4826_, lean_object* v_as_4827_){
_start:
{
uint8_t v_res_4828_; lean_object* v_r_4829_; 
v_res_4828_ = l_Array_allDiff(v_00_u03b1_4825_, v_inst_4826_, v_as_4827_);
lean_dec_ref(v_as_4827_);
v_r_4829_ = lean_box(v_res_4828_);
return v_r_4829_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0(uint8_t v___x_4830_, lean_object* v_x1_4831_, lean_object* v_x2_4832_){
_start:
{
lean_object* v_fst_4833_; uint8_t v___x_4834_; 
v_fst_4833_ = lean_ctor_get(v_x1_4831_, 0);
v___x_4834_ = lean_unbox(v_fst_4833_);
if (v___x_4834_ == 0)
{
lean_object* v_snd_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4843_; 
lean_dec(v_x2_4832_);
v_snd_4835_ = lean_ctor_get(v_x1_4831_, 1);
v_isSharedCheck_4843_ = !lean_is_exclusive(v_x1_4831_);
if (v_isSharedCheck_4843_ == 0)
{
lean_object* v_unused_4844_; 
v_unused_4844_ = lean_ctor_get(v_x1_4831_, 0);
lean_dec(v_unused_4844_);
v___x_4837_ = v_x1_4831_;
v_isShared_4838_ = v_isSharedCheck_4843_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_snd_4835_);
lean_dec(v_x1_4831_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4843_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4839_; lean_object* v___x_4841_; 
v___x_4839_ = lean_box(v___x_4830_);
if (v_isShared_4838_ == 0)
{
lean_ctor_set(v___x_4837_, 0, v___x_4839_);
v___x_4841_ = v___x_4837_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4839_);
lean_ctor_set(v_reuseFailAlloc_4842_, 1, v_snd_4835_);
v___x_4841_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
return v___x_4841_;
}
}
}
else
{
lean_object* v_snd_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4855_; 
v_snd_4845_ = lean_ctor_get(v_x1_4831_, 1);
v_isSharedCheck_4855_ = !lean_is_exclusive(v_x1_4831_);
if (v_isSharedCheck_4855_ == 0)
{
lean_object* v_unused_4856_; 
v_unused_4856_ = lean_ctor_get(v_x1_4831_, 0);
lean_dec(v_unused_4856_);
v___x_4847_ = v_x1_4831_;
v_isShared_4848_ = v_isSharedCheck_4855_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_snd_4845_);
lean_dec(v_x1_4831_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4855_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
uint8_t v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4853_; 
v___x_4849_ = 0;
v___x_4850_ = lean_array_push(v_snd_4845_, v_x2_4832_);
v___x_4851_ = lean_box(v___x_4849_);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 1, v___x_4850_);
lean_ctor_set(v___x_4847_, 0, v___x_4851_);
v___x_4853_ = v___x_4847_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v___x_4851_);
lean_ctor_set(v_reuseFailAlloc_4854_, 1, v___x_4850_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0___boxed(lean_object* v___x_4857_, lean_object* v_x1_4858_, lean_object* v_x2_4859_){
_start:
{
uint8_t v___x_172__boxed_4860_; lean_object* v_res_4861_; 
v___x_172__boxed_4860_ = lean_unbox(v___x_4857_);
v_res_4861_ = l_Array_getEvenElems___redArg___lam__0(v___x_172__boxed_4860_, v_x1_4858_, v_x2_4859_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg(lean_object* v_as_4862_){
_start:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; uint8_t v___x_4867_; 
v___x_4863_ = lean_unsigned_to_nat(0u);
v___x_4864_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_4865_ = lean_array_get_size(v_as_4862_);
v___x_4866_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4867_ = lean_nat_dec_lt(v___x_4863_, v___x_4865_);
if (v___x_4867_ == 0)
{
lean_dec_ref(v_as_4862_);
return v___x_4864_;
}
else
{
lean_object* v___x_4868_; lean_object* v___f_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; uint8_t v___x_4872_; 
v___x_4868_ = lean_box(v___x_4867_);
v___f_4869_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4869_, 0, v___x_4868_);
v___x_4870_ = lean_box(v___x_4867_);
v___x_4871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4871_, 0, v___x_4870_);
lean_ctor_set(v___x_4871_, 1, v___x_4864_);
v___x_4872_ = lean_nat_dec_le(v___x_4865_, v___x_4865_);
if (v___x_4872_ == 0)
{
if (v___x_4867_ == 0)
{
lean_dec_ref_known(v___x_4871_, 2);
lean_dec_ref(v___f_4869_);
lean_dec_ref(v_as_4862_);
return v___x_4864_;
}
else
{
size_t v___x_4873_; size_t v___x_4874_; lean_object* v___x_4875_; lean_object* v_snd_4876_; 
v___x_4873_ = ((size_t)0ULL);
v___x_4874_ = lean_usize_of_nat(v___x_4865_);
v___x_4875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4866_, v___f_4869_, v_as_4862_, v___x_4873_, v___x_4874_, v___x_4871_);
v_snd_4876_ = lean_ctor_get(v___x_4875_, 1);
lean_inc(v_snd_4876_);
lean_dec(v___x_4875_);
return v_snd_4876_;
}
}
else
{
size_t v___x_4877_; size_t v___x_4878_; lean_object* v___x_4879_; lean_object* v_snd_4880_; 
v___x_4877_ = ((size_t)0ULL);
v___x_4878_ = lean_usize_of_nat(v___x_4865_);
v___x_4879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4866_, v___f_4869_, v_as_4862_, v___x_4877_, v___x_4878_, v___x_4871_);
v_snd_4880_ = lean_ctor_get(v___x_4879_, 1);
lean_inc(v_snd_4880_);
lean_dec(v___x_4879_);
return v_snd_4880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems(lean_object* v_00_u03b1_4881_, lean_object* v_as_4882_){
_start:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; uint8_t v___x_4887_; 
v___x_4883_ = lean_unsigned_to_nat(0u);
v___x_4884_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_4885_ = lean_array_get_size(v_as_4882_);
v___x_4886_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4887_ = lean_nat_dec_lt(v___x_4883_, v___x_4885_);
if (v___x_4887_ == 0)
{
lean_dec_ref(v_as_4882_);
return v___x_4884_;
}
else
{
lean_object* v___x_4888_; lean_object* v___f_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; uint8_t v___x_4892_; 
v___x_4888_ = lean_box(v___x_4887_);
v___f_4889_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4889_, 0, v___x_4888_);
v___x_4890_ = lean_box(v___x_4887_);
v___x_4891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4891_, 0, v___x_4890_);
lean_ctor_set(v___x_4891_, 1, v___x_4884_);
v___x_4892_ = lean_nat_dec_le(v___x_4885_, v___x_4885_);
if (v___x_4892_ == 0)
{
if (v___x_4887_ == 0)
{
lean_dec_ref_known(v___x_4891_, 2);
lean_dec_ref(v___f_4889_);
lean_dec_ref(v_as_4882_);
return v___x_4884_;
}
else
{
size_t v___x_4893_; size_t v___x_4894_; lean_object* v___x_4895_; lean_object* v_snd_4896_; 
v___x_4893_ = ((size_t)0ULL);
v___x_4894_ = lean_usize_of_nat(v___x_4885_);
v___x_4895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4886_, v___f_4889_, v_as_4882_, v___x_4893_, v___x_4894_, v___x_4891_);
v_snd_4896_ = lean_ctor_get(v___x_4895_, 1);
lean_inc(v_snd_4896_);
lean_dec(v___x_4895_);
return v_snd_4896_;
}
}
else
{
size_t v___x_4897_; size_t v___x_4898_; lean_object* v___x_4899_; lean_object* v_snd_4900_; 
v___x_4897_ = ((size_t)0ULL);
v___x_4898_ = lean_usize_of_nat(v___x_4885_);
v___x_4899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4886_, v___f_4889_, v_as_4882_, v___x_4897_, v___x_4898_, v___x_4891_);
v_snd_4900_ = lean_ctor_get(v___x_4899_, 1);
lean_inc(v_snd_4900_);
lean_dec(v___x_4899_);
return v_snd_4900_;
}
}
}
}
static lean_object* _init_l_Array_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_4906_; lean_object* v___x_4907_; 
v___x_4906_ = ((lean_object*)(l_term_x23_x5b___x2c_x5d___closed__4));
v___x_4907_ = lean_string_length(v___x_4906_);
return v___x_4907_;
}
}
static lean_object* _init_l_Array_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4908_ = lean_obj_once(&l_Array_repr___redArg___closed__2, &l_Array_repr___redArg___closed__2_once, _init_l_Array_repr___redArg___closed__2);
v___x_4909_ = lean_nat_to_int(v___x_4908_);
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___redArg(lean_object* v_inst_4917_, lean_object* v_xs_4918_){
_start:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; uint8_t v___x_4921_; 
v___x_4919_ = lean_array_get_size(v_xs_4918_);
v___x_4920_ = lean_unsigned_to_nat(0u);
v___x_4921_ = lean_nat_dec_eq(v___x_4919_, v___x_4920_);
if (v___x_4921_ == 0)
{
lean_object* v_x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; 
v_x_4922_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_4922_, 0, lean_box(0));
lean_closure_set(v_x_4922_, 1, v_inst_4917_);
v___x_4923_ = lean_array_to_list(v_xs_4918_);
v___x_4924_ = ((lean_object*)(l_Array_repr___redArg___closed__1));
v___x_4925_ = l_Std_Format_joinSep___redArg(v_x_4922_, v___x_4923_, v___x_4924_);
v___x_4926_ = lean_obj_once(&l_Array_repr___redArg___closed__3, &l_Array_repr___redArg___closed__3_once, _init_l_Array_repr___redArg___closed__3);
v___x_4927_ = ((lean_object*)(l_Array_repr___redArg___closed__4));
v___x_4928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4928_, 0, v___x_4927_);
lean_ctor_set(v___x_4928_, 1, v___x_4925_);
v___x_4929_ = ((lean_object*)(l_Array_repr___redArg___closed__5));
v___x_4930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4930_, 0, v___x_4928_);
lean_ctor_set(v___x_4930_, 1, v___x_4929_);
v___x_4931_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4931_, 0, v___x_4926_);
lean_ctor_set(v___x_4931_, 1, v___x_4930_);
v___x_4932_ = l_Std_Format_fill(v___x_4931_);
return v___x_4932_;
}
else
{
lean_object* v___x_4933_; 
lean_dec_ref(v_xs_4918_);
lean_dec_ref(v_inst_4917_);
v___x_4933_ = ((lean_object*)(l_Array_repr___redArg___closed__7));
return v___x_4933_;
}
}
}
LEAN_EXPORT lean_object* l_Array_repr(lean_object* v_00_u03b1_4934_, lean_object* v_inst_4935_, lean_object* v_xs_4936_){
_start:
{
lean_object* v___x_4937_; 
v___x_4937_ = l_Array_repr___redArg(v_inst_4935_, v_xs_4936_);
return v___x_4937_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0(lean_object* v_inst_4938_, lean_object* v_xs_4939_, lean_object* v_x_4940_){
_start:
{
lean_object* v___x_4941_; 
v___x_4941_ = l_Array_repr___redArg(v_inst_4938_, v_xs_4939_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object* v_inst_4942_, lean_object* v_xs_4943_, lean_object* v_x_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l_Array_instRepr___redArg___lam__0(v_inst_4942_, v_xs_4943_, v_x_4944_);
lean_dec(v_x_4944_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg(lean_object* v_inst_4946_){
_start:
{
lean_object* v___f_4947_; 
v___f_4947_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4947_, 0, v_inst_4946_);
return v___f_4947_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr(lean_object* v_00_u03b1_4948_, lean_object* v_inst_4949_){
_start:
{
lean_object* v___f_4950_; 
v___f_4950_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4950_, 0, v_inst_4949_);
return v___f_4950_;
}
}
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Init_GetElem(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_ToArrayImpl(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_ToArrayImpl(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Set(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Set(uint8_t builtin);
lean_object* runtime_initialize_Init_WF(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_ToArrayImpl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_ToArrayImpl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_swap___auto__1 = _init_l_Array_swap___auto__1();
lean_mark_persistent(l_Array_swap___auto__1);
l_Array_swap___auto__3 = _init_l_Array_swap___auto__3();
lean_mark_persistent(l_Array_swap___auto__3);
l_Array_back___auto__1 = _init_l_Array_back___auto__1();
lean_mark_persistent(l_Array_back___auto__1);
l_Array_swapAt___auto__1 = _init_l_Array_swapAt___auto__1();
lean_mark_persistent(l_Array_swapAt___auto__1);
l_Array_eraseIdx___auto__1 = _init_l_Array_eraseIdx___auto__1();
lean_mark_persistent(l_Array_eraseIdx___auto__1);
l_Array_insertIdx___auto__1 = _init_l_Array_insertIdx___auto__1();
lean_mark_persistent(l_Array_insertIdx___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Do(uint8_t builtin);
lean_object* initialize_Init_GetElem(uint8_t builtin);
lean_object* initialize_Init_Data_List_ToArrayImpl(uint8_t builtin);
lean_object* initialize_Init_Data_List_ToArrayImpl(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Set(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Set(uint8_t builtin);
lean_object* initialize_Init_WF(uint8_t builtin);
lean_object* initialize_Init_MetaTypes(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_ToArrayImpl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_ToArrayImpl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
