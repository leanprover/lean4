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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
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
LEAN_EXPORT lean_object* l_Array_instMembership___redArg();
LEAN_EXPORT lean_object* l_Array_instMembership___redArg___boxed(lean_object*);
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
lean_object* lean_array_mark_linear(lean_object*);
LEAN_EXPORT lean_object* l_Array_markLinear___boxed(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_propagateMark___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___redArg___lam__0(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_instGetElemUSizeLtNatToNatSize___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instGetElemUSizeLtNatToNatSize___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_instGetElemUSizeLtNatToNatSize___redArg___closed__0 = (const lean_object*)&l_Array_instGetElemUSizeLtNatToNatSize___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___redArg();
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize(lean_object*);
static const lean_array_object l_Array_instEmptyCollection___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_instEmptyCollection___redArg___closed__0 = (const lean_object*)&l_Array_instEmptyCollection___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Array_instEmptyCollection___redArg___boxed(lean_object*);
static lean_once_cell_t l_Array_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_instEmptyCollection___closed__0;
LEAN_EXPORT lean_object* l_Array_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Array_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Array_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Array_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_instInhabited___closed__0;
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
LEAN_EXPORT lean_object* l_Array_ofFn_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFn_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFn_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFn_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapM_map___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_map___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_anyM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Array_all___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Array_instAppend___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_append___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_instAppend___redArg___closed__0 = (const lean_object*)&l_Array_instAppend___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_instAppend___redArg();
LEAN_EXPORT lean_object* l_Array_instAppend___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppend(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_appendList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_appendList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_instHAppendList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_appendList, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_instHAppendList___redArg___closed__0 = (const lean_object*)&l_Array_instHAppendList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_instHAppendList___redArg();
LEAN_EXPORT lean_object* l_Array_instHAppendList___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Array_instLT___redArg();
LEAN_EXPORT lean_object* l_Array_instLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_instLT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instLE___redArg();
LEAN_EXPORT lean_object* l_Array_instLE___redArg___boxed(lean_object*);
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
v___x_77_ = l_Array_mkArray0___redArg();
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
lean_object* l_Array_instMembership___redArg(){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lean_box(0);
return v___x_117_;
}
}
LEAN_EXPORT void l_Array_instMembership___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_118_;
v_res_118_ = l_Array_instMembership___redArg();
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l_Array_instMembership___redArg___boxed(lean_object* v___dummy_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Array_instMembership___redArg();
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Array_instMembership(lean_object* v_00_u03b1_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_box(0);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter___redArg(lean_object* v_x_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_){
_start:
{
if (lean_obj_tag(v_x_123_) == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec(v_h__1_124_);
v___x_126_ = lean_box(0);
v___x_127_ = lean_apply_1(v_h__2_125_, v___x_126_);
return v___x_127_;
}
else
{
lean_object* v_val_128_; lean_object* v___x_129_; 
lean_dec(v_h__2_125_);
v_val_128_ = lean_ctor_get(v_x_123_, 0);
lean_inc(v_val_128_);
lean_dec_ref_known(v_x_123_, 1);
v___x_129_ = lean_apply_1(v_h__1_124_, v_val_128_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_130_, lean_object* v_motive_131_, lean_object* v_x_132_, lean_object* v_h__1_133_, lean_object* v_h__2_134_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_h__1_133_);
v___x_135_ = lean_box(0);
v___x_136_ = lean_apply_1(v_h__2_134_, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v_val_137_; lean_object* v___x_138_; 
lean_dec(v_h__2_134_);
v_val_137_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_val_137_);
lean_dec_ref_known(v_x_132_, 1);
v___x_138_ = lean_apply_1(v_h__1_133_, v_val_137_);
return v___x_138_;
}
}
}
LEAN_EXPORT void l_Array_usize_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_140_ = stack[1].m_obj;
size_t v_res_141_;
v_res_141_ = lean_array_size(v_xs_140_);
stack->m_num = v_res_141_;
}
LEAN_EXPORT lean_object* l_Array_usize___boxed(lean_object* v_00_u03b1_142_, lean_object* v_xs_143_){
_start:
{
size_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = lean_array_size(v_xs_143_);
lean_dec_ref(v_xs_143_);
v_r_145_ = lean_box_usize(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT void l_Array_uget_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_147_ = stack[1].m_obj;
size_t v_i_148_ = stack[2].m_num;
lean_object* v_res_150_;
v_res_150_ = lean_array_uget(v_xs_147_, v_i_148_);
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l_Array_uget___boxed(lean_object* v_00_u03b1_151_, lean_object* v_xs_152_, lean_object* v_i_153_, lean_object* v_h_154_){
_start:
{
size_t v_i_boxed_155_; lean_object* v_res_156_; 
v_i_boxed_155_ = lean_unbox_usize(v_i_153_);
lean_dec(v_i_153_);
v_res_156_ = lean_array_uget(v_xs_152_, v_i_boxed_155_);
lean_dec_ref(v_xs_152_);
return v_res_156_;
}
}
LEAN_EXPORT void l_Array_ugetBorrowed_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_158_ = stack[1].m_obj;
size_t v_i_159_ = stack[2].m_num;
lean_object* v_res_161_;
v_res_161_ = lean_array_uget_borrowed(v_xs_158_, v_i_159_);
stack->m_obj
 = v_res_161_;
}
LEAN_EXPORT lean_object* l_Array_ugetBorrowed___boxed(lean_object* v_00_u03b1_162_, lean_object* v_xs_163_, lean_object* v_i_164_, lean_object* v_h_165_){
_start:
{
size_t v_i_boxed_166_; lean_object* v_res_167_; 
v_i_boxed_166_ = lean_unbox_usize(v_i_164_);
lean_dec(v_i_164_);
v_res_167_ = lean_array_uget_borrowed(v_xs_163_, v_i_boxed_166_);
lean_dec_ref(v_xs_163_);
return v_res_167_;
}
}
LEAN_EXPORT void l_Array_uset_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_169_ = stack[1].m_obj;
size_t v_i_170_ = stack[2].m_num;
lean_object* v_v_171_ = stack[3].m_obj;
lean_object* v_res_173_;
v_res_173_ = lean_array_uset(v_xs_169_, v_i_170_, v_v_171_);
stack->m_obj
 = v_res_173_;
}
LEAN_EXPORT lean_object* l_Array_uset___boxed(lean_object* v_00_u03b1_174_, lean_object* v_xs_175_, lean_object* v_i_176_, lean_object* v_v_177_, lean_object* v_h_178_){
_start:
{
size_t v_i_boxed_179_; lean_object* v_res_180_; 
v_i_boxed_179_ = lean_unbox_usize(v_i_176_);
lean_dec(v_i_176_);
v_res_180_ = lean_array_uset(v_xs_175_, v_i_boxed_179_, v_v_177_);
return v_res_180_;
}
}
LEAN_EXPORT void l_Array_pop_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_182_ = stack[1].m_obj;
lean_object* v_res_183_;
v_res_183_ = lean_array_pop(v_xs_182_);
stack->m_obj
 = v_res_183_;
}
LEAN_EXPORT lean_object* l_Array_pop___boxed(lean_object* v_00_u03b1_184_, lean_object* v_xs_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = lean_array_pop(v_xs_185_);
return v_res_186_;
}
}
LEAN_EXPORT void l_Array_markLinear_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_188_ = stack[1].m_obj;
lean_object* v_res_189_;
v_res_189_ = lean_array_mark_linear(v_xs_188_);
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l_Array_markLinear___boxed(lean_object* v_00_u03b1_190_, lean_object* v_xs_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = lean_array_mark_linear(v_xs_191_);
return v_res_192_;
}
}
LEAN_EXPORT void l_Array_propagateMark_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_195_ = stack[2].m_obj;
lean_object* v_ys_196_ = stack[3].m_obj;
lean_object* v_res_197_;
v_res_197_ = lean_array_propagate_mark(v_xs_195_, v_ys_196_);
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l_Array_propagateMark___boxed(lean_object* v_00_u03b1_198_, lean_object* v_00_u03b2_199_, lean_object* v_xs_200_, lean_object* v_ys_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = lean_array_propagate_mark(v_xs_200_, v_ys_201_);
lean_dec_ref(v_xs_200_);
return v_res_202_;
}
}
LEAN_EXPORT void l_Array_replicate_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_204_ = stack[1].m_obj;
lean_object* v_v_205_ = stack[2].m_obj;
lean_object* v_res_206_;
v_res_206_ = lean_mk_array(v_n_204_, v_v_205_);
stack->m_obj
 = v_res_206_;
}
LEAN_EXPORT lean_object* l_Array_replicate___boxed(lean_object* v_00_u03b1_207_, lean_object* v_n_208_, lean_object* v_v_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = lean_mk_array(v_n_208_, v_v_209_);
return v_res_210_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__9(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l_Array_swap___auto__1___closed__8));
v___x_231_ = l_Lean_mkAtom(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__10(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_obj_once(&l_Array_swap___auto__1___closed__9, &l_Array_swap___auto__1___closed__9_once, _init_l_Array_swap___auto__1___closed__9);
v___x_233_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_234_ = lean_array_push(v___x_233_, v___x_232_);
return v___x_234_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__11(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_235_ = lean_obj_once(&l_Array_swap___auto__1___closed__10, &l_Array_swap___auto__1___closed__10_once, _init_l_Array_swap___auto__1___closed__10);
v___x_236_ = ((lean_object*)(l_Array_swap___auto__1___closed__7));
v___x_237_ = lean_box(2);
v___x_238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_236_);
lean_ctor_set(v___x_238_, 2, v___x_235_);
return v___x_238_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__12(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_obj_once(&l_Array_swap___auto__1___closed__11, &l_Array_swap___auto__1___closed__11_once, _init_l_Array_swap___auto__1___closed__11);
v___x_240_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_241_ = lean_array_push(v___x_240_, v___x_239_);
return v___x_241_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__13(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_242_ = lean_obj_once(&l_Array_swap___auto__1___closed__12, &l_Array_swap___auto__1___closed__12_once, _init_l_Array_swap___auto__1___closed__12);
v___x_243_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13));
v___x_244_ = lean_box(2);
v___x_245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
lean_ctor_set(v___x_245_, 2, v___x_242_);
return v___x_245_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__14(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_obj_once(&l_Array_swap___auto__1___closed__13, &l_Array_swap___auto__1___closed__13_once, _init_l_Array_swap___auto__1___closed__13);
v___x_247_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_248_ = lean_array_push(v___x_247_, v___x_246_);
return v___x_248_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__15(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_249_ = lean_obj_once(&l_Array_swap___auto__1___closed__14, &l_Array_swap___auto__1___closed__14_once, _init_l_Array_swap___auto__1___closed__14);
v___x_250_ = ((lean_object*)(l_Array_swap___auto__1___closed__5));
v___x_251_ = lean_box(2);
v___x_252_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_250_);
lean_ctor_set(v___x_252_, 2, v___x_249_);
return v___x_252_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__16(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_obj_once(&l_Array_swap___auto__1___closed__15, &l_Array_swap___auto__1___closed__15_once, _init_l_Array_swap___auto__1___closed__15);
v___x_254_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_255_ = lean_array_push(v___x_254_, v___x_253_);
return v___x_255_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__17(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_256_ = lean_obj_once(&l_Array_swap___auto__1___closed__16, &l_Array_swap___auto__1___closed__16_once, _init_l_Array_swap___auto__1___closed__16);
v___x_257_ = ((lean_object*)(l_Array_swap___auto__1___closed__2));
v___x_258_ = lean_box(2);
v___x_259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_257_);
lean_ctor_set(v___x_259_, 2, v___x_256_);
return v___x_259_;
}
}
static lean_object* _init_l_Array_swap___auto__1(void){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_260_;
}
}
static lean_object* _init_l_Array_swap___auto__3(void){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_261_;
}
}
LEAN_EXPORT void l_Array_swap_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_263_ = stack[1].m_obj;
lean_object* v_i_264_ = stack[2].m_obj;
lean_object* v_j_265_ = stack[3].m_obj;
lean_object* v_res_268_;
v_res_268_ = lean_array_fswap(v_xs_263_, v_i_264_, v_j_265_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l_Array_swap___boxed(lean_object* v_00_u03b1_269_, lean_object* v_xs_270_, lean_object* v_i_271_, lean_object* v_j_272_, lean_object* v_hi_273_, lean_object* v_hj_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = lean_array_fswap(v_xs_270_, v_i_271_, v_j_272_);
lean_dec(v_j_272_);
lean_dec(v_i_271_);
return v_res_275_;
}
}
LEAN_EXPORT void l_Array_swapIfInBounds_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_277_ = stack[1].m_obj;
lean_object* v_i_278_ = stack[2].m_obj;
lean_object* v_j_279_ = stack[3].m_obj;
lean_object* v_res_280_;
v_res_280_ = lean_array_swap(v_xs_277_, v_i_278_, v_j_279_);
stack->m_obj
 = v_res_280_;
}
LEAN_EXPORT lean_object* l_Array_swapIfInBounds___boxed(lean_object* v_00_u03b1_281_, lean_object* v_xs_282_, lean_object* v_i_283_, lean_object* v_j_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = lean_array_swap(v_xs_282_, v_i_283_, v_j_284_);
lean_dec(v_j_284_);
lean_dec(v_i_283_);
return v_res_285_;
}
}
lean_object* l_Array_instGetElemUSizeLtNatToNatSize___redArg___lam__0(lean_object* v_xs_286_, size_t v_i_287_, lean_object* v_h_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lean_array_uget_borrowed(v_xs_286_, v_i_287_);
lean_inc(v___x_289_);
return v___x_289_;
}
}
LEAN_EXPORT void l_Array_instGetElemUSizeLtNatToNatSize___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_286_ = stack[0].m_obj;
size_t v_i_287_ = stack[1].m_num;
lean_object* v_res_290_;
v_res_290_ = l_Array_instGetElemUSizeLtNatToNatSize___redArg___lam__0(v_xs_286_, v_i_287_, lean_box(0));
stack->m_obj
 = v_res_290_;
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___redArg___lam__0___boxed(lean_object* v_xs_291_, lean_object* v_i_292_, lean_object* v_h_293_){
_start:
{
size_t v_i_boxed_294_; lean_object* v_res_295_; 
v_i_boxed_294_ = lean_unbox_usize(v_i_292_);
lean_dec(v_i_292_);
v_res_295_ = l_Array_instGetElemUSizeLtNatToNatSize___redArg___lam__0(v_xs_291_, v_i_boxed_294_, v_h_293_);
lean_dec_ref(v_xs_291_);
return v_res_295_;
}
}
lean_object* l_Array_instGetElemUSizeLtNatToNatSize___redArg(){
_start:
{
lean_object* v___f_298_; 
v___f_298_ = ((lean_object*)(l_Array_instGetElemUSizeLtNatToNatSize___redArg___closed__0));
return v___f_298_;
}
}
LEAN_EXPORT void l_Array_instGetElemUSizeLtNatToNatSize___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_299_;
v_res_299_ = l_Array_instGetElemUSizeLtNatToNatSize___redArg();
stack->m_obj
 = v_res_299_;
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___redArg___boxed(lean_object* v___dummy_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Array_instGetElemUSizeLtNatToNatSize___redArg();
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize(lean_object* v_00_u03b1_302_){
_start:
{
lean_object* v___f_303_; 
v___f_303_ = ((lean_object*)(l_Array_instGetElemUSizeLtNatToNatSize___redArg___closed__0));
return v___f_303_;
}
}
lean_object* l_Array_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
return v___x_307_;
}
}
LEAN_EXPORT void l_Array_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_308_;
v_res_308_ = l_Array_instEmptyCollection___redArg();
stack->m_obj
 = v_res_308_;
}
LEAN_EXPORT lean_object* l_Array_instEmptyCollection___redArg___boxed(lean_object* v___dummy_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Array_instEmptyCollection___redArg();
return v_res_310_;
}
}
static lean_object* _init_l_Array_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Array_instEmptyCollection___redArg();
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Array_instEmptyCollection(lean_object* v_00_u03b1_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = lean_obj_once(&l_Array_instEmptyCollection___closed__0, &l_Array_instEmptyCollection___closed__0_once, _init_l_Array_instEmptyCollection___closed__0);
return v___x_313_;
}
}
lean_object* l_Array_instInhabited___redArg(){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
return v___x_315_;
}
}
LEAN_EXPORT void l_Array_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_316_;
v_res_316_ = l_Array_instInhabited___redArg();
stack->m_obj
 = v_res_316_;
}
LEAN_EXPORT lean_object* l_Array_instInhabited___redArg___boxed(lean_object* v___dummy_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Array_instInhabited___redArg();
return v_res_318_;
}
}
static lean_object* _init_l_Array_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Array_instInhabited___redArg();
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Array_instInhabited(lean_object* v_00_u03b1_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = lean_obj_once(&l_Array_instInhabited___closed__0, &l_Array_instInhabited___closed__0_once, _init_l_Array_instInhabited___closed__0);
return v___x_321_;
}
}
uint8_t l_Array_isEmpty___redArg(lean_object* v_xs_322_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_323_ = lean_array_get_size(v_xs_322_);
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_nat_dec_eq(v___x_323_, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT void l_Array_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_322_ = stack[0].m_obj;
uint8_t v_res_326_;
v_res_326_ = l_Array_isEmpty___redArg(v_xs_322_);
stack->m_num = v_res_326_;
}
LEAN_EXPORT lean_object* l_Array_isEmpty___redArg___boxed(lean_object* v_xs_327_){
_start:
{
uint8_t v_res_328_; lean_object* v_r_329_; 
v_res_328_ = l_Array_isEmpty___redArg(v_xs_327_);
lean_dec_ref(v_xs_327_);
v_r_329_ = lean_box(v_res_328_);
return v_r_329_;
}
}
uint8_t l_Array_isEmpty(lean_object* v_00_u03b1_330_, lean_object* v_xs_331_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_332_ = lean_array_get_size(v_xs_331_);
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = lean_nat_dec_eq(v___x_332_, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT void l_Array_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_331_ = stack[1].m_obj;
uint8_t v_res_335_;
v_res_335_ = l_Array_isEmpty(lean_box(0), v_xs_331_);
stack->m_num = v_res_335_;
}
LEAN_EXPORT lean_object* l_Array_isEmpty___boxed(lean_object* v_00_u03b1_336_, lean_object* v_xs_337_){
_start:
{
uint8_t v_res_338_; lean_object* v_r_339_; 
v_res_338_ = l_Array_isEmpty(v_00_u03b1_336_, v_xs_337_);
lean_dec_ref(v_xs_337_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
uint8_t l_Array_isEqvAux___redArg(lean_object* v_xs_340_, lean_object* v_ys_341_, lean_object* v_p_342_, lean_object* v_x_343_){
_start:
{
lean_object* v_zero_344_; uint8_t v_isZero_345_; 
v_zero_344_ = lean_unsigned_to_nat(0u);
v_isZero_345_ = lean_nat_dec_eq(v_x_343_, v_zero_344_);
if (v_isZero_345_ == 1)
{
lean_dec(v_x_343_);
lean_dec_ref(v_p_342_);
return v_isZero_345_;
}
else
{
lean_object* v_one_346_; lean_object* v_n_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v_one_346_ = lean_unsigned_to_nat(1u);
v_n_347_ = lean_nat_sub(v_x_343_, v_one_346_);
lean_dec(v_x_343_);
v___x_348_ = lean_array_fget_borrowed(v_xs_340_, v_n_347_);
v___x_349_ = lean_array_fget_borrowed(v_ys_341_, v_n_347_);
lean_inc_ref(v_p_342_);
lean_inc(v___x_349_);
lean_inc(v___x_348_);
v___x_350_ = lean_apply_2(v_p_342_, v___x_348_, v___x_349_);
v___x_351_ = lean_unbox(v___x_350_);
if (v___x_351_ == 0)
{
uint8_t v___x_352_; 
lean_dec(v_n_347_);
lean_dec_ref(v_p_342_);
v___x_352_ = lean_unbox(v___x_350_);
return v___x_352_;
}
else
{
v_x_343_ = v_n_347_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_340_ = stack[0].m_obj;
lean_object* v_ys_341_ = stack[1].m_obj;
lean_object* v_p_342_ = stack[2].m_obj;
lean_object* v_x_343_ = stack[3].m_obj;
uint8_t v_res_354_;
v_res_354_ = l_Array_isEqvAux___redArg(v_xs_340_, v_ys_341_, v_p_342_, v_x_343_);
stack->m_num = v_res_354_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___redArg___boxed(lean_object* v_xs_355_, lean_object* v_ys_356_, lean_object* v_p_357_, lean_object* v_x_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Array_isEqvAux___redArg(v_xs_355_, v_ys_356_, v_p_357_, v_x_358_);
lean_dec_ref(v_ys_356_);
lean_dec_ref(v_xs_355_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
uint8_t l_Array_isEqvAux(lean_object* v_00_u03b1_361_, lean_object* v_xs_362_, lean_object* v_ys_363_, lean_object* v_hsz_364_, lean_object* v_p_365_, lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
uint8_t v___x_368_; 
v___x_368_ = l_Array_isEqvAux___redArg(v_xs_362_, v_ys_363_, v_p_365_, v_x_366_);
return v___x_368_;
}
}
LEAN_EXPORT void l_Array_isEqvAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_362_ = stack[1].m_obj;
lean_object* v_ys_363_ = stack[2].m_obj;
lean_object* v_p_365_ = stack[4].m_obj;
lean_object* v_x_366_ = stack[5].m_obj;
uint8_t v_res_369_;
v_res_369_ = l_Array_isEqvAux(lean_box(0), v_xs_362_, v_ys_363_, lean_box(0), v_p_365_, v_x_366_, lean_box(0));
stack->m_num = v_res_369_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___boxed(lean_object* v_00_u03b1_370_, lean_object* v_xs_371_, lean_object* v_ys_372_, lean_object* v_hsz_373_, lean_object* v_p_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_Array_isEqvAux(v_00_u03b1_370_, v_xs_371_, v_ys_372_, v_hsz_373_, v_p_374_, v_x_375_, v_x_376_);
lean_dec_ref(v_ys_372_);
lean_dec_ref(v_xs_371_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
uint8_t l_Array_isEqv___redArg(lean_object* v_xs_379_, lean_object* v_ys_380_, lean_object* v_p_381_){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_382_ = lean_array_get_size(v_xs_379_);
v___x_383_ = lean_array_get_size(v_ys_380_);
v___x_384_ = lean_nat_dec_eq(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_dec_ref(v_p_381_);
return v___x_384_;
}
else
{
uint8_t v___x_385_; 
v___x_385_ = l_Array_isEqvAux___redArg(v_xs_379_, v_ys_380_, v_p_381_, v___x_382_);
return v___x_385_;
}
}
}
LEAN_EXPORT void l_Array_isEqv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_379_ = stack[0].m_obj;
lean_object* v_ys_380_ = stack[1].m_obj;
lean_object* v_p_381_ = stack[2].m_obj;
uint8_t v_res_386_;
v_res_386_ = l_Array_isEqv___redArg(v_xs_379_, v_ys_380_, v_p_381_);
stack->m_num = v_res_386_;
}
LEAN_EXPORT lean_object* l_Array_isEqv___redArg___boxed(lean_object* v_xs_387_, lean_object* v_ys_388_, lean_object* v_p_389_){
_start:
{
uint8_t v_res_390_; lean_object* v_r_391_; 
v_res_390_ = l_Array_isEqv___redArg(v_xs_387_, v_ys_388_, v_p_389_);
lean_dec_ref(v_ys_388_);
lean_dec_ref(v_xs_387_);
v_r_391_ = lean_box(v_res_390_);
return v_r_391_;
}
}
uint8_t l_Array_isEqv(lean_object* v_00_u03b1_392_, lean_object* v_xs_393_, lean_object* v_ys_394_, lean_object* v_p_395_){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_396_ = lean_array_get_size(v_xs_393_);
v___x_397_ = lean_array_get_size(v_ys_394_);
v___x_398_ = lean_nat_dec_eq(v___x_396_, v___x_397_);
if (v___x_398_ == 0)
{
lean_dec_ref(v_p_395_);
return v___x_398_;
}
else
{
uint8_t v___x_399_; 
v___x_399_ = l_Array_isEqvAux___redArg(v_xs_393_, v_ys_394_, v_p_395_, v___x_396_);
return v___x_399_;
}
}
}
LEAN_EXPORT void l_Array_isEqv_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_393_ = stack[1].m_obj;
lean_object* v_ys_394_ = stack[2].m_obj;
lean_object* v_p_395_ = stack[3].m_obj;
uint8_t v_res_400_;
v_res_400_ = l_Array_isEqv(lean_box(0), v_xs_393_, v_ys_394_, v_p_395_);
stack->m_num = v_res_400_;
}
LEAN_EXPORT lean_object* l_Array_isEqv___boxed(lean_object* v_00_u03b1_401_, lean_object* v_xs_402_, lean_object* v_ys_403_, lean_object* v_p_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Array_isEqv(v_00_u03b1_401_, v_xs_402_, v_ys_403_, v_p_404_);
lean_dec_ref(v_ys_403_);
lean_dec_ref(v_xs_402_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
uint8_t l_Array_instBEq___redArg___lam__0(lean_object* v_inst_407_, lean_object* v_xs_408_, lean_object* v_ys_409_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_410_ = lean_array_get_size(v_xs_408_);
v___x_411_ = lean_array_get_size(v_ys_409_);
v___x_412_ = lean_nat_dec_eq(v___x_410_, v___x_411_);
if (v___x_412_ == 0)
{
lean_dec_ref(v_inst_407_);
return v___x_412_;
}
else
{
uint8_t v___x_413_; 
v___x_413_ = l_Array_isEqvAux___redArg(v_xs_408_, v_ys_409_, v_inst_407_, v___x_410_);
return v___x_413_;
}
}
}
LEAN_EXPORT void l_Array_instBEq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_407_ = stack[0].m_obj;
lean_object* v_xs_408_ = stack[1].m_obj;
lean_object* v_ys_409_ = stack[2].m_obj;
uint8_t v_res_414_;
v_res_414_ = l_Array_instBEq___redArg___lam__0(v_inst_407_, v_xs_408_, v_ys_409_);
stack->m_num = v_res_414_;
}
LEAN_EXPORT lean_object* l_Array_instBEq___redArg___lam__0___boxed(lean_object* v_inst_415_, lean_object* v_xs_416_, lean_object* v_ys_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_Array_instBEq___redArg___lam__0(v_inst_415_, v_xs_416_, v_ys_417_);
lean_dec_ref(v_ys_417_);
lean_dec_ref(v_xs_416_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT lean_object* l_Array_instBEq___redArg(lean_object* v_inst_420_){
_start:
{
lean_object* v___f_421_; 
v___f_421_ = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_421_, 0, v_inst_420_);
return v___f_421_;
}
}
LEAN_EXPORT lean_object* l_Array_instBEq(lean_object* v_00_u03b1_422_, lean_object* v_inst_423_){
_start:
{
lean_object* v___f_424_; 
v___f_424_ = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_424_, 0, v_inst_423_);
return v___f_424_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn_go___redArg(lean_object* v_n_425_, lean_object* v_f_426_, lean_object* v_acc_427_, lean_object* v_i_428_){
_start:
{
lean_object* v_zero_429_; uint8_t v_isZero_430_; 
v_zero_429_ = lean_unsigned_to_nat(0u);
v_isZero_430_ = lean_nat_dec_eq(v_i_428_, v_zero_429_);
if (v_isZero_430_ == 1)
{
lean_dec(v_i_428_);
lean_dec(v_f_426_);
return v_acc_427_;
}
else
{
lean_object* v_one_431_; lean_object* v_n_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_one_431_ = lean_unsigned_to_nat(1u);
v_n_432_ = lean_nat_sub(v_i_428_, v_one_431_);
lean_dec(v_i_428_);
v___x_433_ = lean_nat_sub(v_n_425_, v_n_432_);
v___x_434_ = lean_nat_sub(v___x_433_, v_one_431_);
lean_dec(v___x_433_);
lean_inc(v_f_426_);
v___x_435_ = lean_apply_1(v_f_426_, v___x_434_);
v___x_436_ = lean_array_push(v_acc_427_, v___x_435_);
v_acc_427_ = v___x_436_;
v_i_428_ = v_n_432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_ofFn_go___redArg___boxed(lean_object* v_n_438_, lean_object* v_f_439_, lean_object* v_acc_440_, lean_object* v_i_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Array_ofFn_go___redArg(v_n_438_, v_f_439_, v_acc_440_, v_i_441_);
lean_dec(v_n_438_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn_go(lean_object* v_00_u03b1_443_, lean_object* v_n_444_, lean_object* v_f_445_, lean_object* v_acc_446_, lean_object* v_i_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Array_ofFn_go___redArg(v_n_444_, v_f_445_, v_acc_446_, v_i_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn_go___boxed(lean_object* v_00_u03b1_450_, lean_object* v_n_451_, lean_object* v_f_452_, lean_object* v_acc_453_, lean_object* v_i_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Array_ofFn_go(v_00_u03b1_450_, v_n_451_, v_f_452_, v_acc_453_, v_i_454_, v_a_455_);
lean_dec(v_n_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn___redArg(lean_object* v_n_457_, lean_object* v_f_458_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_mk_empty_array_with_capacity(v_n_457_);
lean_inc(v_n_457_);
v___x_460_ = l_Array_ofFn_go___redArg(v_n_457_, v_f_458_, v___x_459_, v_n_457_);
lean_dec(v_n_457_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn(lean_object* v_00_u03b1_461_, lean_object* v_n_462_, lean_object* v_f_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Array_ofFn___redArg(v_n_462_, v_f_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Array_range___lam__0(lean_object* v_i_465_){
_start:
{
lean_inc(v_i_465_);
return v_i_465_;
}
}
LEAN_EXPORT lean_object* l_Array_range___lam__0___boxed(lean_object* v_i_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Array_range___lam__0(v_i_466_);
lean_dec(v_i_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Array_range(lean_object* v_n_469_){
_start:
{
lean_object* v___f_470_; lean_object* v___x_471_; 
v___f_470_ = ((lean_object*)(l_Array_range___closed__0));
v___x_471_ = l_Array_ofFn___redArg(v_n_469_, v___f_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27___lam__0(lean_object* v_step_472_, lean_object* v_start_473_, lean_object* v_i_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_nat_mul(v_step_472_, v_i_474_);
v___x_476_ = lean_nat_add(v_start_473_, v___x_475_);
lean_dec(v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27___lam__0___boxed(lean_object* v_step_477_, lean_object* v_start_478_, lean_object* v_i_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Array_range_x27___lam__0(v_step_477_, v_start_478_, v_i_479_);
lean_dec(v_i_479_);
lean_dec(v_start_478_);
lean_dec(v_step_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27(lean_object* v_start_481_, lean_object* v_size_482_, lean_object* v_step_483_){
_start:
{
lean_object* v___f_484_; lean_object* v___x_485_; 
v___f_484_ = lean_alloc_closure((void*)(l_Array_range_x27___lam__0___boxed), 3, 2);
lean_closure_set(v___f_484_, 0, v_step_483_);
lean_closure_set(v___f_484_, 1, v_start_481_);
v___x_485_ = l_Array_ofFn___redArg(v_size_482_, v___f_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Array_singleton___redArg(lean_object* v_v_486_){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_mk_empty_array_with_capacity(v___x_487_);
v___x_489_ = lean_array_push(v___x_488_, v_v_486_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Array_singleton(lean_object* v_00_u03b1_490_, lean_object* v_v_491_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_unsigned_to_nat(1u);
v___x_493_ = lean_mk_empty_array_with_capacity(v___x_492_);
v___x_494_ = lean_array_push(v___x_493_, v_v_491_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___redArg(lean_object* v_inst_495_, lean_object* v_xs_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_497_ = lean_array_get_size(v_xs_496_);
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = lean_nat_sub(v___x_497_, v___x_498_);
v___x_500_ = lean_array_get_borrowed(v_inst_495_, v_xs_496_, v___x_499_);
lean_dec(v___x_499_);
lean_inc(v___x_500_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___redArg___boxed(lean_object* v_inst_501_, lean_object* v_xs_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Array_back_x21___redArg(v_inst_501_, v_xs_502_);
lean_dec_ref(v_xs_502_);
lean_dec(v_inst_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21(lean_object* v_00_u03b1_504_, lean_object* v_inst_505_, lean_object* v_xs_506_){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_507_ = lean_array_get_size(v_xs_506_);
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = lean_nat_sub(v___x_507_, v___x_508_);
v___x_510_ = lean_array_get_borrowed(v_inst_505_, v_xs_506_, v___x_509_);
lean_dec(v___x_509_);
lean_inc(v___x_510_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___boxed(lean_object* v_00_u03b1_511_, lean_object* v_inst_512_, lean_object* v_xs_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Array_back_x21(v_00_u03b1_511_, v_inst_512_, v_xs_513_);
lean_dec_ref(v_xs_513_);
lean_dec(v_inst_512_);
return v_res_514_;
}
}
static lean_object* _init_l_Array_back___auto__1(void){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Array_back___redArg(lean_object* v_xs_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_517_ = lean_array_get_size(v_xs_516_);
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_sub(v___x_517_, v___x_518_);
v___x_520_ = lean_array_fget_borrowed(v_xs_516_, v___x_519_);
lean_dec(v___x_519_);
lean_inc(v___x_520_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Array_back___redArg___boxed(lean_object* v_xs_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Array_back___redArg(v_xs_521_);
lean_dec_ref(v_xs_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Array_back(lean_object* v_00_u03b1_523_, lean_object* v_xs_524_, lean_object* v_h_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_526_ = lean_array_get_size(v_xs_524_);
v___x_527_ = lean_unsigned_to_nat(1u);
v___x_528_ = lean_nat_sub(v___x_526_, v___x_527_);
v___x_529_ = lean_array_fget_borrowed(v_xs_524_, v___x_528_);
lean_dec(v___x_528_);
lean_inc(v___x_529_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Array_back___boxed(lean_object* v_00_u03b1_530_, lean_object* v_xs_531_, lean_object* v_h_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Array_back(v_00_u03b1_530_, v_xs_531_, v_h_532_);
lean_dec_ref(v_xs_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___redArg(lean_object* v_xs_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_535_ = lean_array_get_size(v_xs_534_);
v___x_536_ = lean_unsigned_to_nat(1u);
v___x_537_ = lean_nat_sub(v___x_535_, v___x_536_);
v___x_538_ = lean_nat_dec_lt(v___x_537_, v___x_535_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; 
lean_dec(v___x_537_);
v___x_539_ = lean_box(0);
return v___x_539_;
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_array_fget_borrowed(v_xs_534_, v___x_537_);
lean_dec(v___x_537_);
lean_inc(v___x_540_);
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___redArg___boxed(lean_object* v_xs_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Array_back_x3f___redArg(v_xs_542_);
lean_dec_ref(v_xs_542_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f(lean_object* v_00_u03b1_544_, lean_object* v_xs_545_){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_546_ = lean_array_get_size(v_xs_545_);
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_nat_sub(v___x_546_, v___x_547_);
v___x_549_ = lean_nat_dec_lt(v___x_548_, v___x_546_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
lean_dec(v___x_548_);
v___x_550_ = lean_box(0);
return v___x_550_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_array_fget_borrowed(v_xs_545_, v___x_548_);
lean_dec(v___x_548_);
lean_inc(v___x_551_);
v___x_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___boxed(lean_object* v_00_u03b1_553_, lean_object* v_xs_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Array_back_x3f(v_00_u03b1_553_, v_xs_554_);
lean_dec_ref(v_xs_554_);
return v_res_555_;
}
}
static lean_object* _init_l_Array_swapAt___auto__1(void){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___redArg(lean_object* v_xs_557_, lean_object* v_i_558_, lean_object* v_v_559_){
_start:
{
lean_object* v_e_560_; lean_object* v_xs_x27_561_; lean_object* v___x_562_; 
v_e_560_ = lean_array_fget(v_xs_557_, v_i_558_);
v_xs_x27_561_ = lean_array_fset(v_xs_557_, v_i_558_, v_v_559_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v_e_560_);
lean_ctor_set(v___x_562_, 1, v_xs_x27_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___redArg___boxed(lean_object* v_xs_563_, lean_object* v_i_564_, lean_object* v_v_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Array_swapAt___redArg(v_xs_563_, v_i_564_, v_v_565_);
lean_dec(v_i_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt(lean_object* v_00_u03b1_567_, lean_object* v_xs_568_, lean_object* v_i_569_, lean_object* v_v_570_, lean_object* v_hi_571_){
_start:
{
lean_object* v_e_572_; lean_object* v_xs_x27_573_; lean_object* v___x_574_; 
v_e_572_ = lean_array_fget(v_xs_568_, v_i_569_);
v_xs_x27_573_ = lean_array_fset(v_xs_568_, v_i_569_, v_v_570_);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_e_572_);
lean_ctor_set(v___x_574_, 1, v_xs_x27_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___boxed(lean_object* v_00_u03b1_575_, lean_object* v_xs_576_, lean_object* v_i_577_, lean_object* v_v_578_, lean_object* v_hi_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Array_swapAt(v_00_u03b1_575_, v_xs_576_, v_i_577_, v_v_578_, v_hi_579_);
lean_dec(v_i_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt_x21___redArg(lean_object* v_xs_585_, lean_object* v_i_586_, lean_object* v_v_587_){
_start:
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = lean_array_get_size(v_xs_585_);
v___x_589_ = lean_nat_dec_lt(v_i_586_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v_this_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_this_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_590_, 0, v_v_587_);
lean_ctor_set(v_this_590_, 1, v_xs_585_);
v___x_591_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_592_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__1));
v___x_593_ = lean_unsigned_to_nat(463u);
v___x_594_ = lean_unsigned_to_nat(4u);
v___x_595_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__2));
v___x_596_ = l_Nat_reprFast(v_i_586_);
v___x_597_ = lean_string_append(v___x_595_, v___x_596_);
lean_dec_ref(v___x_596_);
v___x_598_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__3));
v___x_599_ = lean_string_append(v___x_597_, v___x_598_);
v___x_600_ = l_mkPanicMessageWithDecl(v___x_591_, v___x_592_, v___x_593_, v___x_594_, v___x_599_);
lean_dec_ref(v___x_599_);
v___x_601_ = l_panic___redArg(v_this_590_, v___x_600_);
lean_dec_ref_known(v_this_590_, 2);
return v___x_601_;
}
else
{
lean_object* v_e_602_; lean_object* v_xs_x27_603_; lean_object* v___x_604_; 
v_e_602_ = lean_array_fget(v_xs_585_, v_i_586_);
v_xs_x27_603_ = lean_array_fset(v_xs_585_, v_i_586_, v_v_587_);
lean_dec(v_i_586_);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v_e_602_);
lean_ctor_set(v___x_604_, 1, v_xs_x27_603_);
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l_Array_swapAt_x21(lean_object* v_00_u03b1_605_, lean_object* v_xs_606_, lean_object* v_i_607_, lean_object* v_v_608_){
_start:
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = lean_array_get_size(v_xs_606_);
v___x_610_ = lean_nat_dec_lt(v_i_607_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v_this_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_this_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_611_, 0, v_v_608_);
lean_ctor_set(v_this_611_, 1, v_xs_606_);
v___x_612_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_613_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__1));
v___x_614_ = lean_unsigned_to_nat(463u);
v___x_615_ = lean_unsigned_to_nat(4u);
v___x_616_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__2));
v___x_617_ = l_Nat_reprFast(v_i_607_);
v___x_618_ = lean_string_append(v___x_616_, v___x_617_);
lean_dec_ref(v___x_617_);
v___x_619_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__3));
v___x_620_ = lean_string_append(v___x_618_, v___x_619_);
v___x_621_ = l_mkPanicMessageWithDecl(v___x_612_, v___x_613_, v___x_614_, v___x_615_, v___x_620_);
lean_dec_ref(v___x_620_);
v___x_622_ = l_panic___redArg(v_this_611_, v___x_621_);
lean_dec_ref_known(v_this_611_, 2);
return v___x_622_;
}
else
{
lean_object* v_e_623_; lean_object* v_xs_x27_624_; lean_object* v___x_625_; 
v_e_623_ = lean_array_fget(v_xs_606_, v_i_607_);
v_xs_x27_624_ = lean_array_fset(v_xs_606_, v_i_607_, v_v_608_);
lean_dec(v_i_607_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v_e_623_);
lean_ctor_set(v___x_625_, 1, v_xs_x27_624_);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
lean_object* v_zero_628_; uint8_t v_isZero_629_; 
v_zero_628_ = lean_unsigned_to_nat(0u);
v_isZero_629_ = lean_nat_dec_eq(v_x_626_, v_zero_628_);
if (v_isZero_629_ == 1)
{
lean_dec(v_x_626_);
return v_x_627_;
}
else
{
lean_object* v_one_630_; lean_object* v_n_631_; lean_object* v___x_632_; 
v_one_630_ = lean_unsigned_to_nat(1u);
v_n_631_ = lean_nat_sub(v_x_626_, v_one_630_);
lean_dec(v_x_626_);
v___x_632_ = lean_array_pop(v_x_627_);
v_x_626_ = v_n_631_;
v_x_627_ = v___x_632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_shrink_loop(lean_object* v_00_u03b1_634_, lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(v_x_635_, v_x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___redArg(lean_object* v_xs_638_, lean_object* v_n_639_){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_array_get_size(v_xs_638_);
v___x_641_ = lean_nat_sub(v___x_640_, v_n_639_);
v___x_642_ = l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(v___x_641_, v_xs_638_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___redArg___boxed(lean_object* v_xs_643_, lean_object* v_n_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Array_shrink___redArg(v_xs_643_, v_n_644_);
lean_dec(v_n_644_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink(lean_object* v_00_u03b1_646_, lean_object* v_xs_647_, lean_object* v_n_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Array_shrink___redArg(v_xs_647_, v_n_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___boxed(lean_object* v_00_u03b1_650_, lean_object* v_xs_651_, lean_object* v_n_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Array_shrink(v_00_u03b1_650_, v_xs_651_, v_n_652_);
lean_dec(v_n_652_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Array_take___redArg(lean_object* v_xs_654_, lean_object* v_i_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = l_Array_extract___redArg(v_xs_654_, v___x_656_, v_i_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Array_take___redArg___boxed(lean_object* v_xs_658_, lean_object* v_i_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Array_take___redArg(v_xs_658_, v_i_659_);
lean_dec_ref(v_xs_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Array_take(lean_object* v_00_u03b1_661_, lean_object* v_xs_662_, lean_object* v_i_663_){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = l_Array_extract___redArg(v_xs_662_, v___x_664_, v_i_663_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Array_take___boxed(lean_object* v_00_u03b1_666_, lean_object* v_xs_667_, lean_object* v_i_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Array_take(v_00_u03b1_666_, v_xs_667_, v_i_668_);
lean_dec_ref(v_xs_667_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___redArg(lean_object* v_xs_670_, lean_object* v_i_671_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_array_get_size(v_xs_670_);
v___x_673_ = l_Array_extract___redArg(v_xs_670_, v_i_671_, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___redArg___boxed(lean_object* v_xs_674_, lean_object* v_i_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Array_drop___redArg(v_xs_674_, v_i_675_);
lean_dec_ref(v_xs_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Array_drop(lean_object* v_00_u03b1_677_, lean_object* v_xs_678_, lean_object* v_i_679_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_array_get_size(v_xs_678_);
v___x_681_ = l_Array_extract___redArg(v_xs_678_, v_i_679_, v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___boxed(lean_object* v_00_u03b1_682_, lean_object* v_xs_683_, lean_object* v_i_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Array_drop(v_00_u03b1_682_, v_xs_683_, v_i_684_);
lean_dec_ref(v_xs_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0(lean_object* v_xs_x27_686_, lean_object* v_i_687_, lean_object* v_toPure_688_, lean_object* v_v_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_array_fset(v_xs_x27_686_, v_i_687_, v_v_689_);
v___x_691_ = lean_apply_2(v_toPure_688_, lean_box(0), v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0___boxed(lean_object* v_xs_x27_692_, lean_object* v_i_693_, lean_object* v_toPure_694_, lean_object* v_v_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Array_modifyMUnsafe___redArg___lam__0(v_xs_x27_692_, v_i_693_, v_toPure_694_, v_v_695_);
lean_dec(v_i_693_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg(lean_object* v_inst_697_, lean_object* v_xs_698_, lean_object* v_i_699_, lean_object* v_f_700_){
_start:
{
lean_object* v_toApplicative_701_; lean_object* v_toBind_702_; lean_object* v_toPure_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_toApplicative_701_ = lean_ctor_get(v_inst_697_, 0);
lean_inc_ref(v_toApplicative_701_);
v_toBind_702_ = lean_ctor_get(v_inst_697_, 1);
lean_inc(v_toBind_702_);
lean_dec_ref(v_inst_697_);
v_toPure_703_ = lean_ctor_get(v_toApplicative_701_, 1);
lean_inc(v_toPure_703_);
lean_dec_ref(v_toApplicative_701_);
v___x_704_ = lean_array_get_size(v_xs_698_);
v___x_705_ = lean_nat_dec_lt(v_i_699_, v___x_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; 
lean_dec(v_toBind_702_);
lean_dec(v_f_700_);
lean_dec(v_i_699_);
v___x_706_ = lean_apply_2(v_toPure_703_, lean_box(0), v_xs_698_);
return v___x_706_;
}
else
{
lean_object* v_v_707_; lean_object* v___x_708_; lean_object* v_xs_x27_709_; lean_object* v___f_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_v_707_ = lean_array_fget(v_xs_698_, v_i_699_);
v___x_708_ = lean_box(0);
v_xs_x27_709_ = lean_array_fset(v_xs_698_, v_i_699_, v___x_708_);
v___f_710_ = lean_alloc_closure((void*)(l_Array_modifyMUnsafe___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_710_, 0, v_xs_x27_709_);
lean_closure_set(v___f_710_, 1, v_i_699_);
lean_closure_set(v___f_710_, 2, v_toPure_703_);
v___x_711_ = lean_apply_1(v_f_700_, v_v_707_);
v___x_712_ = lean_apply_4(v_toBind_702_, lean_box(0), lean_box(0), v___x_711_, v___f_710_);
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe(lean_object* v_00_u03b1_713_, lean_object* v_m_714_, lean_object* v_inst_715_, lean_object* v_xs_716_, lean_object* v_i_717_, lean_object* v_f_718_){
_start:
{
lean_object* v_toApplicative_719_; lean_object* v_toBind_720_; lean_object* v_toPure_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_toApplicative_719_ = lean_ctor_get(v_inst_715_, 0);
lean_inc_ref(v_toApplicative_719_);
v_toBind_720_ = lean_ctor_get(v_inst_715_, 1);
lean_inc(v_toBind_720_);
lean_dec_ref(v_inst_715_);
v_toPure_721_ = lean_ctor_get(v_toApplicative_719_, 1);
lean_inc(v_toPure_721_);
lean_dec_ref(v_toApplicative_719_);
v___x_722_ = lean_array_get_size(v_xs_716_);
v___x_723_ = lean_nat_dec_lt(v_i_717_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
lean_dec(v_toBind_720_);
lean_dec(v_f_718_);
lean_dec(v_i_717_);
v___x_724_ = lean_apply_2(v_toPure_721_, lean_box(0), v_xs_716_);
return v___x_724_;
}
else
{
lean_object* v_v_725_; lean_object* v___x_726_; lean_object* v_xs_x27_727_; lean_object* v___f_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_v_725_ = lean_array_fget(v_xs_716_, v_i_717_);
v___x_726_ = lean_box(0);
v_xs_x27_727_ = lean_array_fset(v_xs_716_, v_i_717_, v___x_726_);
v___f_728_ = lean_alloc_closure((void*)(l_Array_modifyMUnsafe___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_728_, 0, v_xs_x27_727_);
lean_closure_set(v___f_728_, 1, v_i_717_);
lean_closure_set(v___f_728_, 2, v_toPure_721_);
v___x_729_ = lean_apply_1(v_f_718_, v_v_725_);
v___x_730_ = lean_apply_4(v_toBind_720_, lean_box(0), lean_box(0), v___x_729_, v___f_728_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___redArg(lean_object* v_xs_731_, lean_object* v_i_732_, lean_object* v_f_733_){
_start:
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = lean_array_get_size(v_xs_731_);
v___x_735_ = lean_nat_dec_lt(v_i_732_, v___x_734_);
if (v___x_735_ == 0)
{
lean_dec(v_f_733_);
return v_xs_731_;
}
else
{
lean_object* v_v_736_; lean_object* v___x_737_; lean_object* v_xs_x27_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_v_736_ = lean_array_fget(v_xs_731_, v_i_732_);
v___x_737_ = lean_box(0);
v_xs_x27_738_ = lean_array_fset(v_xs_731_, v_i_732_, v___x_737_);
v___x_739_ = lean_apply_1(v_f_733_, v_v_736_);
v___x_740_ = lean_array_fset(v_xs_x27_738_, v_i_732_, v___x_739_);
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___redArg___boxed(lean_object* v_xs_741_, lean_object* v_i_742_, lean_object* v_f_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Array_modify___redArg(v_xs_741_, v_i_742_, v_f_743_);
lean_dec(v_i_742_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Array_modify(lean_object* v_00_u03b1_745_, lean_object* v_xs_746_, lean_object* v_i_747_, lean_object* v_f_748_){
_start:
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = lean_array_get_size(v_xs_746_);
v___x_750_ = lean_nat_dec_lt(v_i_747_, v___x_749_);
if (v___x_750_ == 0)
{
lean_dec(v_f_748_);
return v_xs_746_;
}
else
{
lean_object* v_v_751_; lean_object* v___x_752_; lean_object* v_xs_x27_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_v_751_ = lean_array_fget(v_xs_746_, v_i_747_);
v___x_752_ = lean_box(0);
v_xs_x27_753_ = lean_array_fset(v_xs_746_, v_i_747_, v___x_752_);
v___x_754_ = lean_apply_1(v_f_748_, v_v_751_);
v___x_755_ = lean_array_fset(v_xs_x27_753_, v_i_747_, v___x_754_);
return v___x_755_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___boxed(lean_object* v_00_u03b1_756_, lean_object* v_xs_757_, lean_object* v_i_758_, lean_object* v_f_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Array_modify(v_00_u03b1_756_, v_xs_757_, v_i_758_, v_f_759_);
lean_dec(v_i_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg(lean_object* v_xs_761_, lean_object* v_idx_762_, lean_object* v_f_763_){
_start:
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = lean_array_get_size(v_xs_761_);
v___x_765_ = lean_nat_dec_lt(v_idx_762_, v___x_764_);
if (v___x_765_ == 0)
{
lean_dec(v_f_763_);
return v_xs_761_;
}
else
{
lean_object* v_v_766_; lean_object* v___x_767_; lean_object* v_xs_x27_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_v_766_ = lean_array_fget(v_xs_761_, v_idx_762_);
v___x_767_ = lean_box(0);
v_xs_x27_768_ = lean_array_fset(v_xs_761_, v_idx_762_, v___x_767_);
v___x_769_ = lean_apply_1(v_f_763_, v_v_766_);
v___x_770_ = lean_array_fset(v_xs_x27_768_, v_idx_762_, v___x_769_);
return v___x_770_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg___boxed(lean_object* v_xs_771_, lean_object* v_idx_772_, lean_object* v_f_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Array_modifyOp___redArg(v_xs_771_, v_idx_772_, v_f_773_);
lean_dec(v_idx_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp(lean_object* v_00_u03b1_775_, lean_object* v_xs_776_, lean_object* v_idx_777_, lean_object* v_f_778_){
_start:
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = lean_array_get_size(v_xs_776_);
v___x_780_ = lean_nat_dec_lt(v_idx_777_, v___x_779_);
if (v___x_780_ == 0)
{
lean_dec(v_f_778_);
return v_xs_776_;
}
else
{
lean_object* v_v_781_; lean_object* v___x_782_; lean_object* v_xs_x27_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_v_781_ = lean_array_fget(v_xs_776_, v_idx_777_);
v___x_782_ = lean_box(0);
v_xs_x27_783_ = lean_array_fset(v_xs_776_, v_idx_777_, v___x_782_);
v___x_784_ = lean_apply_1(v_f_778_, v_v_781_);
v___x_785_ = lean_array_fset(v_xs_x27_783_, v_idx_777_, v___x_784_);
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___boxed(lean_object* v_00_u03b1_786_, lean_object* v_xs_787_, lean_object* v_idx_788_, lean_object* v_f_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Array_modifyOp(v_00_u03b1_786_, v_xs_787_, v_idx_788_, v_f_789_);
lean_dec(v_idx_788_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed(lean_object* v_toPure_791_, lean_object* v_i_792_, lean_object* v_inst_793_, lean_object* v_as_794_, lean_object* v_f_795_, lean_object* v_sz_796_, lean_object* v_____do__lift_797_){
_start:
{
size_t v_i_boxed_798_; size_t v_sz_boxed_799_; lean_object* v_res_800_; 
v_i_boxed_798_ = lean_unbox_usize(v_i_792_);
lean_dec(v_i_792_);
v_sz_boxed_799_ = lean_unbox_usize(v_sz_796_);
lean_dec(v_sz_796_);
v_res_800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(v_toPure_791_, v_i_boxed_798_, v_inst_793_, v_as_794_, v_f_795_, v_sz_boxed_799_, v_____do__lift_797_);
return v_res_800_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(lean_object* v_inst_801_, lean_object* v_as_802_, lean_object* v_f_803_, size_t v_sz_804_, size_t v_i_805_, lean_object* v_b_806_){
_start:
{
lean_object* v_toApplicative_807_; lean_object* v_toBind_808_; lean_object* v_toPure_809_; uint8_t v___x_810_; 
v_toApplicative_807_ = lean_ctor_get(v_inst_801_, 0);
v_toBind_808_ = lean_ctor_get(v_inst_801_, 1);
lean_inc(v_toBind_808_);
v_toPure_809_ = lean_ctor_get(v_toApplicative_807_, 1);
lean_inc(v_toPure_809_);
v___x_810_ = lean_usize_dec_lt(v_i_805_, v_sz_804_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; 
lean_dec(v_toBind_808_);
lean_dec(v_f_803_);
lean_dec_ref(v_as_802_);
lean_dec_ref(v_inst_801_);
v___x_811_ = lean_apply_2(v_toPure_809_, lean_box(0), v_b_806_);
return v___x_811_;
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___f_814_; lean_object* v_a_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_812_ = lean_box_usize(v_i_805_);
v___x_813_ = lean_box_usize(v_sz_804_);
lean_inc(v_f_803_);
lean_inc_ref(v_as_802_);
v___f_814_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_814_, 0, v_toPure_809_);
lean_closure_set(v___f_814_, 1, v___x_812_);
lean_closure_set(v___f_814_, 2, v_inst_801_);
lean_closure_set(v___f_814_, 3, v_as_802_);
lean_closure_set(v___f_814_, 4, v_f_803_);
lean_closure_set(v___f_814_, 5, v___x_813_);
v_a_815_ = lean_array_uget(v_as_802_, v_i_805_);
lean_dec_ref(v_as_802_);
v___x_816_ = lean_apply_3(v_f_803_, v_a_815_, lean_box(0), v_b_806_);
v___x_817_ = lean_apply_4(v_toBind_808_, lean_box(0), lean_box(0), v___x_816_, v___f_814_);
return v___x_817_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_801_ = stack[0].m_obj;
lean_object* v_as_802_ = stack[1].m_obj;
lean_object* v_f_803_ = stack[2].m_obj;
size_t v_sz_804_ = stack[3].m_num;
size_t v_i_805_ = stack[4].m_num;
lean_object* v_b_806_ = stack[5].m_obj;
lean_object* v_res_818_;
v_res_818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_801_, v_as_802_, v_f_803_, v_sz_804_, v_i_805_, v_b_806_);
stack->m_obj
 = v_res_818_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(lean_object* v_toPure_819_, size_t v_i_820_, lean_object* v_inst_821_, lean_object* v_as_822_, lean_object* v_f_823_, size_t v_sz_824_, lean_object* v_____do__lift_825_){
_start:
{
if (lean_obj_tag(v_____do__lift_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_827_; 
lean_dec(v_f_823_);
lean_dec_ref(v_as_822_);
lean_dec_ref(v_inst_821_);
v_a_826_ = lean_ctor_get(v_____do__lift_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v_____do__lift_825_, 1);
v___x_827_ = lean_apply_2(v_toPure_819_, lean_box(0), v_a_826_);
return v___x_827_;
}
else
{
lean_object* v_a_828_; size_t v___x_829_; size_t v___x_830_; lean_object* v___x_831_; 
lean_dec(v_toPure_819_);
v_a_828_ = lean_ctor_get(v_____do__lift_825_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v_____do__lift_825_, 1);
v___x_829_ = ((size_t)1ULL);
v___x_830_ = lean_usize_add(v_i_820_, v___x_829_);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_821_, v_as_822_, v_f_823_, v_sz_824_, v___x_830_, v_a_828_);
return v___x_831_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_819_ = stack[0].m_obj;
size_t v_i_820_ = stack[1].m_num;
lean_object* v_inst_821_ = stack[2].m_obj;
lean_object* v_as_822_ = stack[3].m_obj;
lean_object* v_f_823_ = stack[4].m_obj;
size_t v_sz_824_ = stack[5].m_num;
lean_object* v_____do__lift_825_ = stack[6].m_obj;
lean_object* v_res_832_;
v_res_832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(v_toPure_819_, v_i_820_, v_inst_821_, v_as_822_, v_f_823_, v_sz_824_, v_____do__lift_825_);
stack->m_obj
 = v_res_832_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___boxed(lean_object* v_inst_833_, lean_object* v_as_834_, lean_object* v_f_835_, lean_object* v_sz_836_, lean_object* v_i_837_, lean_object* v_b_838_){
_start:
{
size_t v_sz_boxed_839_; size_t v_i_boxed_840_; lean_object* v_res_841_; 
v_sz_boxed_839_ = lean_unbox_usize(v_sz_836_);
lean_dec(v_sz_836_);
v_i_boxed_840_ = lean_unbox_usize(v_i_837_);
lean_dec(v_i_837_);
v_res_841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_833_, v_as_834_, v_f_835_, v_sz_boxed_839_, v_i_boxed_840_, v_b_838_);
return v_res_841_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object* v_00_u03b1_842_, lean_object* v_00_u03b2_843_, lean_object* v_m_844_, lean_object* v_inst_845_, lean_object* v_as_846_, lean_object* v_f_847_, size_t v_sz_848_, size_t v_i_849_, lean_object* v_b_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_845_, v_as_846_, v_f_847_, v_sz_848_, v_i_849_, v_b_850_);
return v___x_851_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_845_ = stack[3].m_obj;
lean_object* v_as_846_ = stack[4].m_obj;
lean_object* v_f_847_ = stack[5].m_obj;
size_t v_sz_848_ = stack[6].m_num;
size_t v_i_849_ = stack[7].m_num;
lean_object* v_b_850_ = stack[8].m_obj;
lean_object* v_res_852_;
v_res_852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_845_, v_as_846_, v_f_847_, v_sz_848_, v_i_849_, v_b_850_);
stack->m_obj
 = v_res_852_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___boxed(lean_object* v_00_u03b1_853_, lean_object* v_00_u03b2_854_, lean_object* v_m_855_, lean_object* v_inst_856_, lean_object* v_as_857_, lean_object* v_f_858_, lean_object* v_sz_859_, lean_object* v_i_860_, lean_object* v_b_861_){
_start:
{
size_t v_sz_boxed_862_; size_t v_i_boxed_863_; lean_object* v_res_864_; 
v_sz_boxed_862_ = lean_unbox_usize(v_sz_859_);
lean_dec(v_sz_859_);
v_i_boxed_863_ = lean_unbox_usize(v_i_860_);
lean_dec(v_i_860_);
v_res_864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(v_00_u03b1_853_, v_00_u03b2_854_, v_m_855_, v_inst_856_, v_as_857_, v_f_858_, v_sz_boxed_862_, v_i_boxed_863_, v_b_861_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe___redArg(lean_object* v_inst_865_, lean_object* v_as_866_, lean_object* v_b_867_, lean_object* v_f_868_){
_start:
{
size_t v_sz_869_; size_t v___x_870_; lean_object* v___x_871_; 
v_sz_869_ = lean_array_size(v_as_866_);
v___x_870_ = ((size_t)0ULL);
v___x_871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_865_, v_as_866_, v_f_868_, v_sz_869_, v___x_870_, v_b_867_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe(lean_object* v_00_u03b1_872_, lean_object* v_00_u03b2_873_, lean_object* v_m_874_, lean_object* v_inst_875_, lean_object* v_as_876_, lean_object* v_b_877_, lean_object* v_f_878_){
_start:
{
size_t v_sz_879_; size_t v___x_880_; lean_object* v___x_881_; 
v_sz_879_ = lean_array_size(v_as_876_);
v___x_880_ = ((size_t)0ULL);
v___x_881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_875_, v_as_876_, v_f_878_, v_sz_879_, v___x_880_, v_b_877_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0___boxed(lean_object* v_toPure_882_, lean_object* v_inst_883_, lean_object* v_as_884_, lean_object* v_f_885_, lean_object* v_n_886_, lean_object* v_____do__lift_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Array_forIn_x27_loop___redArg___lam__0(v_toPure_882_, v_inst_883_, v_as_884_, v_f_885_, v_n_886_, v_____do__lift_887_);
lean_dec(v_n_886_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg(lean_object* v_inst_889_, lean_object* v_as_890_, lean_object* v_f_891_, lean_object* v_i_892_, lean_object* v_b_893_){
_start:
{
lean_object* v_toApplicative_894_; lean_object* v_toBind_895_; lean_object* v_toPure_896_; lean_object* v_zero_897_; uint8_t v_isZero_898_; 
v_toApplicative_894_ = lean_ctor_get(v_inst_889_, 0);
v_toBind_895_ = lean_ctor_get(v_inst_889_, 1);
lean_inc(v_toBind_895_);
v_toPure_896_ = lean_ctor_get(v_toApplicative_894_, 1);
lean_inc(v_toPure_896_);
v_zero_897_ = lean_unsigned_to_nat(0u);
v_isZero_898_ = lean_nat_dec_eq(v_i_892_, v_zero_897_);
if (v_isZero_898_ == 1)
{
lean_object* v___x_899_; 
lean_dec(v_toBind_895_);
lean_dec(v_f_891_);
lean_dec_ref(v_as_890_);
lean_dec_ref(v_inst_889_);
v___x_899_ = lean_apply_2(v_toPure_896_, lean_box(0), v_b_893_);
return v___x_899_;
}
else
{
lean_object* v_one_900_; lean_object* v_n_901_; lean_object* v___f_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_one_900_ = lean_unsigned_to_nat(1u);
v_n_901_ = lean_nat_sub(v_i_892_, v_one_900_);
lean_inc(v_n_901_);
lean_inc(v_f_891_);
lean_inc_ref(v_as_890_);
v___f_902_ = lean_alloc_closure((void*)(l_Array_forIn_x27_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_902_, 0, v_toPure_896_);
lean_closure_set(v___f_902_, 1, v_inst_889_);
lean_closure_set(v___f_902_, 2, v_as_890_);
lean_closure_set(v___f_902_, 3, v_f_891_);
lean_closure_set(v___f_902_, 4, v_n_901_);
v___x_903_ = lean_array_get_size(v_as_890_);
v___x_904_ = lean_nat_sub(v___x_903_, v_one_900_);
v___x_905_ = lean_nat_sub(v___x_904_, v_n_901_);
lean_dec(v_n_901_);
lean_dec(v___x_904_);
v___x_906_ = lean_array_fget(v_as_890_, v___x_905_);
lean_dec(v___x_905_);
lean_dec_ref(v_as_890_);
v___x_907_ = lean_apply_3(v_f_891_, v___x_906_, lean_box(0), v_b_893_);
v___x_908_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_907_, v___f_902_);
return v___x_908_;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0(lean_object* v_toPure_909_, lean_object* v_inst_910_, lean_object* v_as_911_, lean_object* v_f_912_, lean_object* v_n_913_, lean_object* v_____do__lift_914_){
_start:
{
if (lean_obj_tag(v_____do__lift_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; 
lean_dec(v_f_912_);
lean_dec_ref(v_as_911_);
lean_dec_ref(v_inst_910_);
v_a_915_ = lean_ctor_get(v_____do__lift_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v_____do__lift_914_, 1);
v___x_916_ = lean_apply_2(v_toPure_909_, lean_box(0), v_a_915_);
return v___x_916_;
}
else
{
lean_object* v_a_917_; lean_object* v___x_918_; 
lean_dec(v_toPure_909_);
v_a_917_ = lean_ctor_get(v_____do__lift_914_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v_____do__lift_914_, 1);
v___x_918_ = l_Array_forIn_x27_loop___redArg(v_inst_910_, v_as_911_, v_f_912_, v_n_913_, v_a_917_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___boxed(lean_object* v_inst_919_, lean_object* v_as_920_, lean_object* v_f_921_, lean_object* v_i_922_, lean_object* v_b_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Array_forIn_x27_loop___redArg(v_inst_919_, v_as_920_, v_f_921_, v_i_922_, v_b_923_);
lean_dec(v_i_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop(lean_object* v_00_u03b1_925_, lean_object* v_00_u03b2_926_, lean_object* v_m_927_, lean_object* v_inst_928_, lean_object* v_as_929_, lean_object* v_f_930_, lean_object* v_i_931_, lean_object* v_h_932_, lean_object* v_b_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Array_forIn_x27_loop___redArg(v_inst_928_, v_as_929_, v_f_930_, v_i_931_, v_b_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___boxed(lean_object* v_00_u03b1_935_, lean_object* v_00_u03b2_936_, lean_object* v_m_937_, lean_object* v_inst_938_, lean_object* v_as_939_, lean_object* v_f_940_, lean_object* v_i_941_, lean_object* v_h_942_, lean_object* v_b_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Array_forIn_x27_loop(v_00_u03b1_935_, v_00_u03b2_936_, v_m_937_, v_inst_938_, v_as_939_, v_f_940_, v_i_941_, v_h_942_, v_b_943_);
lean_dec(v_i_941_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_inst_945_, lean_object* v_00_u03b2_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
size_t v_sz_950_; size_t v___x_951_; lean_object* v___x_952_; 
v_sz_950_ = lean_array_size(v___y_947_);
v___x_951_ = ((size_t)0ULL);
v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_945_, v___y_947_, v___y_949_, v_sz_950_, v___x_951_, v___y_948_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_953_){
_start:
{
lean_object* v___f_954_; 
v___f_954_ = lean_alloc_closure((void*)(l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_954_, 0, v_inst_953_);
return v___f_954_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_00_u03b1_955_, lean_object* v_m_956_, lean_object* v_inst_957_){
_start:
{
lean_object* v___f_958_; 
v___f_958_ = lean_alloc_closure((void*)(l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_958_, 0, v_inst_957_);
return v___f_958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_959_, lean_object* v_inst_960_, lean_object* v_f_961_, lean_object* v_as_962_, lean_object* v_stop_963_, lean_object* v_____do__lift_964_){
_start:
{
size_t v_i_boxed_965_; size_t v_stop_boxed_966_; lean_object* v_res_967_; 
v_i_boxed_965_ = lean_unbox_usize(v_i_959_);
lean_dec(v_i_959_);
v_stop_boxed_966_ = lean_unbox_usize(v_stop_963_);
lean_dec(v_stop_963_);
v_res_967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_965_, v_inst_960_, v_f_961_, v_as_962_, v_stop_boxed_966_, v_____do__lift_964_);
return v_res_967_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(lean_object* v_inst_968_, lean_object* v_f_969_, lean_object* v_as_970_, size_t v_i_971_, size_t v_stop_972_, lean_object* v_b_973_){
_start:
{
lean_object* v_toApplicative_974_; lean_object* v_toBind_975_; lean_object* v_toPure_976_; uint8_t v___x_977_; 
v_toApplicative_974_ = lean_ctor_get(v_inst_968_, 0);
v_toBind_975_ = lean_ctor_get(v_inst_968_, 1);
lean_inc(v_toBind_975_);
v_toPure_976_ = lean_ctor_get(v_toApplicative_974_, 1);
v___x_977_ = lean_usize_dec_eq(v_i_971_, v_stop_972_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___f_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_978_ = lean_box_usize(v_i_971_);
v___x_979_ = lean_box_usize(v_stop_972_);
lean_inc_ref(v_as_970_);
lean_inc(v_f_969_);
v___f_980_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_980_, 0, v___x_978_);
lean_closure_set(v___f_980_, 1, v_inst_968_);
lean_closure_set(v___f_980_, 2, v_f_969_);
lean_closure_set(v___f_980_, 3, v_as_970_);
lean_closure_set(v___f_980_, 4, v___x_979_);
v___x_981_ = lean_array_uget(v_as_970_, v_i_971_);
lean_dec_ref(v_as_970_);
v___x_982_ = lean_apply_2(v_f_969_, v_b_973_, v___x_981_);
v___x_983_ = lean_apply_4(v_toBind_975_, lean_box(0), lean_box(0), v___x_982_, v___f_980_);
return v___x_983_;
}
else
{
lean_object* v___x_984_; 
lean_inc(v_toPure_976_);
lean_dec(v_toBind_975_);
lean_dec_ref(v_as_970_);
lean_dec(v_f_969_);
lean_dec_ref(v_inst_968_);
v___x_984_ = lean_apply_2(v_toPure_976_, lean_box(0), v_b_973_);
return v___x_984_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_968_ = stack[0].m_obj;
lean_object* v_f_969_ = stack[1].m_obj;
lean_object* v_as_970_ = stack[2].m_obj;
size_t v_i_971_ = stack[3].m_num;
size_t v_stop_972_ = stack[4].m_num;
lean_object* v_b_973_ = stack[5].m_obj;
lean_object* v_res_985_;
v_res_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_968_, v_f_969_, v_as_970_, v_i_971_, v_stop_972_, v_b_973_);
stack->m_obj
 = v_res_985_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_986_, lean_object* v_inst_987_, lean_object* v_f_988_, lean_object* v_as_989_, size_t v_stop_990_, lean_object* v_____do__lift_991_){
_start:
{
size_t v___x_992_; size_t v___x_993_; lean_object* v___x_994_; 
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_add(v_i_986_, v___x_992_);
v___x_994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_987_, v_f_988_, v_as_989_, v___x_993_, v_stop_990_, v_____do__lift_991_);
return v___x_994_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_i_986_ = stack[0].m_num;
lean_object* v_inst_987_ = stack[1].m_obj;
lean_object* v_f_988_ = stack[2].m_obj;
lean_object* v_as_989_ = stack[3].m_obj;
size_t v_stop_990_ = stack[4].m_num;
lean_object* v_____do__lift_991_ = stack[5].m_obj;
lean_object* v_res_995_;
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(v_i_986_, v_inst_987_, v_f_988_, v_as_989_, v_stop_990_, v_____do__lift_991_);
stack->m_obj
 = v_res_995_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_996_, lean_object* v_f_997_, lean_object* v_as_998_, lean_object* v_i_999_, lean_object* v_stop_1000_, lean_object* v_b_1001_){
_start:
{
size_t v_i_boxed_1002_; size_t v_stop_boxed_1003_; lean_object* v_res_1004_; 
v_i_boxed_1002_ = lean_unbox_usize(v_i_999_);
lean_dec(v_i_999_);
v_stop_boxed_1003_ = lean_unbox_usize(v_stop_1000_);
lean_dec(v_stop_1000_);
v_res_1004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_996_, v_f_997_, v_as_998_, v_i_boxed_1002_, v_stop_boxed_1003_, v_b_1001_);
return v_res_1004_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object* v_00_u03b1_1005_, lean_object* v_00_u03b2_1006_, lean_object* v_m_1007_, lean_object* v_inst_1008_, lean_object* v_f_1009_, lean_object* v_as_1010_, size_t v_i_1011_, size_t v_stop_1012_, lean_object* v_b_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1008_, v_f_1009_, v_as_1010_, v_i_1011_, v_stop_1012_, v_b_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1008_ = stack[3].m_obj;
lean_object* v_f_1009_ = stack[4].m_obj;
lean_object* v_as_1010_ = stack[5].m_obj;
size_t v_i_1011_ = stack[6].m_num;
size_t v_stop_1012_ = stack[7].m_num;
lean_object* v_b_1013_ = stack[8].m_obj;
lean_object* v_res_1015_;
v_res_1015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1008_, v_f_1009_, v_as_1010_, v_i_1011_, v_stop_1012_, v_b_1013_);
stack->m_obj
 = v_res_1015_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b1_1016_, lean_object* v_00_u03b2_1017_, lean_object* v_m_1018_, lean_object* v_inst_1019_, lean_object* v_f_1020_, lean_object* v_as_1021_, lean_object* v_i_1022_, lean_object* v_stop_1023_, lean_object* v_b_1024_){
_start:
{
size_t v_i_boxed_1025_; size_t v_stop_boxed_1026_; lean_object* v_res_1027_; 
v_i_boxed_1025_ = lean_unbox_usize(v_i_1022_);
lean_dec(v_i_1022_);
v_stop_boxed_1026_ = lean_unbox_usize(v_stop_1023_);
lean_dec(v_stop_1023_);
v_res_1027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(v_00_u03b1_1016_, v_00_u03b2_1017_, v_m_1018_, v_inst_1019_, v_f_1020_, v_as_1021_, v_i_boxed_1025_, v_stop_boxed_1026_, v_b_1024_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg(lean_object* v_inst_1028_, lean_object* v_f_1029_, lean_object* v_init_1030_, lean_object* v_as_1031_, lean_object* v_start_1032_, lean_object* v_stop_1033_){
_start:
{
lean_object* v_toApplicative_1034_; lean_object* v_toPure_1035_; uint8_t v___x_1036_; 
v_toApplicative_1034_ = lean_ctor_get(v_inst_1028_, 0);
v_toPure_1035_ = lean_ctor_get(v_toApplicative_1034_, 1);
v___x_1036_ = lean_nat_dec_lt(v_start_1032_, v_stop_1033_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; 
lean_inc(v_toPure_1035_);
lean_dec_ref(v_as_1031_);
lean_dec(v_f_1029_);
lean_dec_ref(v_inst_1028_);
v___x_1037_ = lean_apply_2(v_toPure_1035_, lean_box(0), v_init_1030_);
return v___x_1037_;
}
else
{
lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = lean_array_get_size(v_as_1031_);
v___x_1039_ = lean_nat_dec_le(v_stop_1033_, v___x_1038_);
if (v___x_1039_ == 0)
{
uint8_t v___x_1040_; 
v___x_1040_ = lean_nat_dec_lt(v_start_1032_, v___x_1038_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_inc(v_toPure_1035_);
lean_dec_ref(v_as_1031_);
lean_dec(v_f_1029_);
lean_dec_ref(v_inst_1028_);
v___x_1041_ = lean_apply_2(v_toPure_1035_, lean_box(0), v_init_1030_);
return v___x_1041_;
}
else
{
size_t v___x_1042_; size_t v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = lean_usize_of_nat(v_start_1032_);
v___x_1043_ = lean_usize_of_nat(v___x_1038_);
v___x_1044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1028_, v_f_1029_, v_as_1031_, v___x_1042_, v___x_1043_, v_init_1030_);
return v___x_1044_;
}
}
else
{
size_t v___x_1045_; size_t v___x_1046_; lean_object* v___x_1047_; 
v___x_1045_ = lean_usize_of_nat(v_start_1032_);
v___x_1046_ = lean_usize_of_nat(v_stop_1033_);
v___x_1047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1028_, v_f_1029_, v_as_1031_, v___x_1045_, v___x_1046_, v_init_1030_);
return v___x_1047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg___boxed(lean_object* v_inst_1048_, lean_object* v_f_1049_, lean_object* v_init_1050_, lean_object* v_as_1051_, lean_object* v_start_1052_, lean_object* v_stop_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Array_foldlMUnsafe___redArg(v_inst_1048_, v_f_1049_, v_init_1050_, v_as_1051_, v_start_1052_, v_stop_1053_);
lean_dec(v_stop_1053_);
lean_dec(v_start_1052_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe(lean_object* v_00_u03b1_1055_, lean_object* v_00_u03b2_1056_, lean_object* v_m_1057_, lean_object* v_inst_1058_, lean_object* v_f_1059_, lean_object* v_init_1060_, lean_object* v_as_1061_, lean_object* v_start_1062_, lean_object* v_stop_1063_){
_start:
{
lean_object* v_toApplicative_1064_; lean_object* v_toPure_1065_; uint8_t v___x_1066_; 
v_toApplicative_1064_ = lean_ctor_get(v_inst_1058_, 0);
v_toPure_1065_ = lean_ctor_get(v_toApplicative_1064_, 1);
v___x_1066_ = lean_nat_dec_lt(v_start_1062_, v_stop_1063_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
lean_inc(v_toPure_1065_);
lean_dec_ref(v_as_1061_);
lean_dec(v_f_1059_);
lean_dec_ref(v_inst_1058_);
v___x_1067_ = lean_apply_2(v_toPure_1065_, lean_box(0), v_init_1060_);
return v___x_1067_;
}
else
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = lean_array_get_size(v_as_1061_);
v___x_1069_ = lean_nat_dec_le(v_stop_1063_, v___x_1068_);
if (v___x_1069_ == 0)
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_nat_dec_lt(v_start_1062_, v___x_1068_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; 
lean_inc(v_toPure_1065_);
lean_dec_ref(v_as_1061_);
lean_dec(v_f_1059_);
lean_dec_ref(v_inst_1058_);
v___x_1071_ = lean_apply_2(v_toPure_1065_, lean_box(0), v_init_1060_);
return v___x_1071_;
}
else
{
size_t v___x_1072_; size_t v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = lean_usize_of_nat(v_start_1062_);
v___x_1073_ = lean_usize_of_nat(v___x_1068_);
v___x_1074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1058_, v_f_1059_, v_as_1061_, v___x_1072_, v___x_1073_, v_init_1060_);
return v___x_1074_;
}
}
else
{
size_t v___x_1075_; size_t v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = lean_usize_of_nat(v_start_1062_);
v___x_1076_ = lean_usize_of_nat(v_stop_1063_);
v___x_1077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1058_, v_f_1059_, v_as_1061_, v___x_1075_, v___x_1076_, v_init_1060_);
return v___x_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___boxed(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_m_1080_, lean_object* v_inst_1081_, lean_object* v_f_1082_, lean_object* v_init_1083_, lean_object* v_as_1084_, lean_object* v_start_1085_, lean_object* v_stop_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Array_foldlMUnsafe(v_00_u03b1_1078_, v_00_u03b2_1079_, v_m_1080_, v_inst_1081_, v_f_1082_, v_init_1083_, v_as_1084_, v_start_1085_, v_stop_1086_);
lean_dec(v_stop_1086_);
lean_dec(v_start_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_1088_, lean_object* v_inst_1089_, lean_object* v_f_1090_, lean_object* v_as_1091_, lean_object* v_stop_1092_, lean_object* v_n_1093_, lean_object* v_____do__lift_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Array_foldlM_loop___redArg___lam__0(v_j_1088_, v_inst_1089_, v_f_1090_, v_as_1091_, v_stop_1092_, v_n_1093_, v_____do__lift_1094_);
lean_dec(v_n_1093_);
lean_dec(v_j_1088_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg(lean_object* v_inst_1096_, lean_object* v_f_1097_, lean_object* v_as_1098_, lean_object* v_stop_1099_, lean_object* v_i_1100_, lean_object* v_j_1101_, lean_object* v_b_1102_){
_start:
{
lean_object* v_toApplicative_1103_; lean_object* v_toBind_1104_; lean_object* v_toPure_1105_; uint8_t v___x_1106_; 
v_toApplicative_1103_ = lean_ctor_get(v_inst_1096_, 0);
v_toBind_1104_ = lean_ctor_get(v_inst_1096_, 1);
lean_inc(v_toBind_1104_);
v_toPure_1105_ = lean_ctor_get(v_toApplicative_1103_, 1);
v___x_1106_ = lean_nat_dec_lt(v_j_1101_, v_stop_1099_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; 
lean_inc(v_toPure_1105_);
lean_dec(v_toBind_1104_);
lean_dec(v_j_1101_);
lean_dec(v_stop_1099_);
lean_dec_ref(v_as_1098_);
lean_dec(v_f_1097_);
lean_dec_ref(v_inst_1096_);
v___x_1107_ = lean_apply_2(v_toPure_1105_, lean_box(0), v_b_1102_);
return v___x_1107_;
}
else
{
lean_object* v_zero_1108_; uint8_t v_isZero_1109_; 
v_zero_1108_ = lean_unsigned_to_nat(0u);
v_isZero_1109_ = lean_nat_dec_eq(v_i_1100_, v_zero_1108_);
if (v_isZero_1109_ == 1)
{
lean_object* v___x_1110_; 
lean_inc(v_toPure_1105_);
lean_dec(v_toBind_1104_);
lean_dec(v_j_1101_);
lean_dec(v_stop_1099_);
lean_dec_ref(v_as_1098_);
lean_dec(v_f_1097_);
lean_dec_ref(v_inst_1096_);
v___x_1110_ = lean_apply_2(v_toPure_1105_, lean_box(0), v_b_1102_);
return v___x_1110_;
}
else
{
lean_object* v_one_1111_; lean_object* v_n_1112_; lean_object* v___f_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v_one_1111_ = lean_unsigned_to_nat(1u);
v_n_1112_ = lean_nat_sub(v_i_1100_, v_one_1111_);
lean_inc_ref(v_as_1098_);
lean_inc(v_f_1097_);
lean_inc(v_j_1101_);
v___f_1113_ = lean_alloc_closure((void*)(l_Array_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1113_, 0, v_j_1101_);
lean_closure_set(v___f_1113_, 1, v_inst_1096_);
lean_closure_set(v___f_1113_, 2, v_f_1097_);
lean_closure_set(v___f_1113_, 3, v_as_1098_);
lean_closure_set(v___f_1113_, 4, v_stop_1099_);
lean_closure_set(v___f_1113_, 5, v_n_1112_);
v___x_1114_ = lean_array_fget(v_as_1098_, v_j_1101_);
lean_dec(v_j_1101_);
lean_dec_ref(v_as_1098_);
v___x_1115_ = lean_apply_2(v_f_1097_, v_b_1102_, v___x_1114_);
v___x_1116_ = lean_apply_4(v_toBind_1104_, lean_box(0), lean_box(0), v___x_1115_, v___f_1113_);
return v___x_1116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0(lean_object* v_j_1117_, lean_object* v_inst_1118_, lean_object* v_f_1119_, lean_object* v_as_1120_, lean_object* v_stop_1121_, lean_object* v_n_1122_, lean_object* v_____do__lift_1123_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = lean_unsigned_to_nat(1u);
v___x_1125_ = lean_nat_add(v_j_1117_, v___x_1124_);
v___x_1126_ = l_Array_foldlM_loop___redArg(v_inst_1118_, v_f_1119_, v_as_1120_, v_stop_1121_, v_n_1122_, v___x_1125_, v_____do__lift_1123_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___boxed(lean_object* v_inst_1127_, lean_object* v_f_1128_, lean_object* v_as_1129_, lean_object* v_stop_1130_, lean_object* v_i_1131_, lean_object* v_j_1132_, lean_object* v_b_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Array_foldlM_loop___redArg(v_inst_1127_, v_f_1128_, v_as_1129_, v_stop_1130_, v_i_1131_, v_j_1132_, v_b_1133_);
lean_dec(v_i_1131_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop(lean_object* v_00_u03b1_1135_, lean_object* v_00_u03b2_1136_, lean_object* v_m_1137_, lean_object* v_inst_1138_, lean_object* v_f_1139_, lean_object* v_as_1140_, lean_object* v_stop_1141_, lean_object* v_h_1142_, lean_object* v_i_1143_, lean_object* v_j_1144_, lean_object* v_b_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Array_foldlM_loop___redArg(v_inst_1138_, v_f_1139_, v_as_1140_, v_stop_1141_, v_i_1143_, v_j_1144_, v_b_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___boxed(lean_object* v_00_u03b1_1147_, lean_object* v_00_u03b2_1148_, lean_object* v_m_1149_, lean_object* v_inst_1150_, lean_object* v_f_1151_, lean_object* v_as_1152_, lean_object* v_stop_1153_, lean_object* v_h_1154_, lean_object* v_i_1155_, lean_object* v_j_1156_, lean_object* v_b_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Array_foldlM_loop(v_00_u03b1_1147_, v_00_u03b2_1148_, v_m_1149_, v_inst_1150_, v_f_1151_, v_as_1152_, v_stop_1153_, v_h_1154_, v_i_1155_, v_j_1156_, v_b_1157_);
lean_dec(v_i_1155_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_inst_1159_, lean_object* v_f_1160_, lean_object* v_as_1161_, lean_object* v___x_1162_, lean_object* v_stop_1163_, lean_object* v_____do__lift_1164_){
_start:
{
size_t v___x_63__boxed_1165_; size_t v_stop_boxed_1166_; lean_object* v_res_1167_; 
v___x_63__boxed_1165_ = lean_unbox_usize(v___x_1162_);
lean_dec(v___x_1162_);
v_stop_boxed_1166_ = lean_unbox_usize(v_stop_1163_);
lean_dec(v_stop_1163_);
v_res_1167_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(v_inst_1159_, v_f_1160_, v_as_1161_, v___x_63__boxed_1165_, v_stop_boxed_1166_, v_____do__lift_1164_);
return v_res_1167_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(lean_object* v_inst_1168_, lean_object* v_f_1169_, lean_object* v_as_1170_, size_t v_i_1171_, size_t v_stop_1172_, lean_object* v_b_1173_){
_start:
{
lean_object* v_toApplicative_1174_; lean_object* v_toBind_1175_; lean_object* v_toPure_1176_; uint8_t v___x_1177_; 
v_toApplicative_1174_ = lean_ctor_get(v_inst_1168_, 0);
v_toBind_1175_ = lean_ctor_get(v_inst_1168_, 1);
lean_inc(v_toBind_1175_);
v_toPure_1176_ = lean_ctor_get(v_toApplicative_1174_, 1);
v___x_1177_ = lean_usize_dec_eq(v_i_1171_, v_stop_1172_);
if (v___x_1177_ == 0)
{
size_t v___x_1178_; size_t v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___f_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_sub(v_i_1171_, v___x_1178_);
v___x_1180_ = lean_box_usize(v___x_1179_);
v___x_1181_ = lean_box_usize(v_stop_1172_);
lean_inc_ref(v_as_1170_);
lean_inc(v_f_1169_);
v___f_1182_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1182_, 0, v_inst_1168_);
lean_closure_set(v___f_1182_, 1, v_f_1169_);
lean_closure_set(v___f_1182_, 2, v_as_1170_);
lean_closure_set(v___f_1182_, 3, v___x_1180_);
lean_closure_set(v___f_1182_, 4, v___x_1181_);
v___x_1183_ = lean_array_uget(v_as_1170_, v___x_1179_);
lean_dec_ref(v_as_1170_);
v___x_1184_ = lean_apply_2(v_f_1169_, v___x_1183_, v_b_1173_);
v___x_1185_ = lean_apply_4(v_toBind_1175_, lean_box(0), lean_box(0), v___x_1184_, v___f_1182_);
return v___x_1185_;
}
else
{
lean_object* v___x_1186_; 
lean_inc(v_toPure_1176_);
lean_dec(v_toBind_1175_);
lean_dec_ref(v_as_1170_);
lean_dec(v_f_1169_);
lean_dec_ref(v_inst_1168_);
v___x_1186_ = lean_apply_2(v_toPure_1176_, lean_box(0), v_b_1173_);
return v___x_1186_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1168_ = stack[0].m_obj;
lean_object* v_f_1169_ = stack[1].m_obj;
lean_object* v_as_1170_ = stack[2].m_obj;
size_t v_i_1171_ = stack[3].m_num;
size_t v_stop_1172_ = stack[4].m_num;
lean_object* v_b_1173_ = stack[5].m_obj;
lean_object* v_res_1187_;
v_res_1187_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1168_, v_f_1169_, v_as_1170_, v_i_1171_, v_stop_1172_, v_b_1173_);
stack->m_obj
 = v_res_1187_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(lean_object* v_inst_1188_, lean_object* v_f_1189_, lean_object* v_as_1190_, size_t v___x_1191_, size_t v_stop_1192_, lean_object* v_____do__lift_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1188_, v_f_1189_, v_as_1190_, v___x_1191_, v_stop_1192_, v_____do__lift_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1188_ = stack[0].m_obj;
lean_object* v_f_1189_ = stack[1].m_obj;
lean_object* v_as_1190_ = stack[2].m_obj;
size_t v___x_1191_ = stack[3].m_num;
size_t v_stop_1192_ = stack[4].m_num;
lean_object* v_____do__lift_1193_ = stack[5].m_obj;
lean_object* v_res_1195_;
v_res_1195_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(v_inst_1188_, v_f_1189_, v_as_1190_, v___x_1191_, v_stop_1192_, v_____do__lift_1193_);
stack->m_obj
 = v_res_1195_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___boxed(lean_object* v_inst_1196_, lean_object* v_f_1197_, lean_object* v_as_1198_, lean_object* v_i_1199_, lean_object* v_stop_1200_, lean_object* v_b_1201_){
_start:
{
size_t v_i_boxed_1202_; size_t v_stop_boxed_1203_; lean_object* v_res_1204_; 
v_i_boxed_1202_ = lean_unbox_usize(v_i_1199_);
lean_dec(v_i_1199_);
v_stop_boxed_1203_ = lean_unbox_usize(v_stop_1200_);
lean_dec(v_stop_1200_);
v_res_1204_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1196_, v_f_1197_, v_as_1198_, v_i_boxed_1202_, v_stop_boxed_1203_, v_b_1201_);
return v_res_1204_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object* v_00_u03b1_1205_, lean_object* v_00_u03b2_1206_, lean_object* v_m_1207_, lean_object* v_inst_1208_, lean_object* v_f_1209_, lean_object* v_as_1210_, size_t v_i_1211_, size_t v_stop_1212_, lean_object* v_b_1213_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1208_, v_f_1209_, v_as_1210_, v_i_1211_, v_stop_1212_, v_b_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1208_ = stack[3].m_obj;
lean_object* v_f_1209_ = stack[4].m_obj;
lean_object* v_as_1210_ = stack[5].m_obj;
size_t v_i_1211_ = stack[6].m_num;
size_t v_stop_1212_ = stack[7].m_num;
lean_object* v_b_1213_ = stack[8].m_obj;
lean_object* v_res_1215_;
v_res_1215_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1208_, v_f_1209_, v_as_1210_, v_i_1211_, v_stop_1212_, v_b_1213_);
stack->m_obj
 = v_res_1215_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___boxed(lean_object* v_00_u03b1_1216_, lean_object* v_00_u03b2_1217_, lean_object* v_m_1218_, lean_object* v_inst_1219_, lean_object* v_f_1220_, lean_object* v_as_1221_, lean_object* v_i_1222_, lean_object* v_stop_1223_, lean_object* v_b_1224_){
_start:
{
size_t v_i_boxed_1225_; size_t v_stop_boxed_1226_; lean_object* v_res_1227_; 
v_i_boxed_1225_ = lean_unbox_usize(v_i_1222_);
lean_dec(v_i_1222_);
v_stop_boxed_1226_ = lean_unbox_usize(v_stop_1223_);
lean_dec(v_stop_1223_);
v_res_1227_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(v_00_u03b1_1216_, v_00_u03b2_1217_, v_m_1218_, v_inst_1219_, v_f_1220_, v_as_1221_, v_i_boxed_1225_, v_stop_boxed_1226_, v_b_1224_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg(lean_object* v_inst_1228_, lean_object* v_f_1229_, lean_object* v_init_1230_, lean_object* v_as_1231_, lean_object* v_start_1232_, lean_object* v_stop_1233_){
_start:
{
lean_object* v_toApplicative_1234_; lean_object* v_toPure_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v_toApplicative_1234_ = lean_ctor_get(v_inst_1228_, 0);
v_toPure_1235_ = lean_ctor_get(v_toApplicative_1234_, 1);
v___x_1236_ = lean_array_get_size(v_as_1231_);
v___x_1237_ = lean_nat_dec_le(v_start_1232_, v___x_1236_);
if (v___x_1237_ == 0)
{
uint8_t v___x_1238_; 
v___x_1238_ = lean_nat_dec_lt(v_stop_1233_, v___x_1236_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_inc(v_toPure_1235_);
lean_dec_ref(v_as_1231_);
lean_dec(v_f_1229_);
lean_dec_ref(v_inst_1228_);
v___x_1239_ = lean_apply_2(v_toPure_1235_, lean_box(0), v_init_1230_);
return v___x_1239_;
}
else
{
size_t v___x_1240_; size_t v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_usize_of_nat(v___x_1236_);
v___x_1241_ = lean_usize_of_nat(v_stop_1233_);
v___x_1242_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1228_, v_f_1229_, v_as_1231_, v___x_1240_, v___x_1241_, v_init_1230_);
return v___x_1242_;
}
}
else
{
uint8_t v___x_1243_; 
v___x_1243_ = lean_nat_dec_lt(v_stop_1233_, v_start_1232_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
lean_inc(v_toPure_1235_);
lean_dec_ref(v_as_1231_);
lean_dec(v_f_1229_);
lean_dec_ref(v_inst_1228_);
v___x_1244_ = lean_apply_2(v_toPure_1235_, lean_box(0), v_init_1230_);
return v___x_1244_;
}
else
{
size_t v___x_1245_; size_t v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_usize_of_nat(v_start_1232_);
v___x_1246_ = lean_usize_of_nat(v_stop_1233_);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1228_, v_f_1229_, v_as_1231_, v___x_1245_, v___x_1246_, v_init_1230_);
return v___x_1247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg___boxed(lean_object* v_inst_1248_, lean_object* v_f_1249_, lean_object* v_init_1250_, lean_object* v_as_1251_, lean_object* v_start_1252_, lean_object* v_stop_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Array_foldrMUnsafe___redArg(v_inst_1248_, v_f_1249_, v_init_1250_, v_as_1251_, v_start_1252_, v_stop_1253_);
lean_dec(v_stop_1253_);
lean_dec(v_start_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe(lean_object* v_00_u03b1_1255_, lean_object* v_00_u03b2_1256_, lean_object* v_m_1257_, lean_object* v_inst_1258_, lean_object* v_f_1259_, lean_object* v_init_1260_, lean_object* v_as_1261_, lean_object* v_start_1262_, lean_object* v_stop_1263_){
_start:
{
lean_object* v_toApplicative_1264_; lean_object* v_toPure_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v_toApplicative_1264_ = lean_ctor_get(v_inst_1258_, 0);
v_toPure_1265_ = lean_ctor_get(v_toApplicative_1264_, 1);
v___x_1266_ = lean_array_get_size(v_as_1261_);
v___x_1267_ = lean_nat_dec_le(v_start_1262_, v___x_1266_);
if (v___x_1267_ == 0)
{
uint8_t v___x_1268_; 
v___x_1268_ = lean_nat_dec_lt(v_stop_1263_, v___x_1266_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; 
lean_inc(v_toPure_1265_);
lean_dec_ref(v_as_1261_);
lean_dec(v_f_1259_);
lean_dec_ref(v_inst_1258_);
v___x_1269_ = lean_apply_2(v_toPure_1265_, lean_box(0), v_init_1260_);
return v___x_1269_;
}
else
{
size_t v___x_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_usize_of_nat(v___x_1266_);
v___x_1271_ = lean_usize_of_nat(v_stop_1263_);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1258_, v_f_1259_, v_as_1261_, v___x_1270_, v___x_1271_, v_init_1260_);
return v___x_1272_;
}
}
else
{
uint8_t v___x_1273_; 
v___x_1273_ = lean_nat_dec_lt(v_stop_1263_, v_start_1262_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; 
lean_inc(v_toPure_1265_);
lean_dec_ref(v_as_1261_);
lean_dec(v_f_1259_);
lean_dec_ref(v_inst_1258_);
v___x_1274_ = lean_apply_2(v_toPure_1265_, lean_box(0), v_init_1260_);
return v___x_1274_;
}
else
{
size_t v___x_1275_; size_t v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = lean_usize_of_nat(v_start_1262_);
v___x_1276_ = lean_usize_of_nat(v_stop_1263_);
v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1258_, v_f_1259_, v_as_1261_, v___x_1275_, v___x_1276_, v_init_1260_);
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___boxed(lean_object* v_00_u03b1_1278_, lean_object* v_00_u03b2_1279_, lean_object* v_m_1280_, lean_object* v_inst_1281_, lean_object* v_f_1282_, lean_object* v_init_1283_, lean_object* v_as_1284_, lean_object* v_start_1285_, lean_object* v_stop_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Array_foldrMUnsafe(v_00_u03b1_1278_, v_00_u03b2_1279_, v_m_1280_, v_inst_1281_, v_f_1282_, v_init_1283_, v_as_1284_, v_start_1285_, v_stop_1286_);
lean_dec(v_stop_1286_);
lean_dec(v_start_1285_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0___boxed(lean_object* v_inst_1288_, lean_object* v_f_1289_, lean_object* v_as_1290_, lean_object* v_stop_1291_, lean_object* v_n_1292_, lean_object* v_____do__lift_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Array_foldrM_fold___redArg___lam__0(v_inst_1288_, v_f_1289_, v_as_1290_, v_stop_1291_, v_n_1292_, v_____do__lift_1293_);
lean_dec(v_n_1292_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg(lean_object* v_inst_1295_, lean_object* v_f_1296_, lean_object* v_as_1297_, lean_object* v_stop_1298_, lean_object* v_i_1299_, lean_object* v_b_1300_){
_start:
{
lean_object* v_toApplicative_1301_; lean_object* v_toBind_1302_; lean_object* v_toPure_1303_; uint8_t v___x_1304_; 
v_toApplicative_1301_ = lean_ctor_get(v_inst_1295_, 0);
v_toBind_1302_ = lean_ctor_get(v_inst_1295_, 1);
lean_inc(v_toBind_1302_);
v_toPure_1303_ = lean_ctor_get(v_toApplicative_1301_, 1);
v___x_1304_ = lean_nat_dec_eq(v_i_1299_, v_stop_1298_);
if (v___x_1304_ == 0)
{
lean_object* v_zero_1305_; uint8_t v_isZero_1306_; 
v_zero_1305_ = lean_unsigned_to_nat(0u);
v_isZero_1306_ = lean_nat_dec_eq(v_i_1299_, v_zero_1305_);
if (v_isZero_1306_ == 1)
{
lean_object* v___x_1307_; 
lean_inc(v_toPure_1303_);
lean_dec(v_toBind_1302_);
lean_dec(v_stop_1298_);
lean_dec_ref(v_as_1297_);
lean_dec(v_f_1296_);
lean_dec_ref(v_inst_1295_);
v___x_1307_ = lean_apply_2(v_toPure_1303_, lean_box(0), v_b_1300_);
return v___x_1307_;
}
else
{
lean_object* v_one_1308_; lean_object* v_n_1309_; lean_object* v___f_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_one_1308_ = lean_unsigned_to_nat(1u);
v_n_1309_ = lean_nat_sub(v_i_1299_, v_one_1308_);
lean_inc(v_n_1309_);
lean_inc_ref(v_as_1297_);
lean_inc(v_f_1296_);
v___f_1310_ = lean_alloc_closure((void*)(l_Array_foldrM_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1310_, 0, v_inst_1295_);
lean_closure_set(v___f_1310_, 1, v_f_1296_);
lean_closure_set(v___f_1310_, 2, v_as_1297_);
lean_closure_set(v___f_1310_, 3, v_stop_1298_);
lean_closure_set(v___f_1310_, 4, v_n_1309_);
v___x_1311_ = lean_array_fget(v_as_1297_, v_n_1309_);
lean_dec(v_n_1309_);
lean_dec_ref(v_as_1297_);
v___x_1312_ = lean_apply_2(v_f_1296_, v___x_1311_, v_b_1300_);
v___x_1313_ = lean_apply_4(v_toBind_1302_, lean_box(0), lean_box(0), v___x_1312_, v___f_1310_);
return v___x_1313_;
}
}
else
{
lean_object* v___x_1314_; 
lean_inc(v_toPure_1303_);
lean_dec(v_toBind_1302_);
lean_dec(v_stop_1298_);
lean_dec_ref(v_as_1297_);
lean_dec(v_f_1296_);
lean_dec_ref(v_inst_1295_);
v___x_1314_ = lean_apply_2(v_toPure_1303_, lean_box(0), v_b_1300_);
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0(lean_object* v_inst_1315_, lean_object* v_f_1316_, lean_object* v_as_1317_, lean_object* v_stop_1318_, lean_object* v_n_1319_, lean_object* v_____do__lift_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Array_foldrM_fold___redArg(v_inst_1315_, v_f_1316_, v_as_1317_, v_stop_1318_, v_n_1319_, v_____do__lift_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___boxed(lean_object* v_inst_1322_, lean_object* v_f_1323_, lean_object* v_as_1324_, lean_object* v_stop_1325_, lean_object* v_i_1326_, lean_object* v_b_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Array_foldrM_fold___redArg(v_inst_1322_, v_f_1323_, v_as_1324_, v_stop_1325_, v_i_1326_, v_b_1327_);
lean_dec(v_i_1326_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold(lean_object* v_00_u03b1_1329_, lean_object* v_00_u03b2_1330_, lean_object* v_m_1331_, lean_object* v_inst_1332_, lean_object* v_f_1333_, lean_object* v_as_1334_, lean_object* v_stop_1335_, lean_object* v_i_1336_, lean_object* v_h_1337_, lean_object* v_b_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Array_foldrM_fold___redArg(v_inst_1332_, v_f_1333_, v_as_1334_, v_stop_1335_, v_i_1336_, v_b_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___boxed(lean_object* v_00_u03b1_1340_, lean_object* v_00_u03b2_1341_, lean_object* v_m_1342_, lean_object* v_inst_1343_, lean_object* v_f_1344_, lean_object* v_as_1345_, lean_object* v_stop_1346_, lean_object* v_i_1347_, lean_object* v_h_1348_, lean_object* v_b_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Array_foldrM_fold(v_00_u03b1_1340_, v_00_u03b2_1341_, v_m_1342_, v_inst_1343_, v_f_1344_, v_as_1345_, v_stop_1346_, v_i_1347_, v_h_1348_, v_b_1349_);
lean_dec(v_i_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed(lean_object* v_i_1351_, lean_object* v_bs_x27_1352_, lean_object* v_inst_1353_, lean_object* v_f_1354_, lean_object* v_sz_1355_, lean_object* v_vNew_1356_){
_start:
{
size_t v_i_boxed_1357_; size_t v_sz_boxed_1358_; lean_object* v_res_1359_; 
v_i_boxed_1357_ = lean_unbox_usize(v_i_1351_);
lean_dec(v_i_1351_);
v_sz_boxed_1358_ = lean_unbox_usize(v_sz_1355_);
lean_dec(v_sz_1355_);
v_res_1359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(v_i_boxed_1357_, v_bs_x27_1352_, v_inst_1353_, v_f_1354_, v_sz_boxed_1358_, v_vNew_1356_);
return v_res_1359_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(lean_object* v_inst_1360_, lean_object* v_f_1361_, size_t v_sz_1362_, size_t v_i_1363_, lean_object* v_bs_1364_){
_start:
{
lean_object* v_toApplicative_1365_; lean_object* v_toBind_1366_; lean_object* v_toPure_1367_; uint8_t v___x_1368_; 
v_toApplicative_1365_ = lean_ctor_get(v_inst_1360_, 0);
v_toBind_1366_ = lean_ctor_get(v_inst_1360_, 1);
lean_inc(v_toBind_1366_);
v_toPure_1367_ = lean_ctor_get(v_toApplicative_1365_, 1);
v___x_1368_ = lean_usize_dec_lt(v_i_1363_, v_sz_1362_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
lean_inc(v_toPure_1367_);
lean_dec(v_toBind_1366_);
lean_dec(v_f_1361_);
lean_dec_ref(v_inst_1360_);
v___x_1369_ = lean_apply_2(v_toPure_1367_, lean_box(0), v_bs_1364_);
return v___x_1369_;
}
else
{
lean_object* v_v_1370_; lean_object* v___x_1371_; lean_object* v_bs_x27_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___f_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_v_1370_ = lean_array_uget(v_bs_1364_, v_i_1363_);
v___x_1371_ = lean_unsigned_to_nat(0u);
v_bs_x27_1372_ = lean_array_uset(v_bs_1364_, v_i_1363_, v___x_1371_);
v___x_1373_ = lean_box_usize(v_i_1363_);
v___x_1374_ = lean_box_usize(v_sz_1362_);
lean_inc(v_f_1361_);
v___f_1375_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1375_, 0, v___x_1373_);
lean_closure_set(v___f_1375_, 1, v_bs_x27_1372_);
lean_closure_set(v___f_1375_, 2, v_inst_1360_);
lean_closure_set(v___f_1375_, 3, v_f_1361_);
lean_closure_set(v___f_1375_, 4, v___x_1374_);
v___x_1376_ = lean_apply_1(v_f_1361_, v_v_1370_);
v___x_1377_ = lean_apply_4(v_toBind_1366_, lean_box(0), lean_box(0), v___x_1376_, v___f_1375_);
return v___x_1377_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1360_ = stack[0].m_obj;
lean_object* v_f_1361_ = stack[1].m_obj;
size_t v_sz_1362_ = stack[2].m_num;
size_t v_i_1363_ = stack[3].m_num;
lean_object* v_bs_1364_ = stack[4].m_obj;
lean_object* v_res_1378_;
v_res_1378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1360_, v_f_1361_, v_sz_1362_, v_i_1363_, v_bs_1364_);
stack->m_obj
 = v_res_1378_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(size_t v_i_1379_, lean_object* v_bs_x27_1380_, lean_object* v_inst_1381_, lean_object* v_f_1382_, size_t v_sz_1383_, lean_object* v_vNew_1384_){
_start:
{
size_t v___x_1385_; size_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1385_ = ((size_t)1ULL);
v___x_1386_ = lean_usize_add(v_i_1379_, v___x_1385_);
v___x_1387_ = lean_array_uset(v_bs_x27_1380_, v_i_1379_, v_vNew_1384_);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1381_, v_f_1382_, v_sz_1383_, v___x_1386_, v___x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_i_1379_ = stack[0].m_num;
lean_object* v_bs_x27_1380_ = stack[1].m_obj;
lean_object* v_inst_1381_ = stack[2].m_obj;
lean_object* v_f_1382_ = stack[3].m_obj;
size_t v_sz_1383_ = stack[4].m_num;
lean_object* v_vNew_1384_ = stack[5].m_obj;
lean_object* v_res_1389_;
v_res_1389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(v_i_1379_, v_bs_x27_1380_, v_inst_1381_, v_f_1382_, v_sz_1383_, v_vNew_1384_);
stack->m_obj
 = v_res_1389_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___boxed(lean_object* v_inst_1390_, lean_object* v_f_1391_, lean_object* v_sz_1392_, lean_object* v_i_1393_, lean_object* v_bs_1394_){
_start:
{
size_t v_sz_boxed_1395_; size_t v_i_boxed_1396_; lean_object* v_res_1397_; 
v_sz_boxed_1395_ = lean_unbox_usize(v_sz_1392_);
lean_dec(v_sz_1392_);
v_i_boxed_1396_ = lean_unbox_usize(v_i_1393_);
lean_dec(v_i_1393_);
v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1390_, v_f_1391_, v_sz_boxed_1395_, v_i_boxed_1396_, v_bs_1394_);
return v_res_1397_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object* v_00_u03b1_1398_, lean_object* v_00_u03b2_1399_, lean_object* v_m_1400_, lean_object* v_inst_1401_, lean_object* v_f_1402_, size_t v_sz_1403_, size_t v_i_1404_, lean_object* v_bs_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1401_, v_f_1402_, v_sz_1403_, v_i_1404_, v_bs_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1401_ = stack[3].m_obj;
lean_object* v_f_1402_ = stack[4].m_obj;
size_t v_sz_1403_ = stack[5].m_num;
size_t v_i_1404_ = stack[6].m_num;
lean_object* v_bs_1405_ = stack[7].m_obj;
lean_object* v_res_1407_;
v_res_1407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1401_, v_f_1402_, v_sz_1403_, v_i_1404_, v_bs_1405_);
stack->m_obj
 = v_res_1407_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___boxed(lean_object* v_00_u03b1_1408_, lean_object* v_00_u03b2_1409_, lean_object* v_m_1410_, lean_object* v_inst_1411_, lean_object* v_f_1412_, lean_object* v_sz_1413_, lean_object* v_i_1414_, lean_object* v_bs_1415_){
_start:
{
size_t v_sz_boxed_1416_; size_t v_i_boxed_1417_; lean_object* v_res_1418_; 
v_sz_boxed_1416_ = lean_unbox_usize(v_sz_1413_);
lean_dec(v_sz_1413_);
v_i_boxed_1417_ = lean_unbox_usize(v_i_1414_);
lean_dec(v_i_1414_);
v_res_1418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(v_00_u03b1_1408_, v_00_u03b2_1409_, v_m_1410_, v_inst_1411_, v_f_1412_, v_sz_boxed_1416_, v_i_boxed_1417_, v_bs_1415_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe___redArg(lean_object* v_inst_1419_, lean_object* v_f_1420_, lean_object* v_as_1421_){
_start:
{
size_t v_sz_1422_; size_t v___x_1423_; lean_object* v___x_1424_; 
v_sz_1422_ = lean_array_size(v_as_1421_);
v___x_1423_ = ((size_t)0ULL);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1419_, v_f_1420_, v_sz_1422_, v___x_1423_, v_as_1421_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe(lean_object* v_00_u03b1_1425_, lean_object* v_00_u03b2_1426_, lean_object* v_m_1427_, lean_object* v_inst_1428_, lean_object* v_f_1429_, lean_object* v_as_1430_){
_start:
{
size_t v_sz_1431_; size_t v___x_1432_; lean_object* v___x_1433_; 
v_sz_1431_ = lean_array_size(v_as_1430_);
v___x_1432_ = ((size_t)0ULL);
v___x_1433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1428_, v_f_1429_, v_sz_1431_, v___x_1432_, v_as_1430_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_map___redArg___lam__0___boxed(lean_object* v_i_1434_, lean_object* v_bs_1435_, lean_object* v_inst_1436_, lean_object* v_f_1437_, lean_object* v_as_1438_, lean_object* v_____do__lift_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Array_mapM_map___redArg___lam__0(v_i_1434_, v_bs_1435_, v_inst_1436_, v_f_1437_, v_as_1438_, v_____do__lift_1439_);
lean_dec(v_i_1434_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_map___redArg(lean_object* v_inst_1441_, lean_object* v_f_1442_, lean_object* v_as_1443_, lean_object* v_i_1444_, lean_object* v_bs_1445_){
_start:
{
lean_object* v_toApplicative_1446_; lean_object* v_toBind_1447_; lean_object* v_toPure_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v_toApplicative_1446_ = lean_ctor_get(v_inst_1441_, 0);
v_toBind_1447_ = lean_ctor_get(v_inst_1441_, 1);
lean_inc(v_toBind_1447_);
v_toPure_1448_ = lean_ctor_get(v_toApplicative_1446_, 1);
v___x_1449_ = lean_array_get_size(v_as_1443_);
v___x_1450_ = lean_nat_dec_lt(v_i_1444_, v___x_1449_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; 
lean_inc(v_toPure_1448_);
lean_dec(v_toBind_1447_);
lean_dec(v_i_1444_);
lean_dec_ref(v_as_1443_);
lean_dec(v_f_1442_);
lean_dec_ref(v_inst_1441_);
v___x_1451_ = lean_apply_2(v_toPure_1448_, lean_box(0), v_bs_1445_);
return v___x_1451_;
}
else
{
lean_object* v___f_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_inc_ref(v_as_1443_);
lean_inc(v_f_1442_);
lean_inc(v_i_1444_);
v___f_1452_ = lean_alloc_closure((void*)(l_Array_mapM_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1452_, 0, v_i_1444_);
lean_closure_set(v___f_1452_, 1, v_bs_1445_);
lean_closure_set(v___f_1452_, 2, v_inst_1441_);
lean_closure_set(v___f_1452_, 3, v_f_1442_);
lean_closure_set(v___f_1452_, 4, v_as_1443_);
v___x_1453_ = lean_array_fget(v_as_1443_, v_i_1444_);
lean_dec(v_i_1444_);
lean_dec_ref(v_as_1443_);
v___x_1454_ = lean_apply_1(v_f_1442_, v___x_1453_);
v___x_1455_ = lean_apply_4(v_toBind_1447_, lean_box(0), lean_box(0), v___x_1454_, v___f_1452_);
return v___x_1455_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapM_map___redArg___lam__0(lean_object* v_i_1456_, lean_object* v_bs_1457_, lean_object* v_inst_1458_, lean_object* v_f_1459_, lean_object* v_as_1460_, lean_object* v_____do__lift_1461_){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1462_ = lean_unsigned_to_nat(1u);
v___x_1463_ = lean_nat_add(v_i_1456_, v___x_1462_);
v___x_1464_ = lean_array_push(v_bs_1457_, v_____do__lift_1461_);
v___x_1465_ = l_Array_mapM_map___redArg(v_inst_1458_, v_f_1459_, v_as_1460_, v___x_1463_, v___x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_map(lean_object* v_00_u03b1_1466_, lean_object* v_00_u03b2_1467_, lean_object* v_m_1468_, lean_object* v_inst_1469_, lean_object* v_f_1470_, lean_object* v_as_1471_, lean_object* v_i_1472_, lean_object* v_bs_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Array_mapM_map___redArg(v_inst_1469_, v_f_1470_, v_as_1471_, v_i_1472_, v_bs_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0___boxed(lean_object* v_i_1475_, lean_object* v_bs_x27_1476_, lean_object* v_inst_1477_, lean_object* v_f_1478_, lean_object* v_sz_1479_, lean_object* v_vNew_1480_){
_start:
{
size_t v_i_boxed_1481_; size_t v_sz_boxed_1482_; lean_object* v_res_1483_; 
v_i_boxed_1481_ = lean_unbox_usize(v_i_1475_);
lean_dec(v_i_1475_);
v_sz_boxed_1482_ = lean_unbox_usize(v_sz_1479_);
lean_dec(v_sz_1479_);
v_res_1483_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0(v_i_boxed_1481_, v_bs_x27_1476_, v_inst_1477_, v_f_1478_, v_sz_boxed_1482_, v_vNew_1480_);
return v_res_1483_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(lean_object* v_inst_1484_, lean_object* v_f_1485_, size_t v_sz_1486_, size_t v_i_1487_, lean_object* v_bs_1488_){
_start:
{
lean_object* v_toApplicative_1489_; lean_object* v_toBind_1490_; lean_object* v_toPure_1491_; uint8_t v___x_1492_; 
v_toApplicative_1489_ = lean_ctor_get(v_inst_1484_, 0);
v_toBind_1490_ = lean_ctor_get(v_inst_1484_, 1);
lean_inc(v_toBind_1490_);
v_toPure_1491_ = lean_ctor_get(v_toApplicative_1489_, 1);
v___x_1492_ = lean_usize_dec_lt(v_i_1487_, v_sz_1486_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; 
lean_inc(v_toPure_1491_);
lean_dec(v_toBind_1490_);
lean_dec(v_f_1485_);
lean_dec_ref(v_inst_1484_);
v___x_1493_ = lean_apply_2(v_toPure_1491_, lean_box(0), v_bs_1488_);
return v___x_1493_;
}
else
{
lean_object* v_v_1494_; lean_object* v___x_1495_; lean_object* v_bs_x27_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___f_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v_v_1494_ = lean_array_uget(v_bs_1488_, v_i_1487_);
v___x_1495_ = lean_unsigned_to_nat(0u);
v_bs_x27_1496_ = lean_array_uset(v_bs_1488_, v_i_1487_, v___x_1495_);
v___x_1497_ = lean_box_usize(v_i_1487_);
v___x_1498_ = lean_box_usize(v_sz_1486_);
lean_inc(v_f_1485_);
v___f_1499_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1499_, 0, v___x_1497_);
lean_closure_set(v___f_1499_, 1, v_bs_x27_1496_);
lean_closure_set(v___f_1499_, 2, v_inst_1484_);
lean_closure_set(v___f_1499_, 3, v_f_1485_);
lean_closure_set(v___f_1499_, 4, v___x_1498_);
v___x_1500_ = lean_usize_to_nat(v_i_1487_);
v___x_1501_ = lean_apply_3(v_f_1485_, v___x_1500_, v_v_1494_, lean_box(0));
v___x_1502_ = lean_apply_4(v_toBind_1490_, lean_box(0), lean_box(0), v___x_1501_, v___f_1499_);
return v___x_1502_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1484_ = stack[0].m_obj;
lean_object* v_f_1485_ = stack[1].m_obj;
size_t v_sz_1486_ = stack[2].m_num;
size_t v_i_1487_ = stack[3].m_num;
lean_object* v_bs_1488_ = stack[4].m_obj;
lean_object* v_res_1503_;
v_res_1503_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1484_, v_f_1485_, v_sz_1486_, v_i_1487_, v_bs_1488_);
stack->m_obj
 = v_res_1503_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0(size_t v_i_1504_, lean_object* v_bs_x27_1505_, lean_object* v_inst_1506_, lean_object* v_f_1507_, size_t v_sz_1508_, lean_object* v_vNew_1509_){
_start:
{
size_t v___x_1510_; size_t v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1510_ = ((size_t)1ULL);
v___x_1511_ = lean_usize_add(v_i_1504_, v___x_1510_);
v___x_1512_ = lean_array_uset(v_bs_x27_1505_, v_i_1504_, v_vNew_1509_);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1506_, v_f_1507_, v_sz_1508_, v___x_1511_, v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_i_1504_ = stack[0].m_num;
lean_object* v_bs_x27_1505_ = stack[1].m_obj;
lean_object* v_inst_1506_ = stack[2].m_obj;
lean_object* v_f_1507_ = stack[3].m_obj;
size_t v_sz_1508_ = stack[4].m_num;
lean_object* v_vNew_1509_ = stack[5].m_obj;
lean_object* v_res_1514_;
v_res_1514_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0(v_i_1504_, v_bs_x27_1505_, v_inst_1506_, v_f_1507_, v_sz_1508_, v_vNew_1509_);
stack->m_obj
 = v_res_1514_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___boxed(lean_object* v_inst_1515_, lean_object* v_f_1516_, lean_object* v_sz_1517_, lean_object* v_i_1518_, lean_object* v_bs_1519_){
_start:
{
size_t v_sz_boxed_1520_; size_t v_i_boxed_1521_; lean_object* v_res_1522_; 
v_sz_boxed_1520_ = lean_unbox_usize(v_sz_1517_);
lean_dec(v_sz_1517_);
v_i_boxed_1521_ = lean_unbox_usize(v_i_1518_);
lean_dec(v_i_1518_);
v_res_1522_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1515_, v_f_1516_, v_sz_boxed_1520_, v_i_boxed_1521_, v_bs_1519_);
return v_res_1522_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object* v_00_u03b1_1523_, lean_object* v_00_u03b2_1524_, lean_object* v_m_1525_, lean_object* v_inst_1526_, lean_object* v_as_1527_, lean_object* v_f_1528_, size_t v_sz_1529_, size_t v_i_1530_, lean_object* v_bs_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1526_, v_f_1528_, v_sz_1529_, v_i_1530_, v_bs_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1526_ = stack[3].m_obj;
lean_object* v_as_1527_ = stack[4].m_obj;
lean_object* v_f_1528_ = stack[5].m_obj;
size_t v_sz_1529_ = stack[6].m_num;
size_t v_i_1530_ = stack[7].m_num;
lean_object* v_bs_1531_ = stack[8].m_obj;
lean_object* v_res_1533_;
v_res_1533_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1526_, v_as_1527_, v_f_1528_, v_sz_1529_, v_i_1530_, v_bs_1531_);
stack->m_obj
 = v_res_1533_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___boxed(lean_object* v_00_u03b1_1534_, lean_object* v_00_u03b2_1535_, lean_object* v_m_1536_, lean_object* v_inst_1537_, lean_object* v_as_1538_, lean_object* v_f_1539_, lean_object* v_sz_1540_, lean_object* v_i_1541_, lean_object* v_bs_1542_){
_start:
{
size_t v_sz_boxed_1543_; size_t v_i_boxed_1544_; lean_object* v_res_1545_; 
v_sz_boxed_1543_ = lean_unbox_usize(v_sz_1540_);
lean_dec(v_sz_1540_);
v_i_boxed_1544_ = lean_unbox_usize(v_i_1541_);
lean_dec(v_i_1541_);
v_res_1545_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(v_00_u03b1_1534_, v_00_u03b2_1535_, v_m_1536_, v_inst_1537_, v_as_1538_, v_f_1539_, v_sz_boxed_1543_, v_i_boxed_1544_, v_bs_1542_);
lean_dec_ref(v_as_1538_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxMUnsafe___redArg(lean_object* v_inst_1546_, lean_object* v_as_1547_, lean_object* v_f_1548_){
_start:
{
size_t v_sz_1549_; size_t v___x_1550_; lean_object* v___x_1551_; 
v_sz_1549_ = lean_array_size(v_as_1547_);
v___x_1550_ = ((size_t)0ULL);
v___x_1551_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1546_, v_f_1548_, v_sz_1549_, v___x_1550_, v_as_1547_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxMUnsafe(lean_object* v_00_u03b1_1552_, lean_object* v_00_u03b2_1553_, lean_object* v_m_1554_, lean_object* v_inst_1555_, lean_object* v_as_1556_, lean_object* v_f_1557_){
_start:
{
size_t v_sz_1558_; size_t v___x_1559_; lean_object* v___x_1560_; 
v_sz_1558_ = lean_array_size(v_as_1556_);
v___x_1559_ = ((size_t)0ULL);
v___x_1560_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1555_, v_f_1557_, v_sz_1558_, v___x_1559_, v_as_1556_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1561_, lean_object* v_bs_1562_, lean_object* v_inst_1563_, lean_object* v_as_1564_, lean_object* v_f_1565_, lean_object* v_n_1566_, lean_object* v_____do__lift_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Array_mapFinIdxM_map___redArg___lam__0(v_j_1561_, v_bs_1562_, v_inst_1563_, v_as_1564_, v_f_1565_, v_n_1566_, v_____do__lift_1567_);
lean_dec(v_n_1566_);
lean_dec(v_j_1561_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg(lean_object* v_inst_1569_, lean_object* v_as_1570_, lean_object* v_f_1571_, lean_object* v_i_1572_, lean_object* v_j_1573_, lean_object* v_bs_1574_){
_start:
{
lean_object* v_toApplicative_1575_; lean_object* v_toBind_1576_; lean_object* v_toPure_1577_; lean_object* v_zero_1578_; uint8_t v_isZero_1579_; 
v_toApplicative_1575_ = lean_ctor_get(v_inst_1569_, 0);
v_toBind_1576_ = lean_ctor_get(v_inst_1569_, 1);
lean_inc(v_toBind_1576_);
v_toPure_1577_ = lean_ctor_get(v_toApplicative_1575_, 1);
v_zero_1578_ = lean_unsigned_to_nat(0u);
v_isZero_1579_ = lean_nat_dec_eq(v_i_1572_, v_zero_1578_);
if (v_isZero_1579_ == 1)
{
lean_object* v___x_1580_; 
lean_inc(v_toPure_1577_);
lean_dec(v_toBind_1576_);
lean_dec(v_j_1573_);
lean_dec(v_f_1571_);
lean_dec_ref(v_as_1570_);
lean_dec_ref(v_inst_1569_);
v___x_1580_ = lean_apply_2(v_toPure_1577_, lean_box(0), v_bs_1574_);
return v___x_1580_;
}
else
{
lean_object* v_one_1581_; lean_object* v_n_1582_; lean_object* v___f_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_one_1581_ = lean_unsigned_to_nat(1u);
v_n_1582_ = lean_nat_sub(v_i_1572_, v_one_1581_);
lean_inc(v_f_1571_);
lean_inc_ref(v_as_1570_);
lean_inc(v_j_1573_);
v___f_1583_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1583_, 0, v_j_1573_);
lean_closure_set(v___f_1583_, 1, v_bs_1574_);
lean_closure_set(v___f_1583_, 2, v_inst_1569_);
lean_closure_set(v___f_1583_, 3, v_as_1570_);
lean_closure_set(v___f_1583_, 4, v_f_1571_);
lean_closure_set(v___f_1583_, 5, v_n_1582_);
v___x_1584_ = lean_array_fget(v_as_1570_, v_j_1573_);
lean_dec_ref(v_as_1570_);
v___x_1585_ = lean_apply_3(v_f_1571_, v_j_1573_, v___x_1584_, lean_box(0));
v___x_1586_ = lean_apply_4(v_toBind_1576_, lean_box(0), lean_box(0), v___x_1585_, v___f_1583_);
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1587_, lean_object* v_bs_1588_, lean_object* v_inst_1589_, lean_object* v_as_1590_, lean_object* v_f_1591_, lean_object* v_n_1592_, lean_object* v_____do__lift_1593_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1594_ = lean_unsigned_to_nat(1u);
v___x_1595_ = lean_nat_add(v_j_1587_, v___x_1594_);
v___x_1596_ = lean_array_push(v_bs_1588_, v_____do__lift_1593_);
v___x_1597_ = l_Array_mapFinIdxM_map___redArg(v_inst_1589_, v_as_1590_, v_f_1591_, v_n_1592_, v___x_1595_, v___x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1598_, lean_object* v_as_1599_, lean_object* v_f_1600_, lean_object* v_i_1601_, lean_object* v_j_1602_, lean_object* v_bs_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Array_mapFinIdxM_map___redArg(v_inst_1598_, v_as_1599_, v_f_1600_, v_i_1601_, v_j_1602_, v_bs_1603_);
lean_dec(v_i_1601_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map(lean_object* v_00_u03b1_1605_, lean_object* v_00_u03b2_1606_, lean_object* v_m_1607_, lean_object* v_inst_1608_, lean_object* v_as_1609_, lean_object* v_f_1610_, lean_object* v_i_1611_, lean_object* v_j_1612_, lean_object* v_inv_1613_, lean_object* v_bs_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Array_mapFinIdxM_map___redArg(v_inst_1608_, v_as_1609_, v_f_1610_, v_i_1611_, v_j_1612_, v_bs_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___boxed(lean_object* v_00_u03b1_1616_, lean_object* v_00_u03b2_1617_, lean_object* v_m_1618_, lean_object* v_inst_1619_, lean_object* v_as_1620_, lean_object* v_f_1621_, lean_object* v_i_1622_, lean_object* v_j_1623_, lean_object* v_inv_1624_, lean_object* v_bs_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Array_mapFinIdxM_map(v_00_u03b1_1616_, v_00_u03b2_1617_, v_m_1618_, v_inst_1619_, v_as_1620_, v_f_1621_, v_i_1622_, v_j_1623_, v_inv_1624_, v_bs_1625_);
lean_dec(v_i_1622_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg___lam__0(lean_object* v_f_1627_, lean_object* v_i_1628_, lean_object* v_a_1629_, lean_object* v_x_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_apply_2(v_f_1627_, v_i_1628_, v_a_1629_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg(lean_object* v_inst_1632_, lean_object* v_f_1633_, lean_object* v_as_1634_){
_start:
{
lean_object* v___f_1635_; size_t v_sz_1636_; size_t v___x_1637_; lean_object* v___x_1638_; 
v___f_1635_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1635_, 0, v_f_1633_);
v_sz_1636_ = lean_array_size(v_as_1634_);
v___x_1637_ = ((size_t)0ULL);
v___x_1638_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1632_, v___f_1635_, v_sz_1636_, v___x_1637_, v_as_1634_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM(lean_object* v_00_u03b1_1639_, lean_object* v_00_u03b2_1640_, lean_object* v_m_1641_, lean_object* v_inst_1642_, lean_object* v_f_1643_, lean_object* v_as_1644_){
_start:
{
lean_object* v___f_1645_; size_t v_sz_1646_; size_t v___x_1647_; lean_object* v___x_1648_; 
v___f_1645_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1645_, 0, v_f_1643_);
v_sz_1646_ = lean_array_size(v_as_1644_);
v___x_1647_ = ((size_t)0ULL);
v___x_1648_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1642_, v___f_1645_, v_sz_1646_, v___x_1647_, v_as_1644_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed(lean_object* v_i_1649_, lean_object* v_inst_1650_, lean_object* v_f_1651_, lean_object* v_as_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(v_i_1649_, v_inst_1650_, v_f_1651_, v_as_1652_, v_x_1653_);
lean_dec(v_i_1649_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(lean_object* v_inst_1655_, lean_object* v_f_1656_, lean_object* v_as_1657_, lean_object* v_i_1658_){
_start:
{
lean_object* v___x_1659_; uint8_t v___x_1660_; 
v___x_1659_ = lean_array_get_size(v_as_1657_);
v___x_1660_ = lean_nat_dec_lt(v_i_1658_, v___x_1659_);
if (v___x_1660_ == 0)
{
lean_object* v_failure_1661_; lean_object* v___x_1662_; 
lean_dec(v_i_1658_);
lean_dec_ref(v_as_1657_);
lean_dec(v_f_1656_);
v_failure_1661_ = lean_ctor_get(v_inst_1655_, 1);
lean_inc(v_failure_1661_);
lean_dec_ref(v_inst_1655_);
v___x_1662_ = lean_apply_1(v_failure_1661_, lean_box(0));
return v___x_1662_;
}
else
{
lean_object* v_orElse_1663_; lean_object* v___f_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_orElse_1663_ = lean_ctor_get(v_inst_1655_, 2);
lean_inc(v_orElse_1663_);
lean_inc_ref(v_as_1657_);
lean_inc(v_f_1656_);
lean_inc(v_i_1658_);
v___f_1664_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1664_, 0, v_i_1658_);
lean_closure_set(v___f_1664_, 1, v_inst_1655_);
lean_closure_set(v___f_1664_, 2, v_f_1656_);
lean_closure_set(v___f_1664_, 3, v_as_1657_);
v___x_1665_ = lean_array_fget(v_as_1657_, v_i_1658_);
lean_dec(v_i_1658_);
lean_dec_ref(v_as_1657_);
v___x_1666_ = lean_apply_1(v_f_1656_, v___x_1665_);
v___x_1667_ = lean_apply_3(v_orElse_1663_, lean_box(0), v___x_1666_, v___f_1664_);
return v___x_1667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(lean_object* v_i_1668_, lean_object* v_inst_1669_, lean_object* v_f_1670_, lean_object* v_as_1671_, lean_object* v_x_1672_){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1673_ = lean_unsigned_to_nat(1u);
v___x_1674_ = lean_nat_add(v_i_1668_, v___x_1673_);
v___x_1675_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1669_, v_f_1670_, v_as_1671_, v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_object* v_00_u03b2_1676_, lean_object* v_00_u03b1_1677_, lean_object* v_m_1678_, lean_object* v_inst_1679_, lean_object* v_f_1680_, lean_object* v_as_1681_, lean_object* v_i_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1679_, v_f_1680_, v_as_1681_, v_i_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM___redArg(lean_object* v_inst_1684_, lean_object* v_f_1685_, lean_object* v_as_1686_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_unsigned_to_nat(0u);
v___x_1688_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1684_, v_f_1685_, v_as_1686_, v___x_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM(lean_object* v_00_u03b2_1689_, lean_object* v_00_u03b1_1690_, lean_object* v_m_1691_, lean_object* v_inst_1692_, lean_object* v_f_1693_, lean_object* v_as_1694_){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = lean_unsigned_to_nat(0u);
v___x_1696_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1692_, v_f_1693_, v_as_1694_, v___x_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__0(lean_object* v___x_1697_, lean_object* v_toPure_1698_, lean_object* v___x_1699_, lean_object* v_____do__lift_1700_){
_start:
{
if (lean_obj_tag(v_____do__lift_1700_) == 1)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_dec_ref(v___x_1699_);
v___x_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1701_, 0, v_____do__lift_1700_);
v___x_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
lean_ctor_set(v___x_1702_, 1, v___x_1697_);
v___x_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
v___x_1704_ = lean_apply_2(v_toPure_1698_, lean_box(0), v___x_1703_);
return v___x_1704_;
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_dec(v_____do__lift_1700_);
v___x_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1699_);
v___x_1706_ = lean_apply_2(v_toPure_1698_, lean_box(0), v___x_1705_);
return v___x_1706_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1(lean_object* v_f_1707_, lean_object* v_toBind_1708_, lean_object* v___f_1709_, lean_object* v_a_1710_, lean_object* v_x_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_apply_1(v_f_1707_, v_a_1710_);
v___x_1714_ = lean_apply_4(v_toBind_1708_, lean_box(0), lean_box(0), v___x_1713_, v___f_1709_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1___boxed(lean_object* v_f_1715_, lean_object* v_toBind_1716_, lean_object* v___f_1717_, lean_object* v_a_1718_, lean_object* v_x_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Array_findSomeM_x3f___redArg___lam__1(v_f_1715_, v_toBind_1716_, v___f_1717_, v_a_1718_, v_x_1719_, v___y_1720_);
lean_dec_ref(v___y_1720_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__2(lean_object* v_toPure_1722_, lean_object* v_____s_1723_){
_start:
{
lean_object* v_fst_1724_; 
v_fst_1724_ = lean_ctor_get(v_____s_1723_, 0);
lean_inc(v_fst_1724_);
lean_dec_ref(v_____s_1723_);
if (lean_obj_tag(v_fst_1724_) == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_box(0);
v___x_1726_ = lean_apply_2(v_toPure_1722_, lean_box(0), v___x_1725_);
return v___x_1726_;
}
else
{
lean_object* v_val_1727_; lean_object* v___x_1728_; 
v_val_1727_ = lean_ctor_get(v_fst_1724_, 0);
lean_inc(v_val_1727_);
lean_dec_ref_known(v_fst_1724_, 1);
v___x_1728_ = lean_apply_2(v_toPure_1722_, lean_box(0), v_val_1727_);
return v___x_1728_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg(lean_object* v_inst_1732_, lean_object* v_f_1733_, lean_object* v_as_1734_){
_start:
{
lean_object* v_toApplicative_1735_; lean_object* v_toBind_1736_; lean_object* v_toPure_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___f_1740_; lean_object* v___f_1741_; lean_object* v___f_1742_; size_t v_sz_1743_; size_t v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v_toApplicative_1735_ = lean_ctor_get(v_inst_1732_, 0);
v_toBind_1736_ = lean_ctor_get(v_inst_1732_, 1);
lean_inc_n(v_toBind_1736_, 2);
v_toPure_1737_ = lean_ctor_get(v_toApplicative_1735_, 1);
v___x_1738_ = lean_box(0);
v___x_1739_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1737_, 2);
v___f_1740_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1740_, 0, v___x_1738_);
lean_closure_set(v___f_1740_, 1, v_toPure_1737_);
lean_closure_set(v___f_1740_, 2, v___x_1739_);
v___f_1741_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1741_, 0, v_f_1733_);
lean_closure_set(v___f_1741_, 1, v_toBind_1736_);
lean_closure_set(v___f_1741_, 2, v___f_1740_);
v___f_1742_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1742_, 0, v_toPure_1737_);
v_sz_1743_ = lean_array_size(v_as_1734_);
v___x_1744_ = ((size_t)0ULL);
v___x_1745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1732_, v_as_1734_, v___f_1741_, v_sz_1743_, v___x_1744_, v___x_1739_);
v___x_1746_ = lean_apply_4(v_toBind_1736_, lean_box(0), lean_box(0), v___x_1745_, v___f_1742_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f(lean_object* v_00_u03b1_1747_, lean_object* v_00_u03b2_1748_, lean_object* v_m_1749_, lean_object* v_inst_1750_, lean_object* v_f_1751_, lean_object* v_as_1752_){
_start:
{
lean_object* v_toApplicative_1753_; lean_object* v_toBind_1754_; lean_object* v_toPure_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___f_1758_; lean_object* v___f_1759_; lean_object* v___f_1760_; size_t v_sz_1761_; size_t v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v_toApplicative_1753_ = lean_ctor_get(v_inst_1750_, 0);
v_toBind_1754_ = lean_ctor_get(v_inst_1750_, 1);
lean_inc_n(v_toBind_1754_, 2);
v_toPure_1755_ = lean_ctor_get(v_toApplicative_1753_, 1);
v___x_1756_ = lean_box(0);
v___x_1757_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1755_, 2);
v___f_1758_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1758_, 0, v___x_1756_);
lean_closure_set(v___f_1758_, 1, v_toPure_1755_);
lean_closure_set(v___f_1758_, 2, v___x_1757_);
v___f_1759_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1759_, 0, v_f_1751_);
lean_closure_set(v___f_1759_, 1, v_toBind_1754_);
lean_closure_set(v___f_1759_, 2, v___f_1758_);
v___f_1760_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1760_, 0, v_toPure_1755_);
v_sz_1761_ = lean_array_size(v_as_1752_);
v___x_1762_ = ((size_t)0ULL);
v___x_1763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1750_, v_as_1752_, v___f_1759_, v_sz_1761_, v___x_1762_, v___x_1757_);
v___x_1764_ = lean_apply_4(v_toBind_1754_, lean_box(0), lean_box(0), v___x_1763_, v___f_1760_);
return v___x_1764_;
}
}
lean_object* l_Array_findM_x3f___redArg___lam__0(lean_object* v___x_1765_, lean_object* v_toPure_1766_, lean_object* v_a_1767_, lean_object* v___x_1768_, uint8_t v_____do__lift_1769_){
_start:
{
if (v_____do__lift_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec(v_a_1767_);
v___x_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1765_);
v___x_1771_ = lean_apply_2(v_toPure_1766_, lean_box(0), v___x_1770_);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_dec_ref(v___x_1765_);
v___x_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1772_, 0, v_a_1767_);
v___x_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
v___x_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
lean_ctor_set(v___x_1774_, 1, v___x_1768_);
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
v___x_1776_ = lean_apply_2(v_toPure_1766_, lean_box(0), v___x_1775_);
return v___x_1776_;
}
}
}
LEAN_EXPORT void l_Array_findM_x3f___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1765_ = stack[0].m_obj;
lean_object* v_toPure_1766_ = stack[1].m_obj;
lean_object* v_a_1767_ = stack[2].m_obj;
lean_object* v___x_1768_ = stack[3].m_obj;
uint8_t v_____do__lift_1769_ = stack[4].m_num;
lean_object* v_res_1777_;
v_res_1777_ = l_Array_findM_x3f___redArg___lam__0(v___x_1765_, v_toPure_1766_, v_a_1767_, v___x_1768_, v_____do__lift_1769_);
stack->m_obj
 = v_res_1777_;
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0___boxed(lean_object* v___x_1778_, lean_object* v_toPure_1779_, lean_object* v_a_1780_, lean_object* v___x_1781_, lean_object* v_____do__lift_1782_){
_start:
{
uint8_t v_____do__lift_185__boxed_1783_; lean_object* v_res_1784_; 
v_____do__lift_185__boxed_1783_ = lean_unbox(v_____do__lift_1782_);
v_res_1784_ = l_Array_findM_x3f___redArg___lam__0(v___x_1778_, v_toPure_1779_, v_a_1780_, v___x_1781_, v_____do__lift_185__boxed_1783_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1(lean_object* v___x_1785_, lean_object* v_toPure_1786_, lean_object* v___x_1787_, lean_object* v_p_1788_, lean_object* v_toBind_1789_, lean_object* v_a_1790_, lean_object* v_x_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___f_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_inc(v_a_1790_);
v___f_1793_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1793_, 0, v___x_1785_);
lean_closure_set(v___f_1793_, 1, v_toPure_1786_);
lean_closure_set(v___f_1793_, 2, v_a_1790_);
lean_closure_set(v___f_1793_, 3, v___x_1787_);
v___x_1794_ = lean_apply_1(v_p_1788_, v_a_1790_);
v___x_1795_ = lean_apply_4(v_toBind_1789_, lean_box(0), lean_box(0), v___x_1794_, v___f_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_1796_, lean_object* v_toPure_1797_, lean_object* v___x_1798_, lean_object* v_p_1799_, lean_object* v_toBind_1800_, lean_object* v_a_1801_, lean_object* v_x_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Array_findM_x3f___redArg___lam__1(v___x_1796_, v_toPure_1797_, v___x_1798_, v_p_1799_, v_toBind_1800_, v_a_1801_, v_x_1802_, v___y_1803_);
lean_dec_ref(v___y_1803_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg(lean_object* v_inst_1805_, lean_object* v_p_1806_, lean_object* v_as_1807_){
_start:
{
lean_object* v_toApplicative_1808_; lean_object* v_toBind_1809_; lean_object* v_toPure_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___f_1813_; lean_object* v___f_1814_; size_t v_sz_1815_; size_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v_toApplicative_1808_ = lean_ctor_get(v_inst_1805_, 0);
v_toBind_1809_ = lean_ctor_get(v_inst_1805_, 1);
lean_inc_n(v_toBind_1809_, 2);
v_toPure_1810_ = lean_ctor_get(v_toApplicative_1808_, 1);
v___x_1811_ = lean_box(0);
v___x_1812_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1810_, 2);
v___f_1813_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1813_, 0, v___x_1812_);
lean_closure_set(v___f_1813_, 1, v_toPure_1810_);
lean_closure_set(v___f_1813_, 2, v___x_1811_);
lean_closure_set(v___f_1813_, 3, v_p_1806_);
lean_closure_set(v___f_1813_, 4, v_toBind_1809_);
v___f_1814_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1814_, 0, v_toPure_1810_);
v_sz_1815_ = lean_array_size(v_as_1807_);
v___x_1816_ = ((size_t)0ULL);
v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1805_, v_as_1807_, v___f_1813_, v_sz_1815_, v___x_1816_, v___x_1812_);
v___x_1818_ = lean_apply_4(v_toBind_1809_, lean_box(0), lean_box(0), v___x_1817_, v___f_1814_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f(lean_object* v_m_1819_, lean_object* v_00_u03b1_1820_, lean_object* v_inst_1821_, lean_object* v_p_1822_, lean_object* v_as_1823_){
_start:
{
lean_object* v_toApplicative_1824_; lean_object* v_toBind_1825_; lean_object* v_toPure_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___f_1829_; lean_object* v___f_1830_; size_t v_sz_1831_; size_t v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v_toApplicative_1824_ = lean_ctor_get(v_inst_1821_, 0);
v_toBind_1825_ = lean_ctor_get(v_inst_1821_, 1);
lean_inc_n(v_toBind_1825_, 2);
v_toPure_1826_ = lean_ctor_get(v_toApplicative_1824_, 1);
v___x_1827_ = lean_box(0);
v___x_1828_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1826_, 2);
v___f_1829_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1829_, 0, v___x_1828_);
lean_closure_set(v___f_1829_, 1, v_toPure_1826_);
lean_closure_set(v___f_1829_, 2, v___x_1827_);
lean_closure_set(v___f_1829_, 3, v_p_1822_);
lean_closure_set(v___f_1829_, 4, v_toBind_1825_);
v___f_1830_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1830_, 0, v_toPure_1826_);
v_sz_1831_ = lean_array_size(v_as_1823_);
v___x_1832_ = ((size_t)0ULL);
v___x_1833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1821_, v_as_1823_, v___f_1829_, v_sz_1831_, v___x_1832_, v___x_1828_);
v___x_1834_ = lean_apply_4(v_toBind_1825_, lean_box(0), lean_box(0), v___x_1833_, v___f_1830_);
return v___x_1834_;
}
}
lean_object* l_Array_findIdxM_x3f___redArg___lam__0(lean_object* v_snd_1835_, lean_object* v___x_1836_, lean_object* v_toPure_1837_, uint8_t v_____do__lift_1838_){
_start:
{
if (v_____do__lift_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1839_ = lean_unsigned_to_nat(1u);
v___x_1840_ = lean_nat_add(v_snd_1835_, v___x_1839_);
lean_dec(v_snd_1835_);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1836_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
v___x_1843_ = lean_apply_2(v_toPure_1837_, lean_box(0), v___x_1842_);
return v___x_1843_;
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec(v___x_1836_);
lean_inc(v_snd_1835_);
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v_snd_1835_);
v___x_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
v___x_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
lean_ctor_set(v___x_1846_, 1, v_snd_1835_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
v___x_1848_ = lean_apply_2(v_toPure_1837_, lean_box(0), v___x_1847_);
return v___x_1848_;
}
}
}
LEAN_EXPORT void l_Array_findIdxM_x3f___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_1835_ = stack[0].m_obj;
lean_object* v___x_1836_ = stack[1].m_obj;
lean_object* v_toPure_1837_ = stack[2].m_obj;
uint8_t v_____do__lift_1838_ = stack[3].m_num;
lean_object* v_res_1849_;
v_res_1849_ = l_Array_findIdxM_x3f___redArg___lam__0(v_snd_1835_, v___x_1836_, v_toPure_1837_, v_____do__lift_1838_);
stack->m_obj
 = v_res_1849_;
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0___boxed(lean_object* v_snd_1850_, lean_object* v___x_1851_, lean_object* v_toPure_1852_, lean_object* v_____do__lift_1853_){
_start:
{
uint8_t v_____do__lift_214__boxed_1854_; lean_object* v_res_1855_; 
v_____do__lift_214__boxed_1854_ = lean_unbox(v_____do__lift_1853_);
v_res_1855_ = l_Array_findIdxM_x3f___redArg___lam__0(v_snd_1850_, v___x_1851_, v_toPure_1852_, v_____do__lift_214__boxed_1854_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__1(lean_object* v___x_1856_, lean_object* v_toPure_1857_, lean_object* v_p_1858_, lean_object* v_toBind_1859_, lean_object* v_a_1860_, lean_object* v_x_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_snd_1863_; lean_object* v___f_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v_snd_1863_ = lean_ctor_get(v___y_1862_, 1);
lean_inc(v_snd_1863_);
lean_dec_ref(v___y_1862_);
v___f_1864_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1864_, 0, v_snd_1863_);
lean_closure_set(v___f_1864_, 1, v___x_1856_);
lean_closure_set(v___f_1864_, 2, v_toPure_1857_);
v___x_1865_ = lean_apply_1(v_p_1858_, v_a_1860_);
v___x_1866_ = lean_apply_4(v_toBind_1859_, lean_box(0), lean_box(0), v___x_1865_, v___f_1864_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__2(lean_object* v_toPure_1867_, lean_object* v_____s_1868_){
_start:
{
lean_object* v_fst_1869_; 
v_fst_1869_ = lean_ctor_get(v_____s_1868_, 0);
lean_inc(v_fst_1869_);
lean_dec_ref(v_____s_1868_);
if (lean_obj_tag(v_fst_1869_) == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_box(0);
v___x_1871_ = lean_apply_2(v_toPure_1867_, lean_box(0), v___x_1870_);
return v___x_1871_;
}
else
{
lean_object* v_val_1872_; lean_object* v___x_1873_; 
v_val_1872_ = lean_ctor_get(v_fst_1869_, 0);
lean_inc(v_val_1872_);
lean_dec_ref_known(v_fst_1869_, 1);
v___x_1873_ = lean_apply_2(v_toPure_1867_, lean_box(0), v_val_1872_);
return v___x_1873_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg(lean_object* v_inst_1877_, lean_object* v_p_1878_, lean_object* v_as_1879_){
_start:
{
lean_object* v_toApplicative_1880_; lean_object* v_toBind_1881_; lean_object* v_toPure_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___f_1885_; lean_object* v___f_1886_; size_t v_sz_1887_; size_t v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v_toApplicative_1880_ = lean_ctor_get(v_inst_1877_, 0);
v_toBind_1881_ = lean_ctor_get(v_inst_1877_, 1);
lean_inc_n(v_toBind_1881_, 2);
v_toPure_1882_ = lean_ctor_get(v_toApplicative_1880_, 1);
v___x_1883_ = lean_box(0);
v___x_1884_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1882_, 2);
v___f_1885_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1885_, 0, v___x_1883_);
lean_closure_set(v___f_1885_, 1, v_toPure_1882_);
lean_closure_set(v___f_1885_, 2, v_p_1878_);
lean_closure_set(v___f_1885_, 3, v_toBind_1881_);
v___f_1886_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1886_, 0, v_toPure_1882_);
v_sz_1887_ = lean_array_size(v_as_1879_);
v___x_1888_ = ((size_t)0ULL);
v___x_1889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1877_, v_as_1879_, v___f_1885_, v_sz_1887_, v___x_1888_, v___x_1884_);
v___x_1890_ = lean_apply_4(v_toBind_1881_, lean_box(0), lean_box(0), v___x_1889_, v___f_1886_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f(lean_object* v_00_u03b1_1891_, lean_object* v_m_1892_, lean_object* v_inst_1893_, lean_object* v_p_1894_, lean_object* v_as_1895_){
_start:
{
lean_object* v_toApplicative_1896_; lean_object* v_toBind_1897_; lean_object* v_toPure_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___f_1901_; lean_object* v___f_1902_; size_t v_sz_1903_; size_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_toApplicative_1896_ = lean_ctor_get(v_inst_1893_, 0);
v_toBind_1897_ = lean_ctor_get(v_inst_1893_, 1);
lean_inc_n(v_toBind_1897_, 2);
v_toPure_1898_ = lean_ctor_get(v_toApplicative_1896_, 1);
v___x_1899_ = lean_box(0);
v___x_1900_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1898_, 2);
v___f_1901_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1901_, 0, v___x_1899_);
lean_closure_set(v___f_1901_, 1, v_toPure_1898_);
lean_closure_set(v___f_1901_, 2, v_p_1894_);
lean_closure_set(v___f_1901_, 3, v_toBind_1897_);
v___f_1902_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1902_, 0, v_toPure_1898_);
v_sz_1903_ = lean_array_size(v_as_1895_);
v___x_1904_ = ((size_t)0ULL);
v___x_1905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1893_, v_as_1895_, v___f_1901_, v_sz_1903_, v___x_1904_, v___x_1900_);
v___x_1906_ = lean_apply_4(v_toBind_1897_, lean_box(0), lean_box(0), v___x_1905_, v___f_1902_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed(lean_object* v_i_1907_, lean_object* v_inst_1908_, lean_object* v_p_1909_, lean_object* v_as_1910_, lean_object* v_stop_1911_, lean_object* v_toPure_1912_, lean_object* v___x_1913_, lean_object* v_____do__lift_1914_){
_start:
{
size_t v_i_boxed_1915_; size_t v_stop_boxed_1916_; uint8_t v___x_78__boxed_1917_; uint8_t v_____do__lift_79__boxed_1918_; lean_object* v_res_1919_; 
v_i_boxed_1915_ = lean_unbox_usize(v_i_1907_);
lean_dec(v_i_1907_);
v_stop_boxed_1916_ = lean_unbox_usize(v_stop_1911_);
lean_dec(v_stop_1911_);
v___x_78__boxed_1917_ = lean_unbox(v___x_1913_);
v_____do__lift_79__boxed_1918_ = lean_unbox(v_____do__lift_1914_);
v_res_1919_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(v_i_boxed_1915_, v_inst_1908_, v_p_1909_, v_as_1910_, v_stop_boxed_1916_, v_toPure_1912_, v___x_78__boxed_1917_, v_____do__lift_79__boxed_1918_);
return v_res_1919_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(lean_object* v_inst_1920_, lean_object* v_p_1921_, lean_object* v_as_1922_, size_t v_i_1923_, size_t v_stop_1924_){
_start:
{
lean_object* v_toApplicative_1925_; lean_object* v_toBind_1926_; lean_object* v_toPure_1927_; uint8_t v___x_1928_; 
v_toApplicative_1925_ = lean_ctor_get(v_inst_1920_, 0);
v_toBind_1926_ = lean_ctor_get(v_inst_1920_, 1);
lean_inc(v_toBind_1926_);
v_toPure_1927_ = lean_ctor_get(v_toApplicative_1925_, 1);
lean_inc(v_toPure_1927_);
v___x_1928_ = lean_usize_dec_eq(v_i_1923_, v_stop_1924_);
if (v___x_1928_ == 0)
{
uint8_t v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___f_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1929_ = 1;
v___x_1930_ = lean_box_usize(v_i_1923_);
v___x_1931_ = lean_box_usize(v_stop_1924_);
v___x_1932_ = lean_box(v___x_1929_);
lean_inc_ref(v_as_1922_);
lean_inc(v_p_1921_);
v___f_1933_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1933_, 0, v___x_1930_);
lean_closure_set(v___f_1933_, 1, v_inst_1920_);
lean_closure_set(v___f_1933_, 2, v_p_1921_);
lean_closure_set(v___f_1933_, 3, v_as_1922_);
lean_closure_set(v___f_1933_, 4, v___x_1931_);
lean_closure_set(v___f_1933_, 5, v_toPure_1927_);
lean_closure_set(v___f_1933_, 6, v___x_1932_);
v___x_1934_ = lean_array_uget(v_as_1922_, v_i_1923_);
lean_dec_ref(v_as_1922_);
v___x_1935_ = lean_apply_1(v_p_1921_, v___x_1934_);
v___x_1936_ = lean_apply_4(v_toBind_1926_, lean_box(0), lean_box(0), v___x_1935_, v___f_1933_);
return v___x_1936_;
}
else
{
uint8_t v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
lean_dec(v_toBind_1926_);
lean_dec_ref(v_as_1922_);
lean_dec(v_p_1921_);
lean_dec_ref(v_inst_1920_);
v___x_1937_ = 0;
v___x_1938_ = lean_box(v___x_1937_);
v___x_1939_ = lean_apply_2(v_toPure_1927_, lean_box(0), v___x_1938_);
return v___x_1939_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1920_ = stack[0].m_obj;
lean_object* v_p_1921_ = stack[1].m_obj;
lean_object* v_as_1922_ = stack[2].m_obj;
size_t v_i_1923_ = stack[3].m_num;
size_t v_stop_1924_ = stack[4].m_num;
lean_object* v_res_1940_;
v_res_1940_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1920_, v_p_1921_, v_as_1922_, v_i_1923_, v_stop_1924_);
stack->m_obj
 = v_res_1940_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(size_t v_i_1941_, lean_object* v_inst_1942_, lean_object* v_p_1943_, lean_object* v_as_1944_, size_t v_stop_1945_, lean_object* v_toPure_1946_, uint8_t v___x_1947_, uint8_t v_____do__lift_1948_){
_start:
{
if (v_____do__lift_1948_ == 0)
{
size_t v___x_1949_; size_t v___x_1950_; lean_object* v___x_1951_; 
lean_dec(v_toPure_1946_);
v___x_1949_ = ((size_t)1ULL);
v___x_1950_ = lean_usize_add(v_i_1941_, v___x_1949_);
v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1942_, v_p_1943_, v_as_1944_, v___x_1950_, v_stop_1945_);
return v___x_1951_;
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_dec_ref(v_as_1944_);
lean_dec(v_p_1943_);
lean_dec_ref(v_inst_1942_);
v___x_1952_ = lean_box(v___x_1947_);
v___x_1953_ = lean_apply_2(v_toPure_1946_, lean_box(0), v___x_1952_);
return v___x_1953_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_i_1941_ = stack[0].m_num;
lean_object* v_inst_1942_ = stack[1].m_obj;
lean_object* v_p_1943_ = stack[2].m_obj;
lean_object* v_as_1944_ = stack[3].m_obj;
size_t v_stop_1945_ = stack[4].m_num;
lean_object* v_toPure_1946_ = stack[5].m_obj;
uint8_t v___x_1947_ = stack[6].m_num;
uint8_t v_____do__lift_1948_ = stack[7].m_num;
lean_object* v_res_1954_;
v_res_1954_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(v_i_1941_, v_inst_1942_, v_p_1943_, v_as_1944_, v_stop_1945_, v_toPure_1946_, v___x_1947_, v_____do__lift_1948_);
stack->m_obj
 = v_res_1954_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___boxed(lean_object* v_inst_1955_, lean_object* v_p_1956_, lean_object* v_as_1957_, lean_object* v_i_1958_, lean_object* v_stop_1959_){
_start:
{
size_t v_i_boxed_1960_; size_t v_stop_boxed_1961_; lean_object* v_res_1962_; 
v_i_boxed_1960_ = lean_unbox_usize(v_i_1958_);
lean_dec(v_i_1958_);
v_stop_boxed_1961_ = lean_unbox_usize(v_stop_1959_);
lean_dec(v_stop_1959_);
v_res_1962_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1955_, v_p_1956_, v_as_1957_, v_i_boxed_1960_, v_stop_boxed_1961_);
return v_res_1962_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object* v_00_u03b1_1963_, lean_object* v_m_1964_, lean_object* v_inst_1965_, lean_object* v_p_1966_, lean_object* v_as_1967_, size_t v_i_1968_, size_t v_stop_1969_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1965_, v_p_1966_, v_as_1967_, v_i_1968_, v_stop_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1965_ = stack[2].m_obj;
lean_object* v_p_1966_ = stack[3].m_obj;
lean_object* v_as_1967_ = stack[4].m_obj;
size_t v_i_1968_ = stack[5].m_num;
size_t v_stop_1969_ = stack[6].m_num;
lean_object* v_res_1971_;
v_res_1971_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_1965_, v_p_1966_, v_as_1967_, v_i_1968_, v_stop_1969_);
stack->m_obj
 = v_res_1971_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___boxed(lean_object* v_00_u03b1_1972_, lean_object* v_m_1973_, lean_object* v_inst_1974_, lean_object* v_p_1975_, lean_object* v_as_1976_, lean_object* v_i_1977_, lean_object* v_stop_1978_){
_start:
{
size_t v_i_boxed_1979_; size_t v_stop_boxed_1980_; lean_object* v_res_1981_; 
v_i_boxed_1979_ = lean_unbox_usize(v_i_1977_);
lean_dec(v_i_1977_);
v_stop_boxed_1980_ = lean_unbox_usize(v_stop_1978_);
lean_dec(v_stop_1978_);
v_res_1981_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(v_00_u03b1_1972_, v_m_1973_, v_inst_1974_, v_p_1975_, v_as_1976_, v_i_boxed_1979_, v_stop_boxed_1980_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg(lean_object* v_inst_1982_, lean_object* v_p_1983_, lean_object* v_as_1984_, lean_object* v_start_1985_, lean_object* v_stop_1986_){
_start:
{
lean_object* v_toApplicative_1987_; lean_object* v_toPure_1988_; lean_object* v___y_1990_; uint8_t v___x_1997_; 
v_toApplicative_1987_ = lean_ctor_get(v_inst_1982_, 0);
v_toPure_1988_ = lean_ctor_get(v_toApplicative_1987_, 1);
v___x_1997_ = lean_nat_dec_lt(v_start_1985_, v_stop_1986_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
lean_inc(v_toPure_1988_);
lean_dec(v_stop_1986_);
lean_dec_ref(v_as_1984_);
lean_dec(v_p_1983_);
lean_dec_ref(v_inst_1982_);
v___x_1998_ = lean_box(v___x_1997_);
v___x_1999_ = lean_apply_2(v_toPure_1988_, lean_box(0), v___x_1998_);
return v___x_1999_;
}
else
{
lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_2000_ = lean_array_get_size(v_as_1984_);
v___x_2001_ = lean_nat_dec_le(v_stop_1986_, v___x_2000_);
if (v___x_2001_ == 0)
{
lean_dec(v_stop_1986_);
v___y_1990_ = v___x_2000_;
goto v___jp_1989_;
}
else
{
v___y_1990_ = v_stop_1986_;
goto v___jp_1989_;
}
}
v___jp_1989_:
{
uint8_t v___x_1991_; 
v___x_1991_ = lean_nat_dec_lt(v_start_1985_, v___y_1990_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
lean_inc(v_toPure_1988_);
lean_dec(v___y_1990_);
lean_dec_ref(v_as_1984_);
lean_dec(v_p_1983_);
lean_dec_ref(v_inst_1982_);
v___x_1992_ = lean_box(v___x_1991_);
v___x_1993_ = lean_apply_2(v_toPure_1988_, lean_box(0), v___x_1992_);
return v___x_1993_;
}
else
{
size_t v___x_1994_; size_t v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = lean_usize_of_nat(v_start_1985_);
v___x_1995_ = lean_usize_of_nat(v___y_1990_);
lean_dec(v___y_1990_);
v___x_1996_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1982_, v_p_1983_, v_as_1984_, v___x_1994_, v___x_1995_);
return v___x_1996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg___boxed(lean_object* v_inst_2002_, lean_object* v_p_2003_, lean_object* v_as_2004_, lean_object* v_start_2005_, lean_object* v_stop_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Array_anyMUnsafe___redArg(v_inst_2002_, v_p_2003_, v_as_2004_, v_start_2005_, v_stop_2006_);
lean_dec(v_start_2005_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe(lean_object* v_00_u03b1_2008_, lean_object* v_m_2009_, lean_object* v_inst_2010_, lean_object* v_p_2011_, lean_object* v_as_2012_, lean_object* v_start_2013_, lean_object* v_stop_2014_){
_start:
{
lean_object* v_toApplicative_2015_; lean_object* v_toPure_2016_; lean_object* v___y_2018_; uint8_t v___x_2025_; 
v_toApplicative_2015_ = lean_ctor_get(v_inst_2010_, 0);
v_toPure_2016_ = lean_ctor_get(v_toApplicative_2015_, 1);
v___x_2025_ = lean_nat_dec_lt(v_start_2013_, v_stop_2014_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_inc(v_toPure_2016_);
lean_dec(v_stop_2014_);
lean_dec_ref(v_as_2012_);
lean_dec(v_p_2011_);
lean_dec_ref(v_inst_2010_);
v___x_2026_ = lean_box(v___x_2025_);
v___x_2027_ = lean_apply_2(v_toPure_2016_, lean_box(0), v___x_2026_);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = lean_array_get_size(v_as_2012_);
v___x_2029_ = lean_nat_dec_le(v_stop_2014_, v___x_2028_);
if (v___x_2029_ == 0)
{
lean_dec(v_stop_2014_);
v___y_2018_ = v___x_2028_;
goto v___jp_2017_;
}
else
{
v___y_2018_ = v_stop_2014_;
goto v___jp_2017_;
}
}
v___jp_2017_:
{
uint8_t v___x_2019_; 
v___x_2019_ = lean_nat_dec_lt(v_start_2013_, v___y_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_inc(v_toPure_2016_);
lean_dec(v___y_2018_);
lean_dec_ref(v_as_2012_);
lean_dec(v_p_2011_);
lean_dec_ref(v_inst_2010_);
v___x_2020_ = lean_box(v___x_2019_);
v___x_2021_ = lean_apply_2(v_toPure_2016_, lean_box(0), v___x_2020_);
return v___x_2021_;
}
else
{
size_t v___x_2022_; size_t v___x_2023_; lean_object* v___x_2024_; 
v___x_2022_ = lean_usize_of_nat(v_start_2013_);
v___x_2023_ = lean_usize_of_nat(v___y_2018_);
lean_dec(v___y_2018_);
v___x_2024_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2010_, v_p_2011_, v_as_2012_, v___x_2022_, v___x_2023_);
return v___x_2024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___boxed(lean_object* v_00_u03b1_2030_, lean_object* v_m_2031_, lean_object* v_inst_2032_, lean_object* v_p_2033_, lean_object* v_as_2034_, lean_object* v_start_2035_, lean_object* v_stop_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Array_anyMUnsafe(v_00_u03b1_2030_, v_m_2031_, v_inst_2032_, v_p_2033_, v_as_2034_, v_start_2035_, v_stop_2036_);
lean_dec(v_start_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0___boxed(lean_object* v_j_2038_, lean_object* v_inst_2039_, lean_object* v_p_2040_, lean_object* v_as_2041_, lean_object* v_stop_2042_, lean_object* v_toPure_2043_, lean_object* v___x_2044_, lean_object* v_____do__lift_2045_){
_start:
{
uint8_t v___x_63__boxed_2046_; uint8_t v_____do__lift_64__boxed_2047_; lean_object* v_res_2048_; 
v___x_63__boxed_2046_ = lean_unbox(v___x_2044_);
v_____do__lift_64__boxed_2047_ = lean_unbox(v_____do__lift_2045_);
v_res_2048_ = l_Array_anyM_loop___redArg___lam__0(v_j_2038_, v_inst_2039_, v_p_2040_, v_as_2041_, v_stop_2042_, v_toPure_2043_, v___x_63__boxed_2046_, v_____do__lift_64__boxed_2047_);
lean_dec(v_j_2038_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg(lean_object* v_inst_2049_, lean_object* v_p_2050_, lean_object* v_as_2051_, lean_object* v_stop_2052_, lean_object* v_j_2053_){
_start:
{
lean_object* v_toApplicative_2054_; lean_object* v_toBind_2055_; lean_object* v_toPure_2056_; uint8_t v___x_2057_; 
v_toApplicative_2054_ = lean_ctor_get(v_inst_2049_, 0);
v_toBind_2055_ = lean_ctor_get(v_inst_2049_, 1);
lean_inc(v_toBind_2055_);
v_toPure_2056_ = lean_ctor_get(v_toApplicative_2054_, 1);
lean_inc(v_toPure_2056_);
v___x_2057_ = lean_nat_dec_lt(v_j_2053_, v_stop_2052_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec(v_toBind_2055_);
lean_dec(v_j_2053_);
lean_dec(v_stop_2052_);
lean_dec_ref(v_as_2051_);
lean_dec(v_p_2050_);
lean_dec_ref(v_inst_2049_);
v___x_2058_ = lean_box(v___x_2057_);
v___x_2059_ = lean_apply_2(v_toPure_2056_, lean_box(0), v___x_2058_);
return v___x_2059_;
}
else
{
lean_object* v___x_2060_; lean_object* v___f_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2060_ = lean_box(v___x_2057_);
lean_inc_ref(v_as_2051_);
lean_inc(v_p_2050_);
lean_inc(v_j_2053_);
v___f_2061_ = lean_alloc_closure((void*)(l_Array_anyM_loop___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_2061_, 0, v_j_2053_);
lean_closure_set(v___f_2061_, 1, v_inst_2049_);
lean_closure_set(v___f_2061_, 2, v_p_2050_);
lean_closure_set(v___f_2061_, 3, v_as_2051_);
lean_closure_set(v___f_2061_, 4, v_stop_2052_);
lean_closure_set(v___f_2061_, 5, v_toPure_2056_);
lean_closure_set(v___f_2061_, 6, v___x_2060_);
v___x_2062_ = lean_array_fget(v_as_2051_, v_j_2053_);
lean_dec(v_j_2053_);
lean_dec_ref(v_as_2051_);
v___x_2063_ = lean_apply_1(v_p_2050_, v___x_2062_);
v___x_2064_ = lean_apply_4(v_toBind_2055_, lean_box(0), lean_box(0), v___x_2063_, v___f_2061_);
return v___x_2064_;
}
}
}
lean_object* l_Array_anyM_loop___redArg___lam__0(lean_object* v_j_2065_, lean_object* v_inst_2066_, lean_object* v_p_2067_, lean_object* v_as_2068_, lean_object* v_stop_2069_, lean_object* v_toPure_2070_, uint8_t v___x_2071_, uint8_t v_____do__lift_2072_){
_start:
{
if (v_____do__lift_2072_ == 0)
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_dec(v_toPure_2070_);
v___x_2073_ = lean_unsigned_to_nat(1u);
v___x_2074_ = lean_nat_add(v_j_2065_, v___x_2073_);
v___x_2075_ = l_Array_anyM_loop___redArg(v_inst_2066_, v_p_2067_, v_as_2068_, v_stop_2069_, v___x_2074_);
return v___x_2075_;
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec(v_stop_2069_);
lean_dec_ref(v_as_2068_);
lean_dec(v_p_2067_);
lean_dec_ref(v_inst_2066_);
v___x_2076_ = lean_box(v___x_2071_);
v___x_2077_ = lean_apply_2(v_toPure_2070_, lean_box(0), v___x_2076_);
return v___x_2077_;
}
}
}
LEAN_EXPORT void l_Array_anyM_loop___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_j_2065_ = stack[0].m_obj;
lean_object* v_inst_2066_ = stack[1].m_obj;
lean_object* v_p_2067_ = stack[2].m_obj;
lean_object* v_as_2068_ = stack[3].m_obj;
lean_object* v_stop_2069_ = stack[4].m_obj;
lean_object* v_toPure_2070_ = stack[5].m_obj;
uint8_t v___x_2071_ = stack[6].m_num;
uint8_t v_____do__lift_2072_ = stack[7].m_num;
lean_object* v_res_2078_;
v_res_2078_ = l_Array_anyM_loop___redArg___lam__0(v_j_2065_, v_inst_2066_, v_p_2067_, v_as_2068_, v_stop_2069_, v_toPure_2070_, v___x_2071_, v_____do__lift_2072_);
stack->m_obj
 = v_res_2078_;
}
LEAN_EXPORT lean_object* l_Array_anyM_loop(lean_object* v_00_u03b1_2079_, lean_object* v_m_2080_, lean_object* v_inst_2081_, lean_object* v_p_2082_, lean_object* v_as_2083_, lean_object* v_stop_2084_, lean_object* v_h_2085_, lean_object* v_j_2086_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Array_anyM_loop___redArg(v_inst_2081_, v_p_2082_, v_as_2083_, v_stop_2084_, v_j_2086_);
return v___x_2087_;
}
}
lean_object* l_Array_allM___redArg___lam__0(lean_object* v_toPure_2088_, uint8_t v_____do__lift_2089_){
_start:
{
if (v_____do__lift_2089_ == 0)
{
uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2090_ = 1;
v___x_2091_ = lean_box(v___x_2090_);
v___x_2092_ = lean_apply_2(v_toPure_2088_, lean_box(0), v___x_2091_);
return v___x_2092_;
}
else
{
uint8_t v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2093_ = 0;
v___x_2094_ = lean_box(v___x_2093_);
v___x_2095_ = lean_apply_2(v_toPure_2088_, lean_box(0), v___x_2094_);
return v___x_2095_;
}
}
}
LEAN_EXPORT void l_Array_allM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_2088_ = stack[0].m_obj;
uint8_t v_____do__lift_2089_ = stack[1].m_num;
lean_object* v_res_2096_;
v_res_2096_ = l_Array_allM___redArg___lam__0(v_toPure_2088_, v_____do__lift_2089_);
stack->m_obj
 = v_res_2096_;
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0___boxed(lean_object* v_toPure_2097_, lean_object* v_____do__lift_2098_){
_start:
{
uint8_t v_____do__lift_117__boxed_2099_; lean_object* v_res_2100_; 
v_____do__lift_117__boxed_2099_ = lean_unbox(v_____do__lift_2098_);
v_res_2100_ = l_Array_allM___redArg___lam__0(v_toPure_2097_, v_____do__lift_117__boxed_2099_);
return v_res_2100_;
}
}
lean_object* l_Array_allM___redArg___lam__1(lean_object* v_toPure_2101_, uint8_t v___x_2102_, uint8_t v_____do__lift_2103_){
_start:
{
if (v_____do__lift_2103_ == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_box(v___x_2102_);
v___x_2105_ = lean_apply_2(v_toPure_2101_, lean_box(0), v___x_2104_);
return v___x_2105_;
}
else
{
uint8_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = 0;
v___x_2107_ = lean_box(v___x_2106_);
v___x_2108_ = lean_apply_2(v_toPure_2101_, lean_box(0), v___x_2107_);
return v___x_2108_;
}
}
}
LEAN_EXPORT void l_Array_allM___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_2101_ = stack[0].m_obj;
uint8_t v___x_2102_ = stack[1].m_num;
uint8_t v_____do__lift_2103_ = stack[2].m_num;
lean_object* v_res_2109_;
v_res_2109_ = l_Array_allM___redArg___lam__1(v_toPure_2101_, v___x_2102_, v_____do__lift_2103_);
stack->m_obj
 = v_res_2109_;
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1___boxed(lean_object* v_toPure_2110_, lean_object* v___x_2111_, lean_object* v_____do__lift_2112_){
_start:
{
uint8_t v___x_140__boxed_2113_; uint8_t v_____do__lift_141__boxed_2114_; lean_object* v_res_2115_; 
v___x_140__boxed_2113_ = lean_unbox(v___x_2111_);
v_____do__lift_141__boxed_2114_ = lean_unbox(v_____do__lift_2112_);
v_res_2115_ = l_Array_allM___redArg___lam__1(v_toPure_2110_, v___x_140__boxed_2113_, v_____do__lift_141__boxed_2114_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__2(lean_object* v_p_2116_, lean_object* v_toBind_2117_, lean_object* v___f_2118_, lean_object* v_v_2119_){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = lean_apply_1(v_p_2116_, v_v_2119_);
v___x_2121_ = lean_apply_4(v_toBind_2117_, lean_box(0), lean_box(0), v___x_2120_, v___f_2118_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg(lean_object* v_inst_2122_, lean_object* v_p_2123_, lean_object* v_as_2124_, lean_object* v_start_2125_, lean_object* v_stop_2126_){
_start:
{
lean_object* v_toApplicative_2127_; lean_object* v_toBind_2128_; lean_object* v_toPure_2129_; lean_object* v___f_2130_; uint8_t v___x_2131_; 
v_toApplicative_2127_ = lean_ctor_get(v_inst_2122_, 0);
v_toBind_2128_ = lean_ctor_get(v_inst_2122_, 1);
lean_inc(v_toBind_2128_);
v_toPure_2129_ = lean_ctor_get(v_toApplicative_2127_, 1);
lean_inc(v_toPure_2129_);
v___f_2130_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2130_, 0, v_toPure_2129_);
v___x_2131_ = lean_nat_dec_lt(v_start_2125_, v_stop_2126_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_inc(v_toPure_2129_);
lean_dec(v_stop_2126_);
lean_dec_ref(v_as_2124_);
lean_dec(v_p_2123_);
lean_dec_ref(v_inst_2122_);
v___x_2132_ = lean_box(v___x_2131_);
v___x_2133_ = lean_apply_2(v_toPure_2129_, lean_box(0), v___x_2132_);
v___x_2134_ = lean_apply_4(v_toBind_2128_, lean_box(0), lean_box(0), v___x_2133_, v___f_2130_);
return v___x_2134_;
}
else
{
lean_object* v___x_2135_; lean_object* v___f_2136_; lean_object* v___f_2137_; lean_object* v___y_2139_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2135_ = lean_box(v___x_2131_);
lean_inc(v_toPure_2129_);
v___f_2136_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2136_, 0, v_toPure_2129_);
lean_closure_set(v___f_2136_, 1, v___x_2135_);
lean_inc(v_toBind_2128_);
v___f_2137_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2137_, 0, v_p_2123_);
lean_closure_set(v___f_2137_, 1, v_toBind_2128_);
lean_closure_set(v___f_2137_, 2, v___f_2136_);
v___x_2148_ = lean_array_get_size(v_as_2124_);
v___x_2149_ = lean_nat_dec_le(v_stop_2126_, v___x_2148_);
if (v___x_2149_ == 0)
{
lean_dec(v_stop_2126_);
v___y_2139_ = v___x_2148_;
goto v___jp_2138_;
}
else
{
v___y_2139_ = v_stop_2126_;
goto v___jp_2138_;
}
v___jp_2138_:
{
uint8_t v___x_2140_; 
v___x_2140_ = lean_nat_dec_lt(v_start_2125_, v___y_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_inc(v_toPure_2129_);
lean_dec(v___y_2139_);
lean_dec_ref(v___f_2137_);
lean_dec_ref(v_as_2124_);
lean_dec_ref(v_inst_2122_);
v___x_2141_ = lean_box(v___x_2140_);
v___x_2142_ = lean_apply_2(v_toPure_2129_, lean_box(0), v___x_2141_);
v___x_2143_ = lean_apply_4(v_toBind_2128_, lean_box(0), lean_box(0), v___x_2142_, v___f_2130_);
return v___x_2143_;
}
else
{
size_t v___x_2144_; size_t v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2144_ = lean_usize_of_nat(v_start_2125_);
v___x_2145_ = lean_usize_of_nat(v___y_2139_);
lean_dec(v___y_2139_);
v___x_2146_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2122_, v___f_2137_, v_as_2124_, v___x_2144_, v___x_2145_);
v___x_2147_ = lean_apply_4(v_toBind_2128_, lean_box(0), lean_box(0), v___x_2146_, v___f_2130_);
return v___x_2147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___boxed(lean_object* v_inst_2150_, lean_object* v_p_2151_, lean_object* v_as_2152_, lean_object* v_start_2153_, lean_object* v_stop_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Array_allM___redArg(v_inst_2150_, v_p_2151_, v_as_2152_, v_start_2153_, v_stop_2154_);
lean_dec(v_start_2153_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Array_allM(lean_object* v_00_u03b1_2156_, lean_object* v_m_2157_, lean_object* v_inst_2158_, lean_object* v_p_2159_, lean_object* v_as_2160_, lean_object* v_start_2161_, lean_object* v_stop_2162_){
_start:
{
lean_object* v_toApplicative_2163_; lean_object* v_toBind_2164_; lean_object* v_toPure_2165_; lean_object* v___f_2166_; uint8_t v___x_2167_; 
v_toApplicative_2163_ = lean_ctor_get(v_inst_2158_, 0);
v_toBind_2164_ = lean_ctor_get(v_inst_2158_, 1);
lean_inc(v_toBind_2164_);
v_toPure_2165_ = lean_ctor_get(v_toApplicative_2163_, 1);
lean_inc(v_toPure_2165_);
v___f_2166_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2166_, 0, v_toPure_2165_);
v___x_2167_ = lean_nat_dec_lt(v_start_2161_, v_stop_2162_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
lean_inc(v_toPure_2165_);
lean_dec(v_stop_2162_);
lean_dec_ref(v_as_2160_);
lean_dec(v_p_2159_);
lean_dec_ref(v_inst_2158_);
v___x_2168_ = lean_box(v___x_2167_);
v___x_2169_ = lean_apply_2(v_toPure_2165_, lean_box(0), v___x_2168_);
v___x_2170_ = lean_apply_4(v_toBind_2164_, lean_box(0), lean_box(0), v___x_2169_, v___f_2166_);
return v___x_2170_;
}
else
{
lean_object* v___x_2171_; lean_object* v___f_2172_; lean_object* v___f_2173_; lean_object* v___y_2175_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2171_ = lean_box(v___x_2167_);
lean_inc(v_toPure_2165_);
v___f_2172_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2172_, 0, v_toPure_2165_);
lean_closure_set(v___f_2172_, 1, v___x_2171_);
lean_inc(v_toBind_2164_);
v___f_2173_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2173_, 0, v_p_2159_);
lean_closure_set(v___f_2173_, 1, v_toBind_2164_);
lean_closure_set(v___f_2173_, 2, v___f_2172_);
v___x_2184_ = lean_array_get_size(v_as_2160_);
v___x_2185_ = lean_nat_dec_le(v_stop_2162_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_dec(v_stop_2162_);
v___y_2175_ = v___x_2184_;
goto v___jp_2174_;
}
else
{
v___y_2175_ = v_stop_2162_;
goto v___jp_2174_;
}
v___jp_2174_:
{
uint8_t v___x_2176_; 
v___x_2176_ = lean_nat_dec_lt(v_start_2161_, v___y_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_inc(v_toPure_2165_);
lean_dec(v___y_2175_);
lean_dec_ref(v___f_2173_);
lean_dec_ref(v_as_2160_);
lean_dec_ref(v_inst_2158_);
v___x_2177_ = lean_box(v___x_2176_);
v___x_2178_ = lean_apply_2(v_toPure_2165_, lean_box(0), v___x_2177_);
v___x_2179_ = lean_apply_4(v_toBind_2164_, lean_box(0), lean_box(0), v___x_2178_, v___f_2166_);
return v___x_2179_;
}
else
{
size_t v___x_2180_; size_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2180_ = lean_usize_of_nat(v_start_2161_);
v___x_2181_ = lean_usize_of_nat(v___y_2175_);
lean_dec(v___y_2175_);
v___x_2182_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2158_, v___f_2173_, v_as_2160_, v___x_2180_, v___x_2181_);
v___x_2183_ = lean_apply_4(v_toBind_2164_, lean_box(0), lean_box(0), v___x_2182_, v___f_2166_);
return v___x_2183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___boxed(lean_object* v_00_u03b1_2186_, lean_object* v_m_2187_, lean_object* v_inst_2188_, lean_object* v_p_2189_, lean_object* v_as_2190_, lean_object* v_start_2191_, lean_object* v_stop_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Array_allM(v_00_u03b1_2186_, v_m_2187_, v_inst_2188_, v_p_2189_, v_as_2190_, v_start_2191_, v_stop_2192_);
lean_dec(v_start_2191_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed(lean_object* v_inst_2194_, lean_object* v_f_2195_, lean_object* v_as_2196_, lean_object* v_n_2197_, lean_object* v_toPure_2198_, lean_object* v_r_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(v_inst_2194_, v_f_2195_, v_as_2196_, v_n_2197_, v_toPure_2198_, v_r_2199_);
lean_dec(v_n_2197_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(lean_object* v_inst_2201_, lean_object* v_f_2202_, lean_object* v_as_2203_, lean_object* v_i_2204_){
_start:
{
lean_object* v_toApplicative_2205_; lean_object* v_toBind_2206_; lean_object* v_toPure_2207_; lean_object* v_zero_2208_; uint8_t v_isZero_2209_; 
v_toApplicative_2205_ = lean_ctor_get(v_inst_2201_, 0);
v_toBind_2206_ = lean_ctor_get(v_inst_2201_, 1);
lean_inc(v_toBind_2206_);
v_toPure_2207_ = lean_ctor_get(v_toApplicative_2205_, 1);
lean_inc(v_toPure_2207_);
v_zero_2208_ = lean_unsigned_to_nat(0u);
v_isZero_2209_ = lean_nat_dec_eq(v_i_2204_, v_zero_2208_);
if (v_isZero_2209_ == 1)
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_dec(v_toBind_2206_);
lean_dec_ref(v_as_2203_);
lean_dec(v_f_2202_);
lean_dec_ref(v_inst_2201_);
v___x_2210_ = lean_box(0);
v___x_2211_ = lean_apply_2(v_toPure_2207_, lean_box(0), v___x_2210_);
return v___x_2211_;
}
else
{
lean_object* v_one_2212_; lean_object* v_n_2213_; lean_object* v___f_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v_one_2212_ = lean_unsigned_to_nat(1u);
v_n_2213_ = lean_nat_sub(v_i_2204_, v_one_2212_);
lean_inc(v_n_2213_);
lean_inc_ref(v_as_2203_);
lean_inc(v_f_2202_);
v___f_2214_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2214_, 0, v_inst_2201_);
lean_closure_set(v___f_2214_, 1, v_f_2202_);
lean_closure_set(v___f_2214_, 2, v_as_2203_);
lean_closure_set(v___f_2214_, 3, v_n_2213_);
lean_closure_set(v___f_2214_, 4, v_toPure_2207_);
v___x_2215_ = lean_array_fget(v_as_2203_, v_n_2213_);
lean_dec(v_n_2213_);
lean_dec_ref(v_as_2203_);
v___x_2216_ = lean_apply_1(v_f_2202_, v___x_2215_);
v___x_2217_ = lean_apply_4(v_toBind_2206_, lean_box(0), lean_box(0), v___x_2216_, v___f_2214_);
return v___x_2217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(lean_object* v_inst_2218_, lean_object* v_f_2219_, lean_object* v_as_2220_, lean_object* v_n_2221_, lean_object* v_toPure_2222_, lean_object* v_r_2223_){
_start:
{
if (lean_obj_tag(v_r_2223_) == 0)
{
lean_object* v___x_2224_; 
lean_dec(v_toPure_2222_);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2218_, v_f_2219_, v_as_2220_, v_n_2221_);
return v___x_2224_;
}
else
{
lean_object* v___x_2225_; 
lean_dec_ref(v_as_2220_);
lean_dec(v_f_2219_);
lean_dec_ref(v_inst_2218_);
v___x_2225_ = lean_apply_2(v_toPure_2222_, lean_box(0), v_r_2223_);
return v___x_2225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___boxed(lean_object* v_inst_2226_, lean_object* v_f_2227_, lean_object* v_as_2228_, lean_object* v_i_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2226_, v_f_2227_, v_as_2228_, v_i_2229_);
lean_dec(v_i_2229_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_object* v_00_u03b1_2231_, lean_object* v_00_u03b2_2232_, lean_object* v_m_2233_, lean_object* v_inst_2234_, lean_object* v_f_2235_, lean_object* v_as_2236_, lean_object* v_i_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2234_, v_f_2235_, v_as_2236_, v_i_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___boxed(lean_object* v_00_u03b1_2240_, lean_object* v_00_u03b2_2241_, lean_object* v_m_2242_, lean_object* v_inst_2243_, lean_object* v_f_2244_, lean_object* v_as_2245_, lean_object* v_i_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(v_00_u03b1_2240_, v_00_u03b2_2241_, v_m_2242_, v_inst_2243_, v_f_2244_, v_as_2245_, v_i_2246_, v_a_2247_);
lean_dec(v_i_2246_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f___redArg(lean_object* v_inst_2249_, lean_object* v_f_2250_, lean_object* v_as_2251_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = lean_array_get_size(v_as_2251_);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2249_, v_f_2250_, v_as_2251_, v___x_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f(lean_object* v_00_u03b1_2254_, lean_object* v_00_u03b2_2255_, lean_object* v_m_2256_, lean_object* v_inst_2257_, lean_object* v_f_2258_, lean_object* v_as_2259_){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = lean_array_get_size(v_as_2259_);
v___x_2261_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2257_, v_f_2258_, v_as_2259_, v___x_2260_);
return v___x_2261_;
}
}
lean_object* l_Array_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2262_, lean_object* v_a_2263_, uint8_t v_____do__lift_2264_){
_start:
{
if (v_____do__lift_2264_ == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
lean_dec(v_a_2263_);
v___x_2265_ = lean_box(0);
v___x_2266_ = lean_apply_2(v_toPure_2262_, lean_box(0), v___x_2265_);
return v___x_2266_;
}
else
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2267_, 0, v_a_2263_);
v___x_2268_ = lean_apply_2(v_toPure_2262_, lean_box(0), v___x_2267_);
return v___x_2268_;
}
}
}
LEAN_EXPORT void l_Array_findRevM_x3f___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_2262_ = stack[0].m_obj;
lean_object* v_a_2263_ = stack[1].m_obj;
uint8_t v_____do__lift_2264_ = stack[2].m_num;
lean_object* v_res_2269_;
v_res_2269_ = l_Array_findRevM_x3f___redArg___lam__0(v_toPure_2262_, v_a_2263_, v_____do__lift_2264_);
stack->m_obj
 = v_res_2269_;
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2270_, lean_object* v_a_2271_, lean_object* v_____do__lift_2272_){
_start:
{
uint8_t v_____do__lift_60__boxed_2273_; lean_object* v_res_2274_; 
v_____do__lift_60__boxed_2273_ = lean_unbox(v_____do__lift_2272_);
v_res_2274_ = l_Array_findRevM_x3f___redArg___lam__0(v_toPure_2270_, v_a_2271_, v_____do__lift_60__boxed_2273_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2275_, lean_object* v_p_2276_, lean_object* v_toBind_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v___f_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
lean_inc(v_a_2278_);
v___f_2279_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2279_, 0, v_toPure_2275_);
lean_closure_set(v___f_2279_, 1, v_a_2278_);
v___x_2280_ = lean_apply_1(v_p_2276_, v_a_2278_);
v___x_2281_ = lean_apply_4(v_toBind_2277_, lean_box(0), lean_box(0), v___x_2280_, v___f_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg(lean_object* v_inst_2282_, lean_object* v_p_2283_, lean_object* v_as_2284_){
_start:
{
lean_object* v_toApplicative_2285_; lean_object* v_toBind_2286_; lean_object* v_toPure_2287_; lean_object* v___f_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v_toApplicative_2285_ = lean_ctor_get(v_inst_2282_, 0);
v_toBind_2286_ = lean_ctor_get(v_inst_2282_, 1);
v_toPure_2287_ = lean_ctor_get(v_toApplicative_2285_, 1);
lean_inc(v_toBind_2286_);
lean_inc(v_toPure_2287_);
v___f_2288_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2288_, 0, v_toPure_2287_);
lean_closure_set(v___f_2288_, 1, v_p_2283_);
lean_closure_set(v___f_2288_, 2, v_toBind_2286_);
v___x_2289_ = lean_array_get_size(v_as_2284_);
v___x_2290_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2282_, v___f_2288_, v_as_2284_, v___x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f(lean_object* v_00_u03b1_2291_, lean_object* v_m_2292_, lean_object* v_inst_2293_, lean_object* v_p_2294_, lean_object* v_as_2295_){
_start:
{
lean_object* v_toApplicative_2296_; lean_object* v_toBind_2297_; lean_object* v_toPure_2298_; lean_object* v___f_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v_toApplicative_2296_ = lean_ctor_get(v_inst_2293_, 0);
v_toBind_2297_ = lean_ctor_get(v_inst_2293_, 1);
v_toPure_2298_ = lean_ctor_get(v_toApplicative_2296_, 1);
lean_inc(v_toBind_2297_);
lean_inc(v_toPure_2298_);
v___f_2299_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2299_, 0, v_toPure_2298_);
lean_closure_set(v___f_2299_, 1, v_p_2294_);
lean_closure_set(v___f_2299_, 2, v_toBind_2297_);
v___x_2300_ = lean_array_get_size(v_as_2295_);
v___x_2301_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2293_, v___f_2299_, v_as_2295_, v___x_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___lam__0(lean_object* v_f_2302_, lean_object* v_x_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_apply_1(v_f_2302_, v___y_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg(lean_object* v_inst_2306_, lean_object* v_f_2307_, lean_object* v_as_2308_, lean_object* v_start_2309_, lean_object* v_stop_2310_){
_start:
{
lean_object* v_toApplicative_2311_; lean_object* v_toPure_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v_toApplicative_2311_ = lean_ctor_get(v_inst_2306_, 0);
v_toPure_2312_ = lean_ctor_get(v_toApplicative_2311_, 1);
v___x_2313_ = lean_box(0);
v___x_2314_ = lean_nat_dec_lt(v_start_2309_, v_stop_2310_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; 
lean_inc(v_toPure_2312_);
lean_dec_ref(v_as_2308_);
lean_dec(v_f_2307_);
lean_dec_ref(v_inst_2306_);
v___x_2315_ = lean_apply_2(v_toPure_2312_, lean_box(0), v___x_2313_);
return v___x_2315_;
}
else
{
lean_object* v___f_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___f_2316_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2316_, 0, v_f_2307_);
v___x_2317_ = lean_array_get_size(v_as_2308_);
v___x_2318_ = lean_nat_dec_le(v_stop_2310_, v___x_2317_);
if (v___x_2318_ == 0)
{
uint8_t v___x_2319_; 
v___x_2319_ = lean_nat_dec_lt(v_start_2309_, v___x_2317_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; 
lean_inc(v_toPure_2312_);
lean_dec_ref(v___f_2316_);
lean_dec_ref(v_as_2308_);
lean_dec_ref(v_inst_2306_);
v___x_2320_ = lean_apply_2(v_toPure_2312_, lean_box(0), v___x_2313_);
return v___x_2320_;
}
else
{
size_t v___x_2321_; size_t v___x_2322_; lean_object* v___x_2323_; 
v___x_2321_ = lean_usize_of_nat(v_start_2309_);
v___x_2322_ = lean_usize_of_nat(v___x_2317_);
v___x_2323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2306_, v___f_2316_, v_as_2308_, v___x_2321_, v___x_2322_, v___x_2313_);
return v___x_2323_;
}
}
else
{
size_t v___x_2324_; size_t v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = lean_usize_of_nat(v_start_2309_);
v___x_2325_ = lean_usize_of_nat(v_stop_2310_);
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2306_, v___f_2316_, v_as_2308_, v___x_2324_, v___x_2325_, v___x_2313_);
return v___x_2326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___boxed(lean_object* v_inst_2327_, lean_object* v_f_2328_, lean_object* v_as_2329_, lean_object* v_start_2330_, lean_object* v_stop_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Array_forM___redArg(v_inst_2327_, v_f_2328_, v_as_2329_, v_start_2330_, v_stop_2331_);
lean_dec(v_stop_2331_);
lean_dec(v_start_2330_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Array_forM(lean_object* v_00_u03b1_2333_, lean_object* v_m_2334_, lean_object* v_inst_2335_, lean_object* v_f_2336_, lean_object* v_as_2337_, lean_object* v_start_2338_, lean_object* v_stop_2339_){
_start:
{
lean_object* v_toApplicative_2340_; lean_object* v_toPure_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v_toApplicative_2340_ = lean_ctor_get(v_inst_2335_, 0);
v_toPure_2341_ = lean_ctor_get(v_toApplicative_2340_, 1);
v___x_2342_ = lean_box(0);
v___x_2343_ = lean_nat_dec_lt(v_start_2338_, v_stop_2339_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; 
lean_inc(v_toPure_2341_);
lean_dec_ref(v_as_2337_);
lean_dec(v_f_2336_);
lean_dec_ref(v_inst_2335_);
v___x_2344_ = lean_apply_2(v_toPure_2341_, lean_box(0), v___x_2342_);
return v___x_2344_;
}
else
{
lean_object* v___f_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___f_2345_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2345_, 0, v_f_2336_);
v___x_2346_ = lean_array_get_size(v_as_2337_);
v___x_2347_ = lean_nat_dec_le(v_stop_2339_, v___x_2346_);
if (v___x_2347_ == 0)
{
uint8_t v___x_2348_; 
v___x_2348_ = lean_nat_dec_lt(v_start_2338_, v___x_2346_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; 
lean_inc(v_toPure_2341_);
lean_dec_ref(v___f_2345_);
lean_dec_ref(v_as_2337_);
lean_dec_ref(v_inst_2335_);
v___x_2349_ = lean_apply_2(v_toPure_2341_, lean_box(0), v___x_2342_);
return v___x_2349_;
}
else
{
size_t v___x_2350_; size_t v___x_2351_; lean_object* v___x_2352_; 
v___x_2350_ = lean_usize_of_nat(v_start_2338_);
v___x_2351_ = lean_usize_of_nat(v___x_2346_);
v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2335_, v___f_2345_, v_as_2337_, v___x_2350_, v___x_2351_, v___x_2342_);
return v___x_2352_;
}
}
else
{
size_t v___x_2353_; size_t v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = lean_usize_of_nat(v_start_2338_);
v___x_2354_ = lean_usize_of_nat(v_stop_2339_);
v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2335_, v___f_2345_, v_as_2337_, v___x_2353_, v___x_2354_, v___x_2342_);
return v___x_2355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___boxed(lean_object* v_00_u03b1_2356_, lean_object* v_m_2357_, lean_object* v_inst_2358_, lean_object* v_f_2359_, lean_object* v_as_2360_, lean_object* v_start_2361_, lean_object* v_stop_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Array_forM(v_00_u03b1_2356_, v_m_2357_, v_inst_2358_, v_f_2359_, v_as_2360_, v_start_2361_, v_stop_2362_);
lean_dec(v_stop_2362_);
lean_dec(v_start_2361_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg___lam__1(lean_object* v_inst_2364_, lean_object* v_xs_2365_, lean_object* v_f_2366_){
_start:
{
lean_object* v_toApplicative_2367_; lean_object* v_toPure_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v_toApplicative_2367_ = lean_ctor_get(v_inst_2364_, 0);
v_toPure_2368_ = lean_ctor_get(v_toApplicative_2367_, 1);
v___x_2369_ = lean_unsigned_to_nat(0u);
v___x_2370_ = lean_array_get_size(v_xs_2365_);
v___x_2371_ = lean_box(0);
v___x_2372_ = lean_nat_dec_lt(v___x_2369_, v___x_2370_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; 
lean_inc(v_toPure_2368_);
lean_dec(v_f_2366_);
lean_dec_ref(v_xs_2365_);
lean_dec_ref(v_inst_2364_);
v___x_2373_ = lean_apply_2(v_toPure_2368_, lean_box(0), v___x_2371_);
return v___x_2373_;
}
else
{
lean_object* v___f_2374_; uint8_t v___x_2375_; 
v___f_2374_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2374_, 0, v_f_2366_);
v___x_2375_ = lean_nat_dec_le(v___x_2370_, v___x_2370_);
if (v___x_2375_ == 0)
{
if (v___x_2372_ == 0)
{
lean_object* v___x_2376_; 
lean_inc(v_toPure_2368_);
lean_dec_ref(v___f_2374_);
lean_dec_ref(v_xs_2365_);
lean_dec_ref(v_inst_2364_);
v___x_2376_ = lean_apply_2(v_toPure_2368_, lean_box(0), v___x_2371_);
return v___x_2376_;
}
else
{
size_t v___x_2377_; size_t v___x_2378_; lean_object* v___x_2379_; 
v___x_2377_ = ((size_t)0ULL);
v___x_2378_ = lean_usize_of_nat(v___x_2370_);
v___x_2379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2364_, v___f_2374_, v_xs_2365_, v___x_2377_, v___x_2378_, v___x_2371_);
return v___x_2379_;
}
}
else
{
size_t v___x_2380_; size_t v___x_2381_; lean_object* v___x_2382_; 
v___x_2380_ = ((size_t)0ULL);
v___x_2381_ = lean_usize_of_nat(v___x_2370_);
v___x_2382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2364_, v___f_2374_, v_xs_2365_, v___x_2380_, v___x_2381_, v___x_2371_);
return v___x_2382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg(lean_object* v_inst_2383_){
_start:
{
lean_object* v___f_2384_; 
v___f_2384_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2384_, 0, v_inst_2383_);
return v___f_2384_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad(lean_object* v_00_u03b1_2385_, lean_object* v_m_2386_, lean_object* v_inst_2387_){
_start:
{
lean_object* v___f_2388_; 
v___f_2388_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2388_, 0, v_inst_2387_);
return v___f_2388_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___lam__0(lean_object* v_f_2389_, lean_object* v_a_2390_, lean_object* v_x_2391_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_apply_1(v_f_2389_, v_a_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg(lean_object* v_inst_2393_, lean_object* v_f_2394_, lean_object* v_as_2395_, lean_object* v_start_2396_, lean_object* v_stop_2397_){
_start:
{
lean_object* v_toApplicative_2398_; lean_object* v_toPure_2399_; lean_object* v___f_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; 
v_toApplicative_2398_ = lean_ctor_get(v_inst_2393_, 0);
v_toPure_2399_ = lean_ctor_get(v_toApplicative_2398_, 1);
v___f_2400_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2400_, 0, v_f_2394_);
v___x_2401_ = lean_box(0);
v___x_2402_ = lean_array_get_size(v_as_2395_);
v___x_2403_ = lean_nat_dec_le(v_start_2396_, v___x_2402_);
if (v___x_2403_ == 0)
{
uint8_t v___x_2404_; 
v___x_2404_ = lean_nat_dec_lt(v_stop_2397_, v___x_2402_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; 
lean_inc(v_toPure_2399_);
lean_dec_ref(v___f_2400_);
lean_dec_ref(v_as_2395_);
lean_dec_ref(v_inst_2393_);
v___x_2405_ = lean_apply_2(v_toPure_2399_, lean_box(0), v___x_2401_);
return v___x_2405_;
}
else
{
size_t v___x_2406_; size_t v___x_2407_; lean_object* v___x_2408_; 
v___x_2406_ = lean_usize_of_nat(v___x_2402_);
v___x_2407_ = lean_usize_of_nat(v_stop_2397_);
v___x_2408_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2393_, v___f_2400_, v_as_2395_, v___x_2406_, v___x_2407_, v___x_2401_);
return v___x_2408_;
}
}
else
{
uint8_t v___x_2409_; 
v___x_2409_ = lean_nat_dec_lt(v_stop_2397_, v_start_2396_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; 
lean_inc(v_toPure_2399_);
lean_dec_ref(v___f_2400_);
lean_dec_ref(v_as_2395_);
lean_dec_ref(v_inst_2393_);
v___x_2410_ = lean_apply_2(v_toPure_2399_, lean_box(0), v___x_2401_);
return v___x_2410_;
}
else
{
size_t v___x_2411_; size_t v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = lean_usize_of_nat(v_start_2396_);
v___x_2412_ = lean_usize_of_nat(v_stop_2397_);
v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2393_, v___f_2400_, v_as_2395_, v___x_2411_, v___x_2412_, v___x_2401_);
return v___x_2413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___boxed(lean_object* v_inst_2414_, lean_object* v_f_2415_, lean_object* v_as_2416_, lean_object* v_start_2417_, lean_object* v_stop_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Array_forRevM___redArg(v_inst_2414_, v_f_2415_, v_as_2416_, v_start_2417_, v_stop_2418_);
lean_dec(v_stop_2418_);
lean_dec(v_start_2417_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM(lean_object* v_00_u03b1_2420_, lean_object* v_m_2421_, lean_object* v_inst_2422_, lean_object* v_f_2423_, lean_object* v_as_2424_, lean_object* v_start_2425_, lean_object* v_stop_2426_){
_start:
{
lean_object* v_toApplicative_2427_; lean_object* v_toPure_2428_; lean_object* v___f_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; 
v_toApplicative_2427_ = lean_ctor_get(v_inst_2422_, 0);
v_toPure_2428_ = lean_ctor_get(v_toApplicative_2427_, 1);
v___f_2429_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2429_, 0, v_f_2423_);
v___x_2430_ = lean_box(0);
v___x_2431_ = lean_array_get_size(v_as_2424_);
v___x_2432_ = lean_nat_dec_le(v_start_2425_, v___x_2431_);
if (v___x_2432_ == 0)
{
uint8_t v___x_2433_; 
v___x_2433_ = lean_nat_dec_lt(v_stop_2426_, v___x_2431_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; 
lean_inc(v_toPure_2428_);
lean_dec_ref(v___f_2429_);
lean_dec_ref(v_as_2424_);
lean_dec_ref(v_inst_2422_);
v___x_2434_ = lean_apply_2(v_toPure_2428_, lean_box(0), v___x_2430_);
return v___x_2434_;
}
else
{
size_t v___x_2435_; size_t v___x_2436_; lean_object* v___x_2437_; 
v___x_2435_ = lean_usize_of_nat(v___x_2431_);
v___x_2436_ = lean_usize_of_nat(v_stop_2426_);
v___x_2437_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2422_, v___f_2429_, v_as_2424_, v___x_2435_, v___x_2436_, v___x_2430_);
return v___x_2437_;
}
}
else
{
uint8_t v___x_2438_; 
v___x_2438_ = lean_nat_dec_lt(v_stop_2426_, v_start_2425_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; 
lean_inc(v_toPure_2428_);
lean_dec_ref(v___f_2429_);
lean_dec_ref(v_as_2424_);
lean_dec_ref(v_inst_2422_);
v___x_2439_ = lean_apply_2(v_toPure_2428_, lean_box(0), v___x_2430_);
return v___x_2439_;
}
else
{
size_t v___x_2440_; size_t v___x_2441_; lean_object* v___x_2442_; 
v___x_2440_ = lean_usize_of_nat(v_start_2425_);
v___x_2441_ = lean_usize_of_nat(v_stop_2426_);
v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2422_, v___f_2429_, v_as_2424_, v___x_2440_, v___x_2441_, v___x_2430_);
return v___x_2442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___boxed(lean_object* v_00_u03b1_2443_, lean_object* v_m_2444_, lean_object* v_inst_2445_, lean_object* v_f_2446_, lean_object* v_as_2447_, lean_object* v_start_2448_, lean_object* v_stop_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Array_forRevM(v_00_u03b1_2443_, v_m_2444_, v_inst_2445_, v_f_2446_, v_as_2447_, v_start_2448_, v_stop_2449_);
lean_dec(v_stop_2449_);
lean_dec(v_start_2448_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___lam__0(lean_object* v_f_2451_, lean_object* v_x1_2452_, lean_object* v_x2_2453_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = lean_apply_2(v_f_2451_, v_x1_2452_, v_x2_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg(lean_object* v_f_2474_, lean_object* v_init_2475_, lean_object* v_as_2476_, lean_object* v_start_2477_, lean_object* v_stop_2478_){
_start:
{
lean_object* v___x_2479_; uint8_t v___x_2480_; 
v___x_2479_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2480_ = lean_nat_dec_lt(v_start_2477_, v_stop_2478_);
if (v___x_2480_ == 0)
{
lean_dec_ref(v_as_2476_);
lean_dec(v_f_2474_);
return v_init_2475_;
}
else
{
lean_object* v___f_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___f_2481_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2481_, 0, v_f_2474_);
v___x_2482_ = lean_array_get_size(v_as_2476_);
v___x_2483_ = lean_nat_dec_le(v_stop_2478_, v___x_2482_);
if (v___x_2483_ == 0)
{
uint8_t v___x_2484_; 
v___x_2484_ = lean_nat_dec_lt(v_start_2477_, v___x_2482_);
if (v___x_2484_ == 0)
{
lean_dec_ref(v___f_2481_);
lean_dec_ref(v_as_2476_);
return v_init_2475_;
}
else
{
size_t v___x_2485_; size_t v___x_2486_; lean_object* v___x_2487_; 
v___x_2485_ = lean_usize_of_nat(v_start_2477_);
v___x_2486_ = lean_usize_of_nat(v___x_2482_);
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2479_, v___f_2481_, v_as_2476_, v___x_2485_, v___x_2486_, v_init_2475_);
return v___x_2487_;
}
}
else
{
size_t v___x_2488_; size_t v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = lean_usize_of_nat(v_start_2477_);
v___x_2489_ = lean_usize_of_nat(v_stop_2478_);
v___x_2490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2479_, v___f_2481_, v_as_2476_, v___x_2488_, v___x_2489_, v_init_2475_);
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___boxed(lean_object* v_f_2491_, lean_object* v_init_2492_, lean_object* v_as_2493_, lean_object* v_start_2494_, lean_object* v_stop_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Array_foldl___redArg(v_f_2491_, v_init_2492_, v_as_2493_, v_start_2494_, v_stop_2495_);
lean_dec(v_stop_2495_);
lean_dec(v_start_2494_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl(lean_object* v_00_u03b1_2497_, lean_object* v_00_u03b2_2498_, lean_object* v_f_2499_, lean_object* v_init_2500_, lean_object* v_as_2501_, lean_object* v_start_2502_, lean_object* v_stop_2503_){
_start:
{
lean_object* v___x_2504_; uint8_t v___x_2505_; 
v___x_2504_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2505_ = lean_nat_dec_lt(v_start_2502_, v_stop_2503_);
if (v___x_2505_ == 0)
{
lean_dec_ref(v_as_2501_);
lean_dec(v_f_2499_);
return v_init_2500_;
}
else
{
lean_object* v___f_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___f_2506_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2506_, 0, v_f_2499_);
v___x_2507_ = lean_array_get_size(v_as_2501_);
v___x_2508_ = lean_nat_dec_le(v_stop_2503_, v___x_2507_);
if (v___x_2508_ == 0)
{
uint8_t v___x_2509_; 
v___x_2509_ = lean_nat_dec_lt(v_start_2502_, v___x_2507_);
if (v___x_2509_ == 0)
{
lean_dec_ref(v___f_2506_);
lean_dec_ref(v_as_2501_);
return v_init_2500_;
}
else
{
size_t v___x_2510_; size_t v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = lean_usize_of_nat(v_start_2502_);
v___x_2511_ = lean_usize_of_nat(v___x_2507_);
v___x_2512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2504_, v___f_2506_, v_as_2501_, v___x_2510_, v___x_2511_, v_init_2500_);
return v___x_2512_;
}
}
else
{
size_t v___x_2513_; size_t v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = lean_usize_of_nat(v_start_2502_);
v___x_2514_ = lean_usize_of_nat(v_stop_2503_);
v___x_2515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2504_, v___f_2506_, v_as_2501_, v___x_2513_, v___x_2514_, v_init_2500_);
return v___x_2515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___boxed(lean_object* v_00_u03b1_2516_, lean_object* v_00_u03b2_2517_, lean_object* v_f_2518_, lean_object* v_init_2519_, lean_object* v_as_2520_, lean_object* v_start_2521_, lean_object* v_stop_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Array_foldl(v_00_u03b1_2516_, v_00_u03b2_2517_, v_f_2518_, v_init_2519_, v_as_2520_, v_start_2521_, v_stop_2522_);
lean_dec(v_stop_2522_);
lean_dec(v_start_2521_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg(lean_object* v_f_2524_, lean_object* v_init_2525_, lean_object* v_as_2526_, lean_object* v_start_2527_, lean_object* v_stop_2528_){
_start:
{
lean_object* v___f_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; 
v___f_2529_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2529_, 0, v_f_2524_);
v___x_2530_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2531_ = lean_array_get_size(v_as_2526_);
v___x_2532_ = lean_nat_dec_le(v_start_2527_, v___x_2531_);
if (v___x_2532_ == 0)
{
uint8_t v___x_2533_; 
v___x_2533_ = lean_nat_dec_lt(v_stop_2528_, v___x_2531_);
if (v___x_2533_ == 0)
{
lean_dec_ref(v___f_2529_);
lean_dec_ref(v_as_2526_);
return v_init_2525_;
}
else
{
size_t v___x_2534_; size_t v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = lean_usize_of_nat(v___x_2531_);
v___x_2535_ = lean_usize_of_nat(v_stop_2528_);
v___x_2536_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2530_, v___f_2529_, v_as_2526_, v___x_2534_, v___x_2535_, v_init_2525_);
return v___x_2536_;
}
}
else
{
uint8_t v___x_2537_; 
v___x_2537_ = lean_nat_dec_lt(v_stop_2528_, v_start_2527_);
if (v___x_2537_ == 0)
{
lean_dec_ref(v___f_2529_);
lean_dec_ref(v_as_2526_);
return v_init_2525_;
}
else
{
size_t v___x_2538_; size_t v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = lean_usize_of_nat(v_start_2527_);
v___x_2539_ = lean_usize_of_nat(v_stop_2528_);
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2530_, v___f_2529_, v_as_2526_, v___x_2538_, v___x_2539_, v_init_2525_);
return v___x_2540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg___boxed(lean_object* v_f_2541_, lean_object* v_init_2542_, lean_object* v_as_2543_, lean_object* v_start_2544_, lean_object* v_stop_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Array_foldr___redArg(v_f_2541_, v_init_2542_, v_as_2543_, v_start_2544_, v_stop_2545_);
lean_dec(v_stop_2545_);
lean_dec(v_start_2544_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr(lean_object* v_00_u03b1_2547_, lean_object* v_00_u03b2_2548_, lean_object* v_f_2549_, lean_object* v_init_2550_, lean_object* v_as_2551_, lean_object* v_start_2552_, lean_object* v_stop_2553_){
_start:
{
lean_object* v___f_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___f_2554_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2554_, 0, v_f_2549_);
v___x_2555_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2556_ = lean_array_get_size(v_as_2551_);
v___x_2557_ = lean_nat_dec_le(v_start_2552_, v___x_2556_);
if (v___x_2557_ == 0)
{
uint8_t v___x_2558_; 
v___x_2558_ = lean_nat_dec_lt(v_stop_2553_, v___x_2556_);
if (v___x_2558_ == 0)
{
lean_dec_ref(v___f_2554_);
lean_dec_ref(v_as_2551_);
return v_init_2550_;
}
else
{
size_t v___x_2559_; size_t v___x_2560_; lean_object* v___x_2561_; 
v___x_2559_ = lean_usize_of_nat(v___x_2556_);
v___x_2560_ = lean_usize_of_nat(v_stop_2553_);
v___x_2561_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2555_, v___f_2554_, v_as_2551_, v___x_2559_, v___x_2560_, v_init_2550_);
return v___x_2561_;
}
}
else
{
uint8_t v___x_2562_; 
v___x_2562_ = lean_nat_dec_lt(v_stop_2553_, v_start_2552_);
if (v___x_2562_ == 0)
{
lean_dec_ref(v___f_2554_);
lean_dec_ref(v_as_2551_);
return v_init_2550_;
}
else
{
size_t v___x_2563_; size_t v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = lean_usize_of_nat(v_start_2552_);
v___x_2564_ = lean_usize_of_nat(v_stop_2553_);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2555_, v___f_2554_, v_as_2551_, v___x_2563_, v___x_2564_, v_init_2550_);
return v___x_2565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___boxed(lean_object* v_00_u03b1_2566_, lean_object* v_00_u03b2_2567_, lean_object* v_f_2568_, lean_object* v_init_2569_, lean_object* v_as_2570_, lean_object* v_start_2571_, lean_object* v_stop_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Array_foldr(v_00_u03b1_2566_, v_00_u03b2_2567_, v_f_2568_, v_init_2569_, v_as_2570_, v_start_2571_, v_stop_2572_);
lean_dec(v_stop_2572_);
lean_dec(v_start_2571_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg___lam__0(lean_object* v_inst_2574_, lean_object* v_x1_2575_, lean_object* v_x2_2576_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = lean_apply_2(v_inst_2574_, v_x1_2575_, v_x2_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg(lean_object* v_inst_2578_, lean_object* v_inst_2579_, lean_object* v_as_2580_){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v___x_2581_ = lean_array_get_size(v_as_2580_);
v___x_2582_ = lean_unsigned_to_nat(0u);
v___x_2583_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2584_ = lean_nat_dec_lt(v___x_2582_, v___x_2581_);
if (v___x_2584_ == 0)
{
lean_dec_ref(v_as_2580_);
lean_dec(v_inst_2578_);
return v_inst_2579_;
}
else
{
lean_object* v___f_2585_; size_t v___x_2586_; size_t v___x_2587_; lean_object* v___x_2588_; 
v___f_2585_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2585_, 0, v_inst_2578_);
v___x_2586_ = lean_usize_of_nat(v___x_2581_);
v___x_2587_ = ((size_t)0ULL);
v___x_2588_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2583_, v___f_2585_, v_as_2580_, v___x_2586_, v___x_2587_, v_inst_2579_);
return v___x_2588_;
}
}
}
LEAN_EXPORT lean_object* l_Array_sum(lean_object* v_00_u03b1_2589_, lean_object* v_inst_2590_, lean_object* v_inst_2591_, lean_object* v_as_2592_){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; uint8_t v___x_2596_; 
v___x_2593_ = lean_array_get_size(v_as_2592_);
v___x_2594_ = lean_unsigned_to_nat(0u);
v___x_2595_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2596_ = lean_nat_dec_lt(v___x_2594_, v___x_2593_);
if (v___x_2596_ == 0)
{
lean_dec_ref(v_as_2592_);
lean_dec(v_inst_2590_);
return v_inst_2591_;
}
else
{
lean_object* v___f_2597_; size_t v___x_2598_; size_t v___x_2599_; lean_object* v___x_2600_; 
v___f_2597_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2597_, 0, v_inst_2590_);
v___x_2598_ = lean_usize_of_nat(v___x_2593_);
v___x_2599_ = ((size_t)0ULL);
v___x_2600_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2595_, v___f_2597_, v_as_2592_, v___x_2598_, v___x_2599_, v_inst_2591_);
return v___x_2600_;
}
}
}
LEAN_EXPORT lean_object* l_Array_prod___redArg(lean_object* v_inst_2601_, lean_object* v_inst_2602_, lean_object* v_as_2603_){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2604_ = lean_array_get_size(v_as_2603_);
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2607_ = lean_nat_dec_lt(v___x_2605_, v___x_2604_);
if (v___x_2607_ == 0)
{
lean_dec_ref(v_as_2603_);
lean_dec(v_inst_2601_);
return v_inst_2602_;
}
else
{
lean_object* v___f_2608_; size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___f_2608_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2608_, 0, v_inst_2601_);
v___x_2609_ = lean_usize_of_nat(v___x_2604_);
v___x_2610_ = ((size_t)0ULL);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2606_, v___f_2608_, v_as_2603_, v___x_2609_, v___x_2610_, v_inst_2602_);
return v___x_2611_;
}
}
}
LEAN_EXPORT lean_object* l_Array_prod(lean_object* v_00_u03b1_2612_, lean_object* v_inst_2613_, lean_object* v_inst_2614_, lean_object* v_as_2615_){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2616_ = lean_array_get_size(v_as_2615_);
v___x_2617_ = lean_unsigned_to_nat(0u);
v___x_2618_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2619_ = lean_nat_dec_lt(v___x_2617_, v___x_2616_);
if (v___x_2619_ == 0)
{
lean_dec_ref(v_as_2615_);
lean_dec(v_inst_2613_);
return v_inst_2614_;
}
else
{
lean_object* v___f_2620_; size_t v___x_2621_; size_t v___x_2622_; lean_object* v___x_2623_; 
v___f_2620_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2620_, 0, v_inst_2613_);
v___x_2621_ = lean_usize_of_nat(v___x_2616_);
v___x_2622_ = ((size_t)0ULL);
v___x_2623_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2618_, v___f_2620_, v_as_2615_, v___x_2621_, v___x_2622_, v_inst_2614_);
return v___x_2623_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0(lean_object* v_p_2624_, lean_object* v_x1_2625_, lean_object* v_x2_2626_){
_start:
{
lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = lean_apply_1(v_p_2624_, v_x1_2625_);
v___x_2628_ = lean_unbox(v___x_2627_);
if (v___x_2628_ == 0)
{
lean_inc(v_x2_2626_);
return v_x2_2626_;
}
else
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = lean_unsigned_to_nat(1u);
v___x_2630_ = lean_nat_add(v_x2_2626_, v___x_2629_);
return v___x_2630_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0___boxed(lean_object* v_p_2631_, lean_object* v_x1_2632_, lean_object* v_x2_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Array_countP___redArg___lam__0(v_p_2631_, v_x1_2632_, v_x2_2633_);
lean_dec(v_x2_2633_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg(lean_object* v_p_2635_, lean_object* v_as_2636_){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; 
v___x_2637_ = lean_unsigned_to_nat(0u);
v___x_2638_ = lean_array_get_size(v_as_2636_);
v___x_2639_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2640_ = lean_nat_dec_lt(v___x_2637_, v___x_2638_);
if (v___x_2640_ == 0)
{
lean_dec_ref(v_as_2636_);
lean_dec_ref(v_p_2635_);
return v___x_2637_;
}
else
{
lean_object* v___f_2641_; size_t v___x_2642_; size_t v___x_2643_; lean_object* v___x_2644_; 
v___f_2641_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2641_, 0, v_p_2635_);
v___x_2642_ = lean_usize_of_nat(v___x_2638_);
v___x_2643_ = ((size_t)0ULL);
v___x_2644_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2639_, v___f_2641_, v_as_2636_, v___x_2642_, v___x_2643_, v___x_2637_);
return v___x_2644_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP(lean_object* v_00_u03b1_2645_, lean_object* v_p_2646_, lean_object* v_as_2647_){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2648_ = lean_unsigned_to_nat(0u);
v___x_2649_ = lean_array_get_size(v_as_2647_);
v___x_2650_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2651_ = lean_nat_dec_lt(v___x_2648_, v___x_2649_);
if (v___x_2651_ == 0)
{
lean_dec_ref(v_as_2647_);
lean_dec_ref(v_p_2646_);
return v___x_2648_;
}
else
{
lean_object* v___f_2652_; size_t v___x_2653_; size_t v___x_2654_; lean_object* v___x_2655_; 
v___f_2652_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2652_, 0, v_p_2646_);
v___x_2653_ = lean_usize_of_nat(v___x_2649_);
v___x_2654_ = ((size_t)0ULL);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2650_, v___f_2652_, v_as_2647_, v___x_2653_, v___x_2654_, v___x_2648_);
return v___x_2655_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0(lean_object* v_inst_2656_, lean_object* v_a_2657_, lean_object* v_x1_2658_, lean_object* v_x2_2659_){
_start:
{
lean_object* v___x_2660_; uint8_t v___x_2661_; 
v___x_2660_ = lean_apply_2(v_inst_2656_, v_x1_2658_, v_a_2657_);
v___x_2661_ = lean_unbox(v___x_2660_);
if (v___x_2661_ == 0)
{
lean_inc(v_x2_2659_);
return v_x2_2659_;
}
else
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = lean_unsigned_to_nat(1u);
v___x_2663_ = lean_nat_add(v_x2_2659_, v___x_2662_);
return v___x_2663_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0___boxed(lean_object* v_inst_2664_, lean_object* v_a_2665_, lean_object* v_x1_2666_, lean_object* v_x2_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Array_count___redArg___lam__0(v_inst_2664_, v_a_2665_, v_x1_2666_, v_x2_2667_);
lean_dec(v_x2_2667_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg(lean_object* v_inst_2669_, lean_object* v_a_2670_, lean_object* v_as_2671_){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v___x_2672_ = lean_unsigned_to_nat(0u);
v___x_2673_ = lean_array_get_size(v_as_2671_);
v___x_2674_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2675_ = lean_nat_dec_lt(v___x_2672_, v___x_2673_);
if (v___x_2675_ == 0)
{
lean_dec_ref(v_as_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_inst_2669_);
return v___x_2672_;
}
else
{
lean_object* v___f_2676_; size_t v___x_2677_; size_t v___x_2678_; lean_object* v___x_2679_; 
v___f_2676_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2676_, 0, v_inst_2669_);
lean_closure_set(v___f_2676_, 1, v_a_2670_);
v___x_2677_ = lean_usize_of_nat(v___x_2673_);
v___x_2678_ = ((size_t)0ULL);
v___x_2679_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2674_, v___f_2676_, v_as_2671_, v___x_2677_, v___x_2678_, v___x_2672_);
return v___x_2679_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count(lean_object* v_00_u03b1_2680_, lean_object* v_inst_2681_, lean_object* v_a_2682_, lean_object* v_as_2683_){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2684_ = lean_unsigned_to_nat(0u);
v___x_2685_ = lean_array_get_size(v_as_2683_);
v___x_2686_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2687_ = lean_nat_dec_lt(v___x_2684_, v___x_2685_);
if (v___x_2687_ == 0)
{
lean_dec_ref(v_as_2683_);
lean_dec(v_a_2682_);
lean_dec_ref(v_inst_2681_);
return v___x_2684_;
}
else
{
lean_object* v___f_2688_; size_t v___x_2689_; size_t v___x_2690_; lean_object* v___x_2691_; 
v___f_2688_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2688_, 0, v_inst_2681_);
lean_closure_set(v___f_2688_, 1, v_a_2682_);
v___x_2689_ = lean_usize_of_nat(v___x_2685_);
v___x_2690_ = ((size_t)0ULL);
v___x_2691_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2686_, v___f_2688_, v_as_2683_, v___x_2689_, v___x_2690_, v___x_2684_);
return v___x_2691_;
}
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg___lam__0(lean_object* v_f_2692_, lean_object* v_x_2693_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = lean_apply_1(v_f_2692_, v_x_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg(lean_object* v_f_2695_, lean_object* v_as_2696_){
_start:
{
lean_object* v___f_2697_; lean_object* v___x_2698_; size_t v_sz_2699_; size_t v___x_2700_; lean_object* v___x_2701_; 
v___f_2697_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2697_, 0, v_f_2695_);
v___x_2698_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2699_ = lean_array_size(v_as_2696_);
v___x_2700_ = ((size_t)0ULL);
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2698_, v___f_2697_, v_sz_2699_, v___x_2700_, v_as_2696_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Array_map(lean_object* v_00_u03b1_2702_, lean_object* v_00_u03b2_2703_, lean_object* v_f_2704_, lean_object* v_as_2705_){
_start:
{
lean_object* v___f_2706_; lean_object* v___x_2707_; size_t v_sz_2708_; size_t v___x_2709_; lean_object* v___x_2710_; 
v___f_2706_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2706_, 0, v_f_2704_);
v___x_2707_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2708_ = lean_array_size(v_as_2705_);
v___x_2709_ = ((size_t)0ULL);
v___x_2710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2707_, v___f_2706_, v_sz_2708_, v___x_2709_, v_as_2705_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0(lean_object* v___y_2711_, lean_object* v_x_2712_){
_start:
{
lean_inc(v___y_2711_);
return v___y_2711_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0___boxed(lean_object* v___y_2713_, lean_object* v_x_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Array_instFunctor___lam__0(v___y_2713_, v_x_2714_);
lean_dec(v_x_2714_);
lean_dec(v___y_2713_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__1(lean_object* v_00_u03b1_2716_, lean_object* v_00_u03b2_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___f_2720_; lean_object* v___x_2721_; size_t v_sz_2722_; size_t v___x_2723_; lean_object* v___x_2724_; 
v___f_2720_ = lean_alloc_closure((void*)(l_Array_instFunctor___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2720_, 0, v___y_2718_);
v___x_2721_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2722_ = lean_array_size(v___y_2719_);
v___x_2723_ = ((size_t)0ULL);
v___x_2724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2721_, v___f_2720_, v_sz_2722_, v___x_2723_, v___y_2719_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg___lam__0(lean_object* v_f_2731_, lean_object* v_x1_2732_, lean_object* v_x2_2733_, lean_object* v_x3_2734_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = lean_apply_3(v_f_2731_, v_x1_2732_, v_x2_2733_, lean_box(0));
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg(lean_object* v_as_2736_, lean_object* v_f_2737_){
_start:
{
lean_object* v___f_2738_; lean_object* v___x_2739_; size_t v_sz_2740_; size_t v___x_2741_; lean_object* v___x_2742_; 
v___f_2738_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2738_, 0, v_f_2737_);
v___x_2739_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2740_ = lean_array_size(v_as_2736_);
v___x_2741_ = ((size_t)0ULL);
v___x_2742_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2739_, v___f_2738_, v_sz_2740_, v___x_2741_, v_as_2736_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx(lean_object* v_00_u03b1_2743_, lean_object* v_00_u03b2_2744_, lean_object* v_as_2745_, lean_object* v_f_2746_){
_start:
{
lean_object* v___f_2747_; lean_object* v___x_2748_; size_t v_sz_2749_; size_t v___x_2750_; lean_object* v___x_2751_; 
v___f_2747_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2747_, 0, v_f_2746_);
v___x_2748_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2749_ = lean_array_size(v_as_2745_);
v___x_2750_ = ((size_t)0ULL);
v___x_2751_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2748_, v___f_2747_, v_sz_2749_, v___x_2750_, v_as_2745_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx___redArg(lean_object* v_f_2752_, lean_object* v_as_2753_){
_start:
{
lean_object* v___f_2754_; lean_object* v___x_2755_; size_t v_sz_2756_; size_t v___x_2757_; lean_object* v___x_2758_; 
v___f_2754_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2754_, 0, v_f_2752_);
v___x_2755_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2756_ = lean_array_size(v_as_2753_);
v___x_2757_ = ((size_t)0ULL);
v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2755_, v___f_2754_, v_sz_2756_, v___x_2757_, v_as_2753_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx(lean_object* v_00_u03b1_2759_, lean_object* v_00_u03b2_2760_, lean_object* v_f_2761_, lean_object* v_as_2762_){
_start:
{
lean_object* v___f_2763_; lean_object* v___x_2764_; size_t v_sz_2765_; size_t v___x_2766_; lean_object* v___x_2767_; 
v___f_2763_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2763_, 0, v_f_2761_);
v___x_2764_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2765_ = lean_array_size(v_as_2762_);
v___x_2766_ = ((size_t)0ULL);
v___x_2767_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2764_, v___f_2763_, v_sz_2765_, v___x_2766_, v_as_2762_);
return v___x_2767_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(lean_object* v_start_2768_, size_t v_sz_2769_, size_t v_i_2770_, lean_object* v_bs_2771_){
_start:
{
uint8_t v___x_2772_; 
v___x_2772_ = lean_usize_dec_lt(v_i_2770_, v_sz_2769_);
if (v___x_2772_ == 0)
{
return v_bs_2771_;
}
else
{
lean_object* v_v_2773_; lean_object* v___x_2774_; lean_object* v_bs_x27_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; size_t v___x_2779_; size_t v___x_2780_; lean_object* v___x_2781_; 
v_v_2773_ = lean_array_uget(v_bs_2771_, v_i_2770_);
v___x_2774_ = lean_unsigned_to_nat(0u);
v_bs_x27_2775_ = lean_array_uset(v_bs_2771_, v_i_2770_, v___x_2774_);
v___x_2776_ = lean_usize_to_nat(v_i_2770_);
v___x_2777_ = lean_nat_add(v_start_2768_, v___x_2776_);
lean_dec(v___x_2776_);
v___x_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2778_, 0, v_v_2773_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = ((size_t)1ULL);
v___x_2780_ = lean_usize_add(v_i_2770_, v___x_2779_);
v___x_2781_ = lean_array_uset(v_bs_x27_2775_, v_i_2770_, v___x_2778_);
v_i_2770_ = v___x_2780_;
v_bs_2771_ = v___x_2781_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_start_2768_ = stack[0].m_obj;
size_t v_sz_2769_ = stack[1].m_num;
size_t v_i_2770_ = stack[2].m_num;
lean_object* v_bs_2771_ = stack[3].m_obj;
lean_object* v_res_2783_;
v_res_2783_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2768_, v_sz_2769_, v_i_2770_, v_bs_2771_);
stack->m_obj
 = v_res_2783_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg___boxed(lean_object* v_start_2784_, lean_object* v_sz_2785_, lean_object* v_i_2786_, lean_object* v_bs_2787_){
_start:
{
size_t v_sz_boxed_2788_; size_t v_i_boxed_2789_; lean_object* v_res_2790_; 
v_sz_boxed_2788_ = lean_unbox_usize(v_sz_2785_);
lean_dec(v_sz_2785_);
v_i_boxed_2789_ = lean_unbox_usize(v_i_2786_);
lean_dec(v_i_2786_);
v_res_2790_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2784_, v_sz_boxed_2788_, v_i_boxed_2789_, v_bs_2787_);
lean_dec(v_start_2784_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg(lean_object* v_xs_2791_, lean_object* v_start_2792_){
_start:
{
size_t v_sz_2793_; size_t v___x_2794_; lean_object* v___x_2795_; 
v_sz_2793_ = lean_array_size(v_xs_2791_);
v___x_2794_ = ((size_t)0ULL);
v___x_2795_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2792_, v_sz_2793_, v___x_2794_, v_xs_2791_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg___boxed(lean_object* v_xs_2796_, lean_object* v_start_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Array_zipIdx___redArg(v_xs_2796_, v_start_2797_);
lean_dec(v_start_2797_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx(lean_object* v_00_u03b1_2799_, lean_object* v_xs_2800_, lean_object* v_start_2801_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l_Array_zipIdx___redArg(v_xs_2800_, v_start_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___boxed(lean_object* v_00_u03b1_2803_, lean_object* v_xs_2804_, lean_object* v_start_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Array_zipIdx(v_00_u03b1_2803_, v_xs_2804_, v_start_2805_);
lean_dec(v_start_2805_);
return v_res_2806_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(lean_object* v_00_u03b1_2807_, lean_object* v_start_2808_, lean_object* v_as_2809_, size_t v_sz_2810_, size_t v_i_2811_, lean_object* v_bs_2812_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2808_, v_sz_2810_, v_i_2811_, v_bs_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_start_2808_ = stack[1].m_obj;
lean_object* v_as_2809_ = stack[2].m_obj;
size_t v_sz_2810_ = stack[3].m_num;
size_t v_i_2811_ = stack[4].m_num;
lean_object* v_bs_2812_ = stack[5].m_obj;
lean_object* v_res_2814_;
v_res_2814_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(lean_box(0), v_start_2808_, v_as_2809_, v_sz_2810_, v_i_2811_, v_bs_2812_);
stack->m_obj
 = v_res_2814_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___boxed(lean_object* v_00_u03b1_2815_, lean_object* v_start_2816_, lean_object* v_as_2817_, lean_object* v_sz_2818_, lean_object* v_i_2819_, lean_object* v_bs_2820_){
_start:
{
size_t v_sz_boxed_2821_; size_t v_i_boxed_2822_; lean_object* v_res_2823_; 
v_sz_boxed_2821_ = lean_unbox_usize(v_sz_2818_);
lean_dec(v_sz_2818_);
v_i_boxed_2822_ = lean_unbox_usize(v_i_2819_);
lean_dec(v_i_2819_);
v_res_2823_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(v_00_u03b1_2815_, v_start_2816_, v_as_2817_, v_sz_boxed_2821_, v_i_boxed_2822_, v_bs_2820_);
lean_dec_ref(v_as_2817_);
lean_dec(v_start_2816_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0(lean_object* v_p_2824_, lean_object* v___x_2825_, lean_object* v___x_2826_, lean_object* v_a_2827_, lean_object* v_x_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___x_2830_; uint8_t v___x_2831_; 
lean_inc(v_a_2827_);
v___x_2830_ = lean_apply_1(v_p_2824_, v_a_2827_);
v___x_2831_ = lean_unbox(v___x_2830_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; 
lean_dec(v_a_2827_);
v___x_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2825_);
return v___x_2832_;
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
lean_dec_ref(v___x_2825_);
v___x_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2833_, 0, v_a_2827_);
v___x_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
v___x_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
lean_ctor_set(v___x_2835_, 1, v___x_2826_);
v___x_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
return v___x_2836_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0___boxed(lean_object* v_p_2837_, lean_object* v___x_2838_, lean_object* v___x_2839_, lean_object* v_a_2840_, lean_object* v_x_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Array_find_x3f___redArg___lam__0(v_p_2837_, v___x_2838_, v___x_2839_, v_a_2840_, v_x_2841_, v___y_2842_);
lean_dec_ref(v___y_2842_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg(lean_object* v_p_2844_, lean_object* v_as_2845_){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___f_2850_; size_t v_sz_2851_; size_t v___x_2852_; lean_object* v___x_2853_; lean_object* v_fst_2854_; 
v___x_2846_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2847_ = lean_box(0);
v___x_2848_ = lean_box(0);
v___x_2849_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2850_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2850_, 0, v_p_2844_);
lean_closure_set(v___f_2850_, 1, v___x_2849_);
lean_closure_set(v___f_2850_, 2, v___x_2848_);
v_sz_2851_ = lean_array_size(v_as_2845_);
v___x_2852_ = ((size_t)0ULL);
v___x_2853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2846_, v_as_2845_, v___f_2850_, v_sz_2851_, v___x_2852_, v___x_2849_);
v_fst_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_fst_2854_);
lean_dec(v___x_2853_);
if (lean_obj_tag(v_fst_2854_) == 0)
{
return v___x_2847_;
}
else
{
lean_object* v_val_2855_; 
v_val_2855_ = lean_ctor_get(v_fst_2854_, 0);
lean_inc(v_val_2855_);
lean_dec_ref_known(v_fst_2854_, 1);
return v_val_2855_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f(lean_object* v_00_u03b1_2856_, lean_object* v_p_2857_, lean_object* v_as_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___f_2863_; size_t v_sz_2864_; size_t v___x_2865_; lean_object* v___x_2866_; lean_object* v_fst_2867_; 
v___x_2859_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2860_ = lean_box(0);
v___x_2861_ = lean_box(0);
v___x_2862_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2863_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2863_, 0, v_p_2857_);
lean_closure_set(v___f_2863_, 1, v___x_2862_);
lean_closure_set(v___f_2863_, 2, v___x_2861_);
v_sz_2864_ = lean_array_size(v_as_2858_);
v___x_2865_ = ((size_t)0ULL);
v___x_2866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2859_, v_as_2858_, v___f_2863_, v_sz_2864_, v___x_2865_, v___x_2862_);
v_fst_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_fst_2867_);
lean_dec(v___x_2866_);
if (lean_obj_tag(v_fst_2867_) == 0)
{
return v___x_2860_;
}
else
{
lean_object* v_val_2868_; 
v_val_2868_ = lean_ctor_get(v_fst_2867_, 0);
lean_inc(v_val_2868_);
lean_dec_ref_known(v_fst_2867_, 1);
return v_val_2868_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0(lean_object* v_f_2869_, lean_object* v___x_2870_, lean_object* v___x_2871_, lean_object* v_a_2872_, lean_object* v_x_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = lean_apply_1(v_f_2869_, v_a_2872_);
if (lean_obj_tag(v___x_2875_) == 1)
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
lean_dec_ref(v___x_2871_);
v___x_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
v___x_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
lean_ctor_set(v___x_2877_, 1, v___x_2870_);
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
return v___x_2878_;
}
else
{
lean_object* v___x_2879_; 
lean_dec(v___x_2875_);
v___x_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2871_);
return v___x_2879_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2880_, lean_object* v___x_2881_, lean_object* v___x_2882_, lean_object* v_a_2883_, lean_object* v_x_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l_Array_findSome_x3f___redArg___lam__0(v_f_2880_, v___x_2881_, v___x_2882_, v_a_2883_, v_x_2884_, v___y_2885_);
lean_dec_ref(v___y_2885_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg(lean_object* v_f_2887_, lean_object* v_as_2888_){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___f_2893_; size_t v_sz_2894_; size_t v___x_2895_; lean_object* v___x_2896_; lean_object* v_fst_2897_; 
v___x_2889_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2890_ = lean_box(0);
v___x_2891_ = lean_box(0);
v___x_2892_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2893_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2893_, 0, v_f_2887_);
lean_closure_set(v___f_2893_, 1, v___x_2891_);
lean_closure_set(v___f_2893_, 2, v___x_2892_);
v_sz_2894_ = lean_array_size(v_as_2888_);
v___x_2895_ = ((size_t)0ULL);
v___x_2896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2889_, v_as_2888_, v___f_2893_, v_sz_2894_, v___x_2895_, v___x_2892_);
v_fst_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_fst_2897_);
lean_dec(v___x_2896_);
if (lean_obj_tag(v_fst_2897_) == 0)
{
return v___x_2890_;
}
else
{
lean_object* v_val_2898_; 
v_val_2898_ = lean_ctor_get(v_fst_2897_, 0);
lean_inc(v_val_2898_);
lean_dec_ref_known(v_fst_2897_, 1);
return v_val_2898_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f(lean_object* v_00_u03b1_2899_, lean_object* v_00_u03b2_2900_, lean_object* v_f_2901_, lean_object* v_as_2902_){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___f_2907_; size_t v_sz_2908_; size_t v___x_2909_; lean_object* v___x_2910_; lean_object* v_fst_2911_; 
v___x_2903_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2904_ = lean_box(0);
v___x_2905_ = lean_box(0);
v___x_2906_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2907_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2907_, 0, v_f_2901_);
lean_closure_set(v___f_2907_, 1, v___x_2905_);
lean_closure_set(v___f_2907_, 2, v___x_2906_);
v_sz_2908_ = lean_array_size(v_as_2902_);
v___x_2909_ = ((size_t)0ULL);
v___x_2910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2903_, v_as_2902_, v___f_2907_, v_sz_2908_, v___x_2909_, v___x_2906_);
v_fst_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_fst_2911_);
lean_dec(v___x_2910_);
if (lean_obj_tag(v_fst_2911_) == 0)
{
return v___x_2904_;
}
else
{
lean_object* v_val_2912_; 
v_val_2912_ = lean_ctor_get(v_fst_2911_, 0);
lean_inc(v_val_2912_);
lean_dec_ref_known(v_fst_2911_, 1);
return v_val_2912_;
}
}
}
static lean_object* _init_l_Array_findSome_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2915_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__1));
v___x_2916_ = lean_unsigned_to_nat(14u);
v___x_2917_ = lean_unsigned_to_nat(1286u);
v___x_2918_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__0));
v___x_2919_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_2920_ = l_mkPanicMessageWithDecl(v___x_2919_, v___x_2918_, v___x_2917_, v___x_2916_, v___x_2915_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg(lean_object* v_inst_2921_, lean_object* v_f_2922_, lean_object* v_xs_2923_){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___f_2930_; size_t v_sz_2931_; size_t v___x_2932_; lean_object* v___x_2933_; lean_object* v_fst_2934_; 
v___x_2927_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2928_ = lean_box(0);
v___x_2929_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2930_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2930_, 0, v_f_2922_);
lean_closure_set(v___f_2930_, 1, v___x_2928_);
lean_closure_set(v___f_2930_, 2, v___x_2929_);
v_sz_2931_ = lean_array_size(v_xs_2923_);
v___x_2932_ = ((size_t)0ULL);
v___x_2933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2927_, v_xs_2923_, v___f_2930_, v_sz_2931_, v___x_2932_, v___x_2929_);
v_fst_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_fst_2934_);
lean_dec(v___x_2933_);
if (lean_obj_tag(v_fst_2934_) == 0)
{
goto v___jp_2924_;
}
else
{
lean_object* v_val_2935_; 
v_val_2935_ = lean_ctor_get(v_fst_2934_, 0);
lean_inc(v_val_2935_);
lean_dec_ref_known(v_fst_2934_, 1);
if (lean_obj_tag(v_val_2935_) == 0)
{
goto v___jp_2924_;
}
else
{
lean_object* v_val_2936_; 
v_val_2936_ = lean_ctor_get(v_val_2935_, 0);
lean_inc(v_val_2936_);
lean_dec_ref_known(v_val_2935_, 1);
return v_val_2936_;
}
}
v___jp_2924_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2926_ = l_panic___redArg(v_inst_2921_, v___x_2925_);
return v___x_2926_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg___boxed(lean_object* v_inst_2937_, lean_object* v_f_2938_, lean_object* v_xs_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_Array_findSome_x21___redArg(v_inst_2937_, v_f_2938_, v_xs_2939_);
lean_dec(v_inst_2937_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21(lean_object* v_00_u03b1_2941_, lean_object* v_00_u03b2_2942_, lean_object* v_inst_2943_, lean_object* v_f_2944_, lean_object* v_xs_2945_){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___f_2952_; size_t v_sz_2953_; size_t v___x_2954_; lean_object* v___x_2955_; lean_object* v_fst_2956_; 
v___x_2949_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2950_ = lean_box(0);
v___x_2951_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2952_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2952_, 0, v_f_2944_);
lean_closure_set(v___f_2952_, 1, v___x_2950_);
lean_closure_set(v___f_2952_, 2, v___x_2951_);
v_sz_2953_ = lean_array_size(v_xs_2945_);
v___x_2954_ = ((size_t)0ULL);
v___x_2955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2949_, v_xs_2945_, v___f_2952_, v_sz_2953_, v___x_2954_, v___x_2951_);
v_fst_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_fst_2956_);
lean_dec(v___x_2955_);
if (lean_obj_tag(v_fst_2956_) == 0)
{
goto v___jp_2946_;
}
else
{
lean_object* v_val_2957_; 
v_val_2957_ = lean_ctor_get(v_fst_2956_, 0);
lean_inc(v_val_2957_);
lean_dec_ref_known(v_fst_2956_, 1);
if (lean_obj_tag(v_val_2957_) == 0)
{
goto v___jp_2946_;
}
else
{
lean_object* v_val_2958_; 
v_val_2958_ = lean_ctor_get(v_val_2957_, 0);
lean_inc(v_val_2958_);
lean_dec_ref_known(v_val_2957_, 1);
return v_val_2958_;
}
}
v___jp_2946_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2948_ = l_panic___redArg(v_inst_2943_, v___x_2947_);
return v___x_2948_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___boxed(lean_object* v_00_u03b1_2959_, lean_object* v_00_u03b2_2960_, lean_object* v_inst_2961_, lean_object* v_f_2962_, lean_object* v_xs_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Array_findSome_x21(v_00_u03b1_2959_, v_00_u03b2_2960_, v_inst_2961_, v_f_2962_, v_xs_2963_);
lean_dec(v_inst_2961_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2965_, lean_object* v_x_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_apply_1(v_f_2965_, v_x_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg(lean_object* v_f_2968_, lean_object* v_as_2969_){
_start:
{
lean_object* v___f_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___f_2970_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2970_, 0, v_f_2968_);
v___x_2971_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2972_ = lean_array_get_size(v_as_2969_);
v___x_2973_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2971_, v___f_2970_, v_as_2969_, v___x_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f(lean_object* v_00_u03b1_2974_, lean_object* v_00_u03b2_2975_, lean_object* v_f_2976_, lean_object* v_as_2977_){
_start:
{
lean_object* v___f_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___f_2978_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2978_, 0, v_f_2976_);
v___x_2979_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2980_ = lean_array_get_size(v_as_2977_);
v___x_2981_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2979_, v___f_2978_, v_as_2977_, v___x_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg___lam__0(lean_object* v_p_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v___x_2984_; uint8_t v___x_2985_; 
lean_inc(v_a_2983_);
v___x_2984_ = lean_apply_1(v_p_2982_, v_a_2983_);
v___x_2985_ = lean_unbox(v___x_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
lean_dec(v_a_2983_);
v___x_2986_ = lean_box(0);
return v___x_2986_;
}
else
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2987_, 0, v_a_2983_);
return v___x_2987_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg(lean_object* v_p_2988_, lean_object* v_as_2989_){
_start:
{
lean_object* v___f_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___f_2990_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2990_, 0, v_p_2988_);
v___x_2991_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2992_ = lean_array_get_size(v_as_2989_);
v___x_2993_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2991_, v___f_2990_, v_as_2989_, v___x_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f(lean_object* v_00_u03b1_2994_, lean_object* v_p_2995_, lean_object* v_as_2996_){
_start:
{
lean_object* v___f_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___f_2997_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2997_, 0, v_p_2995_);
v___x_2998_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2999_ = lean_array_get_size(v_as_2996_);
v___x_3000_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2998_, v___f_2997_, v_as_2996_, v___x_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object* v_p_3001_, lean_object* v_as_3002_, lean_object* v_j_3003_){
_start:
{
lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_3004_ = lean_array_get_size(v_as_3002_);
v___x_3005_ = lean_nat_dec_lt(v_j_3003_, v___x_3004_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; 
lean_dec(v_j_3003_);
lean_dec_ref(v_p_3001_);
v___x_3006_ = lean_box(0);
return v___x_3006_;
}
else
{
lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3007_ = lean_array_fget_borrowed(v_as_3002_, v_j_3003_);
lean_inc_ref(v_p_3001_);
lean_inc(v___x_3007_);
v___x_3008_ = lean_apply_1(v_p_3001_, v___x_3007_);
v___x_3009_ = lean_unbox(v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = lean_unsigned_to_nat(1u);
v___x_3011_ = lean_nat_add(v_j_3003_, v___x_3010_);
lean_dec(v_j_3003_);
v_j_3003_ = v___x_3011_;
goto _start;
}
else
{
lean_object* v___x_3013_; 
lean_dec_ref(v_p_3001_);
v___x_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3013_, 0, v_j_3003_);
return v___x_3013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg___boxed(lean_object* v_p_3014_, lean_object* v_as_3015_, lean_object* v_j_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Array_findIdx_x3f_loop___redArg(v_p_3014_, v_as_3015_, v_j_3016_);
lean_dec_ref(v_as_3015_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop(lean_object* v_00_u03b1_3018_, lean_object* v_p_3019_, lean_object* v_as_3020_, lean_object* v_j_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Array_findIdx_x3f_loop___redArg(v_p_3019_, v_as_3020_, v_j_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___boxed(lean_object* v_00_u03b1_3023_, lean_object* v_p_3024_, lean_object* v_as_3025_, lean_object* v_j_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Array_findIdx_x3f_loop(v_00_u03b1_3023_, v_p_3024_, v_as_3025_, v_j_3026_);
lean_dec_ref(v_as_3025_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg(lean_object* v_p_3028_, lean_object* v_as_3029_){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3030_ = lean_unsigned_to_nat(0u);
v___x_3031_ = l_Array_findIdx_x3f_loop___redArg(v_p_3028_, v_as_3029_, v___x_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg___boxed(lean_object* v_p_3032_, lean_object* v_as_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Array_findIdx_x3f___redArg(v_p_3032_, v_as_3033_);
lean_dec_ref(v_as_3033_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f(lean_object* v_00_u03b1_3035_, lean_object* v_p_3036_, lean_object* v_as_3037_){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3038_ = lean_unsigned_to_nat(0u);
v___x_3039_ = l_Array_findIdx_x3f_loop___redArg(v_p_3036_, v_as_3037_, v___x_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___boxed(lean_object* v_00_u03b1_3040_, lean_object* v_p_3041_, lean_object* v_as_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Array_findIdx_x3f(v_00_u03b1_3040_, v_p_3041_, v_as_3042_);
lean_dec_ref(v_as_3042_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(lean_object* v_p_3044_, lean_object* v_as_3045_, lean_object* v_j_3046_){
_start:
{
lean_object* v___x_3047_; uint8_t v___x_3048_; 
v___x_3047_ = lean_array_get_size(v_as_3045_);
v___x_3048_ = lean_nat_dec_lt(v_j_3046_, v___x_3047_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; 
lean_dec(v_j_3046_);
lean_dec_ref(v_p_3044_);
v___x_3049_ = lean_box(0);
return v___x_3049_;
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; 
v___x_3050_ = lean_array_fget_borrowed(v_as_3045_, v_j_3046_);
lean_inc_ref(v_p_3044_);
lean_inc(v___x_3050_);
v___x_3051_ = lean_apply_1(v_p_3044_, v___x_3050_);
v___x_3052_ = lean_unbox(v___x_3051_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = lean_unsigned_to_nat(1u);
v___x_3054_ = lean_nat_add(v_j_3046_, v___x_3053_);
lean_dec(v_j_3046_);
v_j_3046_ = v___x_3054_;
goto _start;
}
else
{
lean_object* v___x_3056_; 
lean_dec_ref(v_p_3044_);
v___x_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3056_, 0, v_j_3046_);
return v___x_3056_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg___boxed(lean_object* v_p_3057_, lean_object* v_as_3058_, lean_object* v_j_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3057_, v_as_3058_, v_j_3059_);
lean_dec_ref(v_as_3058_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object* v_00_u03b1_3061_, lean_object* v_p_3062_, lean_object* v_as_3063_, lean_object* v_j_3064_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3062_, v_as_3063_, v_j_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___boxed(lean_object* v_00_u03b1_3066_, lean_object* v_p_3067_, lean_object* v_as_3068_, lean_object* v_j_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(v_00_u03b1_3066_, v_p_3067_, v_as_3068_, v_j_3069_);
lean_dec_ref(v_as_3068_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg(lean_object* v_p_3071_, lean_object* v_as_3072_){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = lean_unsigned_to_nat(0u);
v___x_3074_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3071_, v_as_3072_, v___x_3073_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg___boxed(lean_object* v_p_3075_, lean_object* v_as_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Array_findFinIdx_x3f___redArg(v_p_3075_, v_as_3076_);
lean_dec_ref(v_as_3076_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f(lean_object* v_00_u03b1_3078_, lean_object* v_p_3079_, lean_object* v_as_3080_){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = lean_unsigned_to_nat(0u);
v___x_3082_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3079_, v_as_3080_, v___x_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_3083_, lean_object* v_p_3084_, lean_object* v_as_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Array_findFinIdx_x3f(v_00_u03b1_3083_, v_p_3084_, v_as_3085_);
lean_dec_ref(v_as_3085_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg(lean_object* v_p_3087_, lean_object* v_as_3088_){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = lean_unsigned_to_nat(0u);
v___x_3090_ = l_Array_findIdx_x3f_loop___redArg(v_p_3087_, v_as_3088_, v___x_3089_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v___x_3091_; 
v___x_3091_ = lean_array_get_size(v_as_3088_);
return v___x_3091_;
}
else
{
lean_object* v_val_3092_; 
v_val_3092_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_val_3092_);
lean_dec_ref_known(v___x_3090_, 1);
return v_val_3092_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg___boxed(lean_object* v_p_3093_, lean_object* v_as_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Array_findIdx___redArg(v_p_3093_, v_as_3094_);
lean_dec_ref(v_as_3094_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx(lean_object* v_00_u03b1_3096_, lean_object* v_p_3097_, lean_object* v_as_3098_){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = lean_unsigned_to_nat(0u);
v___x_3100_ = l_Array_findIdx_x3f_loop___redArg(v_p_3097_, v_as_3098_, v___x_3099_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v___x_3101_; 
v___x_3101_ = lean_array_get_size(v_as_3098_);
return v___x_3101_;
}
else
{
lean_object* v_val_3102_; 
v_val_3102_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_val_3102_);
lean_dec_ref_known(v___x_3100_, 1);
return v_val_3102_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___boxed(lean_object* v_00_u03b1_3103_, lean_object* v_p_3104_, lean_object* v_as_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Array_findIdx(v_00_u03b1_3103_, v_p_3104_, v_as_3105_);
lean_dec_ref(v_as_3105_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg(lean_object* v_inst_3107_, lean_object* v_xs_3108_, lean_object* v_v_3109_, lean_object* v_i_3110_){
_start:
{
lean_object* v___x_3111_; uint8_t v___x_3112_; 
v___x_3111_ = lean_array_get_size(v_xs_3108_);
v___x_3112_ = lean_nat_dec_lt(v_i_3110_, v___x_3111_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; 
lean_dec(v_i_3110_);
lean_dec(v_v_3109_);
lean_dec_ref(v_inst_3107_);
v___x_3113_ = lean_box(0);
return v___x_3113_;
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
v___x_3114_ = lean_array_fget_borrowed(v_xs_3108_, v_i_3110_);
lean_inc_ref(v_inst_3107_);
lean_inc(v_v_3109_);
lean_inc(v___x_3114_);
v___x_3115_ = lean_apply_2(v_inst_3107_, v___x_3114_, v_v_3109_);
v___x_3116_ = lean_unbox(v___x_3115_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = lean_unsigned_to_nat(1u);
v___x_3118_ = lean_nat_add(v_i_3110_, v___x_3117_);
lean_dec(v_i_3110_);
v_i_3110_ = v___x_3118_;
goto _start;
}
else
{
lean_object* v___x_3120_; 
lean_dec(v_v_3109_);
lean_dec_ref(v_inst_3107_);
v___x_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3120_, 0, v_i_3110_);
return v___x_3120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg___boxed(lean_object* v_inst_3121_, lean_object* v_xs_3122_, lean_object* v_v_3123_, lean_object* v_i_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Array_idxOfAux___redArg(v_inst_3121_, v_xs_3122_, v_v_3123_, v_i_3124_);
lean_dec_ref(v_xs_3122_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux(lean_object* v_00_u03b1_3126_, lean_object* v_inst_3127_, lean_object* v_xs_3128_, lean_object* v_v_3129_, lean_object* v_i_3130_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Array_idxOfAux___redArg(v_inst_3127_, v_xs_3128_, v_v_3129_, v_i_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___boxed(lean_object* v_00_u03b1_3132_, lean_object* v_inst_3133_, lean_object* v_xs_3134_, lean_object* v_v_3135_, lean_object* v_i_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Array_idxOfAux(v_00_u03b1_3132_, v_inst_3133_, v_xs_3134_, v_v_3135_, v_i_3136_);
lean_dec_ref(v_xs_3134_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg(lean_object* v_inst_3138_, lean_object* v_xs_3139_, lean_object* v_v_3140_){
_start:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3141_ = lean_unsigned_to_nat(0u);
v___x_3142_ = l_Array_idxOfAux___redArg(v_inst_3138_, v_xs_3139_, v_v_3140_, v___x_3141_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_3143_, lean_object* v_xs_3144_, lean_object* v_v_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Array_finIdxOf_x3f___redArg(v_inst_3143_, v_xs_3144_, v_v_3145_);
lean_dec_ref(v_xs_3144_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f(lean_object* v_00_u03b1_3147_, lean_object* v_inst_3148_, lean_object* v_xs_3149_, lean_object* v_v_3150_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Array_finIdxOf_x3f___redArg(v_inst_3148_, v_xs_3149_, v_v_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_3152_, lean_object* v_inst_3153_, lean_object* v_xs_3154_, lean_object* v_v_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Array_finIdxOf_x3f(v_00_u03b1_3152_, v_inst_3153_, v_xs_3154_, v_v_3155_);
lean_dec_ref(v_xs_3154_);
return v_res_3156_;
}
}
uint8_t l_Array_idxOf___redArg___lam__0(lean_object* v_inst_3157_, lean_object* v_a_3158_, lean_object* v_x_3159_){
_start:
{
lean_object* v___x_3160_; uint8_t v___x_3161_; 
v___x_3160_ = lean_apply_2(v_inst_3157_, v_x_3159_, v_a_3158_);
v___x_3161_ = lean_unbox(v___x_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT void l_Array_idxOf___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3157_ = stack[0].m_obj;
lean_object* v_a_3158_ = stack[1].m_obj;
lean_object* v_x_3159_ = stack[2].m_obj;
uint8_t v_res_3162_;
v_res_3162_ = l_Array_idxOf___redArg___lam__0(v_inst_3157_, v_a_3158_, v_x_3159_);
stack->m_num = v_res_3162_;
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___lam__0___boxed(lean_object* v_inst_3163_, lean_object* v_a_3164_, lean_object* v_x_3165_){
_start:
{
uint8_t v_res_3166_; lean_object* v_r_3167_; 
v_res_3166_ = l_Array_idxOf___redArg___lam__0(v_inst_3163_, v_a_3164_, v_x_3165_);
v_r_3167_ = lean_box(v_res_3166_);
return v_r_3167_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg(lean_object* v_inst_3168_, lean_object* v_a_3169_, lean_object* v_as_3170_){
_start:
{
lean_object* v___f_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___f_3171_ = lean_alloc_closure((void*)(l_Array_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3171_, 0, v_inst_3168_);
lean_closure_set(v___f_3171_, 1, v_a_3169_);
v___x_3172_ = lean_unsigned_to_nat(0u);
v___x_3173_ = l_Array_findIdx_x3f_loop___redArg(v___f_3171_, v_as_3170_, v___x_3172_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v___x_3174_; 
v___x_3174_ = lean_array_get_size(v_as_3170_);
return v___x_3174_;
}
else
{
lean_object* v_val_3175_; 
v_val_3175_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_val_3175_);
lean_dec_ref_known(v___x_3173_, 1);
return v_val_3175_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___boxed(lean_object* v_inst_3176_, lean_object* v_a_3177_, lean_object* v_as_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Array_idxOf___redArg(v_inst_3176_, v_a_3177_, v_as_3178_);
lean_dec_ref(v_as_3178_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf(lean_object* v_00_u03b1_3180_, lean_object* v_inst_3181_, lean_object* v_a_3182_, lean_object* v_as_3183_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Array_idxOf___redArg(v_inst_3181_, v_a_3182_, v_as_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___boxed(lean_object* v_00_u03b1_3185_, lean_object* v_inst_3186_, lean_object* v_a_3187_, lean_object* v_as_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_Array_idxOf(v_00_u03b1_3185_, v_inst_3186_, v_a_3187_, v_as_3188_);
lean_dec_ref(v_as_3188_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg(lean_object* v_inst_3190_, lean_object* v_xs_3191_, lean_object* v_v_3192_){
_start:
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Array_finIdxOf_x3f___redArg(v_inst_3190_, v_xs_3191_, v_v_3192_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v___x_3194_; 
v___x_3194_ = lean_box(0);
return v___x_3194_;
}
else
{
lean_object* v_val_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
v_val_3195_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3193_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_val_3195_);
lean_dec(v___x_3193_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_val_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg___boxed(lean_object* v_inst_3203_, lean_object* v_xs_3204_, lean_object* v_v_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Array_idxOf_x3f___redArg(v_inst_3203_, v_xs_3204_, v_v_3205_);
lean_dec_ref(v_xs_3204_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f(lean_object* v_00_u03b1_3207_, lean_object* v_inst_3208_, lean_object* v_xs_3209_, lean_object* v_v_3210_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l_Array_idxOf_x3f___redArg(v_inst_3208_, v_xs_3209_, v_v_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___boxed(lean_object* v_00_u03b1_3212_, lean_object* v_inst_3213_, lean_object* v_xs_3214_, lean_object* v_v_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_Array_idxOf_x3f(v_00_u03b1_3212_, v_inst_3213_, v_xs_3214_, v_v_3215_);
lean_dec_ref(v_xs_3214_);
return v_res_3216_;
}
}
uint8_t l_Array_any___redArg___lam__0(lean_object* v_p_3217_, lean_object* v_x_3218_){
_start:
{
lean_object* v___x_3219_; uint8_t v___x_3220_; 
v___x_3219_ = lean_apply_1(v_p_3217_, v_x_3218_);
v___x_3220_ = lean_unbox(v___x_3219_);
return v___x_3220_;
}
}
LEAN_EXPORT void l_Array_any___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3217_ = stack[0].m_obj;
lean_object* v_x_3218_ = stack[1].m_obj;
uint8_t v_res_3221_;
v_res_3221_ = l_Array_any___redArg___lam__0(v_p_3217_, v_x_3218_);
stack->m_num = v_res_3221_;
}
LEAN_EXPORT lean_object* l_Array_any___redArg___lam__0___boxed(lean_object* v_p_3222_, lean_object* v_x_3223_){
_start:
{
uint8_t v_res_3224_; lean_object* v_r_3225_; 
v_res_3224_ = l_Array_any___redArg___lam__0(v_p_3222_, v_x_3223_);
v_r_3225_ = lean_box(v_res_3224_);
return v_r_3225_;
}
}
uint8_t l_Array_any___redArg(lean_object* v_as_3226_, lean_object* v_p_3227_, lean_object* v_start_3228_, lean_object* v_stop_3229_){
_start:
{
lean_object* v___x_3230_; uint8_t v___x_3231_; 
v___x_3230_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3231_ = lean_nat_dec_lt(v_start_3228_, v_stop_3229_);
if (v___x_3231_ == 0)
{
lean_dec(v_stop_3229_);
lean_dec_ref(v_p_3227_);
lean_dec_ref(v_as_3226_);
return v___x_3231_;
}
else
{
lean_object* v___f_3232_; lean_object* v___y_3234_; lean_object* v___x_3240_; uint8_t v___x_3241_; 
v___f_3232_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3232_, 0, v_p_3227_);
v___x_3240_ = lean_array_get_size(v_as_3226_);
v___x_3241_ = lean_nat_dec_le(v_stop_3229_, v___x_3240_);
if (v___x_3241_ == 0)
{
lean_dec(v_stop_3229_);
v___y_3234_ = v___x_3240_;
goto v___jp_3233_;
}
else
{
v___y_3234_ = v_stop_3229_;
goto v___jp_3233_;
}
v___jp_3233_:
{
uint8_t v___x_3235_; 
v___x_3235_ = lean_nat_dec_lt(v_start_3228_, v___y_3234_);
if (v___x_3235_ == 0)
{
lean_dec(v___y_3234_);
lean_dec_ref(v___f_3232_);
lean_dec_ref(v_as_3226_);
return v___x_3235_;
}
else
{
size_t v___x_3236_; size_t v___x_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; 
v___x_3236_ = lean_usize_of_nat(v_start_3228_);
v___x_3237_ = lean_usize_of_nat(v___y_3234_);
lean_dec(v___y_3234_);
v___x_3238_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3230_, v___f_3232_, v_as_3226_, v___x_3236_, v___x_3237_);
v___x_3239_ = lean_unbox(v___x_3238_);
lean_dec(v___x_3238_);
return v___x_3239_;
}
}
}
}
}
LEAN_EXPORT void l_Array_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3226_ = stack[0].m_obj;
lean_object* v_p_3227_ = stack[1].m_obj;
lean_object* v_start_3228_ = stack[2].m_obj;
lean_object* v_stop_3229_ = stack[3].m_obj;
uint8_t v_res_3242_;
v_res_3242_ = l_Array_any___redArg(v_as_3226_, v_p_3227_, v_start_3228_, v_stop_3229_);
stack->m_num = v_res_3242_;
}
LEAN_EXPORT lean_object* l_Array_any___redArg___boxed(lean_object* v_as_3243_, lean_object* v_p_3244_, lean_object* v_start_3245_, lean_object* v_stop_3246_){
_start:
{
uint8_t v_res_3247_; lean_object* v_r_3248_; 
v_res_3247_ = l_Array_any___redArg(v_as_3243_, v_p_3244_, v_start_3245_, v_stop_3246_);
lean_dec(v_start_3245_);
v_r_3248_ = lean_box(v_res_3247_);
return v_r_3248_;
}
}
uint8_t l_Array_any(lean_object* v_00_u03b1_3249_, lean_object* v_as_3250_, lean_object* v_p_3251_, lean_object* v_start_3252_, lean_object* v_stop_3253_){
_start:
{
lean_object* v___x_3254_; uint8_t v___x_3255_; 
v___x_3254_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3255_ = lean_nat_dec_lt(v_start_3252_, v_stop_3253_);
if (v___x_3255_ == 0)
{
lean_dec(v_stop_3253_);
lean_dec_ref(v_p_3251_);
lean_dec_ref(v_as_3250_);
return v___x_3255_;
}
else
{
lean_object* v___f_3256_; lean_object* v___y_3258_; lean_object* v___x_3264_; uint8_t v___x_3265_; 
v___f_3256_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3256_, 0, v_p_3251_);
v___x_3264_ = lean_array_get_size(v_as_3250_);
v___x_3265_ = lean_nat_dec_le(v_stop_3253_, v___x_3264_);
if (v___x_3265_ == 0)
{
lean_dec(v_stop_3253_);
v___y_3258_ = v___x_3264_;
goto v___jp_3257_;
}
else
{
v___y_3258_ = v_stop_3253_;
goto v___jp_3257_;
}
v___jp_3257_:
{
uint8_t v___x_3259_; 
v___x_3259_ = lean_nat_dec_lt(v_start_3252_, v___y_3258_);
if (v___x_3259_ == 0)
{
lean_dec(v___y_3258_);
lean_dec_ref(v___f_3256_);
lean_dec_ref(v_as_3250_);
return v___x_3259_;
}
else
{
size_t v___x_3260_; size_t v___x_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; 
v___x_3260_ = lean_usize_of_nat(v_start_3252_);
v___x_3261_ = lean_usize_of_nat(v___y_3258_);
lean_dec(v___y_3258_);
v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3254_, v___f_3256_, v_as_3250_, v___x_3260_, v___x_3261_);
v___x_3263_ = lean_unbox(v___x_3262_);
lean_dec(v___x_3262_);
return v___x_3263_;
}
}
}
}
}
LEAN_EXPORT void l_Array_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3250_ = stack[1].m_obj;
lean_object* v_p_3251_ = stack[2].m_obj;
lean_object* v_start_3252_ = stack[3].m_obj;
lean_object* v_stop_3253_ = stack[4].m_obj;
uint8_t v_res_3266_;
v_res_3266_ = l_Array_any(lean_box(0), v_as_3250_, v_p_3251_, v_start_3252_, v_stop_3253_);
stack->m_num = v_res_3266_;
}
LEAN_EXPORT lean_object* l_Array_any___boxed(lean_object* v_00_u03b1_3267_, lean_object* v_as_3268_, lean_object* v_p_3269_, lean_object* v_start_3270_, lean_object* v_stop_3271_){
_start:
{
uint8_t v_res_3272_; lean_object* v_r_3273_; 
v_res_3272_ = l_Array_any(v_00_u03b1_3267_, v_as_3268_, v_p_3269_, v_start_3270_, v_stop_3271_);
lean_dec(v_start_3270_);
v_r_3273_ = lean_box(v_res_3272_);
return v_r_3273_;
}
}
uint8_t l_Array_all___redArg___lam__0(lean_object* v_p_3274_, uint8_t v___x_3275_, lean_object* v_v_3276_){
_start:
{
lean_object* v___x_3277_; uint8_t v___x_3278_; 
v___x_3277_ = lean_apply_1(v_p_3274_, v_v_3276_);
v___x_3278_ = lean_unbox(v___x_3277_);
if (v___x_3278_ == 0)
{
return v___x_3275_;
}
else
{
uint8_t v___x_3279_; 
v___x_3279_ = 0;
return v___x_3279_;
}
}
}
LEAN_EXPORT void l_Array_all___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3274_ = stack[0].m_obj;
uint8_t v___x_3275_ = stack[1].m_num;
lean_object* v_v_3276_ = stack[2].m_obj;
uint8_t v_res_3280_;
v_res_3280_ = l_Array_all___redArg___lam__0(v_p_3274_, v___x_3275_, v_v_3276_);
stack->m_num = v_res_3280_;
}
LEAN_EXPORT lean_object* l_Array_all___redArg___lam__0___boxed(lean_object* v_p_3281_, lean_object* v___x_3282_, lean_object* v_v_3283_){
_start:
{
uint8_t v___x_335__boxed_3284_; uint8_t v_res_3285_; lean_object* v_r_3286_; 
v___x_335__boxed_3284_ = lean_unbox(v___x_3282_);
v_res_3285_ = l_Array_all___redArg___lam__0(v_p_3281_, v___x_335__boxed_3284_, v_v_3283_);
v_r_3286_ = lean_box(v_res_3285_);
return v_r_3286_;
}
}
uint8_t l_Array_all___redArg(lean_object* v_as_3287_, lean_object* v_p_3288_, lean_object* v_start_3289_, lean_object* v_stop_3290_){
_start:
{
lean_object* v___x_3291_; uint8_t v___x_3292_; 
v___x_3291_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3292_ = lean_nat_dec_lt(v_start_3289_, v_stop_3290_);
if (v___x_3292_ == 0)
{
uint8_t v___x_3293_; 
lean_dec(v_stop_3290_);
lean_dec_ref(v_p_3288_);
lean_dec_ref(v_as_3287_);
v___x_3293_ = 1;
return v___x_3293_;
}
else
{
lean_object* v___x_3294_; lean_object* v___f_3295_; lean_object* v___y_3297_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v___x_3294_ = lean_box(v___x_3292_);
v___f_3295_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3295_, 0, v_p_3288_);
lean_closure_set(v___f_3295_, 1, v___x_3294_);
v___x_3304_ = lean_array_get_size(v_as_3287_);
v___x_3305_ = lean_nat_dec_le(v_stop_3290_, v___x_3304_);
if (v___x_3305_ == 0)
{
lean_dec(v_stop_3290_);
v___y_3297_ = v___x_3304_;
goto v___jp_3296_;
}
else
{
v___y_3297_ = v_stop_3290_;
goto v___jp_3296_;
}
v___jp_3296_:
{
uint8_t v___x_3298_; 
v___x_3298_ = lean_nat_dec_lt(v_start_3289_, v___y_3297_);
if (v___x_3298_ == 0)
{
lean_dec(v___y_3297_);
lean_dec_ref(v___f_3295_);
lean_dec_ref(v_as_3287_);
return v___x_3292_;
}
else
{
size_t v___x_3299_; size_t v___x_3300_; lean_object* v___x_3301_; uint8_t v___x_3302_; 
v___x_3299_ = lean_usize_of_nat(v_start_3289_);
v___x_3300_ = lean_usize_of_nat(v___y_3297_);
lean_dec(v___y_3297_);
v___x_3301_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3291_, v___f_3295_, v_as_3287_, v___x_3299_, v___x_3300_);
v___x_3302_ = lean_unbox(v___x_3301_);
lean_dec(v___x_3301_);
if (v___x_3302_ == 0)
{
return v___x_3298_;
}
else
{
uint8_t v___x_3303_; 
v___x_3303_ = 0;
return v___x_3303_;
}
}
}
}
}
}
LEAN_EXPORT void l_Array_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3287_ = stack[0].m_obj;
lean_object* v_p_3288_ = stack[1].m_obj;
lean_object* v_start_3289_ = stack[2].m_obj;
lean_object* v_stop_3290_ = stack[3].m_obj;
uint8_t v_res_3306_;
v_res_3306_ = l_Array_all___redArg(v_as_3287_, v_p_3288_, v_start_3289_, v_stop_3290_);
stack->m_num = v_res_3306_;
}
LEAN_EXPORT lean_object* l_Array_all___redArg___boxed(lean_object* v_as_3307_, lean_object* v_p_3308_, lean_object* v_start_3309_, lean_object* v_stop_3310_){
_start:
{
uint8_t v_res_3311_; lean_object* v_r_3312_; 
v_res_3311_ = l_Array_all___redArg(v_as_3307_, v_p_3308_, v_start_3309_, v_stop_3310_);
lean_dec(v_start_3309_);
v_r_3312_ = lean_box(v_res_3311_);
return v_r_3312_;
}
}
uint8_t l_Array_all(lean_object* v_00_u03b1_3313_, lean_object* v_as_3314_, lean_object* v_p_3315_, lean_object* v_start_3316_, lean_object* v_stop_3317_){
_start:
{
lean_object* v___x_3318_; uint8_t v___x_3319_; 
v___x_3318_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3319_ = lean_nat_dec_lt(v_start_3316_, v_stop_3317_);
if (v___x_3319_ == 0)
{
uint8_t v___x_3320_; 
lean_dec(v_stop_3317_);
lean_dec_ref(v_p_3315_);
lean_dec_ref(v_as_3314_);
v___x_3320_ = 1;
return v___x_3320_;
}
else
{
lean_object* v___x_3321_; lean_object* v___f_3322_; lean_object* v___y_3324_; lean_object* v___x_3331_; uint8_t v___x_3332_; 
v___x_3321_ = lean_box(v___x_3319_);
v___f_3322_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3322_, 0, v_p_3315_);
lean_closure_set(v___f_3322_, 1, v___x_3321_);
v___x_3331_ = lean_array_get_size(v_as_3314_);
v___x_3332_ = lean_nat_dec_le(v_stop_3317_, v___x_3331_);
if (v___x_3332_ == 0)
{
lean_dec(v_stop_3317_);
v___y_3324_ = v___x_3331_;
goto v___jp_3323_;
}
else
{
v___y_3324_ = v_stop_3317_;
goto v___jp_3323_;
}
v___jp_3323_:
{
uint8_t v___x_3325_; 
v___x_3325_ = lean_nat_dec_lt(v_start_3316_, v___y_3324_);
if (v___x_3325_ == 0)
{
lean_dec(v___y_3324_);
lean_dec_ref(v___f_3322_);
lean_dec_ref(v_as_3314_);
return v___x_3319_;
}
else
{
size_t v___x_3326_; size_t v___x_3327_; lean_object* v___x_3328_; uint8_t v___x_3329_; 
v___x_3326_ = lean_usize_of_nat(v_start_3316_);
v___x_3327_ = lean_usize_of_nat(v___y_3324_);
lean_dec(v___y_3324_);
v___x_3328_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3318_, v___f_3322_, v_as_3314_, v___x_3326_, v___x_3327_);
v___x_3329_ = lean_unbox(v___x_3328_);
lean_dec(v___x_3328_);
if (v___x_3329_ == 0)
{
return v___x_3325_;
}
else
{
uint8_t v___x_3330_; 
v___x_3330_ = 0;
return v___x_3330_;
}
}
}
}
}
}
LEAN_EXPORT void l_Array_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3314_ = stack[1].m_obj;
lean_object* v_p_3315_ = stack[2].m_obj;
lean_object* v_start_3316_ = stack[3].m_obj;
lean_object* v_stop_3317_ = stack[4].m_obj;
uint8_t v_res_3333_;
v_res_3333_ = l_Array_all(lean_box(0), v_as_3314_, v_p_3315_, v_start_3316_, v_stop_3317_);
stack->m_num = v_res_3333_;
}
LEAN_EXPORT lean_object* l_Array_all___boxed(lean_object* v_00_u03b1_3334_, lean_object* v_as_3335_, lean_object* v_p_3336_, lean_object* v_start_3337_, lean_object* v_stop_3338_){
_start:
{
uint8_t v_res_3339_; lean_object* v_r_3340_; 
v_res_3339_ = l_Array_all(v_00_u03b1_3334_, v_as_3335_, v_p_3336_, v_start_3337_, v_stop_3338_);
lean_dec(v_start_3337_);
v_r_3340_ = lean_box(v_res_3339_);
return v_r_3340_;
}
}
uint8_t l_Array_contains___redArg___lam__0(lean_object* v_inst_3341_, lean_object* v_a_3342_, lean_object* v_x_3343_){
_start:
{
lean_object* v___x_3344_; uint8_t v___x_3345_; 
v___x_3344_ = lean_apply_2(v_inst_3341_, v_a_3342_, v_x_3343_);
v___x_3345_ = lean_unbox(v___x_3344_);
return v___x_3345_;
}
}
LEAN_EXPORT void l_Array_contains___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3341_ = stack[0].m_obj;
lean_object* v_a_3342_ = stack[1].m_obj;
lean_object* v_x_3343_ = stack[2].m_obj;
uint8_t v_res_3346_;
v_res_3346_ = l_Array_contains___redArg___lam__0(v_inst_3341_, v_a_3342_, v_x_3343_);
stack->m_num = v_res_3346_;
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___lam__0___boxed(lean_object* v_inst_3347_, lean_object* v_a_3348_, lean_object* v_x_3349_){
_start:
{
uint8_t v_res_3350_; lean_object* v_r_3351_; 
v_res_3350_ = l_Array_contains___redArg___lam__0(v_inst_3347_, v_a_3348_, v_x_3349_);
v_r_3351_ = lean_box(v_res_3350_);
return v_r_3351_;
}
}
uint8_t l_Array_contains___redArg(lean_object* v_inst_3352_, lean_object* v_as_3353_, lean_object* v_a_3354_){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3355_ = lean_unsigned_to_nat(0u);
v___x_3356_ = lean_array_get_size(v_as_3353_);
v___x_3357_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3358_ = lean_nat_dec_lt(v___x_3355_, v___x_3356_);
if (v___x_3358_ == 0)
{
lean_dec(v_a_3354_);
lean_dec_ref(v_as_3353_);
lean_dec_ref(v_inst_3352_);
return v___x_3358_;
}
else
{
if (v___x_3358_ == 0)
{
lean_dec(v_a_3354_);
lean_dec_ref(v_as_3353_);
lean_dec_ref(v_inst_3352_);
return v___x_3358_;
}
else
{
lean_object* v___f_3359_; size_t v___x_3360_; size_t v___x_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v___f_3359_ = lean_alloc_closure((void*)(l_Array_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3359_, 0, v_inst_3352_);
lean_closure_set(v___f_3359_, 1, v_a_3354_);
v___x_3360_ = ((size_t)0ULL);
v___x_3361_ = lean_usize_of_nat(v___x_3356_);
v___x_3362_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3357_, v___f_3359_, v_as_3353_, v___x_3360_, v___x_3361_);
v___x_3363_ = lean_unbox(v___x_3362_);
lean_dec(v___x_3362_);
return v___x_3363_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3352_ = stack[0].m_obj;
lean_object* v_as_3353_ = stack[1].m_obj;
lean_object* v_a_3354_ = stack[2].m_obj;
uint8_t v_res_3364_;
v_res_3364_ = l_Array_contains___redArg(v_inst_3352_, v_as_3353_, v_a_3354_);
stack->m_num = v_res_3364_;
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___boxed(lean_object* v_inst_3365_, lean_object* v_as_3366_, lean_object* v_a_3367_){
_start:
{
uint8_t v_res_3368_; lean_object* v_r_3369_; 
v_res_3368_ = l_Array_contains___redArg(v_inst_3365_, v_as_3366_, v_a_3367_);
v_r_3369_ = lean_box(v_res_3368_);
return v_r_3369_;
}
}
uint8_t l_Array_contains(lean_object* v_00_u03b1_3370_, lean_object* v_inst_3371_, lean_object* v_as_3372_, lean_object* v_a_3373_){
_start:
{
uint8_t v___x_3374_; 
v___x_3374_ = l_Array_contains___redArg(v_inst_3371_, v_as_3372_, v_a_3373_);
return v___x_3374_;
}
}
LEAN_EXPORT void l_Array_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3371_ = stack[1].m_obj;
lean_object* v_as_3372_ = stack[2].m_obj;
lean_object* v_a_3373_ = stack[3].m_obj;
uint8_t v_res_3375_;
v_res_3375_ = l_Array_contains(lean_box(0), v_inst_3371_, v_as_3372_, v_a_3373_);
stack->m_num = v_res_3375_;
}
LEAN_EXPORT lean_object* l_Array_contains___boxed(lean_object* v_00_u03b1_3376_, lean_object* v_inst_3377_, lean_object* v_as_3378_, lean_object* v_a_3379_){
_start:
{
uint8_t v_res_3380_; lean_object* v_r_3381_; 
v_res_3380_ = l_Array_contains(v_00_u03b1_3376_, v_inst_3377_, v_as_3378_, v_a_3379_);
v_r_3381_ = lean_box(v_res_3380_);
return v_r_3381_;
}
}
uint8_t l_Array_elem___redArg(lean_object* v_inst_3382_, lean_object* v_a_3383_, lean_object* v_as_3384_){
_start:
{
uint8_t v___x_3385_; 
v___x_3385_ = l_Array_contains___redArg(v_inst_3382_, v_as_3384_, v_a_3383_);
return v___x_3385_;
}
}
LEAN_EXPORT void l_Array_elem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3382_ = stack[0].m_obj;
lean_object* v_a_3383_ = stack[1].m_obj;
lean_object* v_as_3384_ = stack[2].m_obj;
uint8_t v_res_3386_;
v_res_3386_ = l_Array_elem___redArg(v_inst_3382_, v_a_3383_, v_as_3384_);
stack->m_num = v_res_3386_;
}
LEAN_EXPORT lean_object* l_Array_elem___redArg___boxed(lean_object* v_inst_3387_, lean_object* v_a_3388_, lean_object* v_as_3389_){
_start:
{
uint8_t v_res_3390_; lean_object* v_r_3391_; 
v_res_3390_ = l_Array_elem___redArg(v_inst_3387_, v_a_3388_, v_as_3389_);
v_r_3391_ = lean_box(v_res_3390_);
return v_r_3391_;
}
}
uint8_t l_Array_elem(lean_object* v_00_u03b1_3392_, lean_object* v_inst_3393_, lean_object* v_a_3394_, lean_object* v_as_3395_){
_start:
{
uint8_t v___x_3396_; 
v___x_3396_ = l_Array_contains___redArg(v_inst_3393_, v_as_3395_, v_a_3394_);
return v___x_3396_;
}
}
LEAN_EXPORT void l_Array_elem_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3393_ = stack[1].m_obj;
lean_object* v_a_3394_ = stack[2].m_obj;
lean_object* v_as_3395_ = stack[3].m_obj;
uint8_t v_res_3397_;
v_res_3397_ = l_Array_elem(lean_box(0), v_inst_3393_, v_a_3394_, v_as_3395_);
stack->m_num = v_res_3397_;
}
LEAN_EXPORT lean_object* l_Array_elem___boxed(lean_object* v_00_u03b1_3398_, lean_object* v_inst_3399_, lean_object* v_a_3400_, lean_object* v_as_3401_){
_start:
{
uint8_t v_res_3402_; lean_object* v_r_3403_; 
v_res_3402_ = l_Array_elem(v_00_u03b1_3398_, v_inst_3399_, v_a_3400_, v_as_3401_);
v_r_3403_ = lean_box(v_res_3402_);
return v_r_3403_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(lean_object* v_as_3404_, size_t v_i_3405_, size_t v_stop_3406_, lean_object* v_b_3407_){
_start:
{
uint8_t v___x_3408_; 
v___x_3408_ = lean_usize_dec_eq(v_i_3405_, v_stop_3406_);
if (v___x_3408_ == 0)
{
size_t v___x_3409_; size_t v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3409_ = ((size_t)1ULL);
v___x_3410_ = lean_usize_sub(v_i_3405_, v___x_3409_);
v___x_3411_ = lean_array_uget_borrowed(v_as_3404_, v___x_3410_);
lean_inc(v___x_3411_);
v___x_3412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
lean_ctor_set(v___x_3412_, 1, v_b_3407_);
v_i_3405_ = v___x_3410_;
v_b_3407_ = v___x_3412_;
goto _start;
}
else
{
return v_b_3407_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3404_ = stack[0].m_obj;
size_t v_i_3405_ = stack[1].m_num;
size_t v_stop_3406_ = stack[2].m_num;
lean_object* v_b_3407_ = stack[3].m_obj;
lean_object* v_res_3414_;
v_res_3414_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3404_, v_i_3405_, v_stop_3406_, v_b_3407_);
stack->m_obj
 = v_res_3414_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg___boxed(lean_object* v_as_3415_, lean_object* v_i_3416_, lean_object* v_stop_3417_, lean_object* v_b_3418_){
_start:
{
size_t v_i_boxed_3419_; size_t v_stop_boxed_3420_; lean_object* v_res_3421_; 
v_i_boxed_3419_ = lean_unbox_usize(v_i_3416_);
lean_dec(v_i_3416_);
v_stop_boxed_3420_ = lean_unbox_usize(v_stop_3417_);
lean_dec(v_stop_3417_);
v_res_3421_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3415_, v_i_boxed_3419_, v_stop_boxed_3420_, v_b_3418_);
lean_dec_ref(v_as_3415_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg(lean_object* v_as_3422_){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v___x_3423_ = lean_box(0);
v___x_3424_ = lean_array_get_size(v_as_3422_);
v___x_3425_ = lean_unsigned_to_nat(0u);
v___x_3426_ = lean_nat_dec_lt(v___x_3425_, v___x_3424_);
if (v___x_3426_ == 0)
{
return v___x_3423_;
}
else
{
size_t v___x_3427_; size_t v___x_3428_; lean_object* v___x_3429_; 
v___x_3427_ = lean_usize_of_nat(v___x_3424_);
v___x_3428_ = ((size_t)0ULL);
v___x_3429_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3422_, v___x_3427_, v___x_3428_, v___x_3423_);
return v___x_3429_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg___boxed(lean_object* v_as_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Array_toListImpl___redArg(v_as_3430_);
lean_dec_ref(v_as_3430_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* lean_array_to_list_impl(lean_object* v_00_u03b1_3432_, lean_object* v_as_3433_){
_start:
{
lean_object* v___x_3434_; 
v___x_3434_ = l_Array_toListImpl___redArg(v_as_3433_);
lean_dec_ref(v_as_3433_);
return v___x_3434_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(lean_object* v_00_u03b1_3435_, lean_object* v_as_3436_, size_t v_i_3437_, size_t v_stop_3438_, lean_object* v_b_3439_){
_start:
{
lean_object* v___x_3440_; 
v___x_3440_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3436_, v_i_3437_, v_stop_3438_, v_b_3439_);
return v___x_3440_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3436_ = stack[1].m_obj;
size_t v_i_3437_ = stack[2].m_num;
size_t v_stop_3438_ = stack[3].m_num;
lean_object* v_b_3439_ = stack[4].m_obj;
lean_object* v_res_3441_;
v_res_3441_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(lean_box(0), v_as_3436_, v_i_3437_, v_stop_3438_, v_b_3439_);
stack->m_obj
 = v_res_3441_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___boxed(lean_object* v_00_u03b1_3442_, lean_object* v_as_3443_, lean_object* v_i_3444_, lean_object* v_stop_3445_, lean_object* v_b_3446_){
_start:
{
size_t v_i_boxed_3447_; size_t v_stop_boxed_3448_; lean_object* v_res_3449_; 
v_i_boxed_3447_ = lean_unbox_usize(v_i_3444_);
lean_dec(v_i_3444_);
v_stop_boxed_3448_ = lean_unbox_usize(v_stop_3445_);
lean_dec(v_stop_3445_);
v_res_3449_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(v_00_u03b1_3442_, v_as_3443_, v_i_boxed_3447_, v_stop_boxed_3448_, v_b_3446_);
lean_dec_ref(v_as_3443_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg___lam__0(lean_object* v_x1_3450_, lean_object* v_x2_3451_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3452_, 0, v_x1_3450_);
lean_ctor_set(v___x_3452_, 1, v_x2_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg(lean_object* v_as_3454_, lean_object* v_l_3455_){
_start:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; uint8_t v___x_3459_; 
v___x_3456_ = lean_array_get_size(v_as_3454_);
v___x_3457_ = lean_unsigned_to_nat(0u);
v___x_3458_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3459_ = lean_nat_dec_lt(v___x_3457_, v___x_3456_);
if (v___x_3459_ == 0)
{
lean_dec_ref(v_as_3454_);
return v_l_3455_;
}
else
{
lean_object* v___f_3460_; size_t v___x_3461_; size_t v___x_3462_; lean_object* v___x_3463_; 
v___f_3460_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3461_ = lean_usize_of_nat(v___x_3456_);
v___x_3462_ = ((size_t)0ULL);
v___x_3463_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3458_, v___f_3460_, v_as_3454_, v___x_3461_, v___x_3462_, v_l_3455_);
return v___x_3463_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend(lean_object* v_00_u03b1_3464_, lean_object* v_as_3465_, lean_object* v_l_3466_){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; uint8_t v___x_3470_; 
v___x_3467_ = lean_array_get_size(v_as_3465_);
v___x_3468_ = lean_unsigned_to_nat(0u);
v___x_3469_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3470_ = lean_nat_dec_lt(v___x_3468_, v___x_3467_);
if (v___x_3470_ == 0)
{
lean_dec_ref(v_as_3465_);
return v_l_3466_;
}
else
{
lean_object* v___f_3471_; size_t v___x_3472_; size_t v___x_3473_; lean_object* v___x_3474_; 
v___f_3471_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3472_ = lean_usize_of_nat(v___x_3467_);
v___x_3473_ = ((size_t)0ULL);
v___x_3474_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3469_, v___f_3471_, v_as_3465_, v___x_3472_, v___x_3473_, v_l_3466_);
return v___x_3474_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(lean_object* v_as_3475_, size_t v_i_3476_, size_t v_stop_3477_, lean_object* v_b_3478_){
_start:
{
uint8_t v___x_3479_; 
v___x_3479_ = lean_usize_dec_eq(v_i_3476_, v_stop_3477_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3480_; lean_object* v___x_3481_; size_t v___x_3482_; size_t v___x_3483_; 
v___x_3480_ = lean_array_uget_borrowed(v_as_3475_, v_i_3476_);
lean_inc(v___x_3480_);
v___x_3481_ = lean_array_push(v_b_3478_, v___x_3480_);
v___x_3482_ = ((size_t)1ULL);
v___x_3483_ = lean_usize_add(v_i_3476_, v___x_3482_);
v_i_3476_ = v___x_3483_;
v_b_3478_ = v___x_3481_;
goto _start;
}
else
{
return v_b_3478_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3475_ = stack[0].m_obj;
size_t v_i_3476_ = stack[1].m_num;
size_t v_stop_3477_ = stack[2].m_num;
lean_object* v_b_3478_ = stack[3].m_obj;
lean_object* v_res_3485_;
v_res_3485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3475_, v_i_3476_, v_stop_3477_, v_b_3478_);
stack->m_obj
 = v_res_3485_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg___boxed(lean_object* v_as_3486_, lean_object* v_i_3487_, lean_object* v_stop_3488_, lean_object* v_b_3489_){
_start:
{
size_t v_i_boxed_3490_; size_t v_stop_boxed_3491_; lean_object* v_res_3492_; 
v_i_boxed_3490_ = lean_unbox_usize(v_i_3487_);
lean_dec(v_i_3487_);
v_stop_boxed_3491_ = lean_unbox_usize(v_stop_3488_);
lean_dec(v_stop_3488_);
v_res_3492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3486_, v_i_boxed_3490_, v_stop_boxed_3491_, v_b_3489_);
lean_dec_ref(v_as_3486_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg(lean_object* v_as_3493_, lean_object* v_bs_3494_){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; 
v___x_3495_ = lean_unsigned_to_nat(0u);
v___x_3496_ = lean_array_get_size(v_bs_3494_);
v___x_3497_ = lean_nat_dec_lt(v___x_3495_, v___x_3496_);
if (v___x_3497_ == 0)
{
return v_as_3493_;
}
else
{
uint8_t v___x_3498_; 
v___x_3498_ = lean_nat_dec_le(v___x_3496_, v___x_3496_);
if (v___x_3498_ == 0)
{
if (v___x_3497_ == 0)
{
return v_as_3493_;
}
else
{
size_t v___x_3499_; size_t v___x_3500_; lean_object* v___x_3501_; 
v___x_3499_ = ((size_t)0ULL);
v___x_3500_ = lean_usize_of_nat(v___x_3496_);
v___x_3501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3494_, v___x_3499_, v___x_3500_, v_as_3493_);
return v___x_3501_;
}
}
else
{
size_t v___x_3502_; size_t v___x_3503_; lean_object* v___x_3504_; 
v___x_3502_ = ((size_t)0ULL);
v___x_3503_ = lean_usize_of_nat(v___x_3496_);
v___x_3504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3494_, v___x_3502_, v___x_3503_, v_as_3493_);
return v___x_3504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg___boxed(lean_object* v_as_3505_, lean_object* v_bs_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Array_append___redArg(v_as_3505_, v_bs_3506_);
lean_dec_ref(v_bs_3506_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Array_append(lean_object* v_00_u03b1_3508_, lean_object* v_as_3509_, lean_object* v_bs_3510_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = l_Array_append___redArg(v_as_3509_, v_bs_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Array_append___boxed(lean_object* v_00_u03b1_3512_, lean_object* v_as_3513_, lean_object* v_bs_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Array_append(v_00_u03b1_3512_, v_as_3513_, v_bs_3514_);
lean_dec_ref(v_bs_3514_);
return v_res_3515_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(lean_object* v_00_u03b1_3516_, lean_object* v_as_3517_, size_t v_i_3518_, size_t v_stop_3519_, lean_object* v_b_3520_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3517_, v_i_3518_, v_stop_3519_, v_b_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3517_ = stack[1].m_obj;
size_t v_i_3518_ = stack[2].m_num;
size_t v_stop_3519_ = stack[3].m_num;
lean_object* v_b_3520_ = stack[4].m_obj;
lean_object* v_res_3522_;
v_res_3522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(lean_box(0), v_as_3517_, v_i_3518_, v_stop_3519_, v_b_3520_);
stack->m_obj
 = v_res_3522_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___boxed(lean_object* v_00_u03b1_3523_, lean_object* v_as_3524_, lean_object* v_i_3525_, lean_object* v_stop_3526_, lean_object* v_b_3527_){
_start:
{
size_t v_i_boxed_3528_; size_t v_stop_boxed_3529_; lean_object* v_res_3530_; 
v_i_boxed_3528_ = lean_unbox_usize(v_i_3525_);
lean_dec(v_i_3525_);
v_stop_boxed_3529_ = lean_unbox_usize(v_stop_3526_);
lean_dec(v_stop_3526_);
v_res_3530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(v_00_u03b1_3523_, v_as_3524_, v_i_boxed_3528_, v_stop_boxed_3529_, v_b_3527_);
lean_dec_ref(v_as_3524_);
return v_res_3530_;
}
}
lean_object* l_Array_instAppend___redArg(){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = ((lean_object*)(l_Array_instAppend___redArg___closed__0));
return v___x_3533_;
}
}
LEAN_EXPORT void l_Array_instAppend___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3534_;
v_res_3534_ = l_Array_instAppend___redArg();
stack->m_obj
 = v_res_3534_;
}
LEAN_EXPORT lean_object* l_Array_instAppend___redArg___boxed(lean_object* v___dummy_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Array_instAppend___redArg();
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend(lean_object* v_00_u03b1_3537_){
_start:
{
lean_object* v___x_3538_; 
v___x_3538_ = ((lean_object*)(l_Array_instAppend___redArg___closed__0));
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object* v_x_3539_, lean_object* v_x_3540_){
_start:
{
if (lean_obj_tag(v_x_3540_) == 0)
{
return v_x_3539_;
}
else
{
lean_object* v_head_3541_; lean_object* v_tail_3542_; lean_object* v___x_3543_; 
v_head_3541_ = lean_ctor_get(v_x_3540_, 0);
lean_inc(v_head_3541_);
v_tail_3542_ = lean_ctor_get(v_x_3540_, 1);
lean_inc(v_tail_3542_);
lean_dec_ref_known(v_x_3540_, 2);
v___x_3543_ = lean_array_push(v_x_3539_, v_head_3541_);
v_x_3539_ = v___x_3543_;
v_x_3540_ = v_tail_3542_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_appendList___redArg(lean_object* v_as_3545_, lean_object* v_bs_3546_){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3545_, v_bs_3546_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Array_appendList(lean_object* v_00_u03b1_3548_, lean_object* v_as_3549_, lean_object* v_bs_3550_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3549_, v_bs_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0(lean_object* v_00_u03b1_3552_, lean_object* v_x_3553_, lean_object* v_x_3554_){
_start:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_3553_, v_x_3554_);
return v___x_3555_;
}
}
lean_object* l_Array_instHAppendList___redArg(){
_start:
{
lean_object* v___x_3558_; 
v___x_3558_ = ((lean_object*)(l_Array_instHAppendList___redArg___closed__0));
return v___x_3558_;
}
}
LEAN_EXPORT void l_Array_instHAppendList___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3559_;
v_res_3559_ = l_Array_instHAppendList___redArg();
stack->m_obj
 = v_res_3559_;
}
LEAN_EXPORT lean_object* l_Array_instHAppendList___redArg___boxed(lean_object* v___dummy_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Array_instHAppendList___redArg();
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList(lean_object* v_00_u03b1_3562_){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = ((lean_object*)(l_Array_instHAppendList___redArg___closed__0));
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0(lean_object* v_bs_3564_, lean_object* v_toPure_3565_, lean_object* v_____do__lift_3566_){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3567_ = l_Array_append___redArg(v_bs_3564_, v_____do__lift_3566_);
v___x_3568_ = lean_apply_2(v_toPure_3565_, lean_box(0), v___x_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0___boxed(lean_object* v_bs_3569_, lean_object* v_toPure_3570_, lean_object* v_____do__lift_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_Array_flatMapM___redArg___lam__0(v_bs_3569_, v_toPure_3570_, v_____do__lift_3571_);
lean_dec_ref(v_____do__lift_3571_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__1(lean_object* v_toPure_3573_, lean_object* v_f_3574_, lean_object* v_toBind_3575_, lean_object* v_bs_3576_, lean_object* v_a_3577_){
_start:
{
lean_object* v___f_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___f_3578_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3578_, 0, v_bs_3576_);
lean_closure_set(v___f_3578_, 1, v_toPure_3573_);
v___x_3579_ = lean_apply_1(v_f_3574_, v_a_3577_);
v___x_3580_ = lean_apply_4(v_toBind_3575_, lean_box(0), lean_box(0), v___x_3579_, v___f_3578_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg(lean_object* v_inst_3581_, lean_object* v_f_3582_, lean_object* v_as_3583_){
_start:
{
lean_object* v_toApplicative_3584_; lean_object* v_toBind_3585_; lean_object* v_toPure_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; uint8_t v___x_3590_; 
v_toApplicative_3584_ = lean_ctor_get(v_inst_3581_, 0);
v_toBind_3585_ = lean_ctor_get(v_inst_3581_, 1);
v_toPure_3586_ = lean_ctor_get(v_toApplicative_3584_, 1);
v___x_3587_ = lean_unsigned_to_nat(0u);
v___x_3588_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3589_ = lean_array_get_size(v_as_3583_);
v___x_3590_ = lean_nat_dec_lt(v___x_3587_, v___x_3589_);
if (v___x_3590_ == 0)
{
lean_object* v___x_3591_; 
lean_inc(v_toPure_3586_);
lean_dec_ref(v_as_3583_);
lean_dec(v_f_3582_);
lean_dec_ref(v_inst_3581_);
v___x_3591_ = lean_apply_2(v_toPure_3586_, lean_box(0), v___x_3588_);
return v___x_3591_;
}
else
{
lean_object* v___f_3592_; uint8_t v___x_3593_; 
lean_inc(v_toBind_3585_);
lean_inc(v_toPure_3586_);
v___f_3592_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3592_, 0, v_toPure_3586_);
lean_closure_set(v___f_3592_, 1, v_f_3582_);
lean_closure_set(v___f_3592_, 2, v_toBind_3585_);
v___x_3593_ = lean_nat_dec_le(v___x_3589_, v___x_3589_);
if (v___x_3593_ == 0)
{
if (v___x_3590_ == 0)
{
lean_object* v___x_3594_; 
lean_inc(v_toPure_3586_);
lean_dec_ref(v___f_3592_);
lean_dec_ref(v_as_3583_);
lean_dec_ref(v_inst_3581_);
v___x_3594_ = lean_apply_2(v_toPure_3586_, lean_box(0), v___x_3588_);
return v___x_3594_;
}
else
{
size_t v___x_3595_; size_t v___x_3596_; lean_object* v___x_3597_; 
v___x_3595_ = ((size_t)0ULL);
v___x_3596_ = lean_usize_of_nat(v___x_3589_);
v___x_3597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3581_, v___f_3592_, v_as_3583_, v___x_3595_, v___x_3596_, v___x_3588_);
return v___x_3597_;
}
}
else
{
size_t v___x_3598_; size_t v___x_3599_; lean_object* v___x_3600_; 
v___x_3598_ = ((size_t)0ULL);
v___x_3599_ = lean_usize_of_nat(v___x_3589_);
v___x_3600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3581_, v___f_3592_, v_as_3583_, v___x_3598_, v___x_3599_, v___x_3588_);
return v___x_3600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM(lean_object* v_00_u03b1_3601_, lean_object* v_m_3602_, lean_object* v_00_u03b2_3603_, lean_object* v_inst_3604_, lean_object* v_f_3605_, lean_object* v_as_3606_){
_start:
{
lean_object* v_toApplicative_3607_; lean_object* v_toBind_3608_; lean_object* v_toPure_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; 
v_toApplicative_3607_ = lean_ctor_get(v_inst_3604_, 0);
v_toBind_3608_ = lean_ctor_get(v_inst_3604_, 1);
v_toPure_3609_ = lean_ctor_get(v_toApplicative_3607_, 1);
v___x_3610_ = lean_unsigned_to_nat(0u);
v___x_3611_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3612_ = lean_array_get_size(v_as_3606_);
v___x_3613_ = lean_nat_dec_lt(v___x_3610_, v___x_3612_);
if (v___x_3613_ == 0)
{
lean_object* v___x_3614_; 
lean_inc(v_toPure_3609_);
lean_dec_ref(v_as_3606_);
lean_dec(v_f_3605_);
lean_dec_ref(v_inst_3604_);
v___x_3614_ = lean_apply_2(v_toPure_3609_, lean_box(0), v___x_3611_);
return v___x_3614_;
}
else
{
lean_object* v___f_3615_; uint8_t v___x_3616_; 
lean_inc(v_toBind_3608_);
lean_inc(v_toPure_3609_);
v___f_3615_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3615_, 0, v_toPure_3609_);
lean_closure_set(v___f_3615_, 1, v_f_3605_);
lean_closure_set(v___f_3615_, 2, v_toBind_3608_);
v___x_3616_ = lean_nat_dec_le(v___x_3612_, v___x_3612_);
if (v___x_3616_ == 0)
{
if (v___x_3613_ == 0)
{
lean_object* v___x_3617_; 
lean_inc(v_toPure_3609_);
lean_dec_ref(v___f_3615_);
lean_dec_ref(v_as_3606_);
lean_dec_ref(v_inst_3604_);
v___x_3617_ = lean_apply_2(v_toPure_3609_, lean_box(0), v___x_3611_);
return v___x_3617_;
}
else
{
size_t v___x_3618_; size_t v___x_3619_; lean_object* v___x_3620_; 
v___x_3618_ = ((size_t)0ULL);
v___x_3619_ = lean_usize_of_nat(v___x_3612_);
v___x_3620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3604_, v___f_3615_, v_as_3606_, v___x_3618_, v___x_3619_, v___x_3611_);
return v___x_3620_;
}
}
else
{
size_t v___x_3621_; size_t v___x_3622_; lean_object* v___x_3623_; 
v___x_3621_ = ((size_t)0ULL);
v___x_3622_ = lean_usize_of_nat(v___x_3612_);
v___x_3623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3604_, v___f_3615_, v_as_3606_, v___x_3621_, v___x_3622_, v___x_3611_);
return v___x_3623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg___lam__0(lean_object* v_f_3624_, lean_object* v_x1_3625_, lean_object* v_x2_3626_){
_start:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3627_ = lean_apply_1(v_f_3624_, v_x2_3626_);
v___x_3628_ = l_Array_append___redArg(v_x1_3625_, v___x_3627_);
lean_dec_ref(v___x_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg(lean_object* v_f_3629_, lean_object* v_as_3630_){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; uint8_t v___x_3635_; 
v___x_3631_ = lean_unsigned_to_nat(0u);
v___x_3632_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3633_ = lean_array_get_size(v_as_3630_);
v___x_3634_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3635_ = lean_nat_dec_lt(v___x_3631_, v___x_3633_);
if (v___x_3635_ == 0)
{
lean_dec_ref(v_as_3630_);
lean_dec_ref(v_f_3629_);
return v___x_3632_;
}
else
{
lean_object* v___f_3636_; uint8_t v___x_3637_; 
v___f_3636_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3636_, 0, v_f_3629_);
v___x_3637_ = lean_nat_dec_le(v___x_3633_, v___x_3633_);
if (v___x_3637_ == 0)
{
if (v___x_3635_ == 0)
{
lean_dec_ref(v___f_3636_);
lean_dec_ref(v_as_3630_);
return v___x_3632_;
}
else
{
size_t v___x_3638_; size_t v___x_3639_; lean_object* v___x_3640_; 
v___x_3638_ = ((size_t)0ULL);
v___x_3639_ = lean_usize_of_nat(v___x_3633_);
v___x_3640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3634_, v___f_3636_, v_as_3630_, v___x_3638_, v___x_3639_, v___x_3632_);
return v___x_3640_;
}
}
else
{
size_t v___x_3641_; size_t v___x_3642_; lean_object* v___x_3643_; 
v___x_3641_ = ((size_t)0ULL);
v___x_3642_ = lean_usize_of_nat(v___x_3633_);
v___x_3643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3634_, v___f_3636_, v_as_3630_, v___x_3641_, v___x_3642_, v___x_3632_);
return v___x_3643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap(lean_object* v_00_u03b1_3644_, lean_object* v_00_u03b2_3645_, lean_object* v_f_3646_, lean_object* v_as_3647_){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; uint8_t v___x_3652_; 
v___x_3648_ = lean_unsigned_to_nat(0u);
v___x_3649_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3650_ = lean_array_get_size(v_as_3647_);
v___x_3651_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3652_ = lean_nat_dec_lt(v___x_3648_, v___x_3650_);
if (v___x_3652_ == 0)
{
lean_dec_ref(v_as_3647_);
lean_dec_ref(v_f_3646_);
return v___x_3649_;
}
else
{
lean_object* v___f_3653_; uint8_t v___x_3654_; 
v___f_3653_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3653_, 0, v_f_3646_);
v___x_3654_ = lean_nat_dec_le(v___x_3650_, v___x_3650_);
if (v___x_3654_ == 0)
{
if (v___x_3652_ == 0)
{
lean_dec_ref(v___f_3653_);
lean_dec_ref(v_as_3647_);
return v___x_3649_;
}
else
{
size_t v___x_3655_; size_t v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = ((size_t)0ULL);
v___x_3656_ = lean_usize_of_nat(v___x_3650_);
v___x_3657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3651_, v___f_3653_, v_as_3647_, v___x_3655_, v___x_3656_, v___x_3649_);
return v___x_3657_;
}
}
else
{
size_t v___x_3658_; size_t v___x_3659_; lean_object* v___x_3660_; 
v___x_3658_ = ((size_t)0ULL);
v___x_3659_ = lean_usize_of_nat(v___x_3650_);
v___x_3660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3651_, v___f_3653_, v_as_3647_, v___x_3658_, v___x_3659_, v___x_3649_);
return v___x_3660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten___redArg(lean_object* v_xss_3662_){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; 
v___x_3663_ = lean_unsigned_to_nat(0u);
v___x_3664_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3665_ = lean_array_get_size(v_xss_3662_);
v___x_3666_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3667_ = lean_nat_dec_lt(v___x_3663_, v___x_3665_);
if (v___x_3667_ == 0)
{
lean_dec_ref(v_xss_3662_);
return v___x_3664_;
}
else
{
lean_object* v___f_3668_; uint8_t v___x_3669_; 
v___f_3668_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3669_ = lean_nat_dec_le(v___x_3665_, v___x_3665_);
if (v___x_3669_ == 0)
{
if (v___x_3667_ == 0)
{
lean_dec_ref(v_xss_3662_);
return v___x_3664_;
}
else
{
size_t v___x_3670_; size_t v___x_3671_; lean_object* v___x_3672_; 
v___x_3670_ = ((size_t)0ULL);
v___x_3671_ = lean_usize_of_nat(v___x_3665_);
v___x_3672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3666_, v___f_3668_, v_xss_3662_, v___x_3670_, v___x_3671_, v___x_3664_);
return v___x_3672_;
}
}
else
{
size_t v___x_3673_; size_t v___x_3674_; lean_object* v___x_3675_; 
v___x_3673_ = ((size_t)0ULL);
v___x_3674_ = lean_usize_of_nat(v___x_3665_);
v___x_3675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3666_, v___f_3668_, v_xss_3662_, v___x_3673_, v___x_3674_, v___x_3664_);
return v___x_3675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten(lean_object* v_00_u03b1_3676_, lean_object* v_xss_3677_){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
v___x_3678_ = lean_unsigned_to_nat(0u);
v___x_3679_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3680_ = lean_array_get_size(v_xss_3677_);
v___x_3681_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3682_ = lean_nat_dec_lt(v___x_3678_, v___x_3680_);
if (v___x_3682_ == 0)
{
lean_dec_ref(v_xss_3677_);
return v___x_3679_;
}
else
{
lean_object* v___f_3683_; uint8_t v___x_3684_; 
v___f_3683_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3684_ = lean_nat_dec_le(v___x_3680_, v___x_3680_);
if (v___x_3684_ == 0)
{
if (v___x_3682_ == 0)
{
lean_dec_ref(v_xss_3677_);
return v___x_3679_;
}
else
{
size_t v___x_3685_; size_t v___x_3686_; lean_object* v___x_3687_; 
v___x_3685_ = ((size_t)0ULL);
v___x_3686_ = lean_usize_of_nat(v___x_3680_);
v___x_3687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3681_, v___f_3683_, v_xss_3677_, v___x_3685_, v___x_3686_, v___x_3679_);
return v___x_3687_;
}
}
else
{
size_t v___x_3688_; size_t v___x_3689_; lean_object* v___x_3690_; 
v___x_3688_ = ((size_t)0ULL);
v___x_3689_ = lean_usize_of_nat(v___x_3680_);
v___x_3690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3681_, v___f_3683_, v_xss_3677_, v___x_3688_, v___x_3689_, v___x_3679_);
return v___x_3690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop___redArg(lean_object* v_as_3691_, lean_object* v_i_3692_, lean_object* v_j_3693_){
_start:
{
uint8_t v___x_3694_; 
v___x_3694_ = lean_nat_dec_lt(v_i_3692_, v_j_3693_);
if (v___x_3694_ == 0)
{
lean_dec(v_j_3693_);
lean_dec(v_i_3692_);
return v_as_3691_;
}
else
{
lean_object* v_as_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v_as_3695_ = lean_array_fswap(v_as_3691_, v_i_3692_, v_j_3693_);
v___x_3696_ = lean_unsigned_to_nat(1u);
v___x_3697_ = lean_nat_add(v_i_3692_, v___x_3696_);
lean_dec(v_i_3692_);
v___x_3698_ = lean_nat_sub(v_j_3693_, v___x_3696_);
lean_dec(v_j_3693_);
v_as_3691_ = v_as_3695_;
v_i_3692_ = v___x_3697_;
v_j_3693_ = v___x_3698_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop(lean_object* v_00_u03b1_3700_, lean_object* v_as_3701_, lean_object* v_i_3702_, lean_object* v_j_3703_){
_start:
{
lean_object* v___x_3704_; 
v___x_3704_ = l_Array_reverse_loop___redArg(v_as_3701_, v_i_3702_, v_j_3703_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l_Array_reverse___redArg(lean_object* v_as_3705_){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; uint8_t v___x_3708_; 
v___x_3706_ = lean_array_get_size(v_as_3705_);
v___x_3707_ = lean_unsigned_to_nat(1u);
v___x_3708_ = lean_nat_dec_le(v___x_3706_, v___x_3707_);
if (v___x_3708_ == 0)
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3709_ = lean_unsigned_to_nat(0u);
v___x_3710_ = lean_nat_sub(v___x_3706_, v___x_3707_);
v___x_3711_ = l_Array_reverse_loop___redArg(v_as_3705_, v___x_3709_, v___x_3710_);
return v___x_3711_;
}
else
{
return v_as_3705_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse(lean_object* v_00_u03b1_3712_, lean_object* v_as_3713_){
_start:
{
lean_object* v___x_3714_; 
v___x_3714_ = l_Array_reverse___redArg(v_as_3713_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___lam__0(lean_object* v_p_3715_, lean_object* v_x1_3716_, lean_object* v_x2_3717_){
_start:
{
lean_object* v___x_3718_; uint8_t v___x_3719_; 
lean_inc(v_x2_3717_);
v___x_3718_ = lean_apply_1(v_p_3715_, v_x2_3717_);
v___x_3719_ = lean_unbox(v___x_3718_);
if (v___x_3719_ == 0)
{
lean_dec(v_x2_3717_);
return v_x1_3716_;
}
else
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_array_push(v_x1_3716_, v_x2_3717_);
return v___x_3720_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg(lean_object* v_p_3723_, lean_object* v_as_3724_, lean_object* v_start_3725_, lean_object* v_stop_3726_){
_start:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; 
v___x_3727_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3728_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3729_ = lean_nat_dec_lt(v_start_3725_, v_stop_3726_);
if (v___x_3729_ == 0)
{
lean_dec_ref(v_as_3724_);
lean_dec_ref(v_p_3723_);
return v___x_3727_;
}
else
{
lean_object* v___f_3730_; lean_object* v___x_3731_; uint8_t v___x_3732_; 
v___f_3730_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3730_, 0, v_p_3723_);
v___x_3731_ = lean_array_get_size(v_as_3724_);
v___x_3732_ = lean_nat_dec_le(v_stop_3726_, v___x_3731_);
if (v___x_3732_ == 0)
{
uint8_t v___x_3733_; 
v___x_3733_ = lean_nat_dec_lt(v_start_3725_, v___x_3731_);
if (v___x_3733_ == 0)
{
lean_dec_ref(v___f_3730_);
lean_dec_ref(v_as_3724_);
return v___x_3727_;
}
else
{
size_t v___x_3734_; size_t v___x_3735_; lean_object* v___x_3736_; 
v___x_3734_ = lean_usize_of_nat(v_start_3725_);
v___x_3735_ = lean_usize_of_nat(v___x_3731_);
v___x_3736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3728_, v___f_3730_, v_as_3724_, v___x_3734_, v___x_3735_, v___x_3727_);
return v___x_3736_;
}
}
else
{
size_t v___x_3737_; size_t v___x_3738_; lean_object* v___x_3739_; 
v___x_3737_ = lean_usize_of_nat(v_start_3725_);
v___x_3738_ = lean_usize_of_nat(v_stop_3726_);
v___x_3739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3728_, v___f_3730_, v_as_3724_, v___x_3737_, v___x_3738_, v___x_3727_);
return v___x_3739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___boxed(lean_object* v_p_3740_, lean_object* v_as_3741_, lean_object* v_start_3742_, lean_object* v_stop_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l_Array_filter___redArg(v_p_3740_, v_as_3741_, v_start_3742_, v_stop_3743_);
lean_dec(v_stop_3743_);
lean_dec(v_start_3742_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l_Array_filter(lean_object* v_00_u03b1_3745_, lean_object* v_p_3746_, lean_object* v_as_3747_, lean_object* v_start_3748_, lean_object* v_stop_3749_){
_start:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; uint8_t v___x_3752_; 
v___x_3750_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3751_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3752_ = lean_nat_dec_lt(v_start_3748_, v_stop_3749_);
if (v___x_3752_ == 0)
{
lean_dec_ref(v_as_3747_);
lean_dec_ref(v_p_3746_);
return v___x_3750_;
}
else
{
lean_object* v___f_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___f_3753_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3753_, 0, v_p_3746_);
v___x_3754_ = lean_array_get_size(v_as_3747_);
v___x_3755_ = lean_nat_dec_le(v_stop_3749_, v___x_3754_);
if (v___x_3755_ == 0)
{
uint8_t v___x_3756_; 
v___x_3756_ = lean_nat_dec_lt(v_start_3748_, v___x_3754_);
if (v___x_3756_ == 0)
{
lean_dec_ref(v___f_3753_);
lean_dec_ref(v_as_3747_);
return v___x_3750_;
}
else
{
size_t v___x_3757_; size_t v___x_3758_; lean_object* v___x_3759_; 
v___x_3757_ = lean_usize_of_nat(v_start_3748_);
v___x_3758_ = lean_usize_of_nat(v___x_3754_);
v___x_3759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3751_, v___f_3753_, v_as_3747_, v___x_3757_, v___x_3758_, v___x_3750_);
return v___x_3759_;
}
}
else
{
size_t v___x_3760_; size_t v___x_3761_; lean_object* v___x_3762_; 
v___x_3760_ = lean_usize_of_nat(v_start_3748_);
v___x_3761_ = lean_usize_of_nat(v_stop_3749_);
v___x_3762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3751_, v___f_3753_, v_as_3747_, v___x_3760_, v___x_3761_, v___x_3750_);
return v___x_3762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___boxed(lean_object* v_00_u03b1_3763_, lean_object* v_p_3764_, lean_object* v_as_3765_, lean_object* v_start_3766_, lean_object* v_stop_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Array_filter(v_00_u03b1_3763_, v_p_3764_, v_as_3765_, v_start_3766_, v_stop_3767_);
lean_dec(v_stop_3767_);
lean_dec(v_start_3766_);
return v_res_3768_;
}
}
lean_object* l_Array_filterM___redArg___lam__0(lean_object* v_toPure_3769_, lean_object* v_acc_3770_, lean_object* v_a_3771_, uint8_t v_____do__lift_3772_){
_start:
{
if (v_____do__lift_3772_ == 0)
{
lean_object* v___x_3773_; 
lean_dec(v_a_3771_);
v___x_3773_ = lean_apply_2(v_toPure_3769_, lean_box(0), v_acc_3770_);
return v___x_3773_;
}
else
{
lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3774_ = lean_array_push(v_acc_3770_, v_a_3771_);
v___x_3775_ = lean_apply_2(v_toPure_3769_, lean_box(0), v___x_3774_);
return v___x_3775_;
}
}
}
LEAN_EXPORT void l_Array_filterM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_3769_ = stack[0].m_obj;
lean_object* v_acc_3770_ = stack[1].m_obj;
lean_object* v_a_3771_ = stack[2].m_obj;
uint8_t v_____do__lift_3772_ = stack[3].m_num;
lean_object* v_res_3776_;
v_res_3776_ = l_Array_filterM___redArg___lam__0(v_toPure_3769_, v_acc_3770_, v_a_3771_, v_____do__lift_3772_);
stack->m_obj
 = v_res_3776_;
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0___boxed(lean_object* v_toPure_3777_, lean_object* v_acc_3778_, lean_object* v_a_3779_, lean_object* v_____do__lift_3780_){
_start:
{
uint8_t v_____do__lift_91__boxed_3781_; lean_object* v_res_3782_; 
v_____do__lift_91__boxed_3781_ = lean_unbox(v_____do__lift_3780_);
v_res_3782_ = l_Array_filterM___redArg___lam__0(v_toPure_3777_, v_acc_3778_, v_a_3779_, v_____do__lift_91__boxed_3781_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__1(lean_object* v_toPure_3783_, lean_object* v_p_3784_, lean_object* v_toBind_3785_, lean_object* v_acc_3786_, lean_object* v_a_3787_){
_start:
{
lean_object* v___f_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
lean_inc(v_a_3787_);
v___f_3788_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3788_, 0, v_toPure_3783_);
lean_closure_set(v___f_3788_, 1, v_acc_3786_);
lean_closure_set(v___f_3788_, 2, v_a_3787_);
v___x_3789_ = lean_apply_1(v_p_3784_, v_a_3787_);
v___x_3790_ = lean_apply_4(v_toBind_3785_, lean_box(0), lean_box(0), v___x_3789_, v___f_3788_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg(lean_object* v_inst_3791_, lean_object* v_p_3792_, lean_object* v_as_3793_, lean_object* v_start_3794_, lean_object* v_stop_3795_){
_start:
{
lean_object* v_toApplicative_3796_; lean_object* v_toBind_3797_; lean_object* v_toPure_3798_; lean_object* v___x_3799_; uint8_t v___x_3800_; 
v_toApplicative_3796_ = lean_ctor_get(v_inst_3791_, 0);
v_toBind_3797_ = lean_ctor_get(v_inst_3791_, 1);
v_toPure_3798_ = lean_ctor_get(v_toApplicative_3796_, 1);
v___x_3799_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3800_ = lean_nat_dec_lt(v_start_3794_, v_stop_3795_);
if (v___x_3800_ == 0)
{
lean_object* v___x_3801_; 
lean_inc(v_toPure_3798_);
lean_dec_ref(v_as_3793_);
lean_dec(v_p_3792_);
lean_dec_ref(v_inst_3791_);
v___x_3801_ = lean_apply_2(v_toPure_3798_, lean_box(0), v___x_3799_);
return v___x_3801_;
}
else
{
lean_object* v___f_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
lean_inc(v_toBind_3797_);
lean_inc(v_toPure_3798_);
v___f_3802_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3802_, 0, v_toPure_3798_);
lean_closure_set(v___f_3802_, 1, v_p_3792_);
lean_closure_set(v___f_3802_, 2, v_toBind_3797_);
v___x_3803_ = lean_array_get_size(v_as_3793_);
v___x_3804_ = lean_nat_dec_le(v_stop_3795_, v___x_3803_);
if (v___x_3804_ == 0)
{
uint8_t v___x_3805_; 
v___x_3805_ = lean_nat_dec_lt(v_start_3794_, v___x_3803_);
if (v___x_3805_ == 0)
{
lean_object* v___x_3806_; 
lean_inc(v_toPure_3798_);
lean_dec_ref(v___f_3802_);
lean_dec_ref(v_as_3793_);
lean_dec_ref(v_inst_3791_);
v___x_3806_ = lean_apply_2(v_toPure_3798_, lean_box(0), v___x_3799_);
return v___x_3806_;
}
else
{
size_t v___x_3807_; size_t v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = lean_usize_of_nat(v_start_3794_);
v___x_3808_ = lean_usize_of_nat(v___x_3803_);
v___x_3809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3791_, v___f_3802_, v_as_3793_, v___x_3807_, v___x_3808_, v___x_3799_);
return v___x_3809_;
}
}
else
{
size_t v___x_3810_; size_t v___x_3811_; lean_object* v___x_3812_; 
v___x_3810_ = lean_usize_of_nat(v_start_3794_);
v___x_3811_ = lean_usize_of_nat(v_stop_3795_);
v___x_3812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3791_, v___f_3802_, v_as_3793_, v___x_3810_, v___x_3811_, v___x_3799_);
return v___x_3812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___boxed(lean_object* v_inst_3813_, lean_object* v_p_3814_, lean_object* v_as_3815_, lean_object* v_start_3816_, lean_object* v_stop_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Array_filterM___redArg(v_inst_3813_, v_p_3814_, v_as_3815_, v_start_3816_, v_stop_3817_);
lean_dec(v_stop_3817_);
lean_dec(v_start_3816_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM(lean_object* v_m_3819_, lean_object* v_00_u03b1_3820_, lean_object* v_inst_3821_, lean_object* v_p_3822_, lean_object* v_as_3823_, lean_object* v_start_3824_, lean_object* v_stop_3825_){
_start:
{
lean_object* v_toApplicative_3826_; lean_object* v_toBind_3827_; lean_object* v_toPure_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; 
v_toApplicative_3826_ = lean_ctor_get(v_inst_3821_, 0);
v_toBind_3827_ = lean_ctor_get(v_inst_3821_, 1);
v_toPure_3828_ = lean_ctor_get(v_toApplicative_3826_, 1);
v___x_3829_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3830_ = lean_nat_dec_lt(v_start_3824_, v_stop_3825_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; 
lean_inc(v_toPure_3828_);
lean_dec_ref(v_as_3823_);
lean_dec(v_p_3822_);
lean_dec_ref(v_inst_3821_);
v___x_3831_ = lean_apply_2(v_toPure_3828_, lean_box(0), v___x_3829_);
return v___x_3831_;
}
else
{
lean_object* v___f_3832_; lean_object* v___x_3833_; uint8_t v___x_3834_; 
lean_inc(v_toBind_3827_);
lean_inc(v_toPure_3828_);
v___f_3832_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3832_, 0, v_toPure_3828_);
lean_closure_set(v___f_3832_, 1, v_p_3822_);
lean_closure_set(v___f_3832_, 2, v_toBind_3827_);
v___x_3833_ = lean_array_get_size(v_as_3823_);
v___x_3834_ = lean_nat_dec_le(v_stop_3825_, v___x_3833_);
if (v___x_3834_ == 0)
{
uint8_t v___x_3835_; 
v___x_3835_ = lean_nat_dec_lt(v_start_3824_, v___x_3833_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; 
lean_inc(v_toPure_3828_);
lean_dec_ref(v___f_3832_);
lean_dec_ref(v_as_3823_);
lean_dec_ref(v_inst_3821_);
v___x_3836_ = lean_apply_2(v_toPure_3828_, lean_box(0), v___x_3829_);
return v___x_3836_;
}
else
{
size_t v___x_3837_; size_t v___x_3838_; lean_object* v___x_3839_; 
v___x_3837_ = lean_usize_of_nat(v_start_3824_);
v___x_3838_ = lean_usize_of_nat(v___x_3833_);
v___x_3839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3821_, v___f_3832_, v_as_3823_, v___x_3837_, v___x_3838_, v___x_3829_);
return v___x_3839_;
}
}
else
{
size_t v___x_3840_; size_t v___x_3841_; lean_object* v___x_3842_; 
v___x_3840_ = lean_usize_of_nat(v_start_3824_);
v___x_3841_ = lean_usize_of_nat(v_stop_3825_);
v___x_3842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3821_, v___f_3832_, v_as_3823_, v___x_3840_, v___x_3841_, v___x_3829_);
return v___x_3842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___boxed(lean_object* v_m_3843_, lean_object* v_00_u03b1_3844_, lean_object* v_inst_3845_, lean_object* v_p_3846_, lean_object* v_as_3847_, lean_object* v_start_3848_, lean_object* v_stop_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Array_filterM(v_m_3843_, v_00_u03b1_3844_, v_inst_3845_, v_p_3846_, v_as_3847_, v_start_3848_, v_stop_3849_);
lean_dec(v_stop_3849_);
lean_dec(v_start_3848_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__1(lean_object* v_toPure_3851_, lean_object* v_p_3852_, lean_object* v_toBind_3853_, lean_object* v_a_3854_, lean_object* v_acc_3855_){
_start:
{
lean_object* v___f_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
lean_inc(v_a_3854_);
v___f_3856_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3856_, 0, v_toPure_3851_);
lean_closure_set(v___f_3856_, 1, v_acc_3855_);
lean_closure_set(v___f_3856_, 2, v_a_3854_);
v___x_3857_ = lean_apply_1(v_p_3852_, v_a_3854_);
v___x_3858_ = lean_apply_4(v_toBind_3853_, lean_box(0), lean_box(0), v___x_3857_, v___f_3856_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg(lean_object* v_inst_3860_, lean_object* v_p_3861_, lean_object* v_as_3862_, lean_object* v_start_3863_, lean_object* v_stop_3864_){
_start:
{
lean_object* v_toApplicative_3865_; lean_object* v_toFunctor_3866_; lean_object* v_toBind_3867_; lean_object* v_toPure_3868_; lean_object* v_map_3869_; lean_object* v___f_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; uint8_t v___x_3874_; 
v_toApplicative_3865_ = lean_ctor_get(v_inst_3860_, 0);
v_toFunctor_3866_ = lean_ctor_get(v_toApplicative_3865_, 0);
v_toBind_3867_ = lean_ctor_get(v_inst_3860_, 1);
v_toPure_3868_ = lean_ctor_get(v_toApplicative_3865_, 1);
v_map_3869_ = lean_ctor_get(v_toFunctor_3866_, 0);
lean_inc(v_map_3869_);
lean_inc(v_toBind_3867_);
lean_inc(v_toPure_3868_);
v___f_3870_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3870_, 0, v_toPure_3868_);
lean_closure_set(v___f_3870_, 1, v_p_3861_);
lean_closure_set(v___f_3870_, 2, v_toBind_3867_);
v___x_3871_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3872_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3873_ = lean_array_get_size(v_as_3862_);
v___x_3874_ = lean_nat_dec_le(v_start_3863_, v___x_3873_);
if (v___x_3874_ == 0)
{
uint8_t v___x_3875_; 
v___x_3875_ = lean_nat_dec_lt(v_stop_3864_, v___x_3873_);
if (v___x_3875_ == 0)
{
lean_object* v___x_3876_; lean_object* v___x_3877_; 
lean_inc(v_toPure_3868_);
lean_dec_ref(v___f_3870_);
lean_dec_ref(v_as_3862_);
lean_dec_ref(v_inst_3860_);
v___x_3876_ = lean_apply_2(v_toPure_3868_, lean_box(0), v___x_3872_);
v___x_3877_ = lean_apply_4(v_map_3869_, lean_box(0), lean_box(0), v___x_3871_, v___x_3876_);
return v___x_3877_;
}
else
{
size_t v___x_3878_; size_t v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3878_ = lean_usize_of_nat(v___x_3873_);
v___x_3879_ = lean_usize_of_nat(v_stop_3864_);
v___x_3880_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3860_, v___f_3870_, v_as_3862_, v___x_3878_, v___x_3879_, v___x_3872_);
v___x_3881_ = lean_apply_4(v_map_3869_, lean_box(0), lean_box(0), v___x_3871_, v___x_3880_);
return v___x_3881_;
}
}
else
{
uint8_t v___x_3882_; 
v___x_3882_ = lean_nat_dec_lt(v_stop_3864_, v_start_3863_);
if (v___x_3882_ == 0)
{
lean_object* v___x_3883_; lean_object* v___x_3884_; 
lean_inc(v_toPure_3868_);
lean_dec_ref(v___f_3870_);
lean_dec_ref(v_as_3862_);
lean_dec_ref(v_inst_3860_);
v___x_3883_ = lean_apply_2(v_toPure_3868_, lean_box(0), v___x_3872_);
v___x_3884_ = lean_apply_4(v_map_3869_, lean_box(0), lean_box(0), v___x_3871_, v___x_3883_);
return v___x_3884_;
}
else
{
size_t v___x_3885_; size_t v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3885_ = lean_usize_of_nat(v_start_3863_);
v___x_3886_ = lean_usize_of_nat(v_stop_3864_);
v___x_3887_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3860_, v___f_3870_, v_as_3862_, v___x_3885_, v___x_3886_, v___x_3872_);
v___x_3888_ = lean_apply_4(v_map_3869_, lean_box(0), lean_box(0), v___x_3871_, v___x_3887_);
return v___x_3888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___boxed(lean_object* v_inst_3889_, lean_object* v_p_3890_, lean_object* v_as_3891_, lean_object* v_start_3892_, lean_object* v_stop_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Array_filterRevM___redArg(v_inst_3889_, v_p_3890_, v_as_3891_, v_start_3892_, v_stop_3893_);
lean_dec(v_stop_3893_);
lean_dec(v_start_3892_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM(lean_object* v_m_3895_, lean_object* v_00_u03b1_3896_, lean_object* v_inst_3897_, lean_object* v_p_3898_, lean_object* v_as_3899_, lean_object* v_start_3900_, lean_object* v_stop_3901_){
_start:
{
lean_object* v_toApplicative_3902_; lean_object* v_toFunctor_3903_; lean_object* v_toBind_3904_; lean_object* v_toPure_3905_; lean_object* v_map_3906_; lean_object* v___f_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; uint8_t v___x_3911_; 
v_toApplicative_3902_ = lean_ctor_get(v_inst_3897_, 0);
v_toFunctor_3903_ = lean_ctor_get(v_toApplicative_3902_, 0);
v_toBind_3904_ = lean_ctor_get(v_inst_3897_, 1);
v_toPure_3905_ = lean_ctor_get(v_toApplicative_3902_, 1);
v_map_3906_ = lean_ctor_get(v_toFunctor_3903_, 0);
lean_inc(v_map_3906_);
lean_inc(v_toBind_3904_);
lean_inc(v_toPure_3905_);
v___f_3907_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3907_, 0, v_toPure_3905_);
lean_closure_set(v___f_3907_, 1, v_p_3898_);
lean_closure_set(v___f_3907_, 2, v_toBind_3904_);
v___x_3908_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3909_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3910_ = lean_array_get_size(v_as_3899_);
v___x_3911_ = lean_nat_dec_le(v_start_3900_, v___x_3910_);
if (v___x_3911_ == 0)
{
uint8_t v___x_3912_; 
v___x_3912_ = lean_nat_dec_lt(v_stop_3901_, v___x_3910_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
lean_inc(v_toPure_3905_);
lean_dec_ref(v___f_3907_);
lean_dec_ref(v_as_3899_);
lean_dec_ref(v_inst_3897_);
v___x_3913_ = lean_apply_2(v_toPure_3905_, lean_box(0), v___x_3909_);
v___x_3914_ = lean_apply_4(v_map_3906_, lean_box(0), lean_box(0), v___x_3908_, v___x_3913_);
return v___x_3914_;
}
else
{
size_t v___x_3915_; size_t v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3915_ = lean_usize_of_nat(v___x_3910_);
v___x_3916_ = lean_usize_of_nat(v_stop_3901_);
v___x_3917_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3897_, v___f_3907_, v_as_3899_, v___x_3915_, v___x_3916_, v___x_3909_);
v___x_3918_ = lean_apply_4(v_map_3906_, lean_box(0), lean_box(0), v___x_3908_, v___x_3917_);
return v___x_3918_;
}
}
else
{
uint8_t v___x_3919_; 
v___x_3919_ = lean_nat_dec_lt(v_stop_3901_, v_start_3900_);
if (v___x_3919_ == 0)
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
lean_inc(v_toPure_3905_);
lean_dec_ref(v___f_3907_);
lean_dec_ref(v_as_3899_);
lean_dec_ref(v_inst_3897_);
v___x_3920_ = lean_apply_2(v_toPure_3905_, lean_box(0), v___x_3909_);
v___x_3921_ = lean_apply_4(v_map_3906_, lean_box(0), lean_box(0), v___x_3908_, v___x_3920_);
return v___x_3921_;
}
else
{
size_t v___x_3922_; size_t v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3922_ = lean_usize_of_nat(v_start_3900_);
v___x_3923_ = lean_usize_of_nat(v_stop_3901_);
v___x_3924_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3897_, v___f_3907_, v_as_3899_, v___x_3922_, v___x_3923_, v___x_3909_);
v___x_3925_ = lean_apply_4(v_map_3906_, lean_box(0), lean_box(0), v___x_3908_, v___x_3924_);
return v___x_3925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___boxed(lean_object* v_m_3926_, lean_object* v_00_u03b1_3927_, lean_object* v_inst_3928_, lean_object* v_p_3929_, lean_object* v_as_3930_, lean_object* v_start_3931_, lean_object* v_stop_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l_Array_filterRevM(v_m_3926_, v_00_u03b1_3927_, v_inst_3928_, v_p_3929_, v_as_3930_, v_start_3931_, v_stop_3932_);
lean_dec(v_stop_3932_);
lean_dec(v_start_3931_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__0(lean_object* v_toPure_3934_, lean_object* v_bs_3935_, lean_object* v_____do__lift_3936_){
_start:
{
if (lean_obj_tag(v_____do__lift_3936_) == 0)
{
lean_object* v___x_3937_; 
v___x_3937_ = lean_apply_2(v_toPure_3934_, lean_box(0), v_bs_3935_);
return v___x_3937_;
}
else
{
lean_object* v_val_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v_val_3938_ = lean_ctor_get(v_____do__lift_3936_, 0);
lean_inc(v_val_3938_);
lean_dec_ref_known(v_____do__lift_3936_, 1);
v___x_3939_ = lean_array_push(v_bs_3935_, v_val_3938_);
v___x_3940_ = lean_apply_2(v_toPure_3934_, lean_box(0), v___x_3939_);
return v___x_3940_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__1(lean_object* v_toPure_3941_, lean_object* v_f_3942_, lean_object* v_toBind_3943_, lean_object* v_bs_3944_, lean_object* v_a_3945_){
_start:
{
lean_object* v___f_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___f_3946_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3946_, 0, v_toPure_3941_);
lean_closure_set(v___f_3946_, 1, v_bs_3944_);
v___x_3947_ = lean_apply_1(v_f_3942_, v_a_3945_);
v___x_3948_ = lean_apply_4(v_toBind_3943_, lean_box(0), lean_box(0), v___x_3947_, v___f_3946_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg(lean_object* v_inst_3949_, lean_object* v_f_3950_, lean_object* v_as_3951_, lean_object* v_start_3952_, lean_object* v_stop_3953_){
_start:
{
lean_object* v_toApplicative_3954_; lean_object* v_toBind_3955_; lean_object* v_toPure_3956_; lean_object* v___x_3957_; uint8_t v___x_3958_; 
v_toApplicative_3954_ = lean_ctor_get(v_inst_3949_, 0);
v_toBind_3955_ = lean_ctor_get(v_inst_3949_, 1);
v_toPure_3956_ = lean_ctor_get(v_toApplicative_3954_, 1);
v___x_3957_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3958_ = lean_nat_dec_lt(v_start_3952_, v_stop_3953_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3959_; 
lean_inc(v_toPure_3956_);
lean_dec_ref(v_as_3951_);
lean_dec(v_f_3950_);
lean_dec_ref(v_inst_3949_);
v___x_3959_ = lean_apply_2(v_toPure_3956_, lean_box(0), v___x_3957_);
return v___x_3959_;
}
else
{
lean_object* v___f_3960_; lean_object* v___x_3961_; uint8_t v___x_3962_; 
lean_inc(v_toBind_3955_);
lean_inc(v_toPure_3956_);
v___f_3960_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3960_, 0, v_toPure_3956_);
lean_closure_set(v___f_3960_, 1, v_f_3950_);
lean_closure_set(v___f_3960_, 2, v_toBind_3955_);
v___x_3961_ = lean_array_get_size(v_as_3951_);
v___x_3962_ = lean_nat_dec_le(v_stop_3953_, v___x_3961_);
if (v___x_3962_ == 0)
{
uint8_t v___x_3963_; 
v___x_3963_ = lean_nat_dec_lt(v_start_3952_, v___x_3961_);
if (v___x_3963_ == 0)
{
lean_object* v___x_3964_; 
lean_inc(v_toPure_3956_);
lean_dec_ref(v___f_3960_);
lean_dec_ref(v_as_3951_);
lean_dec_ref(v_inst_3949_);
v___x_3964_ = lean_apply_2(v_toPure_3956_, lean_box(0), v___x_3957_);
return v___x_3964_;
}
else
{
size_t v___x_3965_; size_t v___x_3966_; lean_object* v___x_3967_; 
v___x_3965_ = lean_usize_of_nat(v_start_3952_);
v___x_3966_ = lean_usize_of_nat(v___x_3961_);
v___x_3967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3949_, v___f_3960_, v_as_3951_, v___x_3965_, v___x_3966_, v___x_3957_);
return v___x_3967_;
}
}
else
{
size_t v___x_3968_; size_t v___x_3969_; lean_object* v___x_3970_; 
v___x_3968_ = lean_usize_of_nat(v_start_3952_);
v___x_3969_ = lean_usize_of_nat(v_stop_3953_);
v___x_3970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3949_, v___f_3960_, v_as_3951_, v___x_3968_, v___x_3969_, v___x_3957_);
return v___x_3970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___boxed(lean_object* v_inst_3971_, lean_object* v_f_3972_, lean_object* v_as_3973_, lean_object* v_start_3974_, lean_object* v_stop_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Array_filterMapM___redArg(v_inst_3971_, v_f_3972_, v_as_3973_, v_start_3974_, v_stop_3975_);
lean_dec(v_stop_3975_);
lean_dec(v_start_3974_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM(lean_object* v_00_u03b1_3977_, lean_object* v_m_3978_, lean_object* v_00_u03b2_3979_, lean_object* v_inst_3980_, lean_object* v_f_3981_, lean_object* v_as_3982_, lean_object* v_start_3983_, lean_object* v_stop_3984_){
_start:
{
lean_object* v___x_3985_; 
v___x_3985_ = l_Array_filterMapM___redArg(v_inst_3980_, v_f_3981_, v_as_3982_, v_start_3983_, v_stop_3984_);
return v___x_3985_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___boxed(lean_object* v_00_u03b1_3986_, lean_object* v_m_3987_, lean_object* v_00_u03b2_3988_, lean_object* v_inst_3989_, lean_object* v_f_3990_, lean_object* v_as_3991_, lean_object* v_start_3992_, lean_object* v_stop_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Array_filterMapM(v_00_u03b1_3986_, v_m_3987_, v_00_u03b2_3988_, v_inst_3989_, v_f_3990_, v_as_3991_, v_start_3992_, v_stop_3993_);
lean_dec(v_stop_3993_);
lean_dec(v_start_3992_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg(lean_object* v_f_3995_, lean_object* v_as_3996_, lean_object* v_start_3997_, lean_object* v_stop_3998_){
_start:
{
lean_object* v___f_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___f_3999_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3999_, 0, v_f_3995_);
v___x_4000_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4001_ = l_Array_filterMapM___redArg(v___x_4000_, v___f_3999_, v_as_3996_, v_start_3997_, v_stop_3998_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg___boxed(lean_object* v_f_4002_, lean_object* v_as_4003_, lean_object* v_start_4004_, lean_object* v_stop_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Array_filterMap___redArg(v_f_4002_, v_as_4003_, v_start_4004_, v_stop_4005_);
lean_dec(v_stop_4005_);
lean_dec(v_start_4004_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap(lean_object* v_00_u03b1_4007_, lean_object* v_00_u03b2_4008_, lean_object* v_f_4009_, lean_object* v_as_4010_, lean_object* v_start_4011_, lean_object* v_stop_4012_){
_start:
{
lean_object* v___f_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___f_4013_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4013_, 0, v_f_4009_);
v___x_4014_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4015_ = l_Array_filterMapM___redArg(v___x_4014_, v___f_4013_, v_as_4010_, v_start_4011_, v_stop_4012_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___boxed(lean_object* v_00_u03b1_4016_, lean_object* v_00_u03b2_4017_, lean_object* v_f_4018_, lean_object* v_as_4019_, lean_object* v_start_4020_, lean_object* v_stop_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Array_filterMap(v_00_u03b1_4016_, v_00_u03b2_4017_, v_f_4018_, v_as_4019_, v_start_4020_, v_stop_4021_);
lean_dec(v_stop_4021_);
lean_dec(v_start_4020_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg___lam__0(lean_object* v_lt_4023_, lean_object* v_x1_4024_, lean_object* v_x2_4025_){
_start:
{
lean_object* v___x_4026_; uint8_t v___x_4027_; 
lean_inc(v_x2_4025_);
lean_inc(v_x1_4024_);
v___x_4026_ = lean_apply_2(v_lt_4023_, v_x1_4024_, v_x2_4025_);
v___x_4027_ = lean_unbox(v___x_4026_);
if (v___x_4027_ == 0)
{
lean_dec(v_x2_4025_);
return v_x1_4024_;
}
else
{
lean_dec(v_x1_4024_);
return v_x2_4025_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg(lean_object* v_as_4028_, lean_object* v_lt_4029_){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; uint8_t v___x_4032_; 
v___x_4030_ = lean_unsigned_to_nat(0u);
v___x_4031_ = lean_array_get_size(v_as_4028_);
v___x_4032_ = lean_nat_dec_lt(v___x_4030_, v___x_4031_);
if (v___x_4032_ == 0)
{
lean_object* v___x_4033_; 
lean_dec_ref(v_lt_4029_);
lean_dec_ref(v_as_4028_);
v___x_4033_ = lean_box(0);
return v___x_4033_;
}
else
{
lean_object* v_a0_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; uint8_t v___x_4037_; 
v_a0_4034_ = lean_array_fget(v_as_4028_, v___x_4030_);
v___x_4035_ = lean_unsigned_to_nat(1u);
v___x_4036_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4037_ = lean_nat_dec_lt(v___x_4035_, v___x_4031_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4038_; 
lean_dec_ref(v_lt_4029_);
lean_dec_ref(v_as_4028_);
v___x_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4038_, 0, v_a0_4034_);
return v___x_4038_;
}
else
{
lean_object* v___f_4039_; uint8_t v___x_4040_; 
v___f_4039_ = lean_alloc_closure((void*)(l_Array_getMax_x3f___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4039_, 0, v_lt_4029_);
v___x_4040_ = lean_nat_dec_le(v___x_4031_, v___x_4031_);
if (v___x_4040_ == 0)
{
if (v___x_4037_ == 0)
{
lean_object* v___x_4041_; 
lean_dec_ref(v___f_4039_);
lean_dec_ref(v_as_4028_);
v___x_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4041_, 0, v_a0_4034_);
return v___x_4041_;
}
else
{
size_t v___x_4042_; size_t v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4042_ = ((size_t)1ULL);
v___x_4043_ = lean_usize_of_nat(v___x_4031_);
v___x_4044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4036_, v___f_4039_, v_as_4028_, v___x_4042_, v___x_4043_, v_a0_4034_);
v___x_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4044_);
return v___x_4045_;
}
}
else
{
size_t v___x_4046_; size_t v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4046_ = ((size_t)1ULL);
v___x_4047_ = lean_usize_of_nat(v___x_4031_);
v___x_4048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4036_, v___f_4039_, v_as_4028_, v___x_4046_, v___x_4047_, v_a0_4034_);
v___x_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
return v___x_4049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f(lean_object* v_00_u03b1_4050_, lean_object* v_as_4051_, lean_object* v_lt_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Array_getMax_x3f___redArg(v_as_4051_, v_lt_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg___lam__0(lean_object* v_p_4054_, lean_object* v_a_4055_, lean_object* v_x_4056_, lean_object* v___y_4057_){
_start:
{
lean_object* v_fst_4058_; lean_object* v_snd_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4075_; 
v_fst_4058_ = lean_ctor_get(v___y_4057_, 0);
v_snd_4059_ = lean_ctor_get(v___y_4057_, 1);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___y_4057_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4061_ = v___y_4057_;
v_isShared_4062_ = v_isSharedCheck_4075_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_snd_4059_);
lean_inc(v_fst_4058_);
lean_dec(v___y_4057_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4075_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4063_; uint8_t v___x_4064_; 
lean_inc(v_a_4055_);
v___x_4063_ = lean_apply_1(v_p_4054_, v_a_4055_);
v___x_4064_ = lean_unbox(v___x_4063_);
if (v___x_4064_ == 0)
{
lean_object* v___x_4065_; lean_object* v___x_4067_; 
v___x_4065_ = lean_array_push(v_snd_4059_, v_a_4055_);
if (v_isShared_4062_ == 0)
{
lean_ctor_set(v___x_4061_, 1, v___x_4065_);
v___x_4067_ = v___x_4061_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_fst_4058_);
lean_ctor_set(v_reuseFailAlloc_4069_, 1, v___x_4065_);
v___x_4067_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
lean_object* v___x_4068_; 
v___x_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
return v___x_4068_;
}
}
else
{
lean_object* v___x_4070_; lean_object* v___x_4072_; 
v___x_4070_ = lean_array_push(v_fst_4058_, v_a_4055_);
if (v_isShared_4062_ == 0)
{
lean_ctor_set(v___x_4061_, 0, v___x_4070_);
v___x_4072_ = v___x_4061_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v___x_4070_);
lean_ctor_set(v_reuseFailAlloc_4074_, 1, v_snd_4059_);
v___x_4072_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4073_; 
v___x_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
return v___x_4073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg(lean_object* v_p_4078_, lean_object* v_as_4079_){
_start:
{
lean_object* v___f_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; size_t v_sz_4083_; size_t v___x_4084_; lean_object* v___x_4085_; lean_object* v_fst_4086_; lean_object* v_snd_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
v___f_4080_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4080_, 0, v_p_4078_);
v___x_4081_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4082_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_4083_ = lean_array_size(v_as_4079_);
v___x_4084_ = ((size_t)0ULL);
v___x_4085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_4081_, v_as_4079_, v___f_4080_, v_sz_4083_, v___x_4084_, v___x_4082_);
v_fst_4086_ = lean_ctor_get(v___x_4085_, 0);
v_snd_4087_ = lean_ctor_get(v___x_4085_, 1);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4085_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4085_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_snd_4087_);
lean_inc(v_fst_4086_);
lean_dec(v___x_4085_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_fst_4086_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v_snd_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition(lean_object* v_00_u03b1_4095_, lean_object* v_p_4096_, lean_object* v_as_4097_){
_start:
{
lean_object* v___f_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; size_t v_sz_4101_; size_t v___x_4102_; lean_object* v___x_4103_; lean_object* v_fst_4104_; lean_object* v_snd_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
v___f_4098_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4098_, 0, v_p_4096_);
v___x_4099_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4100_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_4101_ = lean_array_size(v_as_4097_);
v___x_4102_ = ((size_t)0ULL);
v___x_4103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_4099_, v_as_4097_, v___f_4098_, v_sz_4101_, v___x_4102_, v___x_4100_);
v_fst_4104_ = lean_ctor_get(v___x_4103_, 0);
v_snd_4105_ = lean_ctor_get(v___x_4103_, 1);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_4103_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_snd_4105_);
lean_inc(v_fst_4104_);
lean_dec(v___x_4103_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_fst_4104_);
lean_ctor_set(v_reuseFailAlloc_4111_, 1, v_snd_4105_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile___redArg(lean_object* v_p_4113_, lean_object* v_as_4114_){
_start:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; uint8_t v___x_4117_; 
v___x_4115_ = lean_unsigned_to_nat(0u);
v___x_4116_ = lean_array_get_size(v_as_4114_);
v___x_4117_ = lean_nat_dec_lt(v___x_4115_, v___x_4116_);
if (v___x_4117_ == 0)
{
lean_dec_ref(v_p_4113_);
return v_as_4114_;
}
else
{
lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; uint8_t v___x_4122_; 
v___x_4118_ = lean_unsigned_to_nat(1u);
v___x_4119_ = lean_nat_sub(v___x_4116_, v___x_4118_);
v___x_4120_ = lean_array_fget_borrowed(v_as_4114_, v___x_4119_);
lean_dec(v___x_4119_);
lean_inc_ref(v_p_4113_);
lean_inc(v___x_4120_);
v___x_4121_ = lean_apply_1(v_p_4113_, v___x_4120_);
v___x_4122_ = lean_unbox(v___x_4121_);
if (v___x_4122_ == 0)
{
lean_dec_ref(v_p_4113_);
return v_as_4114_;
}
else
{
lean_object* v___x_4123_; 
v___x_4123_ = lean_array_pop(v_as_4114_);
v_as_4114_ = v___x_4123_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile(lean_object* v_00_u03b1_4125_, lean_object* v_p_4126_, lean_object* v_as_4127_){
_start:
{
lean_object* v___x_4128_; 
v___x_4128_ = l_Array_popWhile___redArg(v_p_4126_, v_as_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(lean_object* v_p_4129_, lean_object* v_as_4130_, lean_object* v_i_4131_, lean_object* v_acc_4132_){
_start:
{
lean_object* v___x_4133_; uint8_t v___x_4134_; 
v___x_4133_ = lean_array_get_size(v_as_4130_);
v___x_4134_ = lean_nat_dec_lt(v_i_4131_, v___x_4133_);
if (v___x_4134_ == 0)
{
lean_dec(v_i_4131_);
lean_dec_ref(v_p_4129_);
return v_acc_4132_;
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4136_; uint8_t v___x_4137_; 
v_a_4135_ = lean_array_fget_borrowed(v_as_4130_, v_i_4131_);
lean_inc_ref(v_p_4129_);
lean_inc(v_a_4135_);
v___x_4136_ = lean_apply_1(v_p_4129_, v_a_4135_);
v___x_4137_ = lean_unbox(v___x_4136_);
if (v___x_4137_ == 0)
{
lean_dec(v_i_4131_);
lean_dec_ref(v_p_4129_);
return v_acc_4132_;
}
else
{
lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4138_ = lean_unsigned_to_nat(1u);
v___x_4139_ = lean_nat_add(v_i_4131_, v___x_4138_);
lean_dec(v_i_4131_);
lean_inc(v_a_4135_);
v___x_4140_ = lean_array_push(v_acc_4132_, v_a_4135_);
v_i_4131_ = v___x_4139_;
v_acc_4132_ = v___x_4140_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg___boxed(lean_object* v_p_4142_, lean_object* v_as_4143_, lean_object* v_i_4144_, lean_object* v_acc_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4142_, v_as_4143_, v_i_4144_, v_acc_4145_);
lean_dec_ref(v_as_4143_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(lean_object* v_00_u03b1_4147_, lean_object* v_p_4148_, lean_object* v_as_4149_, lean_object* v_i_4150_, lean_object* v_acc_4151_){
_start:
{
lean_object* v___x_4152_; 
v___x_4152_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4148_, v_as_4149_, v_i_4150_, v_acc_4151_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___boxed(lean_object* v_00_u03b1_4153_, lean_object* v_p_4154_, lean_object* v_as_4155_, lean_object* v_i_4156_, lean_object* v_acc_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(v_00_u03b1_4153_, v_p_4154_, v_as_4155_, v_i_4156_, v_acc_4157_);
lean_dec_ref(v_as_4155_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg(lean_object* v_p_4159_, lean_object* v_as_4160_){
_start:
{
lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4161_ = lean_unsigned_to_nat(0u);
v___x_4162_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4163_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4159_, v_as_4160_, v___x_4161_, v___x_4162_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg___boxed(lean_object* v_p_4164_, lean_object* v_as_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Array_takeWhile___redArg(v_p_4164_, v_as_4165_);
lean_dec_ref(v_as_4165_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile(lean_object* v_00_u03b1_4167_, lean_object* v_p_4168_, lean_object* v_as_4169_){
_start:
{
lean_object* v___x_4170_; 
v___x_4170_ = l_Array_takeWhile___redArg(v_p_4168_, v_as_4169_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___boxed(lean_object* v_00_u03b1_4171_, lean_object* v_p_4172_, lean_object* v_as_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Array_takeWhile(v_00_u03b1_4171_, v_p_4172_, v_as_4173_);
lean_dec_ref(v_as_4173_);
return v_res_4174_;
}
}
static lean_object* _init_l_Array_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_4175_; 
v___x_4175_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx___redArg(lean_object* v_xs_4176_, lean_object* v_i_4177_){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; 
v___x_4178_ = lean_unsigned_to_nat(1u);
v___x_4179_ = lean_nat_add(v_i_4177_, v___x_4178_);
v___x_4180_ = lean_array_get_size(v_xs_4176_);
v___x_4181_ = lean_nat_dec_lt(v___x_4179_, v___x_4180_);
if (v___x_4181_ == 0)
{
lean_object* v___x_4182_; 
lean_dec(v___x_4179_);
lean_dec(v_i_4177_);
v___x_4182_ = lean_array_pop(v_xs_4176_);
return v___x_4182_;
}
else
{
lean_object* v_xs_x27_4183_; 
v_xs_x27_4183_ = lean_array_fswap(v_xs_4176_, v___x_4179_, v_i_4177_);
lean_dec(v_i_4177_);
v_xs_4176_ = v_xs_x27_4183_;
v_i_4177_ = v___x_4179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx(lean_object* v_00_u03b1_4185_, lean_object* v_xs_4186_, lean_object* v_i_4187_, lean_object* v_h_4188_){
_start:
{
lean_object* v___x_4189_; 
v___x_4189_ = l_Array_eraseIdx___redArg(v_xs_4186_, v_i_4187_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds___redArg(lean_object* v_xs_4190_, lean_object* v_i_4191_){
_start:
{
lean_object* v___x_4192_; uint8_t v___x_4193_; 
v___x_4192_ = lean_array_get_size(v_xs_4190_);
v___x_4193_ = lean_nat_dec_lt(v_i_4191_, v___x_4192_);
if (v___x_4193_ == 0)
{
lean_dec(v_i_4191_);
return v_xs_4190_;
}
else
{
lean_object* v___x_4194_; 
v___x_4194_ = l_Array_eraseIdx___redArg(v_xs_4190_, v_i_4191_);
return v___x_4194_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds(lean_object* v_00_u03b1_4195_, lean_object* v_xs_4196_, lean_object* v_i_4197_){
_start:
{
lean_object* v___x_4198_; 
v___x_4198_ = l_Array_eraseIdxIfInBounds___redArg(v_xs_4196_, v_i_4197_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(lean_object* v_msg_4199_){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = lean_obj_once(&l_Array_instInhabited___closed__0, &l_Array_instInhabited___closed__0_once, _init_l_Array_instInhabited___closed__0);
v___x_4201_ = lean_panic_fn_borrowed(v___x_4200_, v_msg_4199_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0(lean_object* v_00_u03b1_4202_, lean_object* v_msg_4203_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v_msg_4203_);
return v___x_4204_;
}
}
static lean_object* _init_l_Array_eraseIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4207_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4208_ = lean_unsigned_to_nat(47u);
v___x_4209_ = lean_unsigned_to_nat(1874u);
v___x_4210_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__0));
v___x_4211_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4212_ = l_mkPanicMessageWithDecl(v___x_4211_, v___x_4210_, v___x_4209_, v___x_4208_, v___x_4207_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21___redArg(lean_object* v_xs_4213_, lean_object* v_i_4214_){
_start:
{
lean_object* v___x_4215_; uint8_t v___x_4216_; 
v___x_4215_ = lean_array_get_size(v_xs_4213_);
v___x_4216_ = lean_nat_dec_lt(v_i_4214_, v___x_4215_);
if (v___x_4216_ == 0)
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
lean_dec(v_i_4214_);
lean_dec_ref(v_xs_4213_);
v___x_4217_ = lean_obj_once(&l_Array_eraseIdx_x21___redArg___closed__2, &l_Array_eraseIdx_x21___redArg___closed__2_once, _init_l_Array_eraseIdx_x21___redArg___closed__2);
v___x_4218_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4217_);
return v___x_4218_;
}
else
{
lean_object* v___x_4219_; 
v___x_4219_ = l_Array_eraseIdx___redArg(v_xs_4213_, v_i_4214_);
return v___x_4219_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21(lean_object* v_00_u03b1_4220_, lean_object* v_xs_4221_, lean_object* v_i_4222_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l_Array_eraseIdx_x21___redArg(v_xs_4221_, v_i_4222_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Array_erase___redArg(lean_object* v_inst_4224_, lean_object* v_as_4225_, lean_object* v_a_4226_){
_start:
{
lean_object* v___x_4227_; 
v___x_4227_ = l_Array_finIdxOf_x3f___redArg(v_inst_4224_, v_as_4225_, v_a_4226_);
if (lean_obj_tag(v___x_4227_) == 0)
{
return v_as_4225_;
}
else
{
lean_object* v_val_4228_; lean_object* v___x_4229_; 
v_val_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_val_4228_);
lean_dec_ref_known(v___x_4227_, 1);
v___x_4229_ = l_Array_eraseIdx___redArg(v_as_4225_, v_val_4228_);
return v___x_4229_;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase(lean_object* v_00_u03b1_4230_, lean_object* v_inst_4231_, lean_object* v_as_4232_, lean_object* v_a_4233_){
_start:
{
lean_object* v___x_4234_; 
v___x_4234_ = l_Array_erase___redArg(v_inst_4231_, v_as_4232_, v_a_4233_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseP___redArg(lean_object* v_as_4235_, lean_object* v_p_4236_){
_start:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4237_ = lean_unsigned_to_nat(0u);
v___x_4238_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_4236_, v_as_4235_, v___x_4237_);
if (lean_obj_tag(v___x_4238_) == 0)
{
return v_as_4235_;
}
else
{
lean_object* v_val_4239_; lean_object* v___x_4240_; 
v_val_4239_ = lean_ctor_get(v___x_4238_, 0);
lean_inc(v_val_4239_);
lean_dec_ref_known(v___x_4238_, 1);
v___x_4240_ = l_Array_eraseIdx___redArg(v_as_4235_, v_val_4239_);
return v___x_4240_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseP(lean_object* v_00_u03b1_4241_, lean_object* v_as_4242_, lean_object* v_p_4243_){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Array_eraseP___redArg(v_as_4242_, v_p_4243_);
return v___x_4244_;
}
}
static lean_object* _init_l_Array_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_4245_; 
v___x_4245_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(lean_object* v_i_4246_, lean_object* v_as_4247_, lean_object* v_j_4248_){
_start:
{
uint8_t v___x_4249_; 
v___x_4249_ = lean_nat_dec_lt(v_i_4246_, v_j_4248_);
if (v___x_4249_ == 0)
{
lean_dec(v_j_4248_);
return v_as_4247_;
}
else
{
lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v_as_4252_; 
v___x_4250_ = lean_unsigned_to_nat(1u);
v___x_4251_ = lean_nat_sub(v_j_4248_, v___x_4250_);
v_as_4252_ = lean_array_fswap(v_as_4247_, v___x_4251_, v_j_4248_);
lean_dec(v_j_4248_);
v_as_4247_ = v_as_4252_;
v_j_4248_ = v___x_4251_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg___boxed(lean_object* v_i_4254_, lean_object* v_as_4255_, lean_object* v_j_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4254_, v_as_4255_, v_j_4256_);
lean_dec(v_i_4254_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object* v_00_u03b1_4258_, lean_object* v_i_4259_, lean_object* v_as_4260_, lean_object* v_j_4261_){
_start:
{
lean_object* v___x_4262_; 
v___x_4262_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4259_, v_as_4260_, v_j_4261_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___boxed(lean_object* v_00_u03b1_4263_, lean_object* v_i_4264_, lean_object* v_as_4265_, lean_object* v_j_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(v_00_u03b1_4263_, v_i_4264_, v_as_4265_, v_j_4266_);
lean_dec(v_i_4264_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg(lean_object* v_as_4268_, lean_object* v_i_4269_, lean_object* v_a_4270_){
_start:
{
lean_object* v_j_4271_; lean_object* v_as_4272_; lean_object* v___x_4273_; 
v_j_4271_ = lean_array_get_size(v_as_4268_);
v_as_4272_ = lean_array_push(v_as_4268_, v_a_4270_);
v___x_4273_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4269_, v_as_4272_, v_j_4271_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg___boxed(lean_object* v_as_4274_, lean_object* v_i_4275_, lean_object* v_a_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Array_insertIdx___redArg(v_as_4274_, v_i_4275_, v_a_4276_);
lean_dec(v_i_4275_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx(lean_object* v_00_u03b1_4278_, lean_object* v_as_4279_, lean_object* v_i_4280_, lean_object* v_a_4281_, lean_object* v_x_4282_){
_start:
{
lean_object* v_j_4283_; lean_object* v_as_4284_; lean_object* v___x_4285_; 
v_j_4283_ = lean_array_get_size(v_as_4279_);
v_as_4284_ = lean_array_push(v_as_4279_, v_a_4281_);
v___x_4285_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4280_, v_as_4284_, v_j_4283_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___boxed(lean_object* v_00_u03b1_4286_, lean_object* v_as_4287_, lean_object* v_i_4288_, lean_object* v_a_4289_, lean_object* v_x_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l_Array_insertIdx(v_00_u03b1_4286_, v_as_4287_, v_i_4288_, v_a_4289_, v_x_4290_);
lean_dec(v_i_4288_);
return v_res_4291_;
}
}
static lean_object* _init_l_Array_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4293_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4294_ = lean_unsigned_to_nat(7u);
v___x_4295_ = lean_unsigned_to_nat(1956u);
v___x_4296_ = ((lean_object*)(l_Array_insertIdx_x21___redArg___closed__0));
v___x_4297_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4298_ = l_mkPanicMessageWithDecl(v___x_4297_, v___x_4296_, v___x_4295_, v___x_4294_, v___x_4293_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg(lean_object* v_as_4299_, lean_object* v_i_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v___x_4302_; uint8_t v___x_4303_; 
v___x_4302_ = lean_array_get_size(v_as_4299_);
v___x_4303_ = lean_nat_dec_le(v_i_4300_, v___x_4302_);
if (v___x_4303_ == 0)
{
lean_object* v___x_4304_; lean_object* v___x_4305_; 
lean_dec(v_a_4301_);
lean_dec_ref(v_as_4299_);
v___x_4304_ = lean_obj_once(&l_Array_insertIdx_x21___redArg___closed__1, &l_Array_insertIdx_x21___redArg___closed__1_once, _init_l_Array_insertIdx_x21___redArg___closed__1);
v___x_4305_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4304_);
return v___x_4305_;
}
else
{
lean_object* v_as_4306_; lean_object* v___x_4307_; 
v_as_4306_ = lean_array_push(v_as_4299_, v_a_4301_);
v___x_4307_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4300_, v_as_4306_, v___x_4302_);
return v___x_4307_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg___boxed(lean_object* v_as_4308_, lean_object* v_i_4309_, lean_object* v_a_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Array_insertIdx_x21___redArg(v_as_4308_, v_i_4309_, v_a_4310_);
lean_dec(v_i_4309_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21(lean_object* v_00_u03b1_4312_, lean_object* v_as_4313_, lean_object* v_i_4314_, lean_object* v_a_4315_){
_start:
{
lean_object* v___x_4316_; 
v___x_4316_ = l_Array_insertIdx_x21___redArg(v_as_4313_, v_i_4314_, v_a_4315_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___boxed(lean_object* v_00_u03b1_4317_, lean_object* v_as_4318_, lean_object* v_i_4319_, lean_object* v_a_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l_Array_insertIdx_x21(v_00_u03b1_4317_, v_as_4318_, v_i_4319_, v_a_4320_);
lean_dec(v_i_4319_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg(lean_object* v_as_4322_, lean_object* v_i_4323_, lean_object* v_a_4324_){
_start:
{
lean_object* v___x_4325_; uint8_t v___x_4326_; 
v___x_4325_ = lean_array_get_size(v_as_4322_);
v___x_4326_ = lean_nat_dec_le(v_i_4323_, v___x_4325_);
if (v___x_4326_ == 0)
{
lean_dec(v_a_4324_);
return v_as_4322_;
}
else
{
lean_object* v_as_4327_; lean_object* v___x_4328_; 
v_as_4327_ = lean_array_push(v_as_4322_, v_a_4324_);
v___x_4328_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4323_, v_as_4327_, v___x_4325_);
return v___x_4328_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg___boxed(lean_object* v_as_4329_, lean_object* v_i_4330_, lean_object* v_a_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l_Array_insertIdxIfInBounds___redArg(v_as_4329_, v_i_4330_, v_a_4331_);
lean_dec(v_i_4330_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds(lean_object* v_00_u03b1_4333_, lean_object* v_as_4334_, lean_object* v_i_4335_, lean_object* v_a_4336_){
_start:
{
lean_object* v___x_4337_; 
v___x_4337_ = l_Array_insertIdxIfInBounds___redArg(v_as_4334_, v_i_4335_, v_a_4336_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___boxed(lean_object* v_00_u03b1_4338_, lean_object* v_as_4339_, lean_object* v_i_4340_, lean_object* v_a_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_Array_insertIdxIfInBounds(v_00_u03b1_4338_, v_as_4339_, v_i_4340_, v_a_4341_);
lean_dec(v_i_4340_);
return v_res_4342_;
}
}
uint8_t l_Array_isPrefixOfAux___redArg(lean_object* v_inst_4343_, lean_object* v_as_4344_, lean_object* v_bs_4345_, lean_object* v_i_4346_){
_start:
{
lean_object* v___x_4347_; uint8_t v___x_4348_; 
v___x_4347_ = lean_array_get_size(v_as_4344_);
v___x_4348_ = lean_nat_dec_lt(v_i_4346_, v___x_4347_);
if (v___x_4348_ == 0)
{
uint8_t v___x_4349_; 
lean_dec(v_i_4346_);
lean_dec_ref(v_inst_4343_);
v___x_4349_ = 1;
return v___x_4349_;
}
else
{
lean_object* v_a_4350_; lean_object* v_b_4351_; lean_object* v___x_4352_; uint8_t v___x_4353_; 
v_a_4350_ = lean_array_fget_borrowed(v_as_4344_, v_i_4346_);
v_b_4351_ = lean_array_fget_borrowed(v_bs_4345_, v_i_4346_);
lean_inc_ref(v_inst_4343_);
lean_inc(v_b_4351_);
lean_inc(v_a_4350_);
v___x_4352_ = lean_apply_2(v_inst_4343_, v_a_4350_, v_b_4351_);
v___x_4353_ = lean_unbox(v___x_4352_);
if (v___x_4353_ == 0)
{
uint8_t v___x_4354_; 
lean_dec(v_i_4346_);
lean_dec_ref(v_inst_4343_);
v___x_4354_ = lean_unbox(v___x_4352_);
return v___x_4354_;
}
else
{
lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4355_ = lean_unsigned_to_nat(1u);
v___x_4356_ = lean_nat_add(v_i_4346_, v___x_4355_);
lean_dec(v_i_4346_);
v_i_4346_ = v___x_4356_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isPrefixOfAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4343_ = stack[0].m_obj;
lean_object* v_as_4344_ = stack[1].m_obj;
lean_object* v_bs_4345_ = stack[2].m_obj;
lean_object* v_i_4346_ = stack[3].m_obj;
uint8_t v_res_4358_;
v_res_4358_ = l_Array_isPrefixOfAux___redArg(v_inst_4343_, v_as_4344_, v_bs_4345_, v_i_4346_);
stack->m_num = v_res_4358_;
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___redArg___boxed(lean_object* v_inst_4359_, lean_object* v_as_4360_, lean_object* v_bs_4361_, lean_object* v_i_4362_){
_start:
{
uint8_t v_res_4363_; lean_object* v_r_4364_; 
v_res_4363_ = l_Array_isPrefixOfAux___redArg(v_inst_4359_, v_as_4360_, v_bs_4361_, v_i_4362_);
lean_dec_ref(v_bs_4361_);
lean_dec_ref(v_as_4360_);
v_r_4364_ = lean_box(v_res_4363_);
return v_r_4364_;
}
}
uint8_t l_Array_isPrefixOfAux(lean_object* v_00_u03b1_4365_, lean_object* v_inst_4366_, lean_object* v_as_4367_, lean_object* v_bs_4368_, lean_object* v_hle_4369_, lean_object* v_i_4370_){
_start:
{
uint8_t v___x_4371_; 
v___x_4371_ = l_Array_isPrefixOfAux___redArg(v_inst_4366_, v_as_4367_, v_bs_4368_, v_i_4370_);
return v___x_4371_;
}
}
LEAN_EXPORT void l_Array_isPrefixOfAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4366_ = stack[1].m_obj;
lean_object* v_as_4367_ = stack[2].m_obj;
lean_object* v_bs_4368_ = stack[3].m_obj;
lean_object* v_i_4370_ = stack[5].m_obj;
uint8_t v_res_4372_;
v_res_4372_ = l_Array_isPrefixOfAux(lean_box(0), v_inst_4366_, v_as_4367_, v_bs_4368_, lean_box(0), v_i_4370_);
stack->m_num = v_res_4372_;
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___boxed(lean_object* v_00_u03b1_4373_, lean_object* v_inst_4374_, lean_object* v_as_4375_, lean_object* v_bs_4376_, lean_object* v_hle_4377_, lean_object* v_i_4378_){
_start:
{
uint8_t v_res_4379_; lean_object* v_r_4380_; 
v_res_4379_ = l_Array_isPrefixOfAux(v_00_u03b1_4373_, v_inst_4374_, v_as_4375_, v_bs_4376_, v_hle_4377_, v_i_4378_);
lean_dec_ref(v_bs_4376_);
lean_dec_ref(v_as_4375_);
v_r_4380_ = lean_box(v_res_4379_);
return v_r_4380_;
}
}
uint8_t l_Array_isPrefixOf___redArg(lean_object* v_inst_4381_, lean_object* v_as_4382_, lean_object* v_bs_4383_){
_start:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; uint8_t v___x_4386_; 
v___x_4384_ = lean_array_get_size(v_as_4382_);
v___x_4385_ = lean_array_get_size(v_bs_4383_);
v___x_4386_ = lean_nat_dec_le(v___x_4384_, v___x_4385_);
if (v___x_4386_ == 0)
{
lean_dec_ref(v_inst_4381_);
return v___x_4386_;
}
else
{
lean_object* v___x_4387_; uint8_t v___x_4388_; 
v___x_4387_ = lean_unsigned_to_nat(0u);
v___x_4388_ = l_Array_isPrefixOfAux___redArg(v_inst_4381_, v_as_4382_, v_bs_4383_, v___x_4387_);
return v___x_4388_;
}
}
}
LEAN_EXPORT void l_Array_isPrefixOf___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4381_ = stack[0].m_obj;
lean_object* v_as_4382_ = stack[1].m_obj;
lean_object* v_bs_4383_ = stack[2].m_obj;
uint8_t v_res_4389_;
v_res_4389_ = l_Array_isPrefixOf___redArg(v_inst_4381_, v_as_4382_, v_bs_4383_);
stack->m_num = v_res_4389_;
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___redArg___boxed(lean_object* v_inst_4390_, lean_object* v_as_4391_, lean_object* v_bs_4392_){
_start:
{
uint8_t v_res_4393_; lean_object* v_r_4394_; 
v_res_4393_ = l_Array_isPrefixOf___redArg(v_inst_4390_, v_as_4391_, v_bs_4392_);
lean_dec_ref(v_bs_4392_);
lean_dec_ref(v_as_4391_);
v_r_4394_ = lean_box(v_res_4393_);
return v_r_4394_;
}
}
uint8_t l_Array_isPrefixOf(lean_object* v_00_u03b1_4395_, lean_object* v_inst_4396_, lean_object* v_as_4397_, lean_object* v_bs_4398_){
_start:
{
uint8_t v___x_4399_; 
v___x_4399_ = l_Array_isPrefixOf___redArg(v_inst_4396_, v_as_4397_, v_bs_4398_);
return v___x_4399_;
}
}
LEAN_EXPORT void l_Array_isPrefixOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4396_ = stack[1].m_obj;
lean_object* v_as_4397_ = stack[2].m_obj;
lean_object* v_bs_4398_ = stack[3].m_obj;
uint8_t v_res_4400_;
v_res_4400_ = l_Array_isPrefixOf(lean_box(0), v_inst_4396_, v_as_4397_, v_bs_4398_);
stack->m_num = v_res_4400_;
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___boxed(lean_object* v_00_u03b1_4401_, lean_object* v_inst_4402_, lean_object* v_as_4403_, lean_object* v_bs_4404_){
_start:
{
uint8_t v_res_4405_; lean_object* v_r_4406_; 
v_res_4405_ = l_Array_isPrefixOf(v_00_u03b1_4401_, v_inst_4402_, v_as_4403_, v_bs_4404_);
lean_dec_ref(v_bs_4404_);
lean_dec_ref(v_as_4403_);
v_r_4406_ = lean_box(v_res_4405_);
return v_r_4406_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0___boxed(lean_object* v_i_4407_, lean_object* v_cs_4408_, lean_object* v_inst_4409_, lean_object* v_as_4410_, lean_object* v_bs_4411_, lean_object* v_f_4412_, lean_object* v_____do__lift_4413_){
_start:
{
lean_object* v_res_4414_; 
v_res_4414_ = l_Array_zipWithMAux___redArg___lam__0(v_i_4407_, v_cs_4408_, v_inst_4409_, v_as_4410_, v_bs_4411_, v_f_4412_, v_____do__lift_4413_);
lean_dec(v_i_4407_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg(lean_object* v_inst_4415_, lean_object* v_as_4416_, lean_object* v_bs_4417_, lean_object* v_f_4418_, lean_object* v_i_4419_, lean_object* v_cs_4420_){
_start:
{
lean_object* v_toApplicative_4421_; lean_object* v_toBind_4422_; lean_object* v_toPure_4423_; lean_object* v___x_4424_; uint8_t v___x_4425_; 
v_toApplicative_4421_ = lean_ctor_get(v_inst_4415_, 0);
v_toBind_4422_ = lean_ctor_get(v_inst_4415_, 1);
lean_inc(v_toBind_4422_);
v_toPure_4423_ = lean_ctor_get(v_toApplicative_4421_, 1);
v___x_4424_ = lean_array_get_size(v_as_4416_);
v___x_4425_ = lean_nat_dec_lt(v_i_4419_, v___x_4424_);
if (v___x_4425_ == 0)
{
lean_object* v___x_4426_; 
lean_inc(v_toPure_4423_);
lean_dec(v_toBind_4422_);
lean_dec(v_i_4419_);
lean_dec(v_f_4418_);
lean_dec_ref(v_bs_4417_);
lean_dec_ref(v_as_4416_);
lean_dec_ref(v_inst_4415_);
v___x_4426_ = lean_apply_2(v_toPure_4423_, lean_box(0), v_cs_4420_);
return v___x_4426_;
}
else
{
lean_object* v___x_4427_; uint8_t v___x_4428_; 
v___x_4427_ = lean_array_get_size(v_bs_4417_);
v___x_4428_ = lean_nat_dec_lt(v_i_4419_, v___x_4427_);
if (v___x_4428_ == 0)
{
lean_object* v___x_4429_; 
lean_inc(v_toPure_4423_);
lean_dec(v_toBind_4422_);
lean_dec(v_i_4419_);
lean_dec(v_f_4418_);
lean_dec_ref(v_bs_4417_);
lean_dec_ref(v_as_4416_);
lean_dec_ref(v_inst_4415_);
v___x_4429_ = lean_apply_2(v_toPure_4423_, lean_box(0), v_cs_4420_);
return v___x_4429_;
}
else
{
lean_object* v___f_4430_; lean_object* v_a_4431_; lean_object* v_b_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
lean_inc(v_f_4418_);
lean_inc_ref(v_bs_4417_);
lean_inc_ref(v_as_4416_);
lean_inc(v_i_4419_);
v___f_4430_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4430_, 0, v_i_4419_);
lean_closure_set(v___f_4430_, 1, v_cs_4420_);
lean_closure_set(v___f_4430_, 2, v_inst_4415_);
lean_closure_set(v___f_4430_, 3, v_as_4416_);
lean_closure_set(v___f_4430_, 4, v_bs_4417_);
lean_closure_set(v___f_4430_, 5, v_f_4418_);
v_a_4431_ = lean_array_fget(v_as_4416_, v_i_4419_);
lean_dec_ref(v_as_4416_);
v_b_4432_ = lean_array_fget(v_bs_4417_, v_i_4419_);
lean_dec(v_i_4419_);
lean_dec_ref(v_bs_4417_);
v___x_4433_ = lean_apply_2(v_f_4418_, v_a_4431_, v_b_4432_);
v___x_4434_ = lean_apply_4(v_toBind_4422_, lean_box(0), lean_box(0), v___x_4433_, v___f_4430_);
return v___x_4434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0(lean_object* v_i_4435_, lean_object* v_cs_4436_, lean_object* v_inst_4437_, lean_object* v_as_4438_, lean_object* v_bs_4439_, lean_object* v_f_4440_, lean_object* v_____do__lift_4441_){
_start:
{
lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4442_ = lean_unsigned_to_nat(1u);
v___x_4443_ = lean_nat_add(v_i_4435_, v___x_4442_);
v___x_4444_ = lean_array_push(v_cs_4436_, v_____do__lift_4441_);
v___x_4445_ = l_Array_zipWithMAux___redArg(v_inst_4437_, v_as_4438_, v_bs_4439_, v_f_4440_, v___x_4443_, v___x_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux(lean_object* v_00_u03b1_4446_, lean_object* v_00_u03b2_4447_, lean_object* v_00_u03b3_4448_, lean_object* v_m_4449_, lean_object* v_inst_4450_, lean_object* v_as_4451_, lean_object* v_bs_4452_, lean_object* v_f_4453_, lean_object* v_i_4454_, lean_object* v_cs_4455_){
_start:
{
lean_object* v___x_4456_; 
v___x_4456_ = l_Array_zipWithMAux___redArg(v_inst_4450_, v_as_4451_, v_bs_4452_, v_f_4453_, v_i_4454_, v_cs_4455_);
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith___redArg(lean_object* v_f_4457_, lean_object* v_as_4458_, lean_object* v_bs_4459_){
_start:
{
lean_object* v___f_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v___f_4460_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4460_, 0, v_f_4457_);
v___x_4461_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4462_ = lean_unsigned_to_nat(0u);
v___x_4463_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4464_ = l_Array_zipWithMAux___redArg(v___x_4461_, v_as_4458_, v_bs_4459_, v___f_4460_, v___x_4462_, v___x_4463_);
return v___x_4464_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith(lean_object* v_00_u03b1_4465_, lean_object* v_00_u03b2_4466_, lean_object* v_00_u03b3_4467_, lean_object* v_f_4468_, lean_object* v_as_4469_, lean_object* v_bs_4470_){
_start:
{
lean_object* v___f_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___f_4471_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4471_, 0, v_f_4468_);
v___x_4472_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4473_ = lean_unsigned_to_nat(0u);
v___x_4474_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4475_ = l_Array_zipWithMAux___redArg(v___x_4472_, v_as_4469_, v_bs_4470_, v___f_4471_, v___x_4473_, v___x_4474_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(lean_object* v_as_4476_, lean_object* v_bs_4477_, lean_object* v_i_4478_, lean_object* v_cs_4479_){
_start:
{
lean_object* v___x_4480_; uint8_t v___x_4481_; 
v___x_4480_ = lean_array_get_size(v_as_4476_);
v___x_4481_ = lean_nat_dec_lt(v_i_4478_, v___x_4480_);
if (v___x_4481_ == 0)
{
lean_dec(v_i_4478_);
return v_cs_4479_;
}
else
{
lean_object* v___x_4482_; uint8_t v___x_4483_; 
v___x_4482_ = lean_array_get_size(v_bs_4477_);
v___x_4483_ = lean_nat_dec_lt(v_i_4478_, v___x_4482_);
if (v___x_4483_ == 0)
{
lean_dec(v_i_4478_);
return v_cs_4479_;
}
else
{
lean_object* v_a_4484_; lean_object* v_b_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v_a_4484_ = lean_array_fget_borrowed(v_as_4476_, v_i_4478_);
v_b_4485_ = lean_array_fget_borrowed(v_bs_4477_, v_i_4478_);
lean_inc(v_b_4485_);
lean_inc(v_a_4484_);
v___x_4486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4486_, 0, v_a_4484_);
lean_ctor_set(v___x_4486_, 1, v_b_4485_);
v___x_4487_ = lean_unsigned_to_nat(1u);
v___x_4488_ = lean_nat_add(v_i_4478_, v___x_4487_);
lean_dec(v_i_4478_);
v___x_4489_ = lean_array_push(v_cs_4479_, v___x_4486_);
v_i_4478_ = v___x_4488_;
v_cs_4479_ = v___x_4489_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg___boxed(lean_object* v_as_4491_, lean_object* v_bs_4492_, lean_object* v_i_4493_, lean_object* v_cs_4494_){
_start:
{
lean_object* v_res_4495_; 
v_res_4495_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4491_, v_bs_4492_, v_i_4493_, v_cs_4494_);
lean_dec_ref(v_bs_4492_);
lean_dec_ref(v_as_4491_);
return v_res_4495_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg(lean_object* v_as_4498_, lean_object* v_bs_4499_){
_start:
{
lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
v___x_4500_ = lean_unsigned_to_nat(0u);
v___x_4501_ = ((lean_object*)(l_Array_zip___redArg___closed__0));
v___x_4502_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4498_, v_bs_4499_, v___x_4500_, v___x_4501_);
return v___x_4502_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg___boxed(lean_object* v_as_4503_, lean_object* v_bs_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l_Array_zip___redArg(v_as_4503_, v_bs_4504_);
lean_dec_ref(v_bs_4504_);
lean_dec_ref(v_as_4503_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_Array_zip(lean_object* v_00_u03b1_4506_, lean_object* v_00_u03b2_4507_, lean_object* v_as_4508_, lean_object* v_bs_4509_){
_start:
{
lean_object* v___x_4510_; 
v___x_4510_ = l_Array_zip___redArg(v_as_4508_, v_bs_4509_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___boxed(lean_object* v_00_u03b1_4511_, lean_object* v_00_u03b2_4512_, lean_object* v_as_4513_, lean_object* v_bs_4514_){
_start:
{
lean_object* v_res_4515_; 
v_res_4515_ = l_Array_zip(v_00_u03b1_4511_, v_00_u03b2_4512_, v_as_4513_, v_bs_4514_);
lean_dec_ref(v_bs_4514_);
lean_dec_ref(v_as_4513_);
return v_res_4515_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0(lean_object* v_00_u03b1_4516_, lean_object* v_00_u03b2_4517_, lean_object* v_as_4518_, lean_object* v_bs_4519_, lean_object* v_i_4520_, lean_object* v_cs_4521_){
_start:
{
lean_object* v___x_4522_; 
v___x_4522_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4518_, v_bs_4519_, v_i_4520_, v_cs_4521_);
return v___x_4522_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___boxed(lean_object* v_00_u03b1_4523_, lean_object* v_00_u03b2_4524_, lean_object* v_as_4525_, lean_object* v_bs_4526_, lean_object* v_i_4527_, lean_object* v_cs_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l_Array_zipWithMAux___at___00Array_zip_spec__0(v_00_u03b1_4523_, v_00_u03b2_4524_, v_as_4525_, v_bs_4526_, v_i_4527_, v_cs_4528_);
lean_dec_ref(v_bs_4526_);
lean_dec_ref(v_as_4525_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(lean_object* v_f_4530_, lean_object* v_as_4531_, lean_object* v_bs_4532_, lean_object* v_i_4533_, lean_object* v_cs_4534_){
_start:
{
lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4544_; lean_object* v___y_4551_; lean_object* v___x_4558_; lean_object* v___x_4559_; uint8_t v___x_4560_; 
v___x_4558_ = lean_array_get_size(v_as_4531_);
v___x_4559_ = lean_array_get_size(v_bs_4532_);
v___x_4560_ = lean_nat_dec_le(v___x_4558_, v___x_4559_);
if (v___x_4560_ == 0)
{
v___y_4551_ = v___x_4558_;
goto v___jp_4550_;
}
else
{
v___y_4551_ = v___x_4559_;
goto v___jp_4550_;
}
v___jp_4535_:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4538_ = lean_unsigned_to_nat(1u);
v___x_4539_ = lean_nat_add(v_i_4533_, v___x_4538_);
lean_dec(v_i_4533_);
lean_inc(v_f_4530_);
v___x_4540_ = lean_apply_2(v_f_4530_, v___y_4536_, v___y_4537_);
v___x_4541_ = lean_array_push(v_cs_4534_, v___x_4540_);
v_i_4533_ = v___x_4539_;
v_cs_4534_ = v___x_4541_;
goto _start;
}
v___jp_4543_:
{
lean_object* v___x_4545_; uint8_t v___x_4546_; 
v___x_4545_ = lean_array_get_size(v_bs_4532_);
v___x_4546_ = lean_nat_dec_lt(v_i_4533_, v___x_4545_);
if (v___x_4546_ == 0)
{
lean_object* v___x_4547_; 
v___x_4547_ = lean_box(0);
v___y_4536_ = v___y_4544_;
v___y_4537_ = v___x_4547_;
goto v___jp_4535_;
}
else
{
lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4548_ = lean_array_fget_borrowed(v_bs_4532_, v_i_4533_);
lean_inc(v___x_4548_);
v___x_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4548_);
v___y_4536_ = v___y_4544_;
v___y_4537_ = v___x_4549_;
goto v___jp_4535_;
}
}
v___jp_4550_:
{
uint8_t v___x_4552_; 
v___x_4552_ = lean_nat_dec_lt(v_i_4533_, v___y_4551_);
lean_dec(v___y_4551_);
if (v___x_4552_ == 0)
{
lean_dec(v_i_4533_);
lean_dec(v_f_4530_);
return v_cs_4534_;
}
else
{
lean_object* v___x_4553_; uint8_t v___x_4554_; 
v___x_4553_ = lean_array_get_size(v_as_4531_);
v___x_4554_ = lean_nat_dec_lt(v_i_4533_, v___x_4553_);
if (v___x_4554_ == 0)
{
lean_object* v___x_4555_; 
v___x_4555_ = lean_box(0);
v___y_4544_ = v___x_4555_;
goto v___jp_4543_;
}
else
{
lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4556_ = lean_array_fget_borrowed(v_as_4531_, v_i_4533_);
lean_inc(v___x_4556_);
v___x_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
v___y_4544_ = v___x_4557_;
goto v___jp_4543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg___boxed(lean_object* v_f_4561_, lean_object* v_as_4562_, lean_object* v_bs_4563_, lean_object* v_i_4564_, lean_object* v_cs_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4561_, v_as_4562_, v_bs_4563_, v_i_4564_, v_cs_4565_);
lean_dec_ref(v_bs_4563_);
lean_dec_ref(v_as_4562_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(lean_object* v_00_u03b1_4567_, lean_object* v_00_u03b2_4568_, lean_object* v_00_u03b3_4569_, lean_object* v_f_4570_, lean_object* v_as_4571_, lean_object* v_bs_4572_, lean_object* v_i_4573_, lean_object* v_cs_4574_){
_start:
{
lean_object* v___x_4575_; 
v___x_4575_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4570_, v_as_4571_, v_bs_4572_, v_i_4573_, v_cs_4574_);
return v___x_4575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___boxed(lean_object* v_00_u03b1_4576_, lean_object* v_00_u03b2_4577_, lean_object* v_00_u03b3_4578_, lean_object* v_f_4579_, lean_object* v_as_4580_, lean_object* v_bs_4581_, lean_object* v_i_4582_, lean_object* v_cs_4583_){
_start:
{
lean_object* v_res_4584_; 
v_res_4584_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(v_00_u03b1_4576_, v_00_u03b2_4577_, v_00_u03b3_4578_, v_f_4579_, v_as_4580_, v_bs_4581_, v_i_4582_, v_cs_4583_);
lean_dec_ref(v_bs_4581_);
lean_dec_ref(v_as_4580_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg(lean_object* v_f_4585_, lean_object* v_as_4586_, lean_object* v_bs_4587_){
_start:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4588_ = lean_unsigned_to_nat(0u);
v___x_4589_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4590_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4585_, v_as_4586_, v_bs_4587_, v___x_4588_, v___x_4589_);
return v___x_4590_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg___boxed(lean_object* v_f_4591_, lean_object* v_as_4592_, lean_object* v_bs_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_Array_zipWithAll___redArg(v_f_4591_, v_as_4592_, v_bs_4593_);
lean_dec_ref(v_bs_4593_);
lean_dec_ref(v_as_4592_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll(lean_object* v_00_u03b1_4595_, lean_object* v_00_u03b2_4596_, lean_object* v_00_u03b3_4597_, lean_object* v_f_4598_, lean_object* v_as_4599_, lean_object* v_bs_4600_){
_start:
{
lean_object* v___x_4601_; 
v___x_4601_ = l_Array_zipWithAll___redArg(v_f_4598_, v_as_4599_, v_bs_4600_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___boxed(lean_object* v_00_u03b1_4602_, lean_object* v_00_u03b2_4603_, lean_object* v_00_u03b3_4604_, lean_object* v_f_4605_, lean_object* v_as_4606_, lean_object* v_bs_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l_Array_zipWithAll(v_00_u03b1_4602_, v_00_u03b2_4603_, v_00_u03b3_4604_, v_f_4605_, v_as_4606_, v_bs_4607_);
lean_dec_ref(v_bs_4607_);
lean_dec_ref(v_as_4606_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM___redArg(lean_object* v_inst_4609_, lean_object* v_f_4610_, lean_object* v_as_4611_, lean_object* v_bs_4612_){
_start:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4613_ = lean_unsigned_to_nat(0u);
v___x_4614_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4615_ = l_Array_zipWithMAux___redArg(v_inst_4609_, v_as_4611_, v_bs_4612_, v_f_4610_, v___x_4613_, v___x_4614_);
return v___x_4615_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM(lean_object* v_00_u03b1_4616_, lean_object* v_00_u03b2_4617_, lean_object* v_00_u03b3_4618_, lean_object* v_m_4619_, lean_object* v_inst_4620_, lean_object* v_f_4621_, lean_object* v_as_4622_, lean_object* v_bs_4623_){
_start:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4624_ = lean_unsigned_to_nat(0u);
v___x_4625_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4626_ = l_Array_zipWithMAux___redArg(v_inst_4620_, v_as_4622_, v_bs_4623_, v_f_4621_, v___x_4624_, v___x_4625_);
return v___x_4626_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(lean_object* v_as_4627_, size_t v_i_4628_, size_t v_stop_4629_, lean_object* v_b_4630_){
_start:
{
uint8_t v___x_4631_; 
v___x_4631_ = lean_usize_dec_eq(v_i_4628_, v_stop_4629_);
if (v___x_4631_ == 0)
{
lean_object* v_fst_4632_; lean_object* v_snd_4633_; lean_object* v___x_4634_; lean_object* v_fst_4635_; lean_object* v_snd_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4648_; 
v_fst_4632_ = lean_ctor_get(v_b_4630_, 0);
lean_inc(v_fst_4632_);
v_snd_4633_ = lean_ctor_get(v_b_4630_, 1);
lean_inc(v_snd_4633_);
lean_dec_ref(v_b_4630_);
v___x_4634_ = lean_array_uget(v_as_4627_, v_i_4628_);
v_fst_4635_ = lean_ctor_get(v___x_4634_, 0);
v_snd_4636_ = lean_ctor_get(v___x_4634_, 1);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4634_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4638_ = v___x_4634_;
v_isShared_4639_ = v_isSharedCheck_4648_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_snd_4636_);
lean_inc(v_fst_4635_);
lean_dec(v___x_4634_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4648_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4643_; 
v___x_4640_ = lean_array_push(v_fst_4632_, v_fst_4635_);
v___x_4641_ = lean_array_push(v_snd_4633_, v_snd_4636_);
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 1, v___x_4641_);
lean_ctor_set(v___x_4638_, 0, v___x_4640_);
v___x_4643_ = v___x_4638_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4640_);
lean_ctor_set(v_reuseFailAlloc_4647_, 1, v___x_4641_);
v___x_4643_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
size_t v___x_4644_; size_t v___x_4645_; 
v___x_4644_ = ((size_t)1ULL);
v___x_4645_ = lean_usize_add(v_i_4628_, v___x_4644_);
v_i_4628_ = v___x_4645_;
v_b_4630_ = v___x_4643_;
goto _start;
}
}
}
else
{
return v_b_4630_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4627_ = stack[0].m_obj;
size_t v_i_4628_ = stack[1].m_num;
size_t v_stop_4629_ = stack[2].m_num;
lean_object* v_b_4630_ = stack[3].m_obj;
lean_object* v_res_4649_;
v_res_4649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4627_, v_i_4628_, v_stop_4629_, v_b_4630_);
stack->m_obj
 = v_res_4649_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg___boxed(lean_object* v_as_4650_, lean_object* v_i_4651_, lean_object* v_stop_4652_, lean_object* v_b_4653_){
_start:
{
size_t v_i_boxed_4654_; size_t v_stop_boxed_4655_; lean_object* v_res_4656_; 
v_i_boxed_4654_ = lean_unbox_usize(v_i_4651_);
lean_dec(v_i_4651_);
v_stop_boxed_4655_ = lean_unbox_usize(v_stop_4652_);
lean_dec(v_stop_4652_);
v_res_4656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4650_, v_i_boxed_4654_, v_stop_boxed_4655_, v_b_4653_);
lean_dec_ref(v_as_4650_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg(lean_object* v_as_4657_){
_start:
{
lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; uint8_t v___x_4661_; 
v___x_4658_ = lean_unsigned_to_nat(0u);
v___x_4659_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v___x_4660_ = lean_array_get_size(v_as_4657_);
v___x_4661_ = lean_nat_dec_lt(v___x_4658_, v___x_4660_);
if (v___x_4661_ == 0)
{
return v___x_4659_;
}
else
{
uint8_t v___x_4662_; 
v___x_4662_ = lean_nat_dec_le(v___x_4660_, v___x_4660_);
if (v___x_4662_ == 0)
{
if (v___x_4661_ == 0)
{
return v___x_4659_;
}
else
{
size_t v___x_4663_; size_t v___x_4664_; lean_object* v___x_4665_; 
v___x_4663_ = ((size_t)0ULL);
v___x_4664_ = lean_usize_of_nat(v___x_4660_);
v___x_4665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4657_, v___x_4663_, v___x_4664_, v___x_4659_);
return v___x_4665_;
}
}
else
{
size_t v___x_4666_; size_t v___x_4667_; lean_object* v___x_4668_; 
v___x_4666_ = ((size_t)0ULL);
v___x_4667_ = lean_usize_of_nat(v___x_4660_);
v___x_4668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4657_, v___x_4666_, v___x_4667_, v___x_4659_);
return v___x_4668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg___boxed(lean_object* v_as_4669_){
_start:
{
lean_object* v_res_4670_; 
v_res_4670_ = l_Array_unzip___redArg(v_as_4669_);
lean_dec_ref(v_as_4669_);
return v_res_4670_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip(lean_object* v_00_u03b1_4671_, lean_object* v_00_u03b2_4672_, lean_object* v_as_4673_){
_start:
{
lean_object* v___x_4674_; 
v___x_4674_ = l_Array_unzip___redArg(v_as_4673_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___boxed(lean_object* v_00_u03b1_4675_, lean_object* v_00_u03b2_4676_, lean_object* v_as_4677_){
_start:
{
lean_object* v_res_4678_; 
v_res_4678_ = l_Array_unzip(v_00_u03b1_4675_, v_00_u03b2_4676_, v_as_4677_);
lean_dec_ref(v_as_4677_);
return v_res_4678_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(lean_object* v_00_u03b1_4679_, lean_object* v_00_u03b2_4680_, lean_object* v_as_4681_, size_t v_i_4682_, size_t v_stop_4683_, lean_object* v_b_4684_){
_start:
{
lean_object* v___x_4685_; 
v___x_4685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4681_, v_i_4682_, v_stop_4683_, v_b_4684_);
return v___x_4685_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4681_ = stack[2].m_obj;
size_t v_i_4682_ = stack[3].m_num;
size_t v_stop_4683_ = stack[4].m_num;
lean_object* v_b_4684_ = stack[5].m_obj;
lean_object* v_res_4686_;
v_res_4686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(lean_box(0), lean_box(0), v_as_4681_, v_i_4682_, v_stop_4683_, v_b_4684_);
stack->m_obj
 = v_res_4686_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___boxed(lean_object* v_00_u03b1_4687_, lean_object* v_00_u03b2_4688_, lean_object* v_as_4689_, lean_object* v_i_4690_, lean_object* v_stop_4691_, lean_object* v_b_4692_){
_start:
{
size_t v_i_boxed_4693_; size_t v_stop_boxed_4694_; lean_object* v_res_4695_; 
v_i_boxed_4693_ = lean_unbox_usize(v_i_4690_);
lean_dec(v_i_4690_);
v_stop_boxed_4694_ = lean_unbox_usize(v_stop_4691_);
lean_dec(v_stop_4691_);
v_res_4695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(v_00_u03b1_4687_, v_00_u03b2_4688_, v_as_4689_, v_i_boxed_4693_, v_stop_boxed_4694_, v_b_4692_);
lean_dec_ref(v_as_4689_);
return v_res_4695_;
}
}
LEAN_EXPORT lean_object* l_Array_replace___redArg(lean_object* v_inst_4696_, lean_object* v_xs_4697_, lean_object* v_a_4698_, lean_object* v_b_4699_){
_start:
{
lean_object* v___x_4700_; 
v___x_4700_ = l_Array_finIdxOf_x3f___redArg(v_inst_4696_, v_xs_4697_, v_a_4698_);
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_dec(v_b_4699_);
return v_xs_4697_;
}
else
{
lean_object* v_val_4701_; lean_object* v___x_4702_; 
v_val_4701_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_val_4701_);
lean_dec_ref_known(v___x_4700_, 1);
v___x_4702_ = lean_array_fset(v_xs_4697_, v_val_4701_, v_b_4699_);
lean_dec(v_val_4701_);
return v___x_4702_;
}
}
}
LEAN_EXPORT lean_object* l_Array_replace(lean_object* v_00_u03b1_4703_, lean_object* v_inst_4704_, lean_object* v_xs_4705_, lean_object* v_a_4706_, lean_object* v_b_4707_){
_start:
{
lean_object* v___x_4708_; 
v___x_4708_ = l_Array_replace___redArg(v_inst_4704_, v_xs_4705_, v_a_4706_, v_b_4707_);
return v___x_4708_;
}
}
lean_object* l_Array_instLT___redArg(){
_start:
{
lean_object* v___x_4710_; 
v___x_4710_ = lean_box(0);
return v___x_4710_;
}
}
LEAN_EXPORT void l_Array_instLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4711_;
v_res_4711_ = l_Array_instLT___redArg();
stack->m_obj
 = v_res_4711_;
}
LEAN_EXPORT lean_object* l_Array_instLT___redArg___boxed(lean_object* v___dummy_4712_){
_start:
{
lean_object* v_res_4713_; 
v_res_4713_ = l_Array_instLT___redArg();
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l_Array_instLT(lean_object* v_00_u03b1_4714_, lean_object* v_inst_4715_){
_start:
{
lean_object* v___x_4716_; 
v___x_4716_ = lean_box(0);
return v___x_4716_;
}
}
lean_object* l_Array_instLE___redArg(){
_start:
{
lean_object* v___x_4718_; 
v___x_4718_ = lean_box(0);
return v___x_4718_;
}
}
LEAN_EXPORT void l_Array_instLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4719_;
v_res_4719_ = l_Array_instLE___redArg();
stack->m_obj
 = v_res_4719_;
}
LEAN_EXPORT lean_object* l_Array_instLE___redArg___boxed(lean_object* v___dummy_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l_Array_instLE___redArg();
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l_Array_instLE(lean_object* v_00_u03b1_4722_, lean_object* v_inst_4723_){
_start:
{
lean_object* v___x_4724_; 
v___x_4724_ = lean_box(0);
return v___x_4724_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg(lean_object* v_n_4725_, lean_object* v_a_4726_, lean_object* v_xs_4727_){
_start:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; 
v___x_4728_ = lean_array_get_size(v_xs_4727_);
v___x_4729_ = lean_nat_sub(v_n_4725_, v___x_4728_);
v___x_4730_ = lean_mk_array(v___x_4729_, v_a_4726_);
v___x_4731_ = l_Array_append___redArg(v___x_4730_, v_xs_4727_);
return v___x_4731_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg___boxed(lean_object* v_n_4732_, lean_object* v_a_4733_, lean_object* v_xs_4734_){
_start:
{
lean_object* v_res_4735_; 
v_res_4735_ = l_Array_leftpad___redArg(v_n_4732_, v_a_4733_, v_xs_4734_);
lean_dec_ref(v_xs_4734_);
lean_dec(v_n_4732_);
return v_res_4735_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad(lean_object* v_00_u03b1_4736_, lean_object* v_n_4737_, lean_object* v_a_4738_, lean_object* v_xs_4739_){
_start:
{
lean_object* v___x_4740_; 
v___x_4740_ = l_Array_leftpad___redArg(v_n_4737_, v_a_4738_, v_xs_4739_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___boxed(lean_object* v_00_u03b1_4741_, lean_object* v_n_4742_, lean_object* v_a_4743_, lean_object* v_xs_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l_Array_leftpad(v_00_u03b1_4741_, v_n_4742_, v_a_4743_, v_xs_4744_);
lean_dec_ref(v_xs_4744_);
lean_dec(v_n_4742_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg(lean_object* v_n_4746_, lean_object* v_a_4747_, lean_object* v_xs_4748_){
_start:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4749_ = lean_array_get_size(v_xs_4748_);
v___x_4750_ = lean_nat_sub(v_n_4746_, v___x_4749_);
v___x_4751_ = lean_mk_array(v___x_4750_, v_a_4747_);
v___x_4752_ = l_Array_append___redArg(v_xs_4748_, v___x_4751_);
lean_dec_ref(v___x_4751_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg___boxed(lean_object* v_n_4753_, lean_object* v_a_4754_, lean_object* v_xs_4755_){
_start:
{
lean_object* v_res_4756_; 
v_res_4756_ = l_Array_rightpad___redArg(v_n_4753_, v_a_4754_, v_xs_4755_);
lean_dec(v_n_4753_);
return v_res_4756_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad(lean_object* v_00_u03b1_4757_, lean_object* v_n_4758_, lean_object* v_a_4759_, lean_object* v_xs_4760_){
_start:
{
lean_object* v___x_4761_; 
v___x_4761_ = l_Array_rightpad___redArg(v_n_4758_, v_a_4759_, v_xs_4760_);
return v___x_4761_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___boxed(lean_object* v_00_u03b1_4762_, lean_object* v_n_4763_, lean_object* v_a_4764_, lean_object* v_xs_4765_){
_start:
{
lean_object* v_res_4766_; 
v_res_4766_ = l_Array_rightpad(v_00_u03b1_4762_, v_n_4763_, v_a_4764_, v_xs_4765_);
lean_dec(v_n_4763_);
return v_res_4766_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0(lean_object* v_x_4767_){
_start:
{
lean_inc(v_x_4767_);
return v_x_4767_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0___boxed(lean_object* v_x_4768_){
_start:
{
lean_object* v_res_4769_; 
v_res_4769_ = l_Array_reduceOption___redArg___lam__0(v_x_4768_);
lean_dec(v_x_4768_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg(lean_object* v_as_4771_){
_start:
{
lean_object* v___f_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; 
v___f_4772_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4773_ = lean_unsigned_to_nat(0u);
v___x_4774_ = lean_array_get_size(v_as_4771_);
v___x_4775_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4776_ = l_Array_filterMapM___redArg(v___x_4775_, v___f_4772_, v_as_4771_, v___x_4773_, v___x_4774_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption(lean_object* v_00_u03b1_4777_, lean_object* v_as_4778_){
_start:
{
lean_object* v___f_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___f_4779_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4780_ = lean_unsigned_to_nat(0u);
v___x_4781_ = lean_array_get_size(v_as_4778_);
v___x_4782_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4783_ = l_Array_filterMapM___redArg(v___x_4782_, v___f_4779_, v_as_4778_, v___x_4780_, v___x_4781_);
return v___x_4783_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg___lam__0(lean_object* v_inst_4784_, lean_object* v_x1_4785_, lean_object* v_x2_4786_){
_start:
{
lean_object* v_fst_4787_; lean_object* v_snd_4788_; lean_object* v___x_4789_; uint8_t v___x_4790_; 
v_fst_4787_ = lean_ctor_get(v_x1_4785_, 0);
v_snd_4788_ = lean_ctor_get(v_x1_4785_, 1);
lean_inc(v_fst_4787_);
lean_inc(v_x2_4786_);
v___x_4789_ = lean_apply_2(v_inst_4784_, v_x2_4786_, v_fst_4787_);
v___x_4790_ = lean_unbox(v___x_4789_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4798_; 
lean_inc(v_snd_4788_);
lean_inc(v_fst_4787_);
v_isSharedCheck_4798_ = !lean_is_exclusive(v_x1_4785_);
if (v_isSharedCheck_4798_ == 0)
{
lean_object* v_unused_4799_; lean_object* v_unused_4800_; 
v_unused_4799_ = lean_ctor_get(v_x1_4785_, 1);
lean_dec(v_unused_4799_);
v_unused_4800_ = lean_ctor_get(v_x1_4785_, 0);
lean_dec(v_unused_4800_);
v___x_4792_ = v_x1_4785_;
v_isShared_4793_ = v_isSharedCheck_4798_;
goto v_resetjp_4791_;
}
else
{
lean_dec(v_x1_4785_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4798_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4794_; lean_object* v___x_4796_; 
v___x_4794_ = lean_array_push(v_snd_4788_, v_fst_4787_);
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 1, v___x_4794_);
lean_ctor_set(v___x_4792_, 0, v_x2_4786_);
v___x_4796_ = v___x_4792_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_x2_4786_);
lean_ctor_set(v_reuseFailAlloc_4797_, 1, v___x_4794_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
}
else
{
lean_dec(v_x2_4786_);
return v_x1_4785_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg(lean_object* v_inst_4801_, lean_object* v_as_4802_){
_start:
{
lean_object* v___y_4804_; lean_object* v___x_4808_; lean_object* v___x_4809_; uint8_t v___x_4810_; 
v___x_4808_ = lean_unsigned_to_nat(0u);
v___x_4809_ = lean_array_get_size(v_as_4802_);
v___x_4810_ = lean_nat_dec_lt(v___x_4808_, v___x_4809_);
if (v___x_4810_ == 0)
{
lean_object* v___x_4811_; 
lean_dec_ref(v_as_4802_);
lean_dec_ref(v_inst_4801_);
v___x_4811_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
return v___x_4811_;
}
else
{
lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
v___x_4812_ = lean_array_fget_borrowed(v_as_4802_, v___x_4808_);
v___x_4813_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4814_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
if (v___x_4810_ == 0)
{
lean_object* v___x_4815_; 
lean_inc(v___x_4812_);
lean_dec_ref(v_as_4802_);
lean_dec_ref(v_inst_4801_);
v___x_4815_ = lean_array_push(v___x_4813_, v___x_4812_);
return v___x_4815_;
}
else
{
lean_object* v___f_4816_; lean_object* v___x_4817_; uint8_t v___x_4818_; 
v___f_4816_ = lean_alloc_closure((void*)(l_Array_eraseReps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4816_, 0, v_inst_4801_);
lean_inc(v___x_4812_);
v___x_4817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4817_, 0, v___x_4812_);
lean_ctor_set(v___x_4817_, 1, v___x_4813_);
v___x_4818_ = lean_nat_dec_le(v___x_4809_, v___x_4809_);
if (v___x_4818_ == 0)
{
if (v___x_4810_ == 0)
{
lean_object* v___x_4819_; 
lean_inc(v___x_4812_);
lean_dec_ref_known(v___x_4817_, 2);
lean_dec_ref(v___f_4816_);
lean_dec_ref(v_as_4802_);
v___x_4819_ = lean_array_push(v___x_4813_, v___x_4812_);
return v___x_4819_;
}
else
{
size_t v___x_4820_; size_t v___x_4821_; lean_object* v___x_4822_; 
v___x_4820_ = ((size_t)0ULL);
v___x_4821_ = lean_usize_of_nat(v___x_4809_);
v___x_4822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4814_, v___f_4816_, v_as_4802_, v___x_4820_, v___x_4821_, v___x_4817_);
v___y_4804_ = v___x_4822_;
goto v___jp_4803_;
}
}
else
{
size_t v___x_4823_; size_t v___x_4824_; lean_object* v___x_4825_; 
v___x_4823_ = ((size_t)0ULL);
v___x_4824_ = lean_usize_of_nat(v___x_4809_);
v___x_4825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4814_, v___f_4816_, v_as_4802_, v___x_4823_, v___x_4824_, v___x_4817_);
v___y_4804_ = v___x_4825_;
goto v___jp_4803_;
}
}
}
v___jp_4803_:
{
lean_object* v_fst_4805_; lean_object* v_snd_4806_; lean_object* v___x_4807_; 
v_fst_4805_ = lean_ctor_get(v___y_4804_, 0);
lean_inc(v_fst_4805_);
v_snd_4806_ = lean_ctor_get(v___y_4804_, 1);
lean_inc(v_snd_4806_);
lean_dec_ref(v___y_4804_);
v___x_4807_ = lean_array_push(v_snd_4806_, v_fst_4805_);
return v___x_4807_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps(lean_object* v_00_u03b1_4826_, lean_object* v_inst_4827_, lean_object* v_as_4828_){
_start:
{
lean_object* v___x_4829_; 
v___x_4829_ = l_Array_eraseReps___redArg(v_inst_4827_, v_as_4828_);
return v___x_4829_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(lean_object* v_inst_4830_, lean_object* v_as_4831_, lean_object* v_a_4832_, lean_object* v_x_4833_){
_start:
{
lean_object* v_zero_4834_; uint8_t v_isZero_4835_; 
v_zero_4834_ = lean_unsigned_to_nat(0u);
v_isZero_4835_ = lean_nat_dec_eq(v_x_4833_, v_zero_4834_);
if (v_isZero_4835_ == 1)
{
lean_dec(v_x_4833_);
lean_dec(v_a_4832_);
lean_dec_ref(v_inst_4830_);
return v_isZero_4835_;
}
else
{
lean_object* v_one_4836_; lean_object* v_n_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; uint8_t v___x_4840_; 
v_one_4836_ = lean_unsigned_to_nat(1u);
v_n_4837_ = lean_nat_sub(v_x_4833_, v_one_4836_);
lean_dec(v_x_4833_);
v___x_4838_ = lean_array_fget_borrowed(v_as_4831_, v_n_4837_);
lean_inc_ref(v_inst_4830_);
lean_inc(v___x_4838_);
lean_inc(v_a_4832_);
v___x_4839_ = lean_apply_2(v_inst_4830_, v_a_4832_, v___x_4838_);
v___x_4840_ = lean_unbox(v___x_4839_);
if (v___x_4840_ == 0)
{
v_x_4833_ = v_n_4837_;
goto _start;
}
else
{
lean_dec(v_n_4837_);
lean_dec(v_a_4832_);
lean_dec_ref(v_inst_4830_);
return v_isZero_4835_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4830_ = stack[0].m_obj;
lean_object* v_as_4831_ = stack[1].m_obj;
lean_object* v_a_4832_ = stack[2].m_obj;
lean_object* v_x_4833_ = stack[3].m_obj;
uint8_t v_res_4842_;
v_res_4842_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4830_, v_as_4831_, v_a_4832_, v_x_4833_);
stack->m_num = v_res_4842_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg___boxed(lean_object* v_inst_4843_, lean_object* v_as_4844_, lean_object* v_a_4845_, lean_object* v_x_4846_){
_start:
{
uint8_t v_res_4847_; lean_object* v_r_4848_; 
v_res_4847_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4843_, v_as_4844_, v_a_4845_, v_x_4846_);
lean_dec_ref(v_as_4844_);
v_r_4848_ = lean_box(v_res_4847_);
return v_r_4848_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(lean_object* v_00_u03b1_4849_, lean_object* v_inst_4850_, lean_object* v_as_4851_, lean_object* v_a_4852_, lean_object* v_x_4853_, lean_object* v_x_4854_){
_start:
{
uint8_t v___x_4855_; 
v___x_4855_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4850_, v_as_4851_, v_a_4852_, v_x_4853_);
return v___x_4855_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4850_ = stack[1].m_obj;
lean_object* v_as_4851_ = stack[2].m_obj;
lean_object* v_a_4852_ = stack[3].m_obj;
lean_object* v_x_4853_ = stack[4].m_obj;
uint8_t v_res_4856_;
v_res_4856_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(lean_box(0), v_inst_4850_, v_as_4851_, v_a_4852_, v_x_4853_, lean_box(0));
stack->m_num = v_res_4856_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___boxed(lean_object* v_00_u03b1_4857_, lean_object* v_inst_4858_, lean_object* v_as_4859_, lean_object* v_a_4860_, lean_object* v_x_4861_, lean_object* v_x_4862_){
_start:
{
uint8_t v_res_4863_; lean_object* v_r_4864_; 
v_res_4863_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(v_00_u03b1_4857_, v_inst_4858_, v_as_4859_, v_a_4860_, v_x_4861_, v_x_4862_);
lean_dec_ref(v_as_4859_);
v_r_4864_ = lean_box(v_res_4863_);
return v_r_4864_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(lean_object* v_inst_4865_, lean_object* v_as_4866_, lean_object* v_i_4867_){
_start:
{
lean_object* v___x_4868_; uint8_t v___x_4869_; 
v___x_4868_ = lean_array_get_size(v_as_4866_);
v___x_4869_ = lean_nat_dec_lt(v_i_4867_, v___x_4868_);
if (v___x_4869_ == 0)
{
uint8_t v___x_4870_; 
lean_dec(v_i_4867_);
lean_dec_ref(v_inst_4865_);
v___x_4870_ = 1;
return v___x_4870_;
}
else
{
lean_object* v___x_4871_; uint8_t v___x_4872_; 
v___x_4871_ = lean_array_fget_borrowed(v_as_4866_, v_i_4867_);
lean_inc(v_i_4867_);
lean_inc(v___x_4871_);
lean_inc_ref(v_inst_4865_);
v___x_4872_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4865_, v_as_4866_, v___x_4871_, v_i_4867_);
if (v___x_4872_ == 0)
{
lean_dec(v_i_4867_);
lean_dec_ref(v_inst_4865_);
return v___x_4872_;
}
else
{
lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = lean_unsigned_to_nat(1u);
v___x_4874_ = lean_nat_add(v_i_4867_, v___x_4873_);
lean_dec(v_i_4867_);
v_i_4867_ = v___x_4874_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4865_ = stack[0].m_obj;
lean_object* v_as_4866_ = stack[1].m_obj;
lean_object* v_i_4867_ = stack[2].m_obj;
uint8_t v_res_4876_;
v_res_4876_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4865_, v_as_4866_, v_i_4867_);
stack->m_num = v_res_4876_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg___boxed(lean_object* v_inst_4877_, lean_object* v_as_4878_, lean_object* v_i_4879_){
_start:
{
uint8_t v_res_4880_; lean_object* v_r_4881_; 
v_res_4880_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4877_, v_as_4878_, v_i_4879_);
lean_dec_ref(v_as_4878_);
v_r_4881_ = lean_box(v_res_4880_);
return v_r_4881_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux(lean_object* v_00_u03b1_4882_, lean_object* v_inst_4883_, lean_object* v_as_4884_, lean_object* v_i_4885_){
_start:
{
uint8_t v___x_4886_; 
v___x_4886_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4883_, v_as_4884_, v_i_4885_);
return v___x_4886_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_allDiffAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4883_ = stack[1].m_obj;
lean_object* v_as_4884_ = stack[2].m_obj;
lean_object* v_i_4885_ = stack[3].m_obj;
uint8_t v_res_4887_;
v_res_4887_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux(lean_box(0), v_inst_4883_, v_as_4884_, v_i_4885_);
stack->m_num = v_res_4887_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___boxed(lean_object* v_00_u03b1_4888_, lean_object* v_inst_4889_, lean_object* v_as_4890_, lean_object* v_i_4891_){
_start:
{
uint8_t v_res_4892_; lean_object* v_r_4893_; 
v_res_4892_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux(v_00_u03b1_4888_, v_inst_4889_, v_as_4890_, v_i_4891_);
lean_dec_ref(v_as_4890_);
v_r_4893_ = lean_box(v_res_4892_);
return v_r_4893_;
}
}
uint8_t l_Array_allDiff___redArg(lean_object* v_inst_4894_, lean_object* v_as_4895_){
_start:
{
lean_object* v___x_4896_; uint8_t v___x_4897_; 
v___x_4896_ = lean_unsigned_to_nat(0u);
v___x_4897_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4894_, v_as_4895_, v___x_4896_);
return v___x_4897_;
}
}
LEAN_EXPORT void l_Array_allDiff___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4894_ = stack[0].m_obj;
lean_object* v_as_4895_ = stack[1].m_obj;
uint8_t v_res_4898_;
v_res_4898_ = l_Array_allDiff___redArg(v_inst_4894_, v_as_4895_);
stack->m_num = v_res_4898_;
}
LEAN_EXPORT lean_object* l_Array_allDiff___redArg___boxed(lean_object* v_inst_4899_, lean_object* v_as_4900_){
_start:
{
uint8_t v_res_4901_; lean_object* v_r_4902_; 
v_res_4901_ = l_Array_allDiff___redArg(v_inst_4899_, v_as_4900_);
lean_dec_ref(v_as_4900_);
v_r_4902_ = lean_box(v_res_4901_);
return v_r_4902_;
}
}
uint8_t l_Array_allDiff(lean_object* v_00_u03b1_4903_, lean_object* v_inst_4904_, lean_object* v_as_4905_){
_start:
{
uint8_t v___x_4906_; 
v___x_4906_ = l_Array_allDiff___redArg(v_inst_4904_, v_as_4905_);
return v___x_4906_;
}
}
LEAN_EXPORT void l_Array_allDiff_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4904_ = stack[1].m_obj;
lean_object* v_as_4905_ = stack[2].m_obj;
uint8_t v_res_4907_;
v_res_4907_ = l_Array_allDiff(lean_box(0), v_inst_4904_, v_as_4905_);
stack->m_num = v_res_4907_;
}
LEAN_EXPORT lean_object* l_Array_allDiff___boxed(lean_object* v_00_u03b1_4908_, lean_object* v_inst_4909_, lean_object* v_as_4910_){
_start:
{
uint8_t v_res_4911_; lean_object* v_r_4912_; 
v_res_4911_ = l_Array_allDiff(v_00_u03b1_4908_, v_inst_4909_, v_as_4910_);
lean_dec_ref(v_as_4910_);
v_r_4912_ = lean_box(v_res_4911_);
return v_r_4912_;
}
}
lean_object* l_Array_getEvenElems___redArg___lam__0(uint8_t v___x_4913_, lean_object* v_x1_4914_, lean_object* v_x2_4915_){
_start:
{
lean_object* v_fst_4916_; uint8_t v___x_4917_; 
v_fst_4916_ = lean_ctor_get(v_x1_4914_, 0);
v___x_4917_ = lean_unbox(v_fst_4916_);
if (v___x_4917_ == 0)
{
lean_object* v_snd_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4926_; 
lean_dec(v_x2_4915_);
v_snd_4918_ = lean_ctor_get(v_x1_4914_, 1);
v_isSharedCheck_4926_ = !lean_is_exclusive(v_x1_4914_);
if (v_isSharedCheck_4926_ == 0)
{
lean_object* v_unused_4927_; 
v_unused_4927_ = lean_ctor_get(v_x1_4914_, 0);
lean_dec(v_unused_4927_);
v___x_4920_ = v_x1_4914_;
v_isShared_4921_ = v_isSharedCheck_4926_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_snd_4918_);
lean_dec(v_x1_4914_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4926_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4922_; lean_object* v___x_4924_; 
v___x_4922_ = lean_box(v___x_4913_);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 0, v___x_4922_);
v___x_4924_ = v___x_4920_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v___x_4922_);
lean_ctor_set(v_reuseFailAlloc_4925_, 1, v_snd_4918_);
v___x_4924_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
return v___x_4924_;
}
}
}
else
{
lean_object* v_snd_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4938_; 
v_snd_4928_ = lean_ctor_get(v_x1_4914_, 1);
v_isSharedCheck_4938_ = !lean_is_exclusive(v_x1_4914_);
if (v_isSharedCheck_4938_ == 0)
{
lean_object* v_unused_4939_; 
v_unused_4939_ = lean_ctor_get(v_x1_4914_, 0);
lean_dec(v_unused_4939_);
v___x_4930_ = v_x1_4914_;
v_isShared_4931_ = v_isSharedCheck_4938_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_snd_4928_);
lean_dec(v_x1_4914_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4938_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
uint8_t v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4936_; 
v___x_4932_ = 0;
v___x_4933_ = lean_array_push(v_snd_4928_, v_x2_4915_);
v___x_4934_ = lean_box(v___x_4932_);
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 1, v___x_4933_);
lean_ctor_set(v___x_4930_, 0, v___x_4934_);
v___x_4936_ = v___x_4930_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v___x_4934_);
lean_ctor_set(v_reuseFailAlloc_4937_, 1, v___x_4933_);
v___x_4936_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
return v___x_4936_;
}
}
}
}
}
LEAN_EXPORT void l_Array_getEvenElems___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_4913_ = stack[0].m_num;
lean_object* v_x1_4914_ = stack[1].m_obj;
lean_object* v_x2_4915_ = stack[2].m_obj;
lean_object* v_res_4940_;
v_res_4940_ = l_Array_getEvenElems___redArg___lam__0(v___x_4913_, v_x1_4914_, v_x2_4915_);
stack->m_obj
 = v_res_4940_;
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0___boxed(lean_object* v___x_4941_, lean_object* v_x1_4942_, lean_object* v_x2_4943_){
_start:
{
uint8_t v___x_141__boxed_4944_; lean_object* v_res_4945_; 
v___x_141__boxed_4944_ = lean_unbox(v___x_4941_);
v_res_4945_ = l_Array_getEvenElems___redArg___lam__0(v___x_141__boxed_4944_, v_x1_4942_, v_x2_4943_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg(lean_object* v_as_4946_){
_start:
{
lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; uint8_t v___x_4951_; 
v___x_4947_ = lean_unsigned_to_nat(0u);
v___x_4948_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_4949_ = lean_array_get_size(v_as_4946_);
v___x_4950_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4951_ = lean_nat_dec_lt(v___x_4947_, v___x_4949_);
if (v___x_4951_ == 0)
{
lean_dec_ref(v_as_4946_);
return v___x_4948_;
}
else
{
lean_object* v___x_4952_; lean_object* v___f_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; uint8_t v___x_4956_; 
v___x_4952_ = lean_box(v___x_4951_);
v___f_4953_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4953_, 0, v___x_4952_);
v___x_4954_ = lean_box(v___x_4951_);
v___x_4955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4954_);
lean_ctor_set(v___x_4955_, 1, v___x_4948_);
v___x_4956_ = lean_nat_dec_le(v___x_4949_, v___x_4949_);
if (v___x_4956_ == 0)
{
if (v___x_4951_ == 0)
{
lean_dec_ref_known(v___x_4955_, 2);
lean_dec_ref(v___f_4953_);
lean_dec_ref(v_as_4946_);
return v___x_4948_;
}
else
{
size_t v___x_4957_; size_t v___x_4958_; lean_object* v___x_4959_; lean_object* v_snd_4960_; 
v___x_4957_ = ((size_t)0ULL);
v___x_4958_ = lean_usize_of_nat(v___x_4949_);
v___x_4959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4950_, v___f_4953_, v_as_4946_, v___x_4957_, v___x_4958_, v___x_4955_);
v_snd_4960_ = lean_ctor_get(v___x_4959_, 1);
lean_inc(v_snd_4960_);
lean_dec(v___x_4959_);
return v_snd_4960_;
}
}
else
{
size_t v___x_4961_; size_t v___x_4962_; lean_object* v___x_4963_; lean_object* v_snd_4964_; 
v___x_4961_ = ((size_t)0ULL);
v___x_4962_ = lean_usize_of_nat(v___x_4949_);
v___x_4963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4950_, v___f_4953_, v_as_4946_, v___x_4961_, v___x_4962_, v___x_4955_);
v_snd_4964_ = lean_ctor_get(v___x_4963_, 1);
lean_inc(v_snd_4964_);
lean_dec(v___x_4963_);
return v_snd_4964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems(lean_object* v_00_u03b1_4965_, lean_object* v_as_4966_){
_start:
{
lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; uint8_t v___x_4971_; 
v___x_4967_ = lean_unsigned_to_nat(0u);
v___x_4968_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_4969_ = lean_array_get_size(v_as_4966_);
v___x_4970_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4971_ = lean_nat_dec_lt(v___x_4967_, v___x_4969_);
if (v___x_4971_ == 0)
{
lean_dec_ref(v_as_4966_);
return v___x_4968_;
}
else
{
lean_object* v___x_4972_; lean_object* v___f_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; uint8_t v___x_4976_; 
v___x_4972_ = lean_box(v___x_4971_);
v___f_4973_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4973_, 0, v___x_4972_);
v___x_4974_ = lean_box(v___x_4971_);
v___x_4975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4975_, 0, v___x_4974_);
lean_ctor_set(v___x_4975_, 1, v___x_4968_);
v___x_4976_ = lean_nat_dec_le(v___x_4969_, v___x_4969_);
if (v___x_4976_ == 0)
{
if (v___x_4971_ == 0)
{
lean_dec_ref_known(v___x_4975_, 2);
lean_dec_ref(v___f_4973_);
lean_dec_ref(v_as_4966_);
return v___x_4968_;
}
else
{
size_t v___x_4977_; size_t v___x_4978_; lean_object* v___x_4979_; lean_object* v_snd_4980_; 
v___x_4977_ = ((size_t)0ULL);
v___x_4978_ = lean_usize_of_nat(v___x_4969_);
v___x_4979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4970_, v___f_4973_, v_as_4966_, v___x_4977_, v___x_4978_, v___x_4975_);
v_snd_4980_ = lean_ctor_get(v___x_4979_, 1);
lean_inc(v_snd_4980_);
lean_dec(v___x_4979_);
return v_snd_4980_;
}
}
else
{
size_t v___x_4981_; size_t v___x_4982_; lean_object* v___x_4983_; lean_object* v_snd_4984_; 
v___x_4981_ = ((size_t)0ULL);
v___x_4982_ = lean_usize_of_nat(v___x_4969_);
v___x_4983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4970_, v___f_4973_, v_as_4966_, v___x_4981_, v___x_4982_, v___x_4975_);
v_snd_4984_ = lean_ctor_get(v___x_4983_, 1);
lean_inc(v_snd_4984_);
lean_dec(v___x_4983_);
return v_snd_4984_;
}
}
}
}
static lean_object* _init_l_Array_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_4990_; lean_object* v___x_4991_; 
v___x_4990_ = ((lean_object*)(l_term_x23_x5b___x2c_x5d___closed__4));
v___x_4991_ = lean_string_length(v___x_4990_);
return v___x_4991_;
}
}
static lean_object* _init_l_Array_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; 
v___x_4992_ = lean_obj_once(&l_Array_repr___redArg___closed__2, &l_Array_repr___redArg___closed__2_once, _init_l_Array_repr___redArg___closed__2);
v___x_4993_ = lean_nat_to_int(v___x_4992_);
return v___x_4993_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___redArg(lean_object* v_inst_5001_, lean_object* v_xs_5002_){
_start:
{
lean_object* v___x_5003_; lean_object* v___x_5004_; uint8_t v___x_5005_; 
v___x_5003_ = lean_array_get_size(v_xs_5002_);
v___x_5004_ = lean_unsigned_to_nat(0u);
v___x_5005_ = lean_nat_dec_eq(v___x_5003_, v___x_5004_);
if (v___x_5005_ == 0)
{
lean_object* v_x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
v_x_5006_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_5006_, 0, lean_box(0));
lean_closure_set(v_x_5006_, 1, v_inst_5001_);
v___x_5007_ = lean_array_to_list(v_xs_5002_);
v___x_5008_ = ((lean_object*)(l_Array_repr___redArg___closed__1));
v___x_5009_ = l_Std_Format_joinSep___redArg(v_x_5006_, v___x_5007_, v___x_5008_);
v___x_5010_ = lean_obj_once(&l_Array_repr___redArg___closed__3, &l_Array_repr___redArg___closed__3_once, _init_l_Array_repr___redArg___closed__3);
v___x_5011_ = ((lean_object*)(l_Array_repr___redArg___closed__4));
v___x_5012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5012_, 0, v___x_5011_);
lean_ctor_set(v___x_5012_, 1, v___x_5009_);
v___x_5013_ = ((lean_object*)(l_Array_repr___redArg___closed__5));
v___x_5014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5014_, 0, v___x_5012_);
lean_ctor_set(v___x_5014_, 1, v___x_5013_);
v___x_5015_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5015_, 0, v___x_5010_);
lean_ctor_set(v___x_5015_, 1, v___x_5014_);
v___x_5016_ = l_Std_Format_fill(v___x_5015_);
return v___x_5016_;
}
else
{
lean_object* v___x_5017_; 
lean_dec_ref(v_xs_5002_);
lean_dec_ref(v_inst_5001_);
v___x_5017_ = ((lean_object*)(l_Array_repr___redArg___closed__7));
return v___x_5017_;
}
}
}
LEAN_EXPORT lean_object* l_Array_repr(lean_object* v_00_u03b1_5018_, lean_object* v_inst_5019_, lean_object* v_xs_5020_){
_start:
{
lean_object* v___x_5021_; 
v___x_5021_ = l_Array_repr___redArg(v_inst_5019_, v_xs_5020_);
return v___x_5021_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0(lean_object* v_inst_5022_, lean_object* v_xs_5023_, lean_object* v_x_5024_){
_start:
{
lean_object* v___x_5025_; 
v___x_5025_ = l_Array_repr___redArg(v_inst_5022_, v_xs_5023_);
return v___x_5025_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object* v_inst_5026_, lean_object* v_xs_5027_, lean_object* v_x_5028_){
_start:
{
lean_object* v_res_5029_; 
v_res_5029_ = l_Array_instRepr___redArg___lam__0(v_inst_5026_, v_xs_5027_, v_x_5028_);
lean_dec(v_x_5028_);
return v_res_5029_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg(lean_object* v_inst_5030_){
_start:
{
lean_object* v___f_5031_; 
v___f_5031_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5031_, 0, v_inst_5030_);
return v___f_5031_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr(lean_object* v_00_u03b1_5032_, lean_object* v_inst_5033_){
_start:
{
lean_object* v___f_5034_; 
v___f_5034_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5034_, 0, v_inst_5033_);
return v___f_5034_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
