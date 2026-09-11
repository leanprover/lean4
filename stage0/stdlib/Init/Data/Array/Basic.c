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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_instMembership___redArg(){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_box(0);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Array_instMembership___redArg___boxed(lean_object* v___dummy_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Array_instMembership___redArg();
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Array_instMembership(lean_object* v_00_u03b1_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_box(0);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter___redArg(lean_object* v_x_140_, lean_object* v_h__1_141_, lean_object* v_h__2_142_){
_start:
{
if (lean_obj_tag(v_x_140_) == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_dec(v_h__1_141_);
v___x_143_ = lean_box(0);
v___x_144_ = lean_apply_1(v_h__2_142_, v___x_143_);
return v___x_144_;
}
else
{
lean_object* v_val_145_; lean_object* v___x_146_; 
lean_dec(v_h__2_142_);
v_val_145_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_val_145_);
lean_dec_ref_known(v_x_140_, 1);
v___x_146_ = lean_apply_1(v_h__1_141_, v_val_145_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_147_, lean_object* v_motive_148_, lean_object* v_x_149_, lean_object* v_h__1_150_, lean_object* v_h__2_151_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec(v_h__1_150_);
v___x_152_ = lean_box(0);
v___x_153_ = lean_apply_1(v_h__2_151_, v___x_152_);
return v___x_153_;
}
else
{
lean_object* v_val_154_; lean_object* v___x_155_; 
lean_dec(v_h__2_151_);
v_val_154_ = lean_ctor_get(v_x_149_, 0);
lean_inc(v_val_154_);
lean_dec_ref_known(v_x_149_, 1);
v___x_155_ = lean_apply_1(v_h__1_150_, v_val_154_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Array_usize___boxed(lean_object* v_00_u03b1_158_, lean_object* v_xs_159_){
_start:
{
size_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = lean_array_size(v_xs_159_);
lean_dec_ref(v_xs_159_);
v_r_161_ = lean_box_usize(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_Array_uget___boxed(lean_object* v_00_u03b1_166_, lean_object* v_xs_167_, lean_object* v_i_168_, lean_object* v_h_169_){
_start:
{
size_t v_i_boxed_170_; lean_object* v_res_171_; 
v_i_boxed_170_ = lean_unbox_usize(v_i_168_);
lean_dec(v_i_168_);
v_res_171_ = lean_array_uget(v_xs_167_, v_i_boxed_170_);
lean_dec_ref(v_xs_167_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Array_ugetBorrowed___boxed(lean_object* v_00_u03b1_176_, lean_object* v_xs_177_, lean_object* v_i_178_, lean_object* v_h_179_){
_start:
{
size_t v_i_boxed_180_; lean_object* v_res_181_; 
v_i_boxed_180_ = lean_unbox_usize(v_i_178_);
lean_dec(v_i_178_);
v_res_181_ = lean_array_uget_borrowed(v_xs_177_, v_i_boxed_180_);
lean_dec_ref(v_xs_177_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Array_uset___boxed(lean_object* v_00_u03b1_187_, lean_object* v_xs_188_, lean_object* v_i_189_, lean_object* v_v_190_, lean_object* v_h_191_){
_start:
{
size_t v_i_boxed_192_; lean_object* v_res_193_; 
v_i_boxed_192_ = lean_unbox_usize(v_i_189_);
lean_dec(v_i_189_);
v_res_193_ = lean_array_uset(v_xs_188_, v_i_boxed_192_, v_v_190_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Array_pop___boxed(lean_object* v_00_u03b1_196_, lean_object* v_xs_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = lean_array_pop(v_xs_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Array_markLinear___boxed(lean_object* v_00_u03b1_201_, lean_object* v_xs_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = lean_array_mark_linear(v_xs_202_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Array_propagateMark___boxed(lean_object* v_00_u03b1_208_, lean_object* v_00_u03b2_209_, lean_object* v_xs_210_, lean_object* v_ys_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = lean_array_propagate_mark(v_xs_210_, v_ys_211_);
lean_dec_ref(v_xs_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Array_replicate___boxed(lean_object* v_00_u03b1_216_, lean_object* v_n_217_, lean_object* v_v_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = lean_mk_array(v_n_217_, v_v_218_);
return v_res_219_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__9(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = ((lean_object*)(l_Array_swap___auto__1___closed__8));
v___x_240_ = l_Lean_mkAtom(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__10(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_obj_once(&l_Array_swap___auto__1___closed__9, &l_Array_swap___auto__1___closed__9_once, _init_l_Array_swap___auto__1___closed__9);
v___x_242_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_243_ = lean_array_push(v___x_242_, v___x_241_);
return v___x_243_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__11(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_244_ = lean_obj_once(&l_Array_swap___auto__1___closed__10, &l_Array_swap___auto__1___closed__10_once, _init_l_Array_swap___auto__1___closed__10);
v___x_245_ = ((lean_object*)(l_Array_swap___auto__1___closed__7));
v___x_246_ = lean_box(2);
v___x_247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___x_245_);
lean_ctor_set(v___x_247_, 2, v___x_244_);
return v___x_247_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__12(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = lean_obj_once(&l_Array_swap___auto__1___closed__11, &l_Array_swap___auto__1___closed__11_once, _init_l_Array_swap___auto__1___closed__11);
v___x_249_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_250_ = lean_array_push(v___x_249_, v___x_248_);
return v___x_250_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__13(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_251_ = lean_obj_once(&l_Array_swap___auto__1___closed__12, &l_Array_swap___auto__1___closed__12_once, _init_l_Array_swap___auto__1___closed__12);
v___x_252_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13));
v___x_253_ = lean_box(2);
v___x_254_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_252_);
lean_ctor_set(v___x_254_, 2, v___x_251_);
return v___x_254_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__14(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = lean_obj_once(&l_Array_swap___auto__1___closed__13, &l_Array_swap___auto__1___closed__13_once, _init_l_Array_swap___auto__1___closed__13);
v___x_256_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_257_ = lean_array_push(v___x_256_, v___x_255_);
return v___x_257_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__15(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_258_ = lean_obj_once(&l_Array_swap___auto__1___closed__14, &l_Array_swap___auto__1___closed__14_once, _init_l_Array_swap___auto__1___closed__14);
v___x_259_ = ((lean_object*)(l_Array_swap___auto__1___closed__5));
v___x_260_ = lean_box(2);
v___x_261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_259_);
lean_ctor_set(v___x_261_, 2, v___x_258_);
return v___x_261_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__16(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_obj_once(&l_Array_swap___auto__1___closed__15, &l_Array_swap___auto__1___closed__15_once, _init_l_Array_swap___auto__1___closed__15);
v___x_263_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_264_ = lean_array_push(v___x_263_, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__17(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_265_ = lean_obj_once(&l_Array_swap___auto__1___closed__16, &l_Array_swap___auto__1___closed__16_once, _init_l_Array_swap___auto__1___closed__16);
v___x_266_ = ((lean_object*)(l_Array_swap___auto__1___closed__2));
v___x_267_ = lean_box(2);
v___x_268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
lean_ctor_set(v___x_268_, 2, v___x_265_);
return v___x_268_;
}
}
static lean_object* _init_l_Array_swap___auto__1(void){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_269_;
}
}
static lean_object* _init_l_Array_swap___auto__3(void){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Array_swap___boxed(lean_object* v_00_u03b1_277_, lean_object* v_xs_278_, lean_object* v_i_279_, lean_object* v_j_280_, lean_object* v_hi_281_, lean_object* v_hj_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = lean_array_fswap(v_xs_278_, v_i_279_, v_j_280_);
lean_dec(v_j_280_);
lean_dec(v_i_279_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Array_swapIfInBounds___boxed(lean_object* v_00_u03b1_288_, lean_object* v_xs_289_, lean_object* v_i_290_, lean_object* v_j_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = lean_array_swap(v_xs_289_, v_i_290_, v_j_291_);
lean_dec(v_j_291_);
lean_dec(v_i_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___redArg___lam__0(lean_object* v_xs_293_, size_t v_i_294_, lean_object* v_h_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lean_array_uget_borrowed(v_xs_293_, v_i_294_);
lean_inc(v___x_296_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___redArg___lam__0___boxed(lean_object* v_xs_297_, lean_object* v_i_298_, lean_object* v_h_299_){
_start:
{
size_t v_i_boxed_300_; lean_object* v_res_301_; 
v_i_boxed_300_ = lean_unbox_usize(v_i_298_);
lean_dec(v_i_298_);
v_res_301_ = l_Array_instGetElemUSizeLtNatToNatSize___redArg___lam__0(v_xs_297_, v_i_boxed_300_, v_h_299_);
lean_dec_ref(v_xs_297_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___redArg(){
_start:
{
lean_object* v___f_304_; 
v___f_304_ = ((lean_object*)(l_Array_instGetElemUSizeLtNatToNatSize___redArg___closed__0));
return v___f_304_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___redArg___boxed(lean_object* v___dummy_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Array_instGetElemUSizeLtNatToNatSize___redArg();
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize(lean_object* v_00_u03b1_307_){
_start:
{
lean_object* v___f_308_; 
v___f_308_ = ((lean_object*)(l_Array_instGetElemUSizeLtNatToNatSize___redArg___closed__0));
return v___f_308_;
}
}
LEAN_EXPORT lean_object* l_Array_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Array_instEmptyCollection___redArg___boxed(lean_object* v___dummy_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Array_instEmptyCollection___redArg();
return v_res_314_;
}
}
static lean_object* _init_l_Array_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Array_instEmptyCollection___redArg();
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Array_instEmptyCollection(lean_object* v_00_u03b1_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Array_instEmptyCollection___closed__0, &l_Array_instEmptyCollection___closed__0_once, _init_l_Array_instEmptyCollection___closed__0);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Array_instInhabited___redArg(){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Array_instInhabited___redArg___boxed(lean_object* v___dummy_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Array_instInhabited___redArg();
return v_res_321_;
}
}
static lean_object* _init_l_Array_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Array_instInhabited___redArg();
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Array_instInhabited(lean_object* v_00_u03b1_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lean_obj_once(&l_Array_instInhabited___closed__0, &l_Array_instInhabited___closed__0_once, _init_l_Array_instInhabited___closed__0);
return v___x_324_;
}
}
LEAN_EXPORT uint8_t l_Array_isEmpty___redArg(lean_object* v_xs_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_326_ = lean_array_get_size(v_xs_325_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_nat_dec_eq(v___x_326_, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Array_isEmpty___redArg___boxed(lean_object* v_xs_329_){
_start:
{
uint8_t v_res_330_; lean_object* v_r_331_; 
v_res_330_ = l_Array_isEmpty___redArg(v_xs_329_);
lean_dec_ref(v_xs_329_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT uint8_t l_Array_isEmpty(lean_object* v_00_u03b1_332_, lean_object* v_xs_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_334_ = lean_array_get_size(v_xs_333_);
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_nat_dec_eq(v___x_334_, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Array_isEmpty___boxed(lean_object* v_00_u03b1_337_, lean_object* v_xs_338_){
_start:
{
uint8_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = l_Array_isEmpty(v_00_u03b1_337_, v_xs_338_);
lean_dec_ref(v_xs_338_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___redArg(lean_object* v_xs_341_, lean_object* v_ys_342_, lean_object* v_p_343_, lean_object* v_x_344_){
_start:
{
lean_object* v_zero_345_; uint8_t v_isZero_346_; 
v_zero_345_ = lean_unsigned_to_nat(0u);
v_isZero_346_ = lean_nat_dec_eq(v_x_344_, v_zero_345_);
if (v_isZero_346_ == 1)
{
lean_dec(v_x_344_);
lean_dec_ref(v_p_343_);
return v_isZero_346_;
}
else
{
lean_object* v_one_347_; lean_object* v_n_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_one_347_ = lean_unsigned_to_nat(1u);
v_n_348_ = lean_nat_sub(v_x_344_, v_one_347_);
lean_dec(v_x_344_);
v___x_349_ = lean_array_fget_borrowed(v_xs_341_, v_n_348_);
v___x_350_ = lean_array_fget_borrowed(v_ys_342_, v_n_348_);
lean_inc_ref(v_p_343_);
lean_inc(v___x_350_);
lean_inc(v___x_349_);
v___x_351_ = lean_apply_2(v_p_343_, v___x_349_, v___x_350_);
v___x_352_ = lean_unbox(v___x_351_);
if (v___x_352_ == 0)
{
uint8_t v___x_353_; 
lean_dec(v_n_348_);
lean_dec_ref(v_p_343_);
v___x_353_ = lean_unbox(v___x_351_);
return v___x_353_;
}
else
{
v_x_344_ = v_n_348_;
goto _start;
}
}
}
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
LEAN_EXPORT uint8_t l_Array_isEqvAux(lean_object* v_00_u03b1_361_, lean_object* v_xs_362_, lean_object* v_ys_363_, lean_object* v_hsz_364_, lean_object* v_p_365_, lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
uint8_t v___x_368_; 
v___x_368_ = l_Array_isEqvAux___redArg(v_xs_362_, v_ys_363_, v_p_365_, v_x_366_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___boxed(lean_object* v_00_u03b1_369_, lean_object* v_xs_370_, lean_object* v_ys_371_, lean_object* v_hsz_372_, lean_object* v_p_373_, lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
uint8_t v_res_376_; lean_object* v_r_377_; 
v_res_376_ = l_Array_isEqvAux(v_00_u03b1_369_, v_xs_370_, v_ys_371_, v_hsz_372_, v_p_373_, v_x_374_, v_x_375_);
lean_dec_ref(v_ys_371_);
lean_dec_ref(v_xs_370_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqv___redArg(lean_object* v_xs_378_, lean_object* v_ys_379_, lean_object* v_p_380_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_381_ = lean_array_get_size(v_xs_378_);
v___x_382_ = lean_array_get_size(v_ys_379_);
v___x_383_ = lean_nat_dec_eq(v___x_381_, v___x_382_);
if (v___x_383_ == 0)
{
lean_dec_ref(v_p_380_);
return v___x_383_;
}
else
{
uint8_t v___x_384_; 
v___x_384_ = l_Array_isEqvAux___redArg(v_xs_378_, v_ys_379_, v_p_380_, v___x_381_);
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqv___redArg___boxed(lean_object* v_xs_385_, lean_object* v_ys_386_, lean_object* v_p_387_){
_start:
{
uint8_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_Array_isEqv___redArg(v_xs_385_, v_ys_386_, v_p_387_);
lean_dec_ref(v_ys_386_);
lean_dec_ref(v_xs_385_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqv(lean_object* v_00_u03b1_390_, lean_object* v_xs_391_, lean_object* v_ys_392_, lean_object* v_p_393_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_394_ = lean_array_get_size(v_xs_391_);
v___x_395_ = lean_array_get_size(v_ys_392_);
v___x_396_ = lean_nat_dec_eq(v___x_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_dec_ref(v_p_393_);
return v___x_396_;
}
else
{
uint8_t v___x_397_; 
v___x_397_ = l_Array_isEqvAux___redArg(v_xs_391_, v_ys_392_, v_p_393_, v___x_394_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqv___boxed(lean_object* v_00_u03b1_398_, lean_object* v_xs_399_, lean_object* v_ys_400_, lean_object* v_p_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Array_isEqv(v_00_u03b1_398_, v_xs_399_, v_ys_400_, v_p_401_);
lean_dec_ref(v_ys_400_);
lean_dec_ref(v_xs_399_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT uint8_t l_Array_instBEq___redArg___lam__0(lean_object* v_inst_404_, lean_object* v_xs_405_, lean_object* v_ys_406_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_407_ = lean_array_get_size(v_xs_405_);
v___x_408_ = lean_array_get_size(v_ys_406_);
v___x_409_ = lean_nat_dec_eq(v___x_407_, v___x_408_);
if (v___x_409_ == 0)
{
lean_dec_ref(v_inst_404_);
return v___x_409_;
}
else
{
uint8_t v___x_410_; 
v___x_410_ = l_Array_isEqvAux___redArg(v_xs_405_, v_ys_406_, v_inst_404_, v___x_407_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instBEq___redArg___lam__0___boxed(lean_object* v_inst_411_, lean_object* v_xs_412_, lean_object* v_ys_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Array_instBEq___redArg___lam__0(v_inst_411_, v_xs_412_, v_ys_413_);
lean_dec_ref(v_ys_413_);
lean_dec_ref(v_xs_412_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT lean_object* l_Array_instBEq___redArg(lean_object* v_inst_416_){
_start:
{
lean_object* v___f_417_; 
v___f_417_ = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_417_, 0, v_inst_416_);
return v___f_417_;
}
}
LEAN_EXPORT lean_object* l_Array_instBEq(lean_object* v_00_u03b1_418_, lean_object* v_inst_419_){
_start:
{
lean_object* v___f_420_; 
v___f_420_ = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_420_, 0, v_inst_419_);
return v___f_420_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn_go___redArg(lean_object* v_n_421_, lean_object* v_f_422_, lean_object* v_acc_423_, lean_object* v_i_424_){
_start:
{
lean_object* v_zero_425_; uint8_t v_isZero_426_; 
v_zero_425_ = lean_unsigned_to_nat(0u);
v_isZero_426_ = lean_nat_dec_eq(v_i_424_, v_zero_425_);
if (v_isZero_426_ == 1)
{
lean_dec(v_i_424_);
lean_dec(v_f_422_);
return v_acc_423_;
}
else
{
lean_object* v_one_427_; lean_object* v_n_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_one_427_ = lean_unsigned_to_nat(1u);
v_n_428_ = lean_nat_sub(v_i_424_, v_one_427_);
lean_dec(v_i_424_);
v___x_429_ = lean_nat_sub(v_n_421_, v_n_428_);
v___x_430_ = lean_nat_sub(v___x_429_, v_one_427_);
lean_dec(v___x_429_);
lean_inc(v_f_422_);
v___x_431_ = lean_apply_1(v_f_422_, v___x_430_);
v___x_432_ = lean_array_push(v_acc_423_, v___x_431_);
v_acc_423_ = v___x_432_;
v_i_424_ = v_n_428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_ofFn_go___redArg___boxed(lean_object* v_n_434_, lean_object* v_f_435_, lean_object* v_acc_436_, lean_object* v_i_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Array_ofFn_go___redArg(v_n_434_, v_f_435_, v_acc_436_, v_i_437_);
lean_dec(v_n_434_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn_go(lean_object* v_00_u03b1_439_, lean_object* v_n_440_, lean_object* v_f_441_, lean_object* v_acc_442_, lean_object* v_i_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Array_ofFn_go___redArg(v_n_440_, v_f_441_, v_acc_442_, v_i_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn_go___boxed(lean_object* v_00_u03b1_446_, lean_object* v_n_447_, lean_object* v_f_448_, lean_object* v_acc_449_, lean_object* v_i_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Array_ofFn_go(v_00_u03b1_446_, v_n_447_, v_f_448_, v_acc_449_, v_i_450_, v_a_451_);
lean_dec(v_n_447_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn___redArg(lean_object* v_n_453_, lean_object* v_f_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_mk_empty_array_with_capacity(v_n_453_);
lean_inc(v_n_453_);
v___x_456_ = l_Array_ofFn_go___redArg(v_n_453_, v_f_454_, v___x_455_, v_n_453_);
lean_dec(v_n_453_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn(lean_object* v_00_u03b1_457_, lean_object* v_n_458_, lean_object* v_f_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Array_ofFn___redArg(v_n_458_, v_f_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Array_range___lam__0(lean_object* v_i_461_){
_start:
{
lean_inc(v_i_461_);
return v_i_461_;
}
}
LEAN_EXPORT lean_object* l_Array_range___lam__0___boxed(lean_object* v_i_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Array_range___lam__0(v_i_462_);
lean_dec(v_i_462_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Array_range(lean_object* v_n_465_){
_start:
{
lean_object* v___f_466_; lean_object* v___x_467_; 
v___f_466_ = ((lean_object*)(l_Array_range___closed__0));
v___x_467_ = l_Array_ofFn___redArg(v_n_465_, v___f_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27___lam__0(lean_object* v_step_468_, lean_object* v_start_469_, lean_object* v_i_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_nat_mul(v_step_468_, v_i_470_);
v___x_472_ = lean_nat_add(v_start_469_, v___x_471_);
lean_dec(v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27___lam__0___boxed(lean_object* v_step_473_, lean_object* v_start_474_, lean_object* v_i_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Array_range_x27___lam__0(v_step_473_, v_start_474_, v_i_475_);
lean_dec(v_i_475_);
lean_dec(v_start_474_);
lean_dec(v_step_473_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27(lean_object* v_start_477_, lean_object* v_size_478_, lean_object* v_step_479_){
_start:
{
lean_object* v___f_480_; lean_object* v___x_481_; 
v___f_480_ = lean_alloc_closure((void*)(l_Array_range_x27___lam__0___boxed), 3, 2);
lean_closure_set(v___f_480_, 0, v_step_479_);
lean_closure_set(v___f_480_, 1, v_start_477_);
v___x_481_ = l_Array_ofFn___redArg(v_size_478_, v___f_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Array_singleton___redArg(lean_object* v_v_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_mk_empty_array_with_capacity(v___x_483_);
v___x_485_ = lean_array_push(v___x_484_, v_v_482_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Array_singleton(lean_object* v_00_u03b1_486_, lean_object* v_v_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_mk_empty_array_with_capacity(v___x_488_);
v___x_490_ = lean_array_push(v___x_489_, v_v_487_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___redArg(lean_object* v_inst_491_, lean_object* v_xs_492_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_493_ = lean_array_get_size(v_xs_492_);
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_nat_sub(v___x_493_, v___x_494_);
v___x_496_ = lean_array_get_borrowed(v_inst_491_, v_xs_492_, v___x_495_);
lean_dec(v___x_495_);
lean_inc(v___x_496_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___redArg___boxed(lean_object* v_inst_497_, lean_object* v_xs_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Array_back_x21___redArg(v_inst_497_, v_xs_498_);
lean_dec_ref(v_xs_498_);
lean_dec(v_inst_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21(lean_object* v_00_u03b1_500_, lean_object* v_inst_501_, lean_object* v_xs_502_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_503_ = lean_array_get_size(v_xs_502_);
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = lean_nat_sub(v___x_503_, v___x_504_);
v___x_506_ = lean_array_get_borrowed(v_inst_501_, v_xs_502_, v___x_505_);
lean_dec(v___x_505_);
lean_inc(v___x_506_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___boxed(lean_object* v_00_u03b1_507_, lean_object* v_inst_508_, lean_object* v_xs_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Array_back_x21(v_00_u03b1_507_, v_inst_508_, v_xs_509_);
lean_dec_ref(v_xs_509_);
lean_dec(v_inst_508_);
return v_res_510_;
}
}
static lean_object* _init_l_Array_back___auto__1(void){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Array_back___redArg(lean_object* v_xs_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_513_ = lean_array_get_size(v_xs_512_);
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_sub(v___x_513_, v___x_514_);
v___x_516_ = lean_array_fget_borrowed(v_xs_512_, v___x_515_);
lean_dec(v___x_515_);
lean_inc(v___x_516_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Array_back___redArg___boxed(lean_object* v_xs_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Array_back___redArg(v_xs_517_);
lean_dec_ref(v_xs_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Array_back(lean_object* v_00_u03b1_519_, lean_object* v_xs_520_, lean_object* v_h_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_522_ = lean_array_get_size(v_xs_520_);
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_sub(v___x_522_, v___x_523_);
v___x_525_ = lean_array_fget_borrowed(v_xs_520_, v___x_524_);
lean_dec(v___x_524_);
lean_inc(v___x_525_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Array_back___boxed(lean_object* v_00_u03b1_526_, lean_object* v_xs_527_, lean_object* v_h_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Array_back(v_00_u03b1_526_, v_xs_527_, v_h_528_);
lean_dec_ref(v_xs_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___redArg(lean_object* v_xs_530_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_531_ = lean_array_get_size(v_xs_530_);
v___x_532_ = lean_unsigned_to_nat(1u);
v___x_533_ = lean_nat_sub(v___x_531_, v___x_532_);
v___x_534_ = lean_nat_dec_lt(v___x_533_, v___x_531_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
lean_dec(v___x_533_);
v___x_535_ = lean_box(0);
return v___x_535_;
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_array_fget_borrowed(v_xs_530_, v___x_533_);
lean_dec(v___x_533_);
lean_inc(v___x_536_);
v___x_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___redArg___boxed(lean_object* v_xs_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Array_back_x3f___redArg(v_xs_538_);
lean_dec_ref(v_xs_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f(lean_object* v_00_u03b1_540_, lean_object* v_xs_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_542_ = lean_array_get_size(v_xs_541_);
v___x_543_ = lean_unsigned_to_nat(1u);
v___x_544_ = lean_nat_sub(v___x_542_, v___x_543_);
v___x_545_ = lean_nat_dec_lt(v___x_544_, v___x_542_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
lean_dec(v___x_544_);
v___x_546_ = lean_box(0);
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_array_fget_borrowed(v_xs_541_, v___x_544_);
lean_dec(v___x_544_);
lean_inc(v___x_547_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___boxed(lean_object* v_00_u03b1_549_, lean_object* v_xs_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Array_back_x3f(v_00_u03b1_549_, v_xs_550_);
lean_dec_ref(v_xs_550_);
return v_res_551_;
}
}
static lean_object* _init_l_Array_swapAt___auto__1(void){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___redArg(lean_object* v_xs_553_, lean_object* v_i_554_, lean_object* v_v_555_){
_start:
{
lean_object* v_e_556_; lean_object* v_xs_x27_557_; lean_object* v___x_558_; 
v_e_556_ = lean_array_fget(v_xs_553_, v_i_554_);
v_xs_x27_557_ = lean_array_fset(v_xs_553_, v_i_554_, v_v_555_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v_e_556_);
lean_ctor_set(v___x_558_, 1, v_xs_x27_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___redArg___boxed(lean_object* v_xs_559_, lean_object* v_i_560_, lean_object* v_v_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Array_swapAt___redArg(v_xs_559_, v_i_560_, v_v_561_);
lean_dec(v_i_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt(lean_object* v_00_u03b1_563_, lean_object* v_xs_564_, lean_object* v_i_565_, lean_object* v_v_566_, lean_object* v_hi_567_){
_start:
{
lean_object* v_e_568_; lean_object* v_xs_x27_569_; lean_object* v___x_570_; 
v_e_568_ = lean_array_fget(v_xs_564_, v_i_565_);
v_xs_x27_569_ = lean_array_fset(v_xs_564_, v_i_565_, v_v_566_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v_e_568_);
lean_ctor_set(v___x_570_, 1, v_xs_x27_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___boxed(lean_object* v_00_u03b1_571_, lean_object* v_xs_572_, lean_object* v_i_573_, lean_object* v_v_574_, lean_object* v_hi_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Array_swapAt(v_00_u03b1_571_, v_xs_572_, v_i_573_, v_v_574_, v_hi_575_);
lean_dec(v_i_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt_x21___redArg(lean_object* v_xs_581_, lean_object* v_i_582_, lean_object* v_v_583_){
_start:
{
lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_584_ = lean_array_get_size(v_xs_581_);
v___x_585_ = lean_nat_dec_lt(v_i_582_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v_this_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_this_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_586_, 0, v_v_583_);
lean_ctor_set(v_this_586_, 1, v_xs_581_);
v___x_587_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_588_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__1));
v___x_589_ = lean_unsigned_to_nat(463u);
v___x_590_ = lean_unsigned_to_nat(4u);
v___x_591_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__2));
v___x_592_ = l_Nat_reprFast(v_i_582_);
v___x_593_ = lean_string_append(v___x_591_, v___x_592_);
lean_dec_ref(v___x_592_);
v___x_594_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__3));
v___x_595_ = lean_string_append(v___x_593_, v___x_594_);
v___x_596_ = l_mkPanicMessageWithDecl(v___x_587_, v___x_588_, v___x_589_, v___x_590_, v___x_595_);
lean_dec_ref(v___x_595_);
v___x_597_ = l_panic___redArg(v_this_586_, v___x_596_);
lean_dec_ref_known(v_this_586_, 2);
return v___x_597_;
}
else
{
lean_object* v_e_598_; lean_object* v_xs_x27_599_; lean_object* v___x_600_; 
v_e_598_ = lean_array_fget(v_xs_581_, v_i_582_);
v_xs_x27_599_ = lean_array_fset(v_xs_581_, v_i_582_, v_v_583_);
lean_dec(v_i_582_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v_e_598_);
lean_ctor_set(v___x_600_, 1, v_xs_x27_599_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l_Array_swapAt_x21(lean_object* v_00_u03b1_601_, lean_object* v_xs_602_, lean_object* v_i_603_, lean_object* v_v_604_){
_start:
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = lean_array_get_size(v_xs_602_);
v___x_606_ = lean_nat_dec_lt(v_i_603_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v_this_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_this_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_607_, 0, v_v_604_);
lean_ctor_set(v_this_607_, 1, v_xs_602_);
v___x_608_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_609_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__1));
v___x_610_ = lean_unsigned_to_nat(463u);
v___x_611_ = lean_unsigned_to_nat(4u);
v___x_612_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__2));
v___x_613_ = l_Nat_reprFast(v_i_603_);
v___x_614_ = lean_string_append(v___x_612_, v___x_613_);
lean_dec_ref(v___x_613_);
v___x_615_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__3));
v___x_616_ = lean_string_append(v___x_614_, v___x_615_);
v___x_617_ = l_mkPanicMessageWithDecl(v___x_608_, v___x_609_, v___x_610_, v___x_611_, v___x_616_);
lean_dec_ref(v___x_616_);
v___x_618_ = l_panic___redArg(v_this_607_, v___x_617_);
lean_dec_ref_known(v_this_607_, 2);
return v___x_618_;
}
else
{
lean_object* v_e_619_; lean_object* v_xs_x27_620_; lean_object* v___x_621_; 
v_e_619_ = lean_array_fget(v_xs_602_, v_i_603_);
v_xs_x27_620_ = lean_array_fset(v_xs_602_, v_i_603_, v_v_604_);
lean_dec(v_i_603_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v_e_619_);
lean_ctor_set(v___x_621_, 1, v_xs_x27_620_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(lean_object* v_x_622_, lean_object* v_x_623_){
_start:
{
lean_object* v_zero_624_; uint8_t v_isZero_625_; 
v_zero_624_ = lean_unsigned_to_nat(0u);
v_isZero_625_ = lean_nat_dec_eq(v_x_622_, v_zero_624_);
if (v_isZero_625_ == 1)
{
lean_dec(v_x_622_);
return v_x_623_;
}
else
{
lean_object* v_one_626_; lean_object* v_n_627_; lean_object* v___x_628_; 
v_one_626_ = lean_unsigned_to_nat(1u);
v_n_627_ = lean_nat_sub(v_x_622_, v_one_626_);
lean_dec(v_x_622_);
v___x_628_ = lean_array_pop(v_x_623_);
v_x_622_ = v_n_627_;
v_x_623_ = v___x_628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_shrink_loop(lean_object* v_00_u03b1_630_, lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(v_x_631_, v_x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___redArg(lean_object* v_xs_634_, lean_object* v_n_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = lean_array_get_size(v_xs_634_);
v___x_637_ = lean_nat_sub(v___x_636_, v_n_635_);
v___x_638_ = l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(v___x_637_, v_xs_634_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___redArg___boxed(lean_object* v_xs_639_, lean_object* v_n_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Array_shrink___redArg(v_xs_639_, v_n_640_);
lean_dec(v_n_640_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink(lean_object* v_00_u03b1_642_, lean_object* v_xs_643_, lean_object* v_n_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Array_shrink___redArg(v_xs_643_, v_n_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___boxed(lean_object* v_00_u03b1_646_, lean_object* v_xs_647_, lean_object* v_n_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Array_shrink(v_00_u03b1_646_, v_xs_647_, v_n_648_);
lean_dec(v_n_648_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Array_take___redArg(lean_object* v_xs_650_, lean_object* v_i_651_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = l_Array_extract___redArg(v_xs_650_, v___x_652_, v_i_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Array_take___redArg___boxed(lean_object* v_xs_654_, lean_object* v_i_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Array_take___redArg(v_xs_654_, v_i_655_);
lean_dec_ref(v_xs_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Array_take(lean_object* v_00_u03b1_657_, lean_object* v_xs_658_, lean_object* v_i_659_){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = l_Array_extract___redArg(v_xs_658_, v___x_660_, v_i_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Array_take___boxed(lean_object* v_00_u03b1_662_, lean_object* v_xs_663_, lean_object* v_i_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Array_take(v_00_u03b1_662_, v_xs_663_, v_i_664_);
lean_dec_ref(v_xs_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___redArg(lean_object* v_xs_666_, lean_object* v_i_667_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_array_get_size(v_xs_666_);
v___x_669_ = l_Array_extract___redArg(v_xs_666_, v_i_667_, v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___redArg___boxed(lean_object* v_xs_670_, lean_object* v_i_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Array_drop___redArg(v_xs_670_, v_i_671_);
lean_dec_ref(v_xs_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Array_drop(lean_object* v_00_u03b1_673_, lean_object* v_xs_674_, lean_object* v_i_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_array_get_size(v_xs_674_);
v___x_677_ = l_Array_extract___redArg(v_xs_674_, v_i_675_, v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___boxed(lean_object* v_00_u03b1_678_, lean_object* v_xs_679_, lean_object* v_i_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Array_drop(v_00_u03b1_678_, v_xs_679_, v_i_680_);
lean_dec_ref(v_xs_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0(lean_object* v_xs_x27_682_, lean_object* v_i_683_, lean_object* v_toPure_684_, lean_object* v_v_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_array_fset(v_xs_x27_682_, v_i_683_, v_v_685_);
v___x_687_ = lean_apply_2(v_toPure_684_, lean_box(0), v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0___boxed(lean_object* v_xs_x27_688_, lean_object* v_i_689_, lean_object* v_toPure_690_, lean_object* v_v_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Array_modifyMUnsafe___redArg___lam__0(v_xs_x27_688_, v_i_689_, v_toPure_690_, v_v_691_);
lean_dec(v_i_689_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg(lean_object* v_inst_693_, lean_object* v_xs_694_, lean_object* v_i_695_, lean_object* v_f_696_){
_start:
{
lean_object* v_toApplicative_697_; lean_object* v_toBind_698_; lean_object* v_toPure_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v_toApplicative_697_ = lean_ctor_get(v_inst_693_, 0);
lean_inc_ref(v_toApplicative_697_);
v_toBind_698_ = lean_ctor_get(v_inst_693_, 1);
lean_inc(v_toBind_698_);
lean_dec_ref(v_inst_693_);
v_toPure_699_ = lean_ctor_get(v_toApplicative_697_, 1);
lean_inc(v_toPure_699_);
lean_dec_ref(v_toApplicative_697_);
v___x_700_ = lean_array_get_size(v_xs_694_);
v___x_701_ = lean_nat_dec_lt(v_i_695_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
lean_dec(v_toBind_698_);
lean_dec(v_f_696_);
lean_dec(v_i_695_);
v___x_702_ = lean_apply_2(v_toPure_699_, lean_box(0), v_xs_694_);
return v___x_702_;
}
else
{
lean_object* v_v_703_; lean_object* v___x_704_; lean_object* v_xs_x27_705_; lean_object* v___f_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_v_703_ = lean_array_fget(v_xs_694_, v_i_695_);
v___x_704_ = lean_box(0);
v_xs_x27_705_ = lean_array_fset(v_xs_694_, v_i_695_, v___x_704_);
v___f_706_ = lean_alloc_closure((void*)(l_Array_modifyMUnsafe___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_706_, 0, v_xs_x27_705_);
lean_closure_set(v___f_706_, 1, v_i_695_);
lean_closure_set(v___f_706_, 2, v_toPure_699_);
v___x_707_ = lean_apply_1(v_f_696_, v_v_703_);
v___x_708_ = lean_apply_4(v_toBind_698_, lean_box(0), lean_box(0), v___x_707_, v___f_706_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe(lean_object* v_00_u03b1_709_, lean_object* v_m_710_, lean_object* v_inst_711_, lean_object* v_xs_712_, lean_object* v_i_713_, lean_object* v_f_714_){
_start:
{
lean_object* v_toApplicative_715_; lean_object* v_toBind_716_; lean_object* v_toPure_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_toApplicative_715_ = lean_ctor_get(v_inst_711_, 0);
lean_inc_ref(v_toApplicative_715_);
v_toBind_716_ = lean_ctor_get(v_inst_711_, 1);
lean_inc(v_toBind_716_);
lean_dec_ref(v_inst_711_);
v_toPure_717_ = lean_ctor_get(v_toApplicative_715_, 1);
lean_inc(v_toPure_717_);
lean_dec_ref(v_toApplicative_715_);
v___x_718_ = lean_array_get_size(v_xs_712_);
v___x_719_ = lean_nat_dec_lt(v_i_713_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
lean_dec(v_toBind_716_);
lean_dec(v_f_714_);
lean_dec(v_i_713_);
v___x_720_ = lean_apply_2(v_toPure_717_, lean_box(0), v_xs_712_);
return v___x_720_;
}
else
{
lean_object* v_v_721_; lean_object* v___x_722_; lean_object* v_xs_x27_723_; lean_object* v___f_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_v_721_ = lean_array_fget(v_xs_712_, v_i_713_);
v___x_722_ = lean_box(0);
v_xs_x27_723_ = lean_array_fset(v_xs_712_, v_i_713_, v___x_722_);
v___f_724_ = lean_alloc_closure((void*)(l_Array_modifyMUnsafe___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_724_, 0, v_xs_x27_723_);
lean_closure_set(v___f_724_, 1, v_i_713_);
lean_closure_set(v___f_724_, 2, v_toPure_717_);
v___x_725_ = lean_apply_1(v_f_714_, v_v_721_);
v___x_726_ = lean_apply_4(v_toBind_716_, lean_box(0), lean_box(0), v___x_725_, v___f_724_);
return v___x_726_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___redArg(lean_object* v_xs_727_, lean_object* v_i_728_, lean_object* v_f_729_){
_start:
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = lean_array_get_size(v_xs_727_);
v___x_731_ = lean_nat_dec_lt(v_i_728_, v___x_730_);
if (v___x_731_ == 0)
{
lean_dec(v_f_729_);
return v_xs_727_;
}
else
{
lean_object* v_v_732_; lean_object* v___x_733_; lean_object* v_xs_x27_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_v_732_ = lean_array_fget(v_xs_727_, v_i_728_);
v___x_733_ = lean_box(0);
v_xs_x27_734_ = lean_array_fset(v_xs_727_, v_i_728_, v___x_733_);
v___x_735_ = lean_apply_1(v_f_729_, v_v_732_);
v___x_736_ = lean_array_fset(v_xs_x27_734_, v_i_728_, v___x_735_);
return v___x_736_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___redArg___boxed(lean_object* v_xs_737_, lean_object* v_i_738_, lean_object* v_f_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Array_modify___redArg(v_xs_737_, v_i_738_, v_f_739_);
lean_dec(v_i_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Array_modify(lean_object* v_00_u03b1_741_, lean_object* v_xs_742_, lean_object* v_i_743_, lean_object* v_f_744_){
_start:
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = lean_array_get_size(v_xs_742_);
v___x_746_ = lean_nat_dec_lt(v_i_743_, v___x_745_);
if (v___x_746_ == 0)
{
lean_dec(v_f_744_);
return v_xs_742_;
}
else
{
lean_object* v_v_747_; lean_object* v___x_748_; lean_object* v_xs_x27_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_v_747_ = lean_array_fget(v_xs_742_, v_i_743_);
v___x_748_ = lean_box(0);
v_xs_x27_749_ = lean_array_fset(v_xs_742_, v_i_743_, v___x_748_);
v___x_750_ = lean_apply_1(v_f_744_, v_v_747_);
v___x_751_ = lean_array_fset(v_xs_x27_749_, v_i_743_, v___x_750_);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___boxed(lean_object* v_00_u03b1_752_, lean_object* v_xs_753_, lean_object* v_i_754_, lean_object* v_f_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Array_modify(v_00_u03b1_752_, v_xs_753_, v_i_754_, v_f_755_);
lean_dec(v_i_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg(lean_object* v_xs_757_, lean_object* v_idx_758_, lean_object* v_f_759_){
_start:
{
lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_760_ = lean_array_get_size(v_xs_757_);
v___x_761_ = lean_nat_dec_lt(v_idx_758_, v___x_760_);
if (v___x_761_ == 0)
{
lean_dec(v_f_759_);
return v_xs_757_;
}
else
{
lean_object* v_v_762_; lean_object* v___x_763_; lean_object* v_xs_x27_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_v_762_ = lean_array_fget(v_xs_757_, v_idx_758_);
v___x_763_ = lean_box(0);
v_xs_x27_764_ = lean_array_fset(v_xs_757_, v_idx_758_, v___x_763_);
v___x_765_ = lean_apply_1(v_f_759_, v_v_762_);
v___x_766_ = lean_array_fset(v_xs_x27_764_, v_idx_758_, v___x_765_);
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg___boxed(lean_object* v_xs_767_, lean_object* v_idx_768_, lean_object* v_f_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Array_modifyOp___redArg(v_xs_767_, v_idx_768_, v_f_769_);
lean_dec(v_idx_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp(lean_object* v_00_u03b1_771_, lean_object* v_xs_772_, lean_object* v_idx_773_, lean_object* v_f_774_){
_start:
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_array_get_size(v_xs_772_);
v___x_776_ = lean_nat_dec_lt(v_idx_773_, v___x_775_);
if (v___x_776_ == 0)
{
lean_dec(v_f_774_);
return v_xs_772_;
}
else
{
lean_object* v_v_777_; lean_object* v___x_778_; lean_object* v_xs_x27_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_v_777_ = lean_array_fget(v_xs_772_, v_idx_773_);
v___x_778_ = lean_box(0);
v_xs_x27_779_ = lean_array_fset(v_xs_772_, v_idx_773_, v___x_778_);
v___x_780_ = lean_apply_1(v_f_774_, v_v_777_);
v___x_781_ = lean_array_fset(v_xs_x27_779_, v_idx_773_, v___x_780_);
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___boxed(lean_object* v_00_u03b1_782_, lean_object* v_xs_783_, lean_object* v_idx_784_, lean_object* v_f_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Array_modifyOp(v_00_u03b1_782_, v_xs_783_, v_idx_784_, v_f_785_);
lean_dec(v_idx_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed(lean_object* v_toPure_787_, lean_object* v_i_788_, lean_object* v_inst_789_, lean_object* v_as_790_, lean_object* v_f_791_, lean_object* v_sz_792_, lean_object* v_____do__lift_793_){
_start:
{
size_t v_i_boxed_794_; size_t v_sz_boxed_795_; lean_object* v_res_796_; 
v_i_boxed_794_ = lean_unbox_usize(v_i_788_);
lean_dec(v_i_788_);
v_sz_boxed_795_ = lean_unbox_usize(v_sz_792_);
lean_dec(v_sz_792_);
v_res_796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(v_toPure_787_, v_i_boxed_794_, v_inst_789_, v_as_790_, v_f_791_, v_sz_boxed_795_, v_____do__lift_793_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(lean_object* v_inst_797_, lean_object* v_as_798_, lean_object* v_f_799_, size_t v_sz_800_, size_t v_i_801_, lean_object* v_b_802_){
_start:
{
lean_object* v_toApplicative_803_; lean_object* v_toBind_804_; lean_object* v_toPure_805_; uint8_t v___x_806_; 
v_toApplicative_803_ = lean_ctor_get(v_inst_797_, 0);
v_toBind_804_ = lean_ctor_get(v_inst_797_, 1);
lean_inc(v_toBind_804_);
v_toPure_805_ = lean_ctor_get(v_toApplicative_803_, 1);
lean_inc(v_toPure_805_);
v___x_806_ = lean_usize_dec_lt(v_i_801_, v_sz_800_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
lean_dec(v_toBind_804_);
lean_dec(v_f_799_);
lean_dec_ref(v_as_798_);
lean_dec_ref(v_inst_797_);
v___x_807_ = lean_apply_2(v_toPure_805_, lean_box(0), v_b_802_);
return v___x_807_;
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___f_810_; lean_object* v_a_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_808_ = lean_box_usize(v_i_801_);
v___x_809_ = lean_box_usize(v_sz_800_);
lean_inc(v_f_799_);
lean_inc_ref(v_as_798_);
v___f_810_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_810_, 0, v_toPure_805_);
lean_closure_set(v___f_810_, 1, v___x_808_);
lean_closure_set(v___f_810_, 2, v_inst_797_);
lean_closure_set(v___f_810_, 3, v_as_798_);
lean_closure_set(v___f_810_, 4, v_f_799_);
lean_closure_set(v___f_810_, 5, v___x_809_);
v_a_811_ = lean_array_uget(v_as_798_, v_i_801_);
lean_dec_ref(v_as_798_);
v___x_812_ = lean_apply_3(v_f_799_, v_a_811_, lean_box(0), v_b_802_);
v___x_813_ = lean_apply_4(v_toBind_804_, lean_box(0), lean_box(0), v___x_812_, v___f_810_);
return v___x_813_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(lean_object* v_toPure_814_, size_t v_i_815_, lean_object* v_inst_816_, lean_object* v_as_817_, lean_object* v_f_818_, size_t v_sz_819_, lean_object* v_____do__lift_820_){
_start:
{
if (lean_obj_tag(v_____do__lift_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_822_; 
lean_dec(v_f_818_);
lean_dec_ref(v_as_817_);
lean_dec_ref(v_inst_816_);
v_a_821_ = lean_ctor_get(v_____do__lift_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref_known(v_____do__lift_820_, 1);
v___x_822_ = lean_apply_2(v_toPure_814_, lean_box(0), v_a_821_);
return v___x_822_;
}
else
{
lean_object* v_a_823_; size_t v___x_824_; size_t v___x_825_; lean_object* v___x_826_; 
lean_dec(v_toPure_814_);
v_a_823_ = lean_ctor_get(v_____do__lift_820_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v_____do__lift_820_, 1);
v___x_824_ = ((size_t)1ULL);
v___x_825_ = lean_usize_add(v_i_815_, v___x_824_);
v___x_826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_816_, v_as_817_, v_f_818_, v_sz_819_, v___x_825_, v_a_823_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___boxed(lean_object* v_inst_827_, lean_object* v_as_828_, lean_object* v_f_829_, lean_object* v_sz_830_, lean_object* v_i_831_, lean_object* v_b_832_){
_start:
{
size_t v_sz_boxed_833_; size_t v_i_boxed_834_; lean_object* v_res_835_; 
v_sz_boxed_833_ = lean_unbox_usize(v_sz_830_);
lean_dec(v_sz_830_);
v_i_boxed_834_ = lean_unbox_usize(v_i_831_);
lean_dec(v_i_831_);
v_res_835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_827_, v_as_828_, v_f_829_, v_sz_boxed_833_, v_i_boxed_834_, v_b_832_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object* v_00_u03b1_836_, lean_object* v_00_u03b2_837_, lean_object* v_m_838_, lean_object* v_inst_839_, lean_object* v_as_840_, lean_object* v_f_841_, size_t v_sz_842_, size_t v_i_843_, lean_object* v_b_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_839_, v_as_840_, v_f_841_, v_sz_842_, v_i_843_, v_b_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___boxed(lean_object* v_00_u03b1_846_, lean_object* v_00_u03b2_847_, lean_object* v_m_848_, lean_object* v_inst_849_, lean_object* v_as_850_, lean_object* v_f_851_, lean_object* v_sz_852_, lean_object* v_i_853_, lean_object* v_b_854_){
_start:
{
size_t v_sz_boxed_855_; size_t v_i_boxed_856_; lean_object* v_res_857_; 
v_sz_boxed_855_ = lean_unbox_usize(v_sz_852_);
lean_dec(v_sz_852_);
v_i_boxed_856_ = lean_unbox_usize(v_i_853_);
lean_dec(v_i_853_);
v_res_857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(v_00_u03b1_846_, v_00_u03b2_847_, v_m_848_, v_inst_849_, v_as_850_, v_f_851_, v_sz_boxed_855_, v_i_boxed_856_, v_b_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe___redArg(lean_object* v_inst_858_, lean_object* v_as_859_, lean_object* v_b_860_, lean_object* v_f_861_){
_start:
{
size_t v_sz_862_; size_t v___x_863_; lean_object* v___x_864_; 
v_sz_862_ = lean_array_size(v_as_859_);
v___x_863_ = ((size_t)0ULL);
v___x_864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_858_, v_as_859_, v_f_861_, v_sz_862_, v___x_863_, v_b_860_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe(lean_object* v_00_u03b1_865_, lean_object* v_00_u03b2_866_, lean_object* v_m_867_, lean_object* v_inst_868_, lean_object* v_as_869_, lean_object* v_b_870_, lean_object* v_f_871_){
_start:
{
size_t v_sz_872_; size_t v___x_873_; lean_object* v___x_874_; 
v_sz_872_ = lean_array_size(v_as_869_);
v___x_873_ = ((size_t)0ULL);
v___x_874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_868_, v_as_869_, v_f_871_, v_sz_872_, v___x_873_, v_b_870_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0___boxed(lean_object* v_toPure_875_, lean_object* v_inst_876_, lean_object* v_as_877_, lean_object* v_f_878_, lean_object* v_n_879_, lean_object* v_____do__lift_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Array_forIn_x27_loop___redArg___lam__0(v_toPure_875_, v_inst_876_, v_as_877_, v_f_878_, v_n_879_, v_____do__lift_880_);
lean_dec(v_n_879_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg(lean_object* v_inst_882_, lean_object* v_as_883_, lean_object* v_f_884_, lean_object* v_i_885_, lean_object* v_b_886_){
_start:
{
lean_object* v_toApplicative_887_; lean_object* v_toBind_888_; lean_object* v_toPure_889_; lean_object* v_zero_890_; uint8_t v_isZero_891_; 
v_toApplicative_887_ = lean_ctor_get(v_inst_882_, 0);
v_toBind_888_ = lean_ctor_get(v_inst_882_, 1);
lean_inc(v_toBind_888_);
v_toPure_889_ = lean_ctor_get(v_toApplicative_887_, 1);
lean_inc(v_toPure_889_);
v_zero_890_ = lean_unsigned_to_nat(0u);
v_isZero_891_ = lean_nat_dec_eq(v_i_885_, v_zero_890_);
if (v_isZero_891_ == 1)
{
lean_object* v___x_892_; 
lean_dec(v_toBind_888_);
lean_dec(v_f_884_);
lean_dec_ref(v_as_883_);
lean_dec_ref(v_inst_882_);
v___x_892_ = lean_apply_2(v_toPure_889_, lean_box(0), v_b_886_);
return v___x_892_;
}
else
{
lean_object* v_one_893_; lean_object* v_n_894_; lean_object* v___f_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_one_893_ = lean_unsigned_to_nat(1u);
v_n_894_ = lean_nat_sub(v_i_885_, v_one_893_);
lean_inc(v_n_894_);
lean_inc(v_f_884_);
lean_inc_ref(v_as_883_);
v___f_895_ = lean_alloc_closure((void*)(l_Array_forIn_x27_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_895_, 0, v_toPure_889_);
lean_closure_set(v___f_895_, 1, v_inst_882_);
lean_closure_set(v___f_895_, 2, v_as_883_);
lean_closure_set(v___f_895_, 3, v_f_884_);
lean_closure_set(v___f_895_, 4, v_n_894_);
v___x_896_ = lean_array_get_size(v_as_883_);
v___x_897_ = lean_nat_sub(v___x_896_, v_one_893_);
v___x_898_ = lean_nat_sub(v___x_897_, v_n_894_);
lean_dec(v_n_894_);
lean_dec(v___x_897_);
v___x_899_ = lean_array_fget(v_as_883_, v___x_898_);
lean_dec(v___x_898_);
lean_dec_ref(v_as_883_);
v___x_900_ = lean_apply_3(v_f_884_, v___x_899_, lean_box(0), v_b_886_);
v___x_901_ = lean_apply_4(v_toBind_888_, lean_box(0), lean_box(0), v___x_900_, v___f_895_);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0(lean_object* v_toPure_902_, lean_object* v_inst_903_, lean_object* v_as_904_, lean_object* v_f_905_, lean_object* v_n_906_, lean_object* v_____do__lift_907_){
_start:
{
if (lean_obj_tag(v_____do__lift_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_909_; 
lean_dec(v_f_905_);
lean_dec_ref(v_as_904_);
lean_dec_ref(v_inst_903_);
v_a_908_ = lean_ctor_get(v_____do__lift_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v_____do__lift_907_, 1);
v___x_909_ = lean_apply_2(v_toPure_902_, lean_box(0), v_a_908_);
return v___x_909_;
}
else
{
lean_object* v_a_910_; lean_object* v___x_911_; 
lean_dec(v_toPure_902_);
v_a_910_ = lean_ctor_get(v_____do__lift_907_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v_____do__lift_907_, 1);
v___x_911_ = l_Array_forIn_x27_loop___redArg(v_inst_903_, v_as_904_, v_f_905_, v_n_906_, v_a_910_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___boxed(lean_object* v_inst_912_, lean_object* v_as_913_, lean_object* v_f_914_, lean_object* v_i_915_, lean_object* v_b_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Array_forIn_x27_loop___redArg(v_inst_912_, v_as_913_, v_f_914_, v_i_915_, v_b_916_);
lean_dec(v_i_915_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop(lean_object* v_00_u03b1_918_, lean_object* v_00_u03b2_919_, lean_object* v_m_920_, lean_object* v_inst_921_, lean_object* v_as_922_, lean_object* v_f_923_, lean_object* v_i_924_, lean_object* v_h_925_, lean_object* v_b_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Array_forIn_x27_loop___redArg(v_inst_921_, v_as_922_, v_f_923_, v_i_924_, v_b_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___boxed(lean_object* v_00_u03b1_928_, lean_object* v_00_u03b2_929_, lean_object* v_m_930_, lean_object* v_inst_931_, lean_object* v_as_932_, lean_object* v_f_933_, lean_object* v_i_934_, lean_object* v_h_935_, lean_object* v_b_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Array_forIn_x27_loop(v_00_u03b1_928_, v_00_u03b2_929_, v_m_930_, v_inst_931_, v_as_932_, v_f_933_, v_i_934_, v_h_935_, v_b_936_);
lean_dec(v_i_934_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_inst_938_, lean_object* v_00_u03b2_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
size_t v_sz_943_; size_t v___x_944_; lean_object* v___x_945_; 
v_sz_943_ = lean_array_size(v___y_940_);
v___x_944_ = ((size_t)0ULL);
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_938_, v___y_940_, v___y_942_, v_sz_943_, v___x_944_, v___y_941_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_946_){
_start:
{
lean_object* v___f_947_; 
v___f_947_ = lean_alloc_closure((void*)(l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_947_, 0, v_inst_946_);
return v___f_947_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_00_u03b1_948_, lean_object* v_m_949_, lean_object* v_inst_950_){
_start:
{
lean_object* v___f_951_; 
v___f_951_ = lean_alloc_closure((void*)(l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_951_, 0, v_inst_950_);
return v___f_951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_952_, lean_object* v_inst_953_, lean_object* v_f_954_, lean_object* v_as_955_, lean_object* v_stop_956_, lean_object* v_____do__lift_957_){
_start:
{
size_t v_i_boxed_958_; size_t v_stop_boxed_959_; lean_object* v_res_960_; 
v_i_boxed_958_ = lean_unbox_usize(v_i_952_);
lean_dec(v_i_952_);
v_stop_boxed_959_ = lean_unbox_usize(v_stop_956_);
lean_dec(v_stop_956_);
v_res_960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_958_, v_inst_953_, v_f_954_, v_as_955_, v_stop_boxed_959_, v_____do__lift_957_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(lean_object* v_inst_961_, lean_object* v_f_962_, lean_object* v_as_963_, size_t v_i_964_, size_t v_stop_965_, lean_object* v_b_966_){
_start:
{
lean_object* v_toApplicative_967_; lean_object* v_toBind_968_; lean_object* v_toPure_969_; uint8_t v___x_970_; 
v_toApplicative_967_ = lean_ctor_get(v_inst_961_, 0);
v_toBind_968_ = lean_ctor_get(v_inst_961_, 1);
lean_inc(v_toBind_968_);
v_toPure_969_ = lean_ctor_get(v_toApplicative_967_, 1);
v___x_970_ = lean_usize_dec_eq(v_i_964_, v_stop_965_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___f_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_971_ = lean_box_usize(v_i_964_);
v___x_972_ = lean_box_usize(v_stop_965_);
lean_inc_ref(v_as_963_);
lean_inc(v_f_962_);
v___f_973_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_973_, 0, v___x_971_);
lean_closure_set(v___f_973_, 1, v_inst_961_);
lean_closure_set(v___f_973_, 2, v_f_962_);
lean_closure_set(v___f_973_, 3, v_as_963_);
lean_closure_set(v___f_973_, 4, v___x_972_);
v___x_974_ = lean_array_uget(v_as_963_, v_i_964_);
lean_dec_ref(v_as_963_);
v___x_975_ = lean_apply_2(v_f_962_, v_b_966_, v___x_974_);
v___x_976_ = lean_apply_4(v_toBind_968_, lean_box(0), lean_box(0), v___x_975_, v___f_973_);
return v___x_976_;
}
else
{
lean_object* v___x_977_; 
lean_inc(v_toPure_969_);
lean_dec(v_toBind_968_);
lean_dec_ref(v_as_963_);
lean_dec(v_f_962_);
lean_dec_ref(v_inst_961_);
v___x_977_ = lean_apply_2(v_toPure_969_, lean_box(0), v_b_966_);
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_978_, lean_object* v_inst_979_, lean_object* v_f_980_, lean_object* v_as_981_, size_t v_stop_982_, lean_object* v_____do__lift_983_){
_start:
{
size_t v___x_984_; size_t v___x_985_; lean_object* v___x_986_; 
v___x_984_ = ((size_t)1ULL);
v___x_985_ = lean_usize_add(v_i_978_, v___x_984_);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_979_, v_f_980_, v_as_981_, v___x_985_, v_stop_982_, v_____do__lift_983_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_987_, lean_object* v_f_988_, lean_object* v_as_989_, lean_object* v_i_990_, lean_object* v_stop_991_, lean_object* v_b_992_){
_start:
{
size_t v_i_boxed_993_; size_t v_stop_boxed_994_; lean_object* v_res_995_; 
v_i_boxed_993_ = lean_unbox_usize(v_i_990_);
lean_dec(v_i_990_);
v_stop_boxed_994_ = lean_unbox_usize(v_stop_991_);
lean_dec(v_stop_991_);
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_987_, v_f_988_, v_as_989_, v_i_boxed_993_, v_stop_boxed_994_, v_b_992_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object* v_00_u03b1_996_, lean_object* v_00_u03b2_997_, lean_object* v_m_998_, lean_object* v_inst_999_, lean_object* v_f_1000_, lean_object* v_as_1001_, size_t v_i_1002_, size_t v_stop_1003_, lean_object* v_b_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_999_, v_f_1000_, v_as_1001_, v_i_1002_, v_stop_1003_, v_b_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b1_1006_, lean_object* v_00_u03b2_1007_, lean_object* v_m_1008_, lean_object* v_inst_1009_, lean_object* v_f_1010_, lean_object* v_as_1011_, lean_object* v_i_1012_, lean_object* v_stop_1013_, lean_object* v_b_1014_){
_start:
{
size_t v_i_boxed_1015_; size_t v_stop_boxed_1016_; lean_object* v_res_1017_; 
v_i_boxed_1015_ = lean_unbox_usize(v_i_1012_);
lean_dec(v_i_1012_);
v_stop_boxed_1016_ = lean_unbox_usize(v_stop_1013_);
lean_dec(v_stop_1013_);
v_res_1017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(v_00_u03b1_1006_, v_00_u03b2_1007_, v_m_1008_, v_inst_1009_, v_f_1010_, v_as_1011_, v_i_boxed_1015_, v_stop_boxed_1016_, v_b_1014_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg(lean_object* v_inst_1018_, lean_object* v_f_1019_, lean_object* v_init_1020_, lean_object* v_as_1021_, lean_object* v_start_1022_, lean_object* v_stop_1023_){
_start:
{
lean_object* v_toApplicative_1024_; lean_object* v_toPure_1025_; uint8_t v___x_1026_; 
v_toApplicative_1024_ = lean_ctor_get(v_inst_1018_, 0);
v_toPure_1025_ = lean_ctor_get(v_toApplicative_1024_, 1);
v___x_1026_ = lean_nat_dec_lt(v_start_1022_, v_stop_1023_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; 
lean_inc(v_toPure_1025_);
lean_dec_ref(v_as_1021_);
lean_dec(v_f_1019_);
lean_dec_ref(v_inst_1018_);
v___x_1027_ = lean_apply_2(v_toPure_1025_, lean_box(0), v_init_1020_);
return v___x_1027_;
}
else
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_array_get_size(v_as_1021_);
v___x_1029_ = lean_nat_dec_le(v_stop_1023_, v___x_1028_);
if (v___x_1029_ == 0)
{
uint8_t v___x_1030_; 
v___x_1030_ = lean_nat_dec_lt(v_start_1022_, v___x_1028_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; 
lean_inc(v_toPure_1025_);
lean_dec_ref(v_as_1021_);
lean_dec(v_f_1019_);
lean_dec_ref(v_inst_1018_);
v___x_1031_ = lean_apply_2(v_toPure_1025_, lean_box(0), v_init_1020_);
return v___x_1031_;
}
else
{
size_t v___x_1032_; size_t v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = lean_usize_of_nat(v_start_1022_);
v___x_1033_ = lean_usize_of_nat(v___x_1028_);
v___x_1034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1018_, v_f_1019_, v_as_1021_, v___x_1032_, v___x_1033_, v_init_1020_);
return v___x_1034_;
}
}
else
{
size_t v___x_1035_; size_t v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = lean_usize_of_nat(v_start_1022_);
v___x_1036_ = lean_usize_of_nat(v_stop_1023_);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1018_, v_f_1019_, v_as_1021_, v___x_1035_, v___x_1036_, v_init_1020_);
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg___boxed(lean_object* v_inst_1038_, lean_object* v_f_1039_, lean_object* v_init_1040_, lean_object* v_as_1041_, lean_object* v_start_1042_, lean_object* v_stop_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Array_foldlMUnsafe___redArg(v_inst_1038_, v_f_1039_, v_init_1040_, v_as_1041_, v_start_1042_, v_stop_1043_);
lean_dec(v_stop_1043_);
lean_dec(v_start_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe(lean_object* v_00_u03b1_1045_, lean_object* v_00_u03b2_1046_, lean_object* v_m_1047_, lean_object* v_inst_1048_, lean_object* v_f_1049_, lean_object* v_init_1050_, lean_object* v_as_1051_, lean_object* v_start_1052_, lean_object* v_stop_1053_){
_start:
{
lean_object* v_toApplicative_1054_; lean_object* v_toPure_1055_; uint8_t v___x_1056_; 
v_toApplicative_1054_ = lean_ctor_get(v_inst_1048_, 0);
v_toPure_1055_ = lean_ctor_get(v_toApplicative_1054_, 1);
v___x_1056_ = lean_nat_dec_lt(v_start_1052_, v_stop_1053_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
lean_inc(v_toPure_1055_);
lean_dec_ref(v_as_1051_);
lean_dec(v_f_1049_);
lean_dec_ref(v_inst_1048_);
v___x_1057_ = lean_apply_2(v_toPure_1055_, lean_box(0), v_init_1050_);
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = lean_array_get_size(v_as_1051_);
v___x_1059_ = lean_nat_dec_le(v_stop_1053_, v___x_1058_);
if (v___x_1059_ == 0)
{
uint8_t v___x_1060_; 
v___x_1060_ = lean_nat_dec_lt(v_start_1052_, v___x_1058_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
lean_inc(v_toPure_1055_);
lean_dec_ref(v_as_1051_);
lean_dec(v_f_1049_);
lean_dec_ref(v_inst_1048_);
v___x_1061_ = lean_apply_2(v_toPure_1055_, lean_box(0), v_init_1050_);
return v___x_1061_;
}
else
{
size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = lean_usize_of_nat(v_start_1052_);
v___x_1063_ = lean_usize_of_nat(v___x_1058_);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1048_, v_f_1049_, v_as_1051_, v___x_1062_, v___x_1063_, v_init_1050_);
return v___x_1064_;
}
}
else
{
size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = lean_usize_of_nat(v_start_1052_);
v___x_1066_ = lean_usize_of_nat(v_stop_1053_);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1048_, v_f_1049_, v_as_1051_, v___x_1065_, v___x_1066_, v_init_1050_);
return v___x_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___boxed(lean_object* v_00_u03b1_1068_, lean_object* v_00_u03b2_1069_, lean_object* v_m_1070_, lean_object* v_inst_1071_, lean_object* v_f_1072_, lean_object* v_init_1073_, lean_object* v_as_1074_, lean_object* v_start_1075_, lean_object* v_stop_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Array_foldlMUnsafe(v_00_u03b1_1068_, v_00_u03b2_1069_, v_m_1070_, v_inst_1071_, v_f_1072_, v_init_1073_, v_as_1074_, v_start_1075_, v_stop_1076_);
lean_dec(v_stop_1076_);
lean_dec(v_start_1075_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_1078_, lean_object* v_inst_1079_, lean_object* v_f_1080_, lean_object* v_as_1081_, lean_object* v_stop_1082_, lean_object* v_n_1083_, lean_object* v_____do__lift_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Array_foldlM_loop___redArg___lam__0(v_j_1078_, v_inst_1079_, v_f_1080_, v_as_1081_, v_stop_1082_, v_n_1083_, v_____do__lift_1084_);
lean_dec(v_n_1083_);
lean_dec(v_j_1078_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg(lean_object* v_inst_1086_, lean_object* v_f_1087_, lean_object* v_as_1088_, lean_object* v_stop_1089_, lean_object* v_i_1090_, lean_object* v_j_1091_, lean_object* v_b_1092_){
_start:
{
lean_object* v_toApplicative_1093_; lean_object* v_toBind_1094_; lean_object* v_toPure_1095_; uint8_t v___x_1096_; 
v_toApplicative_1093_ = lean_ctor_get(v_inst_1086_, 0);
v_toBind_1094_ = lean_ctor_get(v_inst_1086_, 1);
lean_inc(v_toBind_1094_);
v_toPure_1095_ = lean_ctor_get(v_toApplicative_1093_, 1);
v___x_1096_ = lean_nat_dec_lt(v_j_1091_, v_stop_1089_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
lean_inc(v_toPure_1095_);
lean_dec(v_toBind_1094_);
lean_dec(v_j_1091_);
lean_dec(v_stop_1089_);
lean_dec_ref(v_as_1088_);
lean_dec(v_f_1087_);
lean_dec_ref(v_inst_1086_);
v___x_1097_ = lean_apply_2(v_toPure_1095_, lean_box(0), v_b_1092_);
return v___x_1097_;
}
else
{
lean_object* v_zero_1098_; uint8_t v_isZero_1099_; 
v_zero_1098_ = lean_unsigned_to_nat(0u);
v_isZero_1099_ = lean_nat_dec_eq(v_i_1090_, v_zero_1098_);
if (v_isZero_1099_ == 1)
{
lean_object* v___x_1100_; 
lean_inc(v_toPure_1095_);
lean_dec(v_toBind_1094_);
lean_dec(v_j_1091_);
lean_dec(v_stop_1089_);
lean_dec_ref(v_as_1088_);
lean_dec(v_f_1087_);
lean_dec_ref(v_inst_1086_);
v___x_1100_ = lean_apply_2(v_toPure_1095_, lean_box(0), v_b_1092_);
return v___x_1100_;
}
else
{
lean_object* v_one_1101_; lean_object* v_n_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_one_1101_ = lean_unsigned_to_nat(1u);
v_n_1102_ = lean_nat_sub(v_i_1090_, v_one_1101_);
lean_inc_ref(v_as_1088_);
lean_inc(v_f_1087_);
lean_inc(v_j_1091_);
v___f_1103_ = lean_alloc_closure((void*)(l_Array_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1103_, 0, v_j_1091_);
lean_closure_set(v___f_1103_, 1, v_inst_1086_);
lean_closure_set(v___f_1103_, 2, v_f_1087_);
lean_closure_set(v___f_1103_, 3, v_as_1088_);
lean_closure_set(v___f_1103_, 4, v_stop_1089_);
lean_closure_set(v___f_1103_, 5, v_n_1102_);
v___x_1104_ = lean_array_fget(v_as_1088_, v_j_1091_);
lean_dec(v_j_1091_);
lean_dec_ref(v_as_1088_);
v___x_1105_ = lean_apply_2(v_f_1087_, v_b_1092_, v___x_1104_);
v___x_1106_ = lean_apply_4(v_toBind_1094_, lean_box(0), lean_box(0), v___x_1105_, v___f_1103_);
return v___x_1106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0(lean_object* v_j_1107_, lean_object* v_inst_1108_, lean_object* v_f_1109_, lean_object* v_as_1110_, lean_object* v_stop_1111_, lean_object* v_n_1112_, lean_object* v_____do__lift_1113_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_unsigned_to_nat(1u);
v___x_1115_ = lean_nat_add(v_j_1107_, v___x_1114_);
v___x_1116_ = l_Array_foldlM_loop___redArg(v_inst_1108_, v_f_1109_, v_as_1110_, v_stop_1111_, v_n_1112_, v___x_1115_, v_____do__lift_1113_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___boxed(lean_object* v_inst_1117_, lean_object* v_f_1118_, lean_object* v_as_1119_, lean_object* v_stop_1120_, lean_object* v_i_1121_, lean_object* v_j_1122_, lean_object* v_b_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Array_foldlM_loop___redArg(v_inst_1117_, v_f_1118_, v_as_1119_, v_stop_1120_, v_i_1121_, v_j_1122_, v_b_1123_);
lean_dec(v_i_1121_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop(lean_object* v_00_u03b1_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_m_1127_, lean_object* v_inst_1128_, lean_object* v_f_1129_, lean_object* v_as_1130_, lean_object* v_stop_1131_, lean_object* v_h_1132_, lean_object* v_i_1133_, lean_object* v_j_1134_, lean_object* v_b_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Array_foldlM_loop___redArg(v_inst_1128_, v_f_1129_, v_as_1130_, v_stop_1131_, v_i_1133_, v_j_1134_, v_b_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___boxed(lean_object* v_00_u03b1_1137_, lean_object* v_00_u03b2_1138_, lean_object* v_m_1139_, lean_object* v_inst_1140_, lean_object* v_f_1141_, lean_object* v_as_1142_, lean_object* v_stop_1143_, lean_object* v_h_1144_, lean_object* v_i_1145_, lean_object* v_j_1146_, lean_object* v_b_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Array_foldlM_loop(v_00_u03b1_1137_, v_00_u03b2_1138_, v_m_1139_, v_inst_1140_, v_f_1141_, v_as_1142_, v_stop_1143_, v_h_1144_, v_i_1145_, v_j_1146_, v_b_1147_);
lean_dec(v_i_1145_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_inst_1149_, lean_object* v_f_1150_, lean_object* v_as_1151_, lean_object* v___x_1152_, lean_object* v_stop_1153_, lean_object* v_____do__lift_1154_){
_start:
{
size_t v___x_63__boxed_1155_; size_t v_stop_boxed_1156_; lean_object* v_res_1157_; 
v___x_63__boxed_1155_ = lean_unbox_usize(v___x_1152_);
lean_dec(v___x_1152_);
v_stop_boxed_1156_ = lean_unbox_usize(v_stop_1153_);
lean_dec(v_stop_1153_);
v_res_1157_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(v_inst_1149_, v_f_1150_, v_as_1151_, v___x_63__boxed_1155_, v_stop_boxed_1156_, v_____do__lift_1154_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(lean_object* v_inst_1158_, lean_object* v_f_1159_, lean_object* v_as_1160_, size_t v_i_1161_, size_t v_stop_1162_, lean_object* v_b_1163_){
_start:
{
lean_object* v_toApplicative_1164_; lean_object* v_toBind_1165_; lean_object* v_toPure_1166_; uint8_t v___x_1167_; 
v_toApplicative_1164_ = lean_ctor_get(v_inst_1158_, 0);
v_toBind_1165_ = lean_ctor_get(v_inst_1158_, 1);
lean_inc(v_toBind_1165_);
v_toPure_1166_ = lean_ctor_get(v_toApplicative_1164_, 1);
v___x_1167_ = lean_usize_dec_eq(v_i_1161_, v_stop_1162_);
if (v___x_1167_ == 0)
{
size_t v___x_1168_; size_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___f_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1168_ = ((size_t)1ULL);
v___x_1169_ = lean_usize_sub(v_i_1161_, v___x_1168_);
v___x_1170_ = lean_box_usize(v___x_1169_);
v___x_1171_ = lean_box_usize(v_stop_1162_);
lean_inc_ref(v_as_1160_);
lean_inc(v_f_1159_);
v___f_1172_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1172_, 0, v_inst_1158_);
lean_closure_set(v___f_1172_, 1, v_f_1159_);
lean_closure_set(v___f_1172_, 2, v_as_1160_);
lean_closure_set(v___f_1172_, 3, v___x_1170_);
lean_closure_set(v___f_1172_, 4, v___x_1171_);
v___x_1173_ = lean_array_uget(v_as_1160_, v___x_1169_);
lean_dec_ref(v_as_1160_);
v___x_1174_ = lean_apply_2(v_f_1159_, v___x_1173_, v_b_1163_);
v___x_1175_ = lean_apply_4(v_toBind_1165_, lean_box(0), lean_box(0), v___x_1174_, v___f_1172_);
return v___x_1175_;
}
else
{
lean_object* v___x_1176_; 
lean_inc(v_toPure_1166_);
lean_dec(v_toBind_1165_);
lean_dec_ref(v_as_1160_);
lean_dec(v_f_1159_);
lean_dec_ref(v_inst_1158_);
v___x_1176_ = lean_apply_2(v_toPure_1166_, lean_box(0), v_b_1163_);
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(lean_object* v_inst_1177_, lean_object* v_f_1178_, lean_object* v_as_1179_, size_t v___x_1180_, size_t v_stop_1181_, lean_object* v_____do__lift_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1177_, v_f_1178_, v_as_1179_, v___x_1180_, v_stop_1181_, v_____do__lift_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___boxed(lean_object* v_inst_1184_, lean_object* v_f_1185_, lean_object* v_as_1186_, lean_object* v_i_1187_, lean_object* v_stop_1188_, lean_object* v_b_1189_){
_start:
{
size_t v_i_boxed_1190_; size_t v_stop_boxed_1191_; lean_object* v_res_1192_; 
v_i_boxed_1190_ = lean_unbox_usize(v_i_1187_);
lean_dec(v_i_1187_);
v_stop_boxed_1191_ = lean_unbox_usize(v_stop_1188_);
lean_dec(v_stop_1188_);
v_res_1192_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1184_, v_f_1185_, v_as_1186_, v_i_boxed_1190_, v_stop_boxed_1191_, v_b_1189_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object* v_00_u03b1_1193_, lean_object* v_00_u03b2_1194_, lean_object* v_m_1195_, lean_object* v_inst_1196_, lean_object* v_f_1197_, lean_object* v_as_1198_, size_t v_i_1199_, size_t v_stop_1200_, lean_object* v_b_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1196_, v_f_1197_, v_as_1198_, v_i_1199_, v_stop_1200_, v_b_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___boxed(lean_object* v_00_u03b1_1203_, lean_object* v_00_u03b2_1204_, lean_object* v_m_1205_, lean_object* v_inst_1206_, lean_object* v_f_1207_, lean_object* v_as_1208_, lean_object* v_i_1209_, lean_object* v_stop_1210_, lean_object* v_b_1211_){
_start:
{
size_t v_i_boxed_1212_; size_t v_stop_boxed_1213_; lean_object* v_res_1214_; 
v_i_boxed_1212_ = lean_unbox_usize(v_i_1209_);
lean_dec(v_i_1209_);
v_stop_boxed_1213_ = lean_unbox_usize(v_stop_1210_);
lean_dec(v_stop_1210_);
v_res_1214_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(v_00_u03b1_1203_, v_00_u03b2_1204_, v_m_1205_, v_inst_1206_, v_f_1207_, v_as_1208_, v_i_boxed_1212_, v_stop_boxed_1213_, v_b_1211_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg(lean_object* v_inst_1215_, lean_object* v_f_1216_, lean_object* v_init_1217_, lean_object* v_as_1218_, lean_object* v_start_1219_, lean_object* v_stop_1220_){
_start:
{
lean_object* v_toApplicative_1221_; lean_object* v_toPure_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v_toApplicative_1221_ = lean_ctor_get(v_inst_1215_, 0);
v_toPure_1222_ = lean_ctor_get(v_toApplicative_1221_, 1);
v___x_1223_ = lean_array_get_size(v_as_1218_);
v___x_1224_ = lean_nat_dec_le(v_start_1219_, v___x_1223_);
if (v___x_1224_ == 0)
{
uint8_t v___x_1225_; 
v___x_1225_ = lean_nat_dec_lt(v_stop_1220_, v___x_1223_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; 
lean_inc(v_toPure_1222_);
lean_dec_ref(v_as_1218_);
lean_dec(v_f_1216_);
lean_dec_ref(v_inst_1215_);
v___x_1226_ = lean_apply_2(v_toPure_1222_, lean_box(0), v_init_1217_);
return v___x_1226_;
}
else
{
size_t v___x_1227_; size_t v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = lean_usize_of_nat(v___x_1223_);
v___x_1228_ = lean_usize_of_nat(v_stop_1220_);
v___x_1229_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1215_, v_f_1216_, v_as_1218_, v___x_1227_, v___x_1228_, v_init_1217_);
return v___x_1229_;
}
}
else
{
uint8_t v___x_1230_; 
v___x_1230_ = lean_nat_dec_lt(v_stop_1220_, v_start_1219_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; 
lean_inc(v_toPure_1222_);
lean_dec_ref(v_as_1218_);
lean_dec(v_f_1216_);
lean_dec_ref(v_inst_1215_);
v___x_1231_ = lean_apply_2(v_toPure_1222_, lean_box(0), v_init_1217_);
return v___x_1231_;
}
else
{
size_t v___x_1232_; size_t v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = lean_usize_of_nat(v_start_1219_);
v___x_1233_ = lean_usize_of_nat(v_stop_1220_);
v___x_1234_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1215_, v_f_1216_, v_as_1218_, v___x_1232_, v___x_1233_, v_init_1217_);
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg___boxed(lean_object* v_inst_1235_, lean_object* v_f_1236_, lean_object* v_init_1237_, lean_object* v_as_1238_, lean_object* v_start_1239_, lean_object* v_stop_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Array_foldrMUnsafe___redArg(v_inst_1235_, v_f_1236_, v_init_1237_, v_as_1238_, v_start_1239_, v_stop_1240_);
lean_dec(v_stop_1240_);
lean_dec(v_start_1239_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe(lean_object* v_00_u03b1_1242_, lean_object* v_00_u03b2_1243_, lean_object* v_m_1244_, lean_object* v_inst_1245_, lean_object* v_f_1246_, lean_object* v_init_1247_, lean_object* v_as_1248_, lean_object* v_start_1249_, lean_object* v_stop_1250_){
_start:
{
lean_object* v_toApplicative_1251_; lean_object* v_toPure_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v_toApplicative_1251_ = lean_ctor_get(v_inst_1245_, 0);
v_toPure_1252_ = lean_ctor_get(v_toApplicative_1251_, 1);
v___x_1253_ = lean_array_get_size(v_as_1248_);
v___x_1254_ = lean_nat_dec_le(v_start_1249_, v___x_1253_);
if (v___x_1254_ == 0)
{
uint8_t v___x_1255_; 
v___x_1255_ = lean_nat_dec_lt(v_stop_1250_, v___x_1253_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
lean_inc(v_toPure_1252_);
lean_dec_ref(v_as_1248_);
lean_dec(v_f_1246_);
lean_dec_ref(v_inst_1245_);
v___x_1256_ = lean_apply_2(v_toPure_1252_, lean_box(0), v_init_1247_);
return v___x_1256_;
}
else
{
size_t v___x_1257_; size_t v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_usize_of_nat(v___x_1253_);
v___x_1258_ = lean_usize_of_nat(v_stop_1250_);
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1245_, v_f_1246_, v_as_1248_, v___x_1257_, v___x_1258_, v_init_1247_);
return v___x_1259_;
}
}
else
{
uint8_t v___x_1260_; 
v___x_1260_ = lean_nat_dec_lt(v_stop_1250_, v_start_1249_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; 
lean_inc(v_toPure_1252_);
lean_dec_ref(v_as_1248_);
lean_dec(v_f_1246_);
lean_dec_ref(v_inst_1245_);
v___x_1261_ = lean_apply_2(v_toPure_1252_, lean_box(0), v_init_1247_);
return v___x_1261_;
}
else
{
size_t v___x_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_usize_of_nat(v_start_1249_);
v___x_1263_ = lean_usize_of_nat(v_stop_1250_);
v___x_1264_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1245_, v_f_1246_, v_as_1248_, v___x_1262_, v___x_1263_, v_init_1247_);
return v___x_1264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___boxed(lean_object* v_00_u03b1_1265_, lean_object* v_00_u03b2_1266_, lean_object* v_m_1267_, lean_object* v_inst_1268_, lean_object* v_f_1269_, lean_object* v_init_1270_, lean_object* v_as_1271_, lean_object* v_start_1272_, lean_object* v_stop_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Array_foldrMUnsafe(v_00_u03b1_1265_, v_00_u03b2_1266_, v_m_1267_, v_inst_1268_, v_f_1269_, v_init_1270_, v_as_1271_, v_start_1272_, v_stop_1273_);
lean_dec(v_stop_1273_);
lean_dec(v_start_1272_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0___boxed(lean_object* v_inst_1275_, lean_object* v_f_1276_, lean_object* v_as_1277_, lean_object* v_stop_1278_, lean_object* v_n_1279_, lean_object* v_____do__lift_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Array_foldrM_fold___redArg___lam__0(v_inst_1275_, v_f_1276_, v_as_1277_, v_stop_1278_, v_n_1279_, v_____do__lift_1280_);
lean_dec(v_n_1279_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg(lean_object* v_inst_1282_, lean_object* v_f_1283_, lean_object* v_as_1284_, lean_object* v_stop_1285_, lean_object* v_i_1286_, lean_object* v_b_1287_){
_start:
{
lean_object* v_toApplicative_1288_; lean_object* v_toBind_1289_; lean_object* v_toPure_1290_; uint8_t v___x_1291_; 
v_toApplicative_1288_ = lean_ctor_get(v_inst_1282_, 0);
v_toBind_1289_ = lean_ctor_get(v_inst_1282_, 1);
lean_inc(v_toBind_1289_);
v_toPure_1290_ = lean_ctor_get(v_toApplicative_1288_, 1);
v___x_1291_ = lean_nat_dec_eq(v_i_1286_, v_stop_1285_);
if (v___x_1291_ == 0)
{
lean_object* v_zero_1292_; uint8_t v_isZero_1293_; 
v_zero_1292_ = lean_unsigned_to_nat(0u);
v_isZero_1293_ = lean_nat_dec_eq(v_i_1286_, v_zero_1292_);
if (v_isZero_1293_ == 1)
{
lean_object* v___x_1294_; 
lean_inc(v_toPure_1290_);
lean_dec(v_toBind_1289_);
lean_dec(v_stop_1285_);
lean_dec_ref(v_as_1284_);
lean_dec(v_f_1283_);
lean_dec_ref(v_inst_1282_);
v___x_1294_ = lean_apply_2(v_toPure_1290_, lean_box(0), v_b_1287_);
return v___x_1294_;
}
else
{
lean_object* v_one_1295_; lean_object* v_n_1296_; lean_object* v___f_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_one_1295_ = lean_unsigned_to_nat(1u);
v_n_1296_ = lean_nat_sub(v_i_1286_, v_one_1295_);
lean_inc(v_n_1296_);
lean_inc_ref(v_as_1284_);
lean_inc(v_f_1283_);
v___f_1297_ = lean_alloc_closure((void*)(l_Array_foldrM_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1297_, 0, v_inst_1282_);
lean_closure_set(v___f_1297_, 1, v_f_1283_);
lean_closure_set(v___f_1297_, 2, v_as_1284_);
lean_closure_set(v___f_1297_, 3, v_stop_1285_);
lean_closure_set(v___f_1297_, 4, v_n_1296_);
v___x_1298_ = lean_array_fget(v_as_1284_, v_n_1296_);
lean_dec(v_n_1296_);
lean_dec_ref(v_as_1284_);
v___x_1299_ = lean_apply_2(v_f_1283_, v___x_1298_, v_b_1287_);
v___x_1300_ = lean_apply_4(v_toBind_1289_, lean_box(0), lean_box(0), v___x_1299_, v___f_1297_);
return v___x_1300_;
}
}
else
{
lean_object* v___x_1301_; 
lean_inc(v_toPure_1290_);
lean_dec(v_toBind_1289_);
lean_dec(v_stop_1285_);
lean_dec_ref(v_as_1284_);
lean_dec(v_f_1283_);
lean_dec_ref(v_inst_1282_);
v___x_1301_ = lean_apply_2(v_toPure_1290_, lean_box(0), v_b_1287_);
return v___x_1301_;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0(lean_object* v_inst_1302_, lean_object* v_f_1303_, lean_object* v_as_1304_, lean_object* v_stop_1305_, lean_object* v_n_1306_, lean_object* v_____do__lift_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Array_foldrM_fold___redArg(v_inst_1302_, v_f_1303_, v_as_1304_, v_stop_1305_, v_n_1306_, v_____do__lift_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___boxed(lean_object* v_inst_1309_, lean_object* v_f_1310_, lean_object* v_as_1311_, lean_object* v_stop_1312_, lean_object* v_i_1313_, lean_object* v_b_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Array_foldrM_fold___redArg(v_inst_1309_, v_f_1310_, v_as_1311_, v_stop_1312_, v_i_1313_, v_b_1314_);
lean_dec(v_i_1313_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold(lean_object* v_00_u03b1_1316_, lean_object* v_00_u03b2_1317_, lean_object* v_m_1318_, lean_object* v_inst_1319_, lean_object* v_f_1320_, lean_object* v_as_1321_, lean_object* v_stop_1322_, lean_object* v_i_1323_, lean_object* v_h_1324_, lean_object* v_b_1325_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Array_foldrM_fold___redArg(v_inst_1319_, v_f_1320_, v_as_1321_, v_stop_1322_, v_i_1323_, v_b_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___boxed(lean_object* v_00_u03b1_1327_, lean_object* v_00_u03b2_1328_, lean_object* v_m_1329_, lean_object* v_inst_1330_, lean_object* v_f_1331_, lean_object* v_as_1332_, lean_object* v_stop_1333_, lean_object* v_i_1334_, lean_object* v_h_1335_, lean_object* v_b_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Array_foldrM_fold(v_00_u03b1_1327_, v_00_u03b2_1328_, v_m_1329_, v_inst_1330_, v_f_1331_, v_as_1332_, v_stop_1333_, v_i_1334_, v_h_1335_, v_b_1336_);
lean_dec(v_i_1334_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed(lean_object* v_i_1338_, lean_object* v_bs_x27_1339_, lean_object* v_inst_1340_, lean_object* v_f_1341_, lean_object* v_sz_1342_, lean_object* v_vNew_1343_){
_start:
{
size_t v_i_boxed_1344_; size_t v_sz_boxed_1345_; lean_object* v_res_1346_; 
v_i_boxed_1344_ = lean_unbox_usize(v_i_1338_);
lean_dec(v_i_1338_);
v_sz_boxed_1345_ = lean_unbox_usize(v_sz_1342_);
lean_dec(v_sz_1342_);
v_res_1346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(v_i_boxed_1344_, v_bs_x27_1339_, v_inst_1340_, v_f_1341_, v_sz_boxed_1345_, v_vNew_1343_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(lean_object* v_inst_1347_, lean_object* v_f_1348_, size_t v_sz_1349_, size_t v_i_1350_, lean_object* v_bs_1351_){
_start:
{
lean_object* v_toApplicative_1352_; lean_object* v_toBind_1353_; lean_object* v_toPure_1354_; uint8_t v___x_1355_; 
v_toApplicative_1352_ = lean_ctor_get(v_inst_1347_, 0);
v_toBind_1353_ = lean_ctor_get(v_inst_1347_, 1);
lean_inc(v_toBind_1353_);
v_toPure_1354_ = lean_ctor_get(v_toApplicative_1352_, 1);
v___x_1355_ = lean_usize_dec_lt(v_i_1350_, v_sz_1349_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; 
lean_inc(v_toPure_1354_);
lean_dec(v_toBind_1353_);
lean_dec(v_f_1348_);
lean_dec_ref(v_inst_1347_);
v___x_1356_ = lean_apply_2(v_toPure_1354_, lean_box(0), v_bs_1351_);
return v___x_1356_;
}
else
{
lean_object* v_v_1357_; lean_object* v___x_1358_; lean_object* v_bs_x27_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___f_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v_v_1357_ = lean_array_uget(v_bs_1351_, v_i_1350_);
v___x_1358_ = lean_unsigned_to_nat(0u);
v_bs_x27_1359_ = lean_array_uset(v_bs_1351_, v_i_1350_, v___x_1358_);
v___x_1360_ = lean_box_usize(v_i_1350_);
v___x_1361_ = lean_box_usize(v_sz_1349_);
lean_inc(v_f_1348_);
v___f_1362_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1362_, 0, v___x_1360_);
lean_closure_set(v___f_1362_, 1, v_bs_x27_1359_);
lean_closure_set(v___f_1362_, 2, v_inst_1347_);
lean_closure_set(v___f_1362_, 3, v_f_1348_);
lean_closure_set(v___f_1362_, 4, v___x_1361_);
v___x_1363_ = lean_apply_1(v_f_1348_, v_v_1357_);
v___x_1364_ = lean_apply_4(v_toBind_1353_, lean_box(0), lean_box(0), v___x_1363_, v___f_1362_);
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(size_t v_i_1365_, lean_object* v_bs_x27_1366_, lean_object* v_inst_1367_, lean_object* v_f_1368_, size_t v_sz_1369_, lean_object* v_vNew_1370_){
_start:
{
size_t v___x_1371_; size_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1371_ = ((size_t)1ULL);
v___x_1372_ = lean_usize_add(v_i_1365_, v___x_1371_);
v___x_1373_ = lean_array_uset(v_bs_x27_1366_, v_i_1365_, v_vNew_1370_);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1367_, v_f_1368_, v_sz_1369_, v___x_1372_, v___x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___boxed(lean_object* v_inst_1375_, lean_object* v_f_1376_, lean_object* v_sz_1377_, lean_object* v_i_1378_, lean_object* v_bs_1379_){
_start:
{
size_t v_sz_boxed_1380_; size_t v_i_boxed_1381_; lean_object* v_res_1382_; 
v_sz_boxed_1380_ = lean_unbox_usize(v_sz_1377_);
lean_dec(v_sz_1377_);
v_i_boxed_1381_ = lean_unbox_usize(v_i_1378_);
lean_dec(v_i_1378_);
v_res_1382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1375_, v_f_1376_, v_sz_boxed_1380_, v_i_boxed_1381_, v_bs_1379_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object* v_00_u03b1_1383_, lean_object* v_00_u03b2_1384_, lean_object* v_m_1385_, lean_object* v_inst_1386_, lean_object* v_f_1387_, size_t v_sz_1388_, size_t v_i_1389_, lean_object* v_bs_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1386_, v_f_1387_, v_sz_1388_, v_i_1389_, v_bs_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___boxed(lean_object* v_00_u03b1_1392_, lean_object* v_00_u03b2_1393_, lean_object* v_m_1394_, lean_object* v_inst_1395_, lean_object* v_f_1396_, lean_object* v_sz_1397_, lean_object* v_i_1398_, lean_object* v_bs_1399_){
_start:
{
size_t v_sz_boxed_1400_; size_t v_i_boxed_1401_; lean_object* v_res_1402_; 
v_sz_boxed_1400_ = lean_unbox_usize(v_sz_1397_);
lean_dec(v_sz_1397_);
v_i_boxed_1401_ = lean_unbox_usize(v_i_1398_);
lean_dec(v_i_1398_);
v_res_1402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(v_00_u03b1_1392_, v_00_u03b2_1393_, v_m_1394_, v_inst_1395_, v_f_1396_, v_sz_boxed_1400_, v_i_boxed_1401_, v_bs_1399_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe___redArg(lean_object* v_inst_1403_, lean_object* v_f_1404_, lean_object* v_as_1405_){
_start:
{
size_t v_sz_1406_; size_t v___x_1407_; lean_object* v___x_1408_; 
v_sz_1406_ = lean_array_size(v_as_1405_);
v___x_1407_ = ((size_t)0ULL);
v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1403_, v_f_1404_, v_sz_1406_, v___x_1407_, v_as_1405_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe(lean_object* v_00_u03b1_1409_, lean_object* v_00_u03b2_1410_, lean_object* v_m_1411_, lean_object* v_inst_1412_, lean_object* v_f_1413_, lean_object* v_as_1414_){
_start:
{
size_t v_sz_1415_; size_t v___x_1416_; lean_object* v___x_1417_; 
v_sz_1415_ = lean_array_size(v_as_1414_);
v___x_1416_ = ((size_t)0ULL);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1412_, v_f_1413_, v_sz_1415_, v___x_1416_, v_as_1414_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_map___redArg___lam__0___boxed(lean_object* v_i_1418_, lean_object* v_bs_1419_, lean_object* v_inst_1420_, lean_object* v_f_1421_, lean_object* v_as_1422_, lean_object* v_____do__lift_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Array_mapM_map___redArg___lam__0(v_i_1418_, v_bs_1419_, v_inst_1420_, v_f_1421_, v_as_1422_, v_____do__lift_1423_);
lean_dec(v_i_1418_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_map___redArg(lean_object* v_inst_1425_, lean_object* v_f_1426_, lean_object* v_as_1427_, lean_object* v_i_1428_, lean_object* v_bs_1429_){
_start:
{
lean_object* v_toApplicative_1430_; lean_object* v_toBind_1431_; lean_object* v_toPure_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v_toApplicative_1430_ = lean_ctor_get(v_inst_1425_, 0);
v_toBind_1431_ = lean_ctor_get(v_inst_1425_, 1);
lean_inc(v_toBind_1431_);
v_toPure_1432_ = lean_ctor_get(v_toApplicative_1430_, 1);
v___x_1433_ = lean_array_get_size(v_as_1427_);
v___x_1434_ = lean_nat_dec_lt(v_i_1428_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; 
lean_inc(v_toPure_1432_);
lean_dec(v_toBind_1431_);
lean_dec(v_i_1428_);
lean_dec_ref(v_as_1427_);
lean_dec(v_f_1426_);
lean_dec_ref(v_inst_1425_);
v___x_1435_ = lean_apply_2(v_toPure_1432_, lean_box(0), v_bs_1429_);
return v___x_1435_;
}
else
{
lean_object* v___f_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_inc_ref(v_as_1427_);
lean_inc(v_f_1426_);
lean_inc(v_i_1428_);
v___f_1436_ = lean_alloc_closure((void*)(l_Array_mapM_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1436_, 0, v_i_1428_);
lean_closure_set(v___f_1436_, 1, v_bs_1429_);
lean_closure_set(v___f_1436_, 2, v_inst_1425_);
lean_closure_set(v___f_1436_, 3, v_f_1426_);
lean_closure_set(v___f_1436_, 4, v_as_1427_);
v___x_1437_ = lean_array_fget(v_as_1427_, v_i_1428_);
lean_dec(v_i_1428_);
lean_dec_ref(v_as_1427_);
v___x_1438_ = lean_apply_1(v_f_1426_, v___x_1437_);
v___x_1439_ = lean_apply_4(v_toBind_1431_, lean_box(0), lean_box(0), v___x_1438_, v___f_1436_);
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapM_map___redArg___lam__0(lean_object* v_i_1440_, lean_object* v_bs_1441_, lean_object* v_inst_1442_, lean_object* v_f_1443_, lean_object* v_as_1444_, lean_object* v_____do__lift_1445_){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_add(v_i_1440_, v___x_1446_);
v___x_1448_ = lean_array_push(v_bs_1441_, v_____do__lift_1445_);
v___x_1449_ = l_Array_mapM_map___redArg(v_inst_1442_, v_f_1443_, v_as_1444_, v___x_1447_, v___x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_map(lean_object* v_00_u03b1_1450_, lean_object* v_00_u03b2_1451_, lean_object* v_m_1452_, lean_object* v_inst_1453_, lean_object* v_f_1454_, lean_object* v_as_1455_, lean_object* v_i_1456_, lean_object* v_bs_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Array_mapM_map___redArg(v_inst_1453_, v_f_1454_, v_as_1455_, v_i_1456_, v_bs_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0___boxed(lean_object* v_i_1459_, lean_object* v_bs_x27_1460_, lean_object* v_inst_1461_, lean_object* v_f_1462_, lean_object* v_sz_1463_, lean_object* v_vNew_1464_){
_start:
{
size_t v_i_boxed_1465_; size_t v_sz_boxed_1466_; lean_object* v_res_1467_; 
v_i_boxed_1465_ = lean_unbox_usize(v_i_1459_);
lean_dec(v_i_1459_);
v_sz_boxed_1466_ = lean_unbox_usize(v_sz_1463_);
lean_dec(v_sz_1463_);
v_res_1467_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0(v_i_boxed_1465_, v_bs_x27_1460_, v_inst_1461_, v_f_1462_, v_sz_boxed_1466_, v_vNew_1464_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(lean_object* v_inst_1468_, lean_object* v_f_1469_, size_t v_sz_1470_, size_t v_i_1471_, lean_object* v_bs_1472_){
_start:
{
lean_object* v_toApplicative_1473_; lean_object* v_toBind_1474_; lean_object* v_toPure_1475_; uint8_t v___x_1476_; 
v_toApplicative_1473_ = lean_ctor_get(v_inst_1468_, 0);
v_toBind_1474_ = lean_ctor_get(v_inst_1468_, 1);
lean_inc(v_toBind_1474_);
v_toPure_1475_ = lean_ctor_get(v_toApplicative_1473_, 1);
v___x_1476_ = lean_usize_dec_lt(v_i_1471_, v_sz_1470_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_inc(v_toPure_1475_);
lean_dec(v_toBind_1474_);
lean_dec(v_f_1469_);
lean_dec_ref(v_inst_1468_);
v___x_1477_ = lean_apply_2(v_toPure_1475_, lean_box(0), v_bs_1472_);
return v___x_1477_;
}
else
{
lean_object* v_v_1478_; lean_object* v___x_1479_; lean_object* v_bs_x27_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___f_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v_v_1478_ = lean_array_uget(v_bs_1472_, v_i_1471_);
v___x_1479_ = lean_unsigned_to_nat(0u);
v_bs_x27_1480_ = lean_array_uset(v_bs_1472_, v_i_1471_, v___x_1479_);
v___x_1481_ = lean_box_usize(v_i_1471_);
v___x_1482_ = lean_box_usize(v_sz_1470_);
lean_inc(v_f_1469_);
v___f_1483_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1483_, 0, v___x_1481_);
lean_closure_set(v___f_1483_, 1, v_bs_x27_1480_);
lean_closure_set(v___f_1483_, 2, v_inst_1468_);
lean_closure_set(v___f_1483_, 3, v_f_1469_);
lean_closure_set(v___f_1483_, 4, v___x_1482_);
v___x_1484_ = lean_usize_to_nat(v_i_1471_);
v___x_1485_ = lean_apply_3(v_f_1469_, v___x_1484_, v_v_1478_, lean_box(0));
v___x_1486_ = lean_apply_4(v_toBind_1474_, lean_box(0), lean_box(0), v___x_1485_, v___f_1483_);
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0(size_t v_i_1487_, lean_object* v_bs_x27_1488_, lean_object* v_inst_1489_, lean_object* v_f_1490_, size_t v_sz_1491_, lean_object* v_vNew_1492_){
_start:
{
size_t v___x_1493_; size_t v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1493_ = ((size_t)1ULL);
v___x_1494_ = lean_usize_add(v_i_1487_, v___x_1493_);
v___x_1495_ = lean_array_uset(v_bs_x27_1488_, v_i_1487_, v_vNew_1492_);
v___x_1496_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1489_, v_f_1490_, v_sz_1491_, v___x_1494_, v___x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___boxed(lean_object* v_inst_1497_, lean_object* v_f_1498_, lean_object* v_sz_1499_, lean_object* v_i_1500_, lean_object* v_bs_1501_){
_start:
{
size_t v_sz_boxed_1502_; size_t v_i_boxed_1503_; lean_object* v_res_1504_; 
v_sz_boxed_1502_ = lean_unbox_usize(v_sz_1499_);
lean_dec(v_sz_1499_);
v_i_boxed_1503_ = lean_unbox_usize(v_i_1500_);
lean_dec(v_i_1500_);
v_res_1504_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1497_, v_f_1498_, v_sz_boxed_1502_, v_i_boxed_1503_, v_bs_1501_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object* v_00_u03b1_1505_, lean_object* v_00_u03b2_1506_, lean_object* v_m_1507_, lean_object* v_inst_1508_, lean_object* v_as_1509_, lean_object* v_f_1510_, size_t v_sz_1511_, size_t v_i_1512_, lean_object* v_bs_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1508_, v_f_1510_, v_sz_1511_, v_i_1512_, v_bs_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___boxed(lean_object* v_00_u03b1_1515_, lean_object* v_00_u03b2_1516_, lean_object* v_m_1517_, lean_object* v_inst_1518_, lean_object* v_as_1519_, lean_object* v_f_1520_, lean_object* v_sz_1521_, lean_object* v_i_1522_, lean_object* v_bs_1523_){
_start:
{
size_t v_sz_boxed_1524_; size_t v_i_boxed_1525_; lean_object* v_res_1526_; 
v_sz_boxed_1524_ = lean_unbox_usize(v_sz_1521_);
lean_dec(v_sz_1521_);
v_i_boxed_1525_ = lean_unbox_usize(v_i_1522_);
lean_dec(v_i_1522_);
v_res_1526_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(v_00_u03b1_1515_, v_00_u03b2_1516_, v_m_1517_, v_inst_1518_, v_as_1519_, v_f_1520_, v_sz_boxed_1524_, v_i_boxed_1525_, v_bs_1523_);
lean_dec_ref(v_as_1519_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxMUnsafe___redArg(lean_object* v_inst_1527_, lean_object* v_as_1528_, lean_object* v_f_1529_){
_start:
{
size_t v_sz_1530_; size_t v___x_1531_; lean_object* v___x_1532_; 
v_sz_1530_ = lean_array_size(v_as_1528_);
v___x_1531_ = ((size_t)0ULL);
v___x_1532_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1527_, v_f_1529_, v_sz_1530_, v___x_1531_, v_as_1528_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxMUnsafe(lean_object* v_00_u03b1_1533_, lean_object* v_00_u03b2_1534_, lean_object* v_m_1535_, lean_object* v_inst_1536_, lean_object* v_as_1537_, lean_object* v_f_1538_){
_start:
{
size_t v_sz_1539_; size_t v___x_1540_; lean_object* v___x_1541_; 
v_sz_1539_ = lean_array_size(v_as_1537_);
v___x_1540_ = ((size_t)0ULL);
v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1536_, v_f_1538_, v_sz_1539_, v___x_1540_, v_as_1537_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1542_, lean_object* v_bs_1543_, lean_object* v_inst_1544_, lean_object* v_as_1545_, lean_object* v_f_1546_, lean_object* v_n_1547_, lean_object* v_____do__lift_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Array_mapFinIdxM_map___redArg___lam__0(v_j_1542_, v_bs_1543_, v_inst_1544_, v_as_1545_, v_f_1546_, v_n_1547_, v_____do__lift_1548_);
lean_dec(v_n_1547_);
lean_dec(v_j_1542_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg(lean_object* v_inst_1550_, lean_object* v_as_1551_, lean_object* v_f_1552_, lean_object* v_i_1553_, lean_object* v_j_1554_, lean_object* v_bs_1555_){
_start:
{
lean_object* v_toApplicative_1556_; lean_object* v_toBind_1557_; lean_object* v_toPure_1558_; lean_object* v_zero_1559_; uint8_t v_isZero_1560_; 
v_toApplicative_1556_ = lean_ctor_get(v_inst_1550_, 0);
v_toBind_1557_ = lean_ctor_get(v_inst_1550_, 1);
lean_inc(v_toBind_1557_);
v_toPure_1558_ = lean_ctor_get(v_toApplicative_1556_, 1);
v_zero_1559_ = lean_unsigned_to_nat(0u);
v_isZero_1560_ = lean_nat_dec_eq(v_i_1553_, v_zero_1559_);
if (v_isZero_1560_ == 1)
{
lean_object* v___x_1561_; 
lean_inc(v_toPure_1558_);
lean_dec(v_toBind_1557_);
lean_dec(v_j_1554_);
lean_dec(v_f_1552_);
lean_dec_ref(v_as_1551_);
lean_dec_ref(v_inst_1550_);
v___x_1561_ = lean_apply_2(v_toPure_1558_, lean_box(0), v_bs_1555_);
return v___x_1561_;
}
else
{
lean_object* v_one_1562_; lean_object* v_n_1563_; lean_object* v___f_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v_one_1562_ = lean_unsigned_to_nat(1u);
v_n_1563_ = lean_nat_sub(v_i_1553_, v_one_1562_);
lean_inc(v_f_1552_);
lean_inc_ref(v_as_1551_);
lean_inc(v_j_1554_);
v___f_1564_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1564_, 0, v_j_1554_);
lean_closure_set(v___f_1564_, 1, v_bs_1555_);
lean_closure_set(v___f_1564_, 2, v_inst_1550_);
lean_closure_set(v___f_1564_, 3, v_as_1551_);
lean_closure_set(v___f_1564_, 4, v_f_1552_);
lean_closure_set(v___f_1564_, 5, v_n_1563_);
v___x_1565_ = lean_array_fget(v_as_1551_, v_j_1554_);
lean_dec_ref(v_as_1551_);
v___x_1566_ = lean_apply_3(v_f_1552_, v_j_1554_, v___x_1565_, lean_box(0));
v___x_1567_ = lean_apply_4(v_toBind_1557_, lean_box(0), lean_box(0), v___x_1566_, v___f_1564_);
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1568_, lean_object* v_bs_1569_, lean_object* v_inst_1570_, lean_object* v_as_1571_, lean_object* v_f_1572_, lean_object* v_n_1573_, lean_object* v_____do__lift_1574_){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1575_ = lean_unsigned_to_nat(1u);
v___x_1576_ = lean_nat_add(v_j_1568_, v___x_1575_);
v___x_1577_ = lean_array_push(v_bs_1569_, v_____do__lift_1574_);
v___x_1578_ = l_Array_mapFinIdxM_map___redArg(v_inst_1570_, v_as_1571_, v_f_1572_, v_n_1573_, v___x_1576_, v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1579_, lean_object* v_as_1580_, lean_object* v_f_1581_, lean_object* v_i_1582_, lean_object* v_j_1583_, lean_object* v_bs_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Array_mapFinIdxM_map___redArg(v_inst_1579_, v_as_1580_, v_f_1581_, v_i_1582_, v_j_1583_, v_bs_1584_);
lean_dec(v_i_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map(lean_object* v_00_u03b1_1586_, lean_object* v_00_u03b2_1587_, lean_object* v_m_1588_, lean_object* v_inst_1589_, lean_object* v_as_1590_, lean_object* v_f_1591_, lean_object* v_i_1592_, lean_object* v_j_1593_, lean_object* v_inv_1594_, lean_object* v_bs_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Array_mapFinIdxM_map___redArg(v_inst_1589_, v_as_1590_, v_f_1591_, v_i_1592_, v_j_1593_, v_bs_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___boxed(lean_object* v_00_u03b1_1597_, lean_object* v_00_u03b2_1598_, lean_object* v_m_1599_, lean_object* v_inst_1600_, lean_object* v_as_1601_, lean_object* v_f_1602_, lean_object* v_i_1603_, lean_object* v_j_1604_, lean_object* v_inv_1605_, lean_object* v_bs_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Array_mapFinIdxM_map(v_00_u03b1_1597_, v_00_u03b2_1598_, v_m_1599_, v_inst_1600_, v_as_1601_, v_f_1602_, v_i_1603_, v_j_1604_, v_inv_1605_, v_bs_1606_);
lean_dec(v_i_1603_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg___lam__0(lean_object* v_f_1608_, lean_object* v_i_1609_, lean_object* v_a_1610_, lean_object* v_x_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_apply_2(v_f_1608_, v_i_1609_, v_a_1610_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg(lean_object* v_inst_1613_, lean_object* v_f_1614_, lean_object* v_as_1615_){
_start:
{
lean_object* v___f_1616_; size_t v_sz_1617_; size_t v___x_1618_; lean_object* v___x_1619_; 
v___f_1616_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1616_, 0, v_f_1614_);
v_sz_1617_ = lean_array_size(v_as_1615_);
v___x_1618_ = ((size_t)0ULL);
v___x_1619_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1613_, v___f_1616_, v_sz_1617_, v___x_1618_, v_as_1615_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM(lean_object* v_00_u03b1_1620_, lean_object* v_00_u03b2_1621_, lean_object* v_m_1622_, lean_object* v_inst_1623_, lean_object* v_f_1624_, lean_object* v_as_1625_){
_start:
{
lean_object* v___f_1626_; size_t v_sz_1627_; size_t v___x_1628_; lean_object* v___x_1629_; 
v___f_1626_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1626_, 0, v_f_1624_);
v_sz_1627_ = lean_array_size(v_as_1625_);
v___x_1628_ = ((size_t)0ULL);
v___x_1629_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1623_, v___f_1626_, v_sz_1627_, v___x_1628_, v_as_1625_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed(lean_object* v_i_1630_, lean_object* v_inst_1631_, lean_object* v_f_1632_, lean_object* v_as_1633_, lean_object* v_x_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(v_i_1630_, v_inst_1631_, v_f_1632_, v_as_1633_, v_x_1634_);
lean_dec(v_i_1630_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(lean_object* v_inst_1636_, lean_object* v_f_1637_, lean_object* v_as_1638_, lean_object* v_i_1639_){
_start:
{
lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1640_ = lean_array_get_size(v_as_1638_);
v___x_1641_ = lean_nat_dec_lt(v_i_1639_, v___x_1640_);
if (v___x_1641_ == 0)
{
lean_object* v_failure_1642_; lean_object* v___x_1643_; 
lean_dec(v_i_1639_);
lean_dec_ref(v_as_1638_);
lean_dec(v_f_1637_);
v_failure_1642_ = lean_ctor_get(v_inst_1636_, 1);
lean_inc(v_failure_1642_);
lean_dec_ref(v_inst_1636_);
v___x_1643_ = lean_apply_1(v_failure_1642_, lean_box(0));
return v___x_1643_;
}
else
{
lean_object* v_orElse_1644_; lean_object* v___f_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_orElse_1644_ = lean_ctor_get(v_inst_1636_, 2);
lean_inc(v_orElse_1644_);
lean_inc_ref(v_as_1638_);
lean_inc(v_f_1637_);
lean_inc(v_i_1639_);
v___f_1645_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1645_, 0, v_i_1639_);
lean_closure_set(v___f_1645_, 1, v_inst_1636_);
lean_closure_set(v___f_1645_, 2, v_f_1637_);
lean_closure_set(v___f_1645_, 3, v_as_1638_);
v___x_1646_ = lean_array_fget(v_as_1638_, v_i_1639_);
lean_dec(v_i_1639_);
lean_dec_ref(v_as_1638_);
v___x_1647_ = lean_apply_1(v_f_1637_, v___x_1646_);
v___x_1648_ = lean_apply_3(v_orElse_1644_, lean_box(0), v___x_1647_, v___f_1645_);
return v___x_1648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(lean_object* v_i_1649_, lean_object* v_inst_1650_, lean_object* v_f_1651_, lean_object* v_as_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = lean_unsigned_to_nat(1u);
v___x_1655_ = lean_nat_add(v_i_1649_, v___x_1654_);
v___x_1656_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1650_, v_f_1651_, v_as_1652_, v___x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_object* v_00_u03b2_1657_, lean_object* v_00_u03b1_1658_, lean_object* v_m_1659_, lean_object* v_inst_1660_, lean_object* v_f_1661_, lean_object* v_as_1662_, lean_object* v_i_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1660_, v_f_1661_, v_as_1662_, v_i_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM___redArg(lean_object* v_inst_1665_, lean_object* v_f_1666_, lean_object* v_as_1667_){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = lean_unsigned_to_nat(0u);
v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1665_, v_f_1666_, v_as_1667_, v___x_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM(lean_object* v_00_u03b2_1670_, lean_object* v_00_u03b1_1671_, lean_object* v_m_1672_, lean_object* v_inst_1673_, lean_object* v_f_1674_, lean_object* v_as_1675_){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1673_, v_f_1674_, v_as_1675_, v___x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__0(lean_object* v___x_1678_, lean_object* v_toPure_1679_, lean_object* v___x_1680_, lean_object* v_____do__lift_1681_){
_start:
{
if (lean_obj_tag(v_____do__lift_1681_) == 1)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec_ref(v___x_1680_);
v___x_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1682_, 0, v_____do__lift_1681_);
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
lean_ctor_set(v___x_1683_, 1, v___x_1678_);
v___x_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
v___x_1685_ = lean_apply_2(v_toPure_1679_, lean_box(0), v___x_1684_);
return v___x_1685_;
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_dec(v_____do__lift_1681_);
v___x_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1680_);
v___x_1687_ = lean_apply_2(v_toPure_1679_, lean_box(0), v___x_1686_);
return v___x_1687_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1(lean_object* v_f_1688_, lean_object* v_toBind_1689_, lean_object* v___f_1690_, lean_object* v_a_1691_, lean_object* v_x_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_apply_1(v_f_1688_, v_a_1691_);
v___x_1695_ = lean_apply_4(v_toBind_1689_, lean_box(0), lean_box(0), v___x_1694_, v___f_1690_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1___boxed(lean_object* v_f_1696_, lean_object* v_toBind_1697_, lean_object* v___f_1698_, lean_object* v_a_1699_, lean_object* v_x_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Array_findSomeM_x3f___redArg___lam__1(v_f_1696_, v_toBind_1697_, v___f_1698_, v_a_1699_, v_x_1700_, v___y_1701_);
lean_dec_ref(v___y_1701_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__2(lean_object* v_toPure_1703_, lean_object* v_____s_1704_){
_start:
{
lean_object* v_fst_1705_; 
v_fst_1705_ = lean_ctor_get(v_____s_1704_, 0);
lean_inc(v_fst_1705_);
lean_dec_ref(v_____s_1704_);
if (lean_obj_tag(v_fst_1705_) == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_box(0);
v___x_1707_ = lean_apply_2(v_toPure_1703_, lean_box(0), v___x_1706_);
return v___x_1707_;
}
else
{
lean_object* v_val_1708_; lean_object* v___x_1709_; 
v_val_1708_ = lean_ctor_get(v_fst_1705_, 0);
lean_inc(v_val_1708_);
lean_dec_ref_known(v_fst_1705_, 1);
v___x_1709_ = lean_apply_2(v_toPure_1703_, lean_box(0), v_val_1708_);
return v___x_1709_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg(lean_object* v_inst_1713_, lean_object* v_f_1714_, lean_object* v_as_1715_){
_start:
{
lean_object* v_toApplicative_1716_; lean_object* v_toBind_1717_; lean_object* v_toPure_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___f_1721_; lean_object* v___f_1722_; lean_object* v___f_1723_; size_t v_sz_1724_; size_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_toApplicative_1716_ = lean_ctor_get(v_inst_1713_, 0);
v_toBind_1717_ = lean_ctor_get(v_inst_1713_, 1);
lean_inc_n(v_toBind_1717_, 2);
v_toPure_1718_ = lean_ctor_get(v_toApplicative_1716_, 1);
v___x_1719_ = lean_box(0);
v___x_1720_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1718_, 2);
v___f_1721_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1721_, 0, v___x_1719_);
lean_closure_set(v___f_1721_, 1, v_toPure_1718_);
lean_closure_set(v___f_1721_, 2, v___x_1720_);
v___f_1722_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1722_, 0, v_f_1714_);
lean_closure_set(v___f_1722_, 1, v_toBind_1717_);
lean_closure_set(v___f_1722_, 2, v___f_1721_);
v___f_1723_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1723_, 0, v_toPure_1718_);
v_sz_1724_ = lean_array_size(v_as_1715_);
v___x_1725_ = ((size_t)0ULL);
v___x_1726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1713_, v_as_1715_, v___f_1722_, v_sz_1724_, v___x_1725_, v___x_1720_);
v___x_1727_ = lean_apply_4(v_toBind_1717_, lean_box(0), lean_box(0), v___x_1726_, v___f_1723_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f(lean_object* v_00_u03b1_1728_, lean_object* v_00_u03b2_1729_, lean_object* v_m_1730_, lean_object* v_inst_1731_, lean_object* v_f_1732_, lean_object* v_as_1733_){
_start:
{
lean_object* v_toApplicative_1734_; lean_object* v_toBind_1735_; lean_object* v_toPure_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___f_1739_; lean_object* v___f_1740_; lean_object* v___f_1741_; size_t v_sz_1742_; size_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_toApplicative_1734_ = lean_ctor_get(v_inst_1731_, 0);
v_toBind_1735_ = lean_ctor_get(v_inst_1731_, 1);
lean_inc_n(v_toBind_1735_, 2);
v_toPure_1736_ = lean_ctor_get(v_toApplicative_1734_, 1);
v___x_1737_ = lean_box(0);
v___x_1738_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1736_, 2);
v___f_1739_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1739_, 0, v___x_1737_);
lean_closure_set(v___f_1739_, 1, v_toPure_1736_);
lean_closure_set(v___f_1739_, 2, v___x_1738_);
v___f_1740_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1740_, 0, v_f_1732_);
lean_closure_set(v___f_1740_, 1, v_toBind_1735_);
lean_closure_set(v___f_1740_, 2, v___f_1739_);
v___f_1741_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1741_, 0, v_toPure_1736_);
v_sz_1742_ = lean_array_size(v_as_1733_);
v___x_1743_ = ((size_t)0ULL);
v___x_1744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1731_, v_as_1733_, v___f_1740_, v_sz_1742_, v___x_1743_, v___x_1738_);
v___x_1745_ = lean_apply_4(v_toBind_1735_, lean_box(0), lean_box(0), v___x_1744_, v___f_1741_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0(lean_object* v___x_1746_, lean_object* v_toPure_1747_, lean_object* v_a_1748_, lean_object* v___x_1749_, uint8_t v_____do__lift_1750_){
_start:
{
if (v_____do__lift_1750_ == 0)
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec(v_a_1748_);
v___x_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1746_);
v___x_1752_ = lean_apply_2(v_toPure_1747_, lean_box(0), v___x_1751_);
return v___x_1752_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec_ref(v___x_1746_);
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_a_1748_);
v___x_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v___x_1749_);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
v___x_1757_ = lean_apply_2(v_toPure_1747_, lean_box(0), v___x_1756_);
return v___x_1757_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0___boxed(lean_object* v___x_1758_, lean_object* v_toPure_1759_, lean_object* v_a_1760_, lean_object* v___x_1761_, lean_object* v_____do__lift_1762_){
_start:
{
uint8_t v_____do__lift_185__boxed_1763_; lean_object* v_res_1764_; 
v_____do__lift_185__boxed_1763_ = lean_unbox(v_____do__lift_1762_);
v_res_1764_ = l_Array_findM_x3f___redArg___lam__0(v___x_1758_, v_toPure_1759_, v_a_1760_, v___x_1761_, v_____do__lift_185__boxed_1763_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1(lean_object* v___x_1765_, lean_object* v_toPure_1766_, lean_object* v___x_1767_, lean_object* v_p_1768_, lean_object* v_toBind_1769_, lean_object* v_a_1770_, lean_object* v_x_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___f_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_inc(v_a_1770_);
v___f_1773_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1773_, 0, v___x_1765_);
lean_closure_set(v___f_1773_, 1, v_toPure_1766_);
lean_closure_set(v___f_1773_, 2, v_a_1770_);
lean_closure_set(v___f_1773_, 3, v___x_1767_);
v___x_1774_ = lean_apply_1(v_p_1768_, v_a_1770_);
v___x_1775_ = lean_apply_4(v_toBind_1769_, lean_box(0), lean_box(0), v___x_1774_, v___f_1773_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_1776_, lean_object* v_toPure_1777_, lean_object* v___x_1778_, lean_object* v_p_1779_, lean_object* v_toBind_1780_, lean_object* v_a_1781_, lean_object* v_x_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Array_findM_x3f___redArg___lam__1(v___x_1776_, v_toPure_1777_, v___x_1778_, v_p_1779_, v_toBind_1780_, v_a_1781_, v_x_1782_, v___y_1783_);
lean_dec_ref(v___y_1783_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg(lean_object* v_inst_1785_, lean_object* v_p_1786_, lean_object* v_as_1787_){
_start:
{
lean_object* v_toApplicative_1788_; lean_object* v_toBind_1789_; lean_object* v_toPure_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___f_1793_; lean_object* v___f_1794_; size_t v_sz_1795_; size_t v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v_toApplicative_1788_ = lean_ctor_get(v_inst_1785_, 0);
v_toBind_1789_ = lean_ctor_get(v_inst_1785_, 1);
lean_inc_n(v_toBind_1789_, 2);
v_toPure_1790_ = lean_ctor_get(v_toApplicative_1788_, 1);
v___x_1791_ = lean_box(0);
v___x_1792_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1790_, 2);
v___f_1793_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1793_, 0, v___x_1792_);
lean_closure_set(v___f_1793_, 1, v_toPure_1790_);
lean_closure_set(v___f_1793_, 2, v___x_1791_);
lean_closure_set(v___f_1793_, 3, v_p_1786_);
lean_closure_set(v___f_1793_, 4, v_toBind_1789_);
v___f_1794_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1794_, 0, v_toPure_1790_);
v_sz_1795_ = lean_array_size(v_as_1787_);
v___x_1796_ = ((size_t)0ULL);
v___x_1797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1785_, v_as_1787_, v___f_1793_, v_sz_1795_, v___x_1796_, v___x_1792_);
v___x_1798_ = lean_apply_4(v_toBind_1789_, lean_box(0), lean_box(0), v___x_1797_, v___f_1794_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f(lean_object* v_m_1799_, lean_object* v_00_u03b1_1800_, lean_object* v_inst_1801_, lean_object* v_p_1802_, lean_object* v_as_1803_){
_start:
{
lean_object* v_toApplicative_1804_; lean_object* v_toBind_1805_; lean_object* v_toPure_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___f_1809_; lean_object* v___f_1810_; size_t v_sz_1811_; size_t v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v_toApplicative_1804_ = lean_ctor_get(v_inst_1801_, 0);
v_toBind_1805_ = lean_ctor_get(v_inst_1801_, 1);
lean_inc_n(v_toBind_1805_, 2);
v_toPure_1806_ = lean_ctor_get(v_toApplicative_1804_, 1);
v___x_1807_ = lean_box(0);
v___x_1808_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1806_, 2);
v___f_1809_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1809_, 0, v___x_1808_);
lean_closure_set(v___f_1809_, 1, v_toPure_1806_);
lean_closure_set(v___f_1809_, 2, v___x_1807_);
lean_closure_set(v___f_1809_, 3, v_p_1802_);
lean_closure_set(v___f_1809_, 4, v_toBind_1805_);
v___f_1810_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1810_, 0, v_toPure_1806_);
v_sz_1811_ = lean_array_size(v_as_1803_);
v___x_1812_ = ((size_t)0ULL);
v___x_1813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1801_, v_as_1803_, v___f_1809_, v_sz_1811_, v___x_1812_, v___x_1808_);
v___x_1814_ = lean_apply_4(v_toBind_1805_, lean_box(0), lean_box(0), v___x_1813_, v___f_1810_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0(lean_object* v_snd_1815_, lean_object* v___x_1816_, lean_object* v_toPure_1817_, uint8_t v_____do__lift_1818_){
_start:
{
if (v_____do__lift_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1819_ = lean_unsigned_to_nat(1u);
v___x_1820_ = lean_nat_add(v_snd_1815_, v___x_1819_);
lean_dec(v_snd_1815_);
v___x_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1816_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
v___x_1823_ = lean_apply_2(v_toPure_1817_, lean_box(0), v___x_1822_);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec(v___x_1816_);
lean_inc(v_snd_1815_);
v___x_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_snd_1815_);
v___x_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v_snd_1815_);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
v___x_1828_ = lean_apply_2(v_toPure_1817_, lean_box(0), v___x_1827_);
return v___x_1828_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0___boxed(lean_object* v_snd_1829_, lean_object* v___x_1830_, lean_object* v_toPure_1831_, lean_object* v_____do__lift_1832_){
_start:
{
uint8_t v_____do__lift_214__boxed_1833_; lean_object* v_res_1834_; 
v_____do__lift_214__boxed_1833_ = lean_unbox(v_____do__lift_1832_);
v_res_1834_ = l_Array_findIdxM_x3f___redArg___lam__0(v_snd_1829_, v___x_1830_, v_toPure_1831_, v_____do__lift_214__boxed_1833_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__1(lean_object* v___x_1835_, lean_object* v_toPure_1836_, lean_object* v_p_1837_, lean_object* v_toBind_1838_, lean_object* v_a_1839_, lean_object* v_x_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_snd_1842_; lean_object* v___f_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v_snd_1842_ = lean_ctor_get(v___y_1841_, 1);
lean_inc(v_snd_1842_);
lean_dec_ref(v___y_1841_);
v___f_1843_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1843_, 0, v_snd_1842_);
lean_closure_set(v___f_1843_, 1, v___x_1835_);
lean_closure_set(v___f_1843_, 2, v_toPure_1836_);
v___x_1844_ = lean_apply_1(v_p_1837_, v_a_1839_);
v___x_1845_ = lean_apply_4(v_toBind_1838_, lean_box(0), lean_box(0), v___x_1844_, v___f_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__2(lean_object* v_toPure_1846_, lean_object* v_____s_1847_){
_start:
{
lean_object* v_fst_1848_; 
v_fst_1848_ = lean_ctor_get(v_____s_1847_, 0);
lean_inc(v_fst_1848_);
lean_dec_ref(v_____s_1847_);
if (lean_obj_tag(v_fst_1848_) == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_box(0);
v___x_1850_ = lean_apply_2(v_toPure_1846_, lean_box(0), v___x_1849_);
return v___x_1850_;
}
else
{
lean_object* v_val_1851_; lean_object* v___x_1852_; 
v_val_1851_ = lean_ctor_get(v_fst_1848_, 0);
lean_inc(v_val_1851_);
lean_dec_ref_known(v_fst_1848_, 1);
v___x_1852_ = lean_apply_2(v_toPure_1846_, lean_box(0), v_val_1851_);
return v___x_1852_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg(lean_object* v_inst_1856_, lean_object* v_p_1857_, lean_object* v_as_1858_){
_start:
{
lean_object* v_toApplicative_1859_; lean_object* v_toBind_1860_; lean_object* v_toPure_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___f_1864_; lean_object* v___f_1865_; size_t v_sz_1866_; size_t v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_toApplicative_1859_ = lean_ctor_get(v_inst_1856_, 0);
v_toBind_1860_ = lean_ctor_get(v_inst_1856_, 1);
lean_inc_n(v_toBind_1860_, 2);
v_toPure_1861_ = lean_ctor_get(v_toApplicative_1859_, 1);
v___x_1862_ = lean_box(0);
v___x_1863_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1861_, 2);
v___f_1864_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1864_, 0, v___x_1862_);
lean_closure_set(v___f_1864_, 1, v_toPure_1861_);
lean_closure_set(v___f_1864_, 2, v_p_1857_);
lean_closure_set(v___f_1864_, 3, v_toBind_1860_);
v___f_1865_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1865_, 0, v_toPure_1861_);
v_sz_1866_ = lean_array_size(v_as_1858_);
v___x_1867_ = ((size_t)0ULL);
v___x_1868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1856_, v_as_1858_, v___f_1864_, v_sz_1866_, v___x_1867_, v___x_1863_);
v___x_1869_ = lean_apply_4(v_toBind_1860_, lean_box(0), lean_box(0), v___x_1868_, v___f_1865_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f(lean_object* v_00_u03b1_1870_, lean_object* v_m_1871_, lean_object* v_inst_1872_, lean_object* v_p_1873_, lean_object* v_as_1874_){
_start:
{
lean_object* v_toApplicative_1875_; lean_object* v_toBind_1876_; lean_object* v_toPure_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___f_1880_; lean_object* v___f_1881_; size_t v_sz_1882_; size_t v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v_toApplicative_1875_ = lean_ctor_get(v_inst_1872_, 0);
v_toBind_1876_ = lean_ctor_get(v_inst_1872_, 1);
lean_inc_n(v_toBind_1876_, 2);
v_toPure_1877_ = lean_ctor_get(v_toApplicative_1875_, 1);
v___x_1878_ = lean_box(0);
v___x_1879_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1877_, 2);
v___f_1880_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1880_, 0, v___x_1878_);
lean_closure_set(v___f_1880_, 1, v_toPure_1877_);
lean_closure_set(v___f_1880_, 2, v_p_1873_);
lean_closure_set(v___f_1880_, 3, v_toBind_1876_);
v___f_1881_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1881_, 0, v_toPure_1877_);
v_sz_1882_ = lean_array_size(v_as_1874_);
v___x_1883_ = ((size_t)0ULL);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1872_, v_as_1874_, v___f_1880_, v_sz_1882_, v___x_1883_, v___x_1879_);
v___x_1885_ = lean_apply_4(v_toBind_1876_, lean_box(0), lean_box(0), v___x_1884_, v___f_1881_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed(lean_object* v_i_1886_, lean_object* v_inst_1887_, lean_object* v_p_1888_, lean_object* v_as_1889_, lean_object* v_stop_1890_, lean_object* v_toPure_1891_, lean_object* v___x_1892_, lean_object* v_____do__lift_1893_){
_start:
{
size_t v_i_boxed_1894_; size_t v_stop_boxed_1895_; uint8_t v___x_78__boxed_1896_; uint8_t v_____do__lift_79__boxed_1897_; lean_object* v_res_1898_; 
v_i_boxed_1894_ = lean_unbox_usize(v_i_1886_);
lean_dec(v_i_1886_);
v_stop_boxed_1895_ = lean_unbox_usize(v_stop_1890_);
lean_dec(v_stop_1890_);
v___x_78__boxed_1896_ = lean_unbox(v___x_1892_);
v_____do__lift_79__boxed_1897_ = lean_unbox(v_____do__lift_1893_);
v_res_1898_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(v_i_boxed_1894_, v_inst_1887_, v_p_1888_, v_as_1889_, v_stop_boxed_1895_, v_toPure_1891_, v___x_78__boxed_1896_, v_____do__lift_79__boxed_1897_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(lean_object* v_inst_1899_, lean_object* v_p_1900_, lean_object* v_as_1901_, size_t v_i_1902_, size_t v_stop_1903_){
_start:
{
lean_object* v_toApplicative_1904_; lean_object* v_toBind_1905_; lean_object* v_toPure_1906_; uint8_t v___x_1907_; 
v_toApplicative_1904_ = lean_ctor_get(v_inst_1899_, 0);
v_toBind_1905_ = lean_ctor_get(v_inst_1899_, 1);
lean_inc(v_toBind_1905_);
v_toPure_1906_ = lean_ctor_get(v_toApplicative_1904_, 1);
lean_inc(v_toPure_1906_);
v___x_1907_ = lean_usize_dec_eq(v_i_1902_, v_stop_1903_);
if (v___x_1907_ == 0)
{
uint8_t v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___f_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1908_ = 1;
v___x_1909_ = lean_box_usize(v_i_1902_);
v___x_1910_ = lean_box_usize(v_stop_1903_);
v___x_1911_ = lean_box(v___x_1908_);
lean_inc_ref(v_as_1901_);
lean_inc(v_p_1900_);
v___f_1912_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1912_, 0, v___x_1909_);
lean_closure_set(v___f_1912_, 1, v_inst_1899_);
lean_closure_set(v___f_1912_, 2, v_p_1900_);
lean_closure_set(v___f_1912_, 3, v_as_1901_);
lean_closure_set(v___f_1912_, 4, v___x_1910_);
lean_closure_set(v___f_1912_, 5, v_toPure_1906_);
lean_closure_set(v___f_1912_, 6, v___x_1911_);
v___x_1913_ = lean_array_uget(v_as_1901_, v_i_1902_);
lean_dec_ref(v_as_1901_);
v___x_1914_ = lean_apply_1(v_p_1900_, v___x_1913_);
v___x_1915_ = lean_apply_4(v_toBind_1905_, lean_box(0), lean_box(0), v___x_1914_, v___f_1912_);
return v___x_1915_;
}
else
{
uint8_t v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_dec(v_toBind_1905_);
lean_dec_ref(v_as_1901_);
lean_dec(v_p_1900_);
lean_dec_ref(v_inst_1899_);
v___x_1916_ = 0;
v___x_1917_ = lean_box(v___x_1916_);
v___x_1918_ = lean_apply_2(v_toPure_1906_, lean_box(0), v___x_1917_);
return v___x_1918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(size_t v_i_1919_, lean_object* v_inst_1920_, lean_object* v_p_1921_, lean_object* v_as_1922_, size_t v_stop_1923_, lean_object* v_toPure_1924_, uint8_t v___x_1925_, uint8_t v_____do__lift_1926_){
_start:
{
if (v_____do__lift_1926_ == 0)
{
size_t v___x_1927_; size_t v___x_1928_; lean_object* v___x_1929_; 
lean_dec(v_toPure_1924_);
v___x_1927_ = ((size_t)1ULL);
v___x_1928_ = lean_usize_add(v_i_1919_, v___x_1927_);
v___x_1929_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1920_, v_p_1921_, v_as_1922_, v___x_1928_, v_stop_1923_);
return v___x_1929_;
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
lean_dec_ref(v_as_1922_);
lean_dec(v_p_1921_);
lean_dec_ref(v_inst_1920_);
v___x_1930_ = lean_box(v___x_1925_);
v___x_1931_ = lean_apply_2(v_toPure_1924_, lean_box(0), v___x_1930_);
return v___x_1931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___boxed(lean_object* v_inst_1932_, lean_object* v_p_1933_, lean_object* v_as_1934_, lean_object* v_i_1935_, lean_object* v_stop_1936_){
_start:
{
size_t v_i_boxed_1937_; size_t v_stop_boxed_1938_; lean_object* v_res_1939_; 
v_i_boxed_1937_ = lean_unbox_usize(v_i_1935_);
lean_dec(v_i_1935_);
v_stop_boxed_1938_ = lean_unbox_usize(v_stop_1936_);
lean_dec(v_stop_1936_);
v_res_1939_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1932_, v_p_1933_, v_as_1934_, v_i_boxed_1937_, v_stop_boxed_1938_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object* v_00_u03b1_1940_, lean_object* v_m_1941_, lean_object* v_inst_1942_, lean_object* v_p_1943_, lean_object* v_as_1944_, size_t v_i_1945_, size_t v_stop_1946_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1942_, v_p_1943_, v_as_1944_, v_i_1945_, v_stop_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___boxed(lean_object* v_00_u03b1_1948_, lean_object* v_m_1949_, lean_object* v_inst_1950_, lean_object* v_p_1951_, lean_object* v_as_1952_, lean_object* v_i_1953_, lean_object* v_stop_1954_){
_start:
{
size_t v_i_boxed_1955_; size_t v_stop_boxed_1956_; lean_object* v_res_1957_; 
v_i_boxed_1955_ = lean_unbox_usize(v_i_1953_);
lean_dec(v_i_1953_);
v_stop_boxed_1956_ = lean_unbox_usize(v_stop_1954_);
lean_dec(v_stop_1954_);
v_res_1957_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(v_00_u03b1_1948_, v_m_1949_, v_inst_1950_, v_p_1951_, v_as_1952_, v_i_boxed_1955_, v_stop_boxed_1956_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg(lean_object* v_inst_1958_, lean_object* v_p_1959_, lean_object* v_as_1960_, lean_object* v_start_1961_, lean_object* v_stop_1962_){
_start:
{
lean_object* v_toApplicative_1963_; lean_object* v_toPure_1964_; lean_object* v___y_1966_; uint8_t v___x_1973_; 
v_toApplicative_1963_ = lean_ctor_get(v_inst_1958_, 0);
v_toPure_1964_ = lean_ctor_get(v_toApplicative_1963_, 1);
v___x_1973_ = lean_nat_dec_lt(v_start_1961_, v_stop_1962_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_inc(v_toPure_1964_);
lean_dec(v_stop_1962_);
lean_dec_ref(v_as_1960_);
lean_dec(v_p_1959_);
lean_dec_ref(v_inst_1958_);
v___x_1974_ = lean_box(v___x_1973_);
v___x_1975_ = lean_apply_2(v_toPure_1964_, lean_box(0), v___x_1974_);
return v___x_1975_;
}
else
{
lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1976_ = lean_array_get_size(v_as_1960_);
v___x_1977_ = lean_nat_dec_le(v_stop_1962_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_dec(v_stop_1962_);
v___y_1966_ = v___x_1976_;
goto v___jp_1965_;
}
else
{
v___y_1966_ = v_stop_1962_;
goto v___jp_1965_;
}
}
v___jp_1965_:
{
uint8_t v___x_1967_; 
v___x_1967_ = lean_nat_dec_lt(v_start_1961_, v___y_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_inc(v_toPure_1964_);
lean_dec(v___y_1966_);
lean_dec_ref(v_as_1960_);
lean_dec(v_p_1959_);
lean_dec_ref(v_inst_1958_);
v___x_1968_ = lean_box(v___x_1967_);
v___x_1969_ = lean_apply_2(v_toPure_1964_, lean_box(0), v___x_1968_);
return v___x_1969_;
}
else
{
size_t v___x_1970_; size_t v___x_1971_; lean_object* v___x_1972_; 
v___x_1970_ = lean_usize_of_nat(v_start_1961_);
v___x_1971_ = lean_usize_of_nat(v___y_1966_);
lean_dec(v___y_1966_);
v___x_1972_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1958_, v_p_1959_, v_as_1960_, v___x_1970_, v___x_1971_);
return v___x_1972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg___boxed(lean_object* v_inst_1978_, lean_object* v_p_1979_, lean_object* v_as_1980_, lean_object* v_start_1981_, lean_object* v_stop_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Array_anyMUnsafe___redArg(v_inst_1978_, v_p_1979_, v_as_1980_, v_start_1981_, v_stop_1982_);
lean_dec(v_start_1981_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe(lean_object* v_00_u03b1_1984_, lean_object* v_m_1985_, lean_object* v_inst_1986_, lean_object* v_p_1987_, lean_object* v_as_1988_, lean_object* v_start_1989_, lean_object* v_stop_1990_){
_start:
{
lean_object* v_toApplicative_1991_; lean_object* v_toPure_1992_; lean_object* v___y_1994_; uint8_t v___x_2001_; 
v_toApplicative_1991_ = lean_ctor_get(v_inst_1986_, 0);
v_toPure_1992_ = lean_ctor_get(v_toApplicative_1991_, 1);
v___x_2001_ = lean_nat_dec_lt(v_start_1989_, v_stop_1990_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_inc(v_toPure_1992_);
lean_dec(v_stop_1990_);
lean_dec_ref(v_as_1988_);
lean_dec(v_p_1987_);
lean_dec_ref(v_inst_1986_);
v___x_2002_ = lean_box(v___x_2001_);
v___x_2003_ = lean_apply_2(v_toPure_1992_, lean_box(0), v___x_2002_);
return v___x_2003_;
}
else
{
lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2004_ = lean_array_get_size(v_as_1988_);
v___x_2005_ = lean_nat_dec_le(v_stop_1990_, v___x_2004_);
if (v___x_2005_ == 0)
{
lean_dec(v_stop_1990_);
v___y_1994_ = v___x_2004_;
goto v___jp_1993_;
}
else
{
v___y_1994_ = v_stop_1990_;
goto v___jp_1993_;
}
}
v___jp_1993_:
{
uint8_t v___x_1995_; 
v___x_1995_ = lean_nat_dec_lt(v_start_1989_, v___y_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_inc(v_toPure_1992_);
lean_dec(v___y_1994_);
lean_dec_ref(v_as_1988_);
lean_dec(v_p_1987_);
lean_dec_ref(v_inst_1986_);
v___x_1996_ = lean_box(v___x_1995_);
v___x_1997_ = lean_apply_2(v_toPure_1992_, lean_box(0), v___x_1996_);
return v___x_1997_;
}
else
{
size_t v___x_1998_; size_t v___x_1999_; lean_object* v___x_2000_; 
v___x_1998_ = lean_usize_of_nat(v_start_1989_);
v___x_1999_ = lean_usize_of_nat(v___y_1994_);
lean_dec(v___y_1994_);
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1986_, v_p_1987_, v_as_1988_, v___x_1998_, v___x_1999_);
return v___x_2000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___boxed(lean_object* v_00_u03b1_2006_, lean_object* v_m_2007_, lean_object* v_inst_2008_, lean_object* v_p_2009_, lean_object* v_as_2010_, lean_object* v_start_2011_, lean_object* v_stop_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Array_anyMUnsafe(v_00_u03b1_2006_, v_m_2007_, v_inst_2008_, v_p_2009_, v_as_2010_, v_start_2011_, v_stop_2012_);
lean_dec(v_start_2011_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0___boxed(lean_object* v_j_2014_, lean_object* v_inst_2015_, lean_object* v_p_2016_, lean_object* v_as_2017_, lean_object* v_stop_2018_, lean_object* v_toPure_2019_, lean_object* v___x_2020_, lean_object* v_____do__lift_2021_){
_start:
{
uint8_t v___x_63__boxed_2022_; uint8_t v_____do__lift_64__boxed_2023_; lean_object* v_res_2024_; 
v___x_63__boxed_2022_ = lean_unbox(v___x_2020_);
v_____do__lift_64__boxed_2023_ = lean_unbox(v_____do__lift_2021_);
v_res_2024_ = l_Array_anyM_loop___redArg___lam__0(v_j_2014_, v_inst_2015_, v_p_2016_, v_as_2017_, v_stop_2018_, v_toPure_2019_, v___x_63__boxed_2022_, v_____do__lift_64__boxed_2023_);
lean_dec(v_j_2014_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg(lean_object* v_inst_2025_, lean_object* v_p_2026_, lean_object* v_as_2027_, lean_object* v_stop_2028_, lean_object* v_j_2029_){
_start:
{
lean_object* v_toApplicative_2030_; lean_object* v_toBind_2031_; lean_object* v_toPure_2032_; uint8_t v___x_2033_; 
v_toApplicative_2030_ = lean_ctor_get(v_inst_2025_, 0);
v_toBind_2031_ = lean_ctor_get(v_inst_2025_, 1);
lean_inc(v_toBind_2031_);
v_toPure_2032_ = lean_ctor_get(v_toApplicative_2030_, 1);
lean_inc(v_toPure_2032_);
v___x_2033_ = lean_nat_dec_lt(v_j_2029_, v_stop_2028_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_dec(v_toBind_2031_);
lean_dec(v_j_2029_);
lean_dec(v_stop_2028_);
lean_dec_ref(v_as_2027_);
lean_dec(v_p_2026_);
lean_dec_ref(v_inst_2025_);
v___x_2034_ = lean_box(v___x_2033_);
v___x_2035_ = lean_apply_2(v_toPure_2032_, lean_box(0), v___x_2034_);
return v___x_2035_;
}
else
{
lean_object* v___x_2036_; lean_object* v___f_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2036_ = lean_box(v___x_2033_);
lean_inc_ref(v_as_2027_);
lean_inc(v_p_2026_);
lean_inc(v_j_2029_);
v___f_2037_ = lean_alloc_closure((void*)(l_Array_anyM_loop___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_2037_, 0, v_j_2029_);
lean_closure_set(v___f_2037_, 1, v_inst_2025_);
lean_closure_set(v___f_2037_, 2, v_p_2026_);
lean_closure_set(v___f_2037_, 3, v_as_2027_);
lean_closure_set(v___f_2037_, 4, v_stop_2028_);
lean_closure_set(v___f_2037_, 5, v_toPure_2032_);
lean_closure_set(v___f_2037_, 6, v___x_2036_);
v___x_2038_ = lean_array_fget(v_as_2027_, v_j_2029_);
lean_dec(v_j_2029_);
lean_dec_ref(v_as_2027_);
v___x_2039_ = lean_apply_1(v_p_2026_, v___x_2038_);
v___x_2040_ = lean_apply_4(v_toBind_2031_, lean_box(0), lean_box(0), v___x_2039_, v___f_2037_);
return v___x_2040_;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0(lean_object* v_j_2041_, lean_object* v_inst_2042_, lean_object* v_p_2043_, lean_object* v_as_2044_, lean_object* v_stop_2045_, lean_object* v_toPure_2046_, uint8_t v___x_2047_, uint8_t v_____do__lift_2048_){
_start:
{
if (v_____do__lift_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
lean_dec(v_toPure_2046_);
v___x_2049_ = lean_unsigned_to_nat(1u);
v___x_2050_ = lean_nat_add(v_j_2041_, v___x_2049_);
v___x_2051_ = l_Array_anyM_loop___redArg(v_inst_2042_, v_p_2043_, v_as_2044_, v_stop_2045_, v___x_2050_);
return v___x_2051_;
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_dec(v_stop_2045_);
lean_dec_ref(v_as_2044_);
lean_dec(v_p_2043_);
lean_dec_ref(v_inst_2042_);
v___x_2052_ = lean_box(v___x_2047_);
v___x_2053_ = lean_apply_2(v_toPure_2046_, lean_box(0), v___x_2052_);
return v___x_2053_;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop(lean_object* v_00_u03b1_2054_, lean_object* v_m_2055_, lean_object* v_inst_2056_, lean_object* v_p_2057_, lean_object* v_as_2058_, lean_object* v_stop_2059_, lean_object* v_h_2060_, lean_object* v_j_2061_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = l_Array_anyM_loop___redArg(v_inst_2056_, v_p_2057_, v_as_2058_, v_stop_2059_, v_j_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0(lean_object* v_toPure_2063_, uint8_t v_____do__lift_2064_){
_start:
{
if (v_____do__lift_2064_ == 0)
{
uint8_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = 1;
v___x_2066_ = lean_box(v___x_2065_);
v___x_2067_ = lean_apply_2(v_toPure_2063_, lean_box(0), v___x_2066_);
return v___x_2067_;
}
else
{
uint8_t v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2068_ = 0;
v___x_2069_ = lean_box(v___x_2068_);
v___x_2070_ = lean_apply_2(v_toPure_2063_, lean_box(0), v___x_2069_);
return v___x_2070_;
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0___boxed(lean_object* v_toPure_2071_, lean_object* v_____do__lift_2072_){
_start:
{
uint8_t v_____do__lift_117__boxed_2073_; lean_object* v_res_2074_; 
v_____do__lift_117__boxed_2073_ = lean_unbox(v_____do__lift_2072_);
v_res_2074_ = l_Array_allM___redArg___lam__0(v_toPure_2071_, v_____do__lift_117__boxed_2073_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1(lean_object* v_toPure_2075_, uint8_t v___x_2076_, uint8_t v_____do__lift_2077_){
_start:
{
if (v_____do__lift_2077_ == 0)
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_box(v___x_2076_);
v___x_2079_ = lean_apply_2(v_toPure_2075_, lean_box(0), v___x_2078_);
return v___x_2079_;
}
else
{
uint8_t v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = 0;
v___x_2081_ = lean_box(v___x_2080_);
v___x_2082_ = lean_apply_2(v_toPure_2075_, lean_box(0), v___x_2081_);
return v___x_2082_;
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1___boxed(lean_object* v_toPure_2083_, lean_object* v___x_2084_, lean_object* v_____do__lift_2085_){
_start:
{
uint8_t v___x_132__boxed_2086_; uint8_t v_____do__lift_133__boxed_2087_; lean_object* v_res_2088_; 
v___x_132__boxed_2086_ = lean_unbox(v___x_2084_);
v_____do__lift_133__boxed_2087_ = lean_unbox(v_____do__lift_2085_);
v_res_2088_ = l_Array_allM___redArg___lam__1(v_toPure_2083_, v___x_132__boxed_2086_, v_____do__lift_133__boxed_2087_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__2(lean_object* v_p_2089_, lean_object* v_toBind_2090_, lean_object* v___f_2091_, lean_object* v_v_2092_){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_apply_1(v_p_2089_, v_v_2092_);
v___x_2094_ = lean_apply_4(v_toBind_2090_, lean_box(0), lean_box(0), v___x_2093_, v___f_2091_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg(lean_object* v_inst_2095_, lean_object* v_p_2096_, lean_object* v_as_2097_, lean_object* v_start_2098_, lean_object* v_stop_2099_){
_start:
{
lean_object* v_toApplicative_2100_; lean_object* v_toBind_2101_; lean_object* v_toPure_2102_; lean_object* v___f_2103_; uint8_t v___x_2104_; 
v_toApplicative_2100_ = lean_ctor_get(v_inst_2095_, 0);
v_toBind_2101_ = lean_ctor_get(v_inst_2095_, 1);
lean_inc(v_toBind_2101_);
v_toPure_2102_ = lean_ctor_get(v_toApplicative_2100_, 1);
lean_inc(v_toPure_2102_);
v___f_2103_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2103_, 0, v_toPure_2102_);
v___x_2104_ = lean_nat_dec_lt(v_start_2098_, v_stop_2099_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
lean_inc(v_toPure_2102_);
lean_dec(v_stop_2099_);
lean_dec_ref(v_as_2097_);
lean_dec(v_p_2096_);
lean_dec_ref(v_inst_2095_);
v___x_2105_ = lean_box(v___x_2104_);
v___x_2106_ = lean_apply_2(v_toPure_2102_, lean_box(0), v___x_2105_);
v___x_2107_ = lean_apply_4(v_toBind_2101_, lean_box(0), lean_box(0), v___x_2106_, v___f_2103_);
return v___x_2107_;
}
else
{
lean_object* v___x_2108_; lean_object* v___f_2109_; lean_object* v___f_2110_; lean_object* v___y_2112_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2108_ = lean_box(v___x_2104_);
lean_inc(v_toPure_2102_);
v___f_2109_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2109_, 0, v_toPure_2102_);
lean_closure_set(v___f_2109_, 1, v___x_2108_);
lean_inc(v_toBind_2101_);
v___f_2110_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2110_, 0, v_p_2096_);
lean_closure_set(v___f_2110_, 1, v_toBind_2101_);
lean_closure_set(v___f_2110_, 2, v___f_2109_);
v___x_2121_ = lean_array_get_size(v_as_2097_);
v___x_2122_ = lean_nat_dec_le(v_stop_2099_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_dec(v_stop_2099_);
v___y_2112_ = v___x_2121_;
goto v___jp_2111_;
}
else
{
v___y_2112_ = v_stop_2099_;
goto v___jp_2111_;
}
v___jp_2111_:
{
uint8_t v___x_2113_; 
v___x_2113_ = lean_nat_dec_lt(v_start_2098_, v___y_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_inc(v_toPure_2102_);
lean_dec(v___y_2112_);
lean_dec_ref(v___f_2110_);
lean_dec_ref(v_as_2097_);
lean_dec_ref(v_inst_2095_);
v___x_2114_ = lean_box(v___x_2113_);
v___x_2115_ = lean_apply_2(v_toPure_2102_, lean_box(0), v___x_2114_);
v___x_2116_ = lean_apply_4(v_toBind_2101_, lean_box(0), lean_box(0), v___x_2115_, v___f_2103_);
return v___x_2116_;
}
else
{
size_t v___x_2117_; size_t v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2117_ = lean_usize_of_nat(v_start_2098_);
v___x_2118_ = lean_usize_of_nat(v___y_2112_);
lean_dec(v___y_2112_);
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2095_, v___f_2110_, v_as_2097_, v___x_2117_, v___x_2118_);
v___x_2120_ = lean_apply_4(v_toBind_2101_, lean_box(0), lean_box(0), v___x_2119_, v___f_2103_);
return v___x_2120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___boxed(lean_object* v_inst_2123_, lean_object* v_p_2124_, lean_object* v_as_2125_, lean_object* v_start_2126_, lean_object* v_stop_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Array_allM___redArg(v_inst_2123_, v_p_2124_, v_as_2125_, v_start_2126_, v_stop_2127_);
lean_dec(v_start_2126_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Array_allM(lean_object* v_00_u03b1_2129_, lean_object* v_m_2130_, lean_object* v_inst_2131_, lean_object* v_p_2132_, lean_object* v_as_2133_, lean_object* v_start_2134_, lean_object* v_stop_2135_){
_start:
{
lean_object* v_toApplicative_2136_; lean_object* v_toBind_2137_; lean_object* v_toPure_2138_; lean_object* v___f_2139_; uint8_t v___x_2140_; 
v_toApplicative_2136_ = lean_ctor_get(v_inst_2131_, 0);
v_toBind_2137_ = lean_ctor_get(v_inst_2131_, 1);
lean_inc(v_toBind_2137_);
v_toPure_2138_ = lean_ctor_get(v_toApplicative_2136_, 1);
lean_inc(v_toPure_2138_);
v___f_2139_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2139_, 0, v_toPure_2138_);
v___x_2140_ = lean_nat_dec_lt(v_start_2134_, v_stop_2135_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_inc(v_toPure_2138_);
lean_dec(v_stop_2135_);
lean_dec_ref(v_as_2133_);
lean_dec(v_p_2132_);
lean_dec_ref(v_inst_2131_);
v___x_2141_ = lean_box(v___x_2140_);
v___x_2142_ = lean_apply_2(v_toPure_2138_, lean_box(0), v___x_2141_);
v___x_2143_ = lean_apply_4(v_toBind_2137_, lean_box(0), lean_box(0), v___x_2142_, v___f_2139_);
return v___x_2143_;
}
else
{
lean_object* v___x_2144_; lean_object* v___f_2145_; lean_object* v___f_2146_; lean_object* v___y_2148_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2144_ = lean_box(v___x_2140_);
lean_inc(v_toPure_2138_);
v___f_2145_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2145_, 0, v_toPure_2138_);
lean_closure_set(v___f_2145_, 1, v___x_2144_);
lean_inc(v_toBind_2137_);
v___f_2146_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2146_, 0, v_p_2132_);
lean_closure_set(v___f_2146_, 1, v_toBind_2137_);
lean_closure_set(v___f_2146_, 2, v___f_2145_);
v___x_2157_ = lean_array_get_size(v_as_2133_);
v___x_2158_ = lean_nat_dec_le(v_stop_2135_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_dec(v_stop_2135_);
v___y_2148_ = v___x_2157_;
goto v___jp_2147_;
}
else
{
v___y_2148_ = v_stop_2135_;
goto v___jp_2147_;
}
v___jp_2147_:
{
uint8_t v___x_2149_; 
v___x_2149_ = lean_nat_dec_lt(v_start_2134_, v___y_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
lean_inc(v_toPure_2138_);
lean_dec(v___y_2148_);
lean_dec_ref(v___f_2146_);
lean_dec_ref(v_as_2133_);
lean_dec_ref(v_inst_2131_);
v___x_2150_ = lean_box(v___x_2149_);
v___x_2151_ = lean_apply_2(v_toPure_2138_, lean_box(0), v___x_2150_);
v___x_2152_ = lean_apply_4(v_toBind_2137_, lean_box(0), lean_box(0), v___x_2151_, v___f_2139_);
return v___x_2152_;
}
else
{
size_t v___x_2153_; size_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2153_ = lean_usize_of_nat(v_start_2134_);
v___x_2154_ = lean_usize_of_nat(v___y_2148_);
lean_dec(v___y_2148_);
v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2131_, v___f_2146_, v_as_2133_, v___x_2153_, v___x_2154_);
v___x_2156_ = lean_apply_4(v_toBind_2137_, lean_box(0), lean_box(0), v___x_2155_, v___f_2139_);
return v___x_2156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___boxed(lean_object* v_00_u03b1_2159_, lean_object* v_m_2160_, lean_object* v_inst_2161_, lean_object* v_p_2162_, lean_object* v_as_2163_, lean_object* v_start_2164_, lean_object* v_stop_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Array_allM(v_00_u03b1_2159_, v_m_2160_, v_inst_2161_, v_p_2162_, v_as_2163_, v_start_2164_, v_stop_2165_);
lean_dec(v_start_2164_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed(lean_object* v_inst_2167_, lean_object* v_f_2168_, lean_object* v_as_2169_, lean_object* v_n_2170_, lean_object* v_toPure_2171_, lean_object* v_r_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(v_inst_2167_, v_f_2168_, v_as_2169_, v_n_2170_, v_toPure_2171_, v_r_2172_);
lean_dec(v_n_2170_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(lean_object* v_inst_2174_, lean_object* v_f_2175_, lean_object* v_as_2176_, lean_object* v_i_2177_){
_start:
{
lean_object* v_toApplicative_2178_; lean_object* v_toBind_2179_; lean_object* v_toPure_2180_; lean_object* v_zero_2181_; uint8_t v_isZero_2182_; 
v_toApplicative_2178_ = lean_ctor_get(v_inst_2174_, 0);
v_toBind_2179_ = lean_ctor_get(v_inst_2174_, 1);
lean_inc(v_toBind_2179_);
v_toPure_2180_ = lean_ctor_get(v_toApplicative_2178_, 1);
lean_inc(v_toPure_2180_);
v_zero_2181_ = lean_unsigned_to_nat(0u);
v_isZero_2182_ = lean_nat_dec_eq(v_i_2177_, v_zero_2181_);
if (v_isZero_2182_ == 1)
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_dec(v_toBind_2179_);
lean_dec_ref(v_as_2176_);
lean_dec(v_f_2175_);
lean_dec_ref(v_inst_2174_);
v___x_2183_ = lean_box(0);
v___x_2184_ = lean_apply_2(v_toPure_2180_, lean_box(0), v___x_2183_);
return v___x_2184_;
}
else
{
lean_object* v_one_2185_; lean_object* v_n_2186_; lean_object* v___f_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v_one_2185_ = lean_unsigned_to_nat(1u);
v_n_2186_ = lean_nat_sub(v_i_2177_, v_one_2185_);
lean_inc(v_n_2186_);
lean_inc_ref(v_as_2176_);
lean_inc(v_f_2175_);
v___f_2187_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2187_, 0, v_inst_2174_);
lean_closure_set(v___f_2187_, 1, v_f_2175_);
lean_closure_set(v___f_2187_, 2, v_as_2176_);
lean_closure_set(v___f_2187_, 3, v_n_2186_);
lean_closure_set(v___f_2187_, 4, v_toPure_2180_);
v___x_2188_ = lean_array_fget(v_as_2176_, v_n_2186_);
lean_dec(v_n_2186_);
lean_dec_ref(v_as_2176_);
v___x_2189_ = lean_apply_1(v_f_2175_, v___x_2188_);
v___x_2190_ = lean_apply_4(v_toBind_2179_, lean_box(0), lean_box(0), v___x_2189_, v___f_2187_);
return v___x_2190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(lean_object* v_inst_2191_, lean_object* v_f_2192_, lean_object* v_as_2193_, lean_object* v_n_2194_, lean_object* v_toPure_2195_, lean_object* v_r_2196_){
_start:
{
if (lean_obj_tag(v_r_2196_) == 0)
{
lean_object* v___x_2197_; 
lean_dec(v_toPure_2195_);
v___x_2197_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2191_, v_f_2192_, v_as_2193_, v_n_2194_);
return v___x_2197_;
}
else
{
lean_object* v___x_2198_; 
lean_dec_ref(v_as_2193_);
lean_dec(v_f_2192_);
lean_dec_ref(v_inst_2191_);
v___x_2198_ = lean_apply_2(v_toPure_2195_, lean_box(0), v_r_2196_);
return v___x_2198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___boxed(lean_object* v_inst_2199_, lean_object* v_f_2200_, lean_object* v_as_2201_, lean_object* v_i_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2199_, v_f_2200_, v_as_2201_, v_i_2202_);
lean_dec(v_i_2202_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_object* v_00_u03b1_2204_, lean_object* v_00_u03b2_2205_, lean_object* v_m_2206_, lean_object* v_inst_2207_, lean_object* v_f_2208_, lean_object* v_as_2209_, lean_object* v_i_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2207_, v_f_2208_, v_as_2209_, v_i_2210_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___boxed(lean_object* v_00_u03b1_2213_, lean_object* v_00_u03b2_2214_, lean_object* v_m_2215_, lean_object* v_inst_2216_, lean_object* v_f_2217_, lean_object* v_as_2218_, lean_object* v_i_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(v_00_u03b1_2213_, v_00_u03b2_2214_, v_m_2215_, v_inst_2216_, v_f_2217_, v_as_2218_, v_i_2219_, v_a_2220_);
lean_dec(v_i_2219_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f___redArg(lean_object* v_inst_2222_, lean_object* v_f_2223_, lean_object* v_as_2224_){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_array_get_size(v_as_2224_);
v___x_2226_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2222_, v_f_2223_, v_as_2224_, v___x_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f(lean_object* v_00_u03b1_2227_, lean_object* v_00_u03b2_2228_, lean_object* v_m_2229_, lean_object* v_inst_2230_, lean_object* v_f_2231_, lean_object* v_as_2232_){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_array_get_size(v_as_2232_);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2230_, v_f_2231_, v_as_2232_, v___x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2235_, lean_object* v_a_2236_, uint8_t v_____do__lift_2237_){
_start:
{
if (v_____do__lift_2237_ == 0)
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec(v_a_2236_);
v___x_2238_ = lean_box(0);
v___x_2239_ = lean_apply_2(v_toPure_2235_, lean_box(0), v___x_2238_);
return v___x_2239_;
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2240_, 0, v_a_2236_);
v___x_2241_ = lean_apply_2(v_toPure_2235_, lean_box(0), v___x_2240_);
return v___x_2241_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2242_, lean_object* v_a_2243_, lean_object* v_____do__lift_2244_){
_start:
{
uint8_t v_____do__lift_60__boxed_2245_; lean_object* v_res_2246_; 
v_____do__lift_60__boxed_2245_ = lean_unbox(v_____do__lift_2244_);
v_res_2246_ = l_Array_findRevM_x3f___redArg___lam__0(v_toPure_2242_, v_a_2243_, v_____do__lift_60__boxed_2245_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2247_, lean_object* v_p_2248_, lean_object* v_toBind_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v___f_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_inc(v_a_2250_);
v___f_2251_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2251_, 0, v_toPure_2247_);
lean_closure_set(v___f_2251_, 1, v_a_2250_);
v___x_2252_ = lean_apply_1(v_p_2248_, v_a_2250_);
v___x_2253_ = lean_apply_4(v_toBind_2249_, lean_box(0), lean_box(0), v___x_2252_, v___f_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg(lean_object* v_inst_2254_, lean_object* v_p_2255_, lean_object* v_as_2256_){
_start:
{
lean_object* v_toApplicative_2257_; lean_object* v_toBind_2258_; lean_object* v_toPure_2259_; lean_object* v___f_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v_toApplicative_2257_ = lean_ctor_get(v_inst_2254_, 0);
v_toBind_2258_ = lean_ctor_get(v_inst_2254_, 1);
v_toPure_2259_ = lean_ctor_get(v_toApplicative_2257_, 1);
lean_inc(v_toBind_2258_);
lean_inc(v_toPure_2259_);
v___f_2260_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2260_, 0, v_toPure_2259_);
lean_closure_set(v___f_2260_, 1, v_p_2255_);
lean_closure_set(v___f_2260_, 2, v_toBind_2258_);
v___x_2261_ = lean_array_get_size(v_as_2256_);
v___x_2262_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2254_, v___f_2260_, v_as_2256_, v___x_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f(lean_object* v_00_u03b1_2263_, lean_object* v_m_2264_, lean_object* v_inst_2265_, lean_object* v_p_2266_, lean_object* v_as_2267_){
_start:
{
lean_object* v_toApplicative_2268_; lean_object* v_toBind_2269_; lean_object* v_toPure_2270_; lean_object* v___f_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v_toApplicative_2268_ = lean_ctor_get(v_inst_2265_, 0);
v_toBind_2269_ = lean_ctor_get(v_inst_2265_, 1);
v_toPure_2270_ = lean_ctor_get(v_toApplicative_2268_, 1);
lean_inc(v_toBind_2269_);
lean_inc(v_toPure_2270_);
v___f_2271_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2271_, 0, v_toPure_2270_);
lean_closure_set(v___f_2271_, 1, v_p_2266_);
lean_closure_set(v___f_2271_, 2, v_toBind_2269_);
v___x_2272_ = lean_array_get_size(v_as_2267_);
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2265_, v___f_2271_, v_as_2267_, v___x_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___lam__0(lean_object* v_f_2274_, lean_object* v_x_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = lean_apply_1(v_f_2274_, v___y_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg(lean_object* v_inst_2278_, lean_object* v_f_2279_, lean_object* v_as_2280_, lean_object* v_start_2281_, lean_object* v_stop_2282_){
_start:
{
lean_object* v_toApplicative_2283_; lean_object* v_toPure_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; 
v_toApplicative_2283_ = lean_ctor_get(v_inst_2278_, 0);
v_toPure_2284_ = lean_ctor_get(v_toApplicative_2283_, 1);
v___x_2285_ = lean_box(0);
v___x_2286_ = lean_nat_dec_lt(v_start_2281_, v_stop_2282_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; 
lean_inc(v_toPure_2284_);
lean_dec_ref(v_as_2280_);
lean_dec(v_f_2279_);
lean_dec_ref(v_inst_2278_);
v___x_2287_ = lean_apply_2(v_toPure_2284_, lean_box(0), v___x_2285_);
return v___x_2287_;
}
else
{
lean_object* v___f_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; 
v___f_2288_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2288_, 0, v_f_2279_);
v___x_2289_ = lean_array_get_size(v_as_2280_);
v___x_2290_ = lean_nat_dec_le(v_stop_2282_, v___x_2289_);
if (v___x_2290_ == 0)
{
uint8_t v___x_2291_; 
v___x_2291_ = lean_nat_dec_lt(v_start_2281_, v___x_2289_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; 
lean_inc(v_toPure_2284_);
lean_dec_ref(v___f_2288_);
lean_dec_ref(v_as_2280_);
lean_dec_ref(v_inst_2278_);
v___x_2292_ = lean_apply_2(v_toPure_2284_, lean_box(0), v___x_2285_);
return v___x_2292_;
}
else
{
size_t v___x_2293_; size_t v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = lean_usize_of_nat(v_start_2281_);
v___x_2294_ = lean_usize_of_nat(v___x_2289_);
v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2278_, v___f_2288_, v_as_2280_, v___x_2293_, v___x_2294_, v___x_2285_);
return v___x_2295_;
}
}
else
{
size_t v___x_2296_; size_t v___x_2297_; lean_object* v___x_2298_; 
v___x_2296_ = lean_usize_of_nat(v_start_2281_);
v___x_2297_ = lean_usize_of_nat(v_stop_2282_);
v___x_2298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2278_, v___f_2288_, v_as_2280_, v___x_2296_, v___x_2297_, v___x_2285_);
return v___x_2298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___boxed(lean_object* v_inst_2299_, lean_object* v_f_2300_, lean_object* v_as_2301_, lean_object* v_start_2302_, lean_object* v_stop_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Array_forM___redArg(v_inst_2299_, v_f_2300_, v_as_2301_, v_start_2302_, v_stop_2303_);
lean_dec(v_stop_2303_);
lean_dec(v_start_2302_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Array_forM(lean_object* v_00_u03b1_2305_, lean_object* v_m_2306_, lean_object* v_inst_2307_, lean_object* v_f_2308_, lean_object* v_as_2309_, lean_object* v_start_2310_, lean_object* v_stop_2311_){
_start:
{
lean_object* v_toApplicative_2312_; lean_object* v_toPure_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; 
v_toApplicative_2312_ = lean_ctor_get(v_inst_2307_, 0);
v_toPure_2313_ = lean_ctor_get(v_toApplicative_2312_, 1);
v___x_2314_ = lean_box(0);
v___x_2315_ = lean_nat_dec_lt(v_start_2310_, v_stop_2311_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; 
lean_inc(v_toPure_2313_);
lean_dec_ref(v_as_2309_);
lean_dec(v_f_2308_);
lean_dec_ref(v_inst_2307_);
v___x_2316_ = lean_apply_2(v_toPure_2313_, lean_box(0), v___x_2314_);
return v___x_2316_;
}
else
{
lean_object* v___f_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___f_2317_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2317_, 0, v_f_2308_);
v___x_2318_ = lean_array_get_size(v_as_2309_);
v___x_2319_ = lean_nat_dec_le(v_stop_2311_, v___x_2318_);
if (v___x_2319_ == 0)
{
uint8_t v___x_2320_; 
v___x_2320_ = lean_nat_dec_lt(v_start_2310_, v___x_2318_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; 
lean_inc(v_toPure_2313_);
lean_dec_ref(v___f_2317_);
lean_dec_ref(v_as_2309_);
lean_dec_ref(v_inst_2307_);
v___x_2321_ = lean_apply_2(v_toPure_2313_, lean_box(0), v___x_2314_);
return v___x_2321_;
}
else
{
size_t v___x_2322_; size_t v___x_2323_; lean_object* v___x_2324_; 
v___x_2322_ = lean_usize_of_nat(v_start_2310_);
v___x_2323_ = lean_usize_of_nat(v___x_2318_);
v___x_2324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2307_, v___f_2317_, v_as_2309_, v___x_2322_, v___x_2323_, v___x_2314_);
return v___x_2324_;
}
}
else
{
size_t v___x_2325_; size_t v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = lean_usize_of_nat(v_start_2310_);
v___x_2326_ = lean_usize_of_nat(v_stop_2311_);
v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2307_, v___f_2317_, v_as_2309_, v___x_2325_, v___x_2326_, v___x_2314_);
return v___x_2327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___boxed(lean_object* v_00_u03b1_2328_, lean_object* v_m_2329_, lean_object* v_inst_2330_, lean_object* v_f_2331_, lean_object* v_as_2332_, lean_object* v_start_2333_, lean_object* v_stop_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Array_forM(v_00_u03b1_2328_, v_m_2329_, v_inst_2330_, v_f_2331_, v_as_2332_, v_start_2333_, v_stop_2334_);
lean_dec(v_stop_2334_);
lean_dec(v_start_2333_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg___lam__1(lean_object* v_inst_2336_, lean_object* v_xs_2337_, lean_object* v_f_2338_){
_start:
{
lean_object* v_toApplicative_2339_; lean_object* v_toPure_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v_toApplicative_2339_ = lean_ctor_get(v_inst_2336_, 0);
v_toPure_2340_ = lean_ctor_get(v_toApplicative_2339_, 1);
v___x_2341_ = lean_unsigned_to_nat(0u);
v___x_2342_ = lean_array_get_size(v_xs_2337_);
v___x_2343_ = lean_box(0);
v___x_2344_ = lean_nat_dec_lt(v___x_2341_, v___x_2342_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_inc(v_toPure_2340_);
lean_dec(v_f_2338_);
lean_dec_ref(v_xs_2337_);
lean_dec_ref(v_inst_2336_);
v___x_2345_ = lean_apply_2(v_toPure_2340_, lean_box(0), v___x_2343_);
return v___x_2345_;
}
else
{
lean_object* v___f_2346_; uint8_t v___x_2347_; 
v___f_2346_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2346_, 0, v_f_2338_);
v___x_2347_ = lean_nat_dec_le(v___x_2342_, v___x_2342_);
if (v___x_2347_ == 0)
{
if (v___x_2344_ == 0)
{
lean_object* v___x_2348_; 
lean_inc(v_toPure_2340_);
lean_dec_ref(v___f_2346_);
lean_dec_ref(v_xs_2337_);
lean_dec_ref(v_inst_2336_);
v___x_2348_ = lean_apply_2(v_toPure_2340_, lean_box(0), v___x_2343_);
return v___x_2348_;
}
else
{
size_t v___x_2349_; size_t v___x_2350_; lean_object* v___x_2351_; 
v___x_2349_ = ((size_t)0ULL);
v___x_2350_ = lean_usize_of_nat(v___x_2342_);
v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2336_, v___f_2346_, v_xs_2337_, v___x_2349_, v___x_2350_, v___x_2343_);
return v___x_2351_;
}
}
else
{
size_t v___x_2352_; size_t v___x_2353_; lean_object* v___x_2354_; 
v___x_2352_ = ((size_t)0ULL);
v___x_2353_ = lean_usize_of_nat(v___x_2342_);
v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2336_, v___f_2346_, v_xs_2337_, v___x_2352_, v___x_2353_, v___x_2343_);
return v___x_2354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg(lean_object* v_inst_2355_){
_start:
{
lean_object* v___f_2356_; 
v___f_2356_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2356_, 0, v_inst_2355_);
return v___f_2356_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad(lean_object* v_00_u03b1_2357_, lean_object* v_m_2358_, lean_object* v_inst_2359_){
_start:
{
lean_object* v___f_2360_; 
v___f_2360_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2360_, 0, v_inst_2359_);
return v___f_2360_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___lam__0(lean_object* v_f_2361_, lean_object* v_a_2362_, lean_object* v_x_2363_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_apply_1(v_f_2361_, v_a_2362_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg(lean_object* v_inst_2365_, lean_object* v_f_2366_, lean_object* v_as_2367_, lean_object* v_start_2368_, lean_object* v_stop_2369_){
_start:
{
lean_object* v_toApplicative_2370_; lean_object* v_toPure_2371_; lean_object* v___f_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; 
v_toApplicative_2370_ = lean_ctor_get(v_inst_2365_, 0);
v_toPure_2371_ = lean_ctor_get(v_toApplicative_2370_, 1);
v___f_2372_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2372_, 0, v_f_2366_);
v___x_2373_ = lean_box(0);
v___x_2374_ = lean_array_get_size(v_as_2367_);
v___x_2375_ = lean_nat_dec_le(v_start_2368_, v___x_2374_);
if (v___x_2375_ == 0)
{
uint8_t v___x_2376_; 
v___x_2376_ = lean_nat_dec_lt(v_stop_2369_, v___x_2374_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; 
lean_inc(v_toPure_2371_);
lean_dec_ref(v___f_2372_);
lean_dec_ref(v_as_2367_);
lean_dec_ref(v_inst_2365_);
v___x_2377_ = lean_apply_2(v_toPure_2371_, lean_box(0), v___x_2373_);
return v___x_2377_;
}
else
{
size_t v___x_2378_; size_t v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = lean_usize_of_nat(v___x_2374_);
v___x_2379_ = lean_usize_of_nat(v_stop_2369_);
v___x_2380_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2365_, v___f_2372_, v_as_2367_, v___x_2378_, v___x_2379_, v___x_2373_);
return v___x_2380_;
}
}
else
{
uint8_t v___x_2381_; 
v___x_2381_ = lean_nat_dec_lt(v_stop_2369_, v_start_2368_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; 
lean_inc(v_toPure_2371_);
lean_dec_ref(v___f_2372_);
lean_dec_ref(v_as_2367_);
lean_dec_ref(v_inst_2365_);
v___x_2382_ = lean_apply_2(v_toPure_2371_, lean_box(0), v___x_2373_);
return v___x_2382_;
}
else
{
size_t v___x_2383_; size_t v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = lean_usize_of_nat(v_start_2368_);
v___x_2384_ = lean_usize_of_nat(v_stop_2369_);
v___x_2385_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2365_, v___f_2372_, v_as_2367_, v___x_2383_, v___x_2384_, v___x_2373_);
return v___x_2385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___boxed(lean_object* v_inst_2386_, lean_object* v_f_2387_, lean_object* v_as_2388_, lean_object* v_start_2389_, lean_object* v_stop_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Array_forRevM___redArg(v_inst_2386_, v_f_2387_, v_as_2388_, v_start_2389_, v_stop_2390_);
lean_dec(v_stop_2390_);
lean_dec(v_start_2389_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM(lean_object* v_00_u03b1_2392_, lean_object* v_m_2393_, lean_object* v_inst_2394_, lean_object* v_f_2395_, lean_object* v_as_2396_, lean_object* v_start_2397_, lean_object* v_stop_2398_){
_start:
{
lean_object* v_toApplicative_2399_; lean_object* v_toPure_2400_; lean_object* v___f_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v_toApplicative_2399_ = lean_ctor_get(v_inst_2394_, 0);
v_toPure_2400_ = lean_ctor_get(v_toApplicative_2399_, 1);
v___f_2401_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2401_, 0, v_f_2395_);
v___x_2402_ = lean_box(0);
v___x_2403_ = lean_array_get_size(v_as_2396_);
v___x_2404_ = lean_nat_dec_le(v_start_2397_, v___x_2403_);
if (v___x_2404_ == 0)
{
uint8_t v___x_2405_; 
v___x_2405_ = lean_nat_dec_lt(v_stop_2398_, v___x_2403_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; 
lean_inc(v_toPure_2400_);
lean_dec_ref(v___f_2401_);
lean_dec_ref(v_as_2396_);
lean_dec_ref(v_inst_2394_);
v___x_2406_ = lean_apply_2(v_toPure_2400_, lean_box(0), v___x_2402_);
return v___x_2406_;
}
else
{
size_t v___x_2407_; size_t v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = lean_usize_of_nat(v___x_2403_);
v___x_2408_ = lean_usize_of_nat(v_stop_2398_);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2394_, v___f_2401_, v_as_2396_, v___x_2407_, v___x_2408_, v___x_2402_);
return v___x_2409_;
}
}
else
{
uint8_t v___x_2410_; 
v___x_2410_ = lean_nat_dec_lt(v_stop_2398_, v_start_2397_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; 
lean_inc(v_toPure_2400_);
lean_dec_ref(v___f_2401_);
lean_dec_ref(v_as_2396_);
lean_dec_ref(v_inst_2394_);
v___x_2411_ = lean_apply_2(v_toPure_2400_, lean_box(0), v___x_2402_);
return v___x_2411_;
}
else
{
size_t v___x_2412_; size_t v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = lean_usize_of_nat(v_start_2397_);
v___x_2413_ = lean_usize_of_nat(v_stop_2398_);
v___x_2414_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2394_, v___f_2401_, v_as_2396_, v___x_2412_, v___x_2413_, v___x_2402_);
return v___x_2414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___boxed(lean_object* v_00_u03b1_2415_, lean_object* v_m_2416_, lean_object* v_inst_2417_, lean_object* v_f_2418_, lean_object* v_as_2419_, lean_object* v_start_2420_, lean_object* v_stop_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Array_forRevM(v_00_u03b1_2415_, v_m_2416_, v_inst_2417_, v_f_2418_, v_as_2419_, v_start_2420_, v_stop_2421_);
lean_dec(v_stop_2421_);
lean_dec(v_start_2420_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___lam__0(lean_object* v_f_2423_, lean_object* v_x1_2424_, lean_object* v_x2_2425_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_apply_2(v_f_2423_, v_x1_2424_, v_x2_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg(lean_object* v_f_2446_, lean_object* v_init_2447_, lean_object* v_as_2448_, lean_object* v_start_2449_, lean_object* v_stop_2450_){
_start:
{
lean_object* v___x_2451_; uint8_t v___x_2452_; 
v___x_2451_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2452_ = lean_nat_dec_lt(v_start_2449_, v_stop_2450_);
if (v___x_2452_ == 0)
{
lean_dec_ref(v_as_2448_);
lean_dec(v_f_2446_);
return v_init_2447_;
}
else
{
lean_object* v___f_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___f_2453_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2453_, 0, v_f_2446_);
v___x_2454_ = lean_array_get_size(v_as_2448_);
v___x_2455_ = lean_nat_dec_le(v_stop_2450_, v___x_2454_);
if (v___x_2455_ == 0)
{
uint8_t v___x_2456_; 
v___x_2456_ = lean_nat_dec_lt(v_start_2449_, v___x_2454_);
if (v___x_2456_ == 0)
{
lean_dec_ref(v___f_2453_);
lean_dec_ref(v_as_2448_);
return v_init_2447_;
}
else
{
size_t v___x_2457_; size_t v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = lean_usize_of_nat(v_start_2449_);
v___x_2458_ = lean_usize_of_nat(v___x_2454_);
v___x_2459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2451_, v___f_2453_, v_as_2448_, v___x_2457_, v___x_2458_, v_init_2447_);
return v___x_2459_;
}
}
else
{
size_t v___x_2460_; size_t v___x_2461_; lean_object* v___x_2462_; 
v___x_2460_ = lean_usize_of_nat(v_start_2449_);
v___x_2461_ = lean_usize_of_nat(v_stop_2450_);
v___x_2462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2451_, v___f_2453_, v_as_2448_, v___x_2460_, v___x_2461_, v_init_2447_);
return v___x_2462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___boxed(lean_object* v_f_2463_, lean_object* v_init_2464_, lean_object* v_as_2465_, lean_object* v_start_2466_, lean_object* v_stop_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Array_foldl___redArg(v_f_2463_, v_init_2464_, v_as_2465_, v_start_2466_, v_stop_2467_);
lean_dec(v_stop_2467_);
lean_dec(v_start_2466_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl(lean_object* v_00_u03b1_2469_, lean_object* v_00_u03b2_2470_, lean_object* v_f_2471_, lean_object* v_init_2472_, lean_object* v_as_2473_, lean_object* v_start_2474_, lean_object* v_stop_2475_){
_start:
{
lean_object* v___x_2476_; uint8_t v___x_2477_; 
v___x_2476_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2477_ = lean_nat_dec_lt(v_start_2474_, v_stop_2475_);
if (v___x_2477_ == 0)
{
lean_dec_ref(v_as_2473_);
lean_dec(v_f_2471_);
return v_init_2472_;
}
else
{
lean_object* v___f_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
v___f_2478_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2478_, 0, v_f_2471_);
v___x_2479_ = lean_array_get_size(v_as_2473_);
v___x_2480_ = lean_nat_dec_le(v_stop_2475_, v___x_2479_);
if (v___x_2480_ == 0)
{
uint8_t v___x_2481_; 
v___x_2481_ = lean_nat_dec_lt(v_start_2474_, v___x_2479_);
if (v___x_2481_ == 0)
{
lean_dec_ref(v___f_2478_);
lean_dec_ref(v_as_2473_);
return v_init_2472_;
}
else
{
size_t v___x_2482_; size_t v___x_2483_; lean_object* v___x_2484_; 
v___x_2482_ = lean_usize_of_nat(v_start_2474_);
v___x_2483_ = lean_usize_of_nat(v___x_2479_);
v___x_2484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2476_, v___f_2478_, v_as_2473_, v___x_2482_, v___x_2483_, v_init_2472_);
return v___x_2484_;
}
}
else
{
size_t v___x_2485_; size_t v___x_2486_; lean_object* v___x_2487_; 
v___x_2485_ = lean_usize_of_nat(v_start_2474_);
v___x_2486_ = lean_usize_of_nat(v_stop_2475_);
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2476_, v___f_2478_, v_as_2473_, v___x_2485_, v___x_2486_, v_init_2472_);
return v___x_2487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___boxed(lean_object* v_00_u03b1_2488_, lean_object* v_00_u03b2_2489_, lean_object* v_f_2490_, lean_object* v_init_2491_, lean_object* v_as_2492_, lean_object* v_start_2493_, lean_object* v_stop_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Array_foldl(v_00_u03b1_2488_, v_00_u03b2_2489_, v_f_2490_, v_init_2491_, v_as_2492_, v_start_2493_, v_stop_2494_);
lean_dec(v_stop_2494_);
lean_dec(v_start_2493_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg(lean_object* v_f_2496_, lean_object* v_init_2497_, lean_object* v_as_2498_, lean_object* v_start_2499_, lean_object* v_stop_2500_){
_start:
{
lean_object* v___f_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; uint8_t v___x_2504_; 
v___f_2501_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2501_, 0, v_f_2496_);
v___x_2502_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2503_ = lean_array_get_size(v_as_2498_);
v___x_2504_ = lean_nat_dec_le(v_start_2499_, v___x_2503_);
if (v___x_2504_ == 0)
{
uint8_t v___x_2505_; 
v___x_2505_ = lean_nat_dec_lt(v_stop_2500_, v___x_2503_);
if (v___x_2505_ == 0)
{
lean_dec_ref(v___f_2501_);
lean_dec_ref(v_as_2498_);
return v_init_2497_;
}
else
{
size_t v___x_2506_; size_t v___x_2507_; lean_object* v___x_2508_; 
v___x_2506_ = lean_usize_of_nat(v___x_2503_);
v___x_2507_ = lean_usize_of_nat(v_stop_2500_);
v___x_2508_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2502_, v___f_2501_, v_as_2498_, v___x_2506_, v___x_2507_, v_init_2497_);
return v___x_2508_;
}
}
else
{
uint8_t v___x_2509_; 
v___x_2509_ = lean_nat_dec_lt(v_stop_2500_, v_start_2499_);
if (v___x_2509_ == 0)
{
lean_dec_ref(v___f_2501_);
lean_dec_ref(v_as_2498_);
return v_init_2497_;
}
else
{
size_t v___x_2510_; size_t v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = lean_usize_of_nat(v_start_2499_);
v___x_2511_ = lean_usize_of_nat(v_stop_2500_);
v___x_2512_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2502_, v___f_2501_, v_as_2498_, v___x_2510_, v___x_2511_, v_init_2497_);
return v___x_2512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg___boxed(lean_object* v_f_2513_, lean_object* v_init_2514_, lean_object* v_as_2515_, lean_object* v_start_2516_, lean_object* v_stop_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Array_foldr___redArg(v_f_2513_, v_init_2514_, v_as_2515_, v_start_2516_, v_stop_2517_);
lean_dec(v_stop_2517_);
lean_dec(v_start_2516_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr(lean_object* v_00_u03b1_2519_, lean_object* v_00_u03b2_2520_, lean_object* v_f_2521_, lean_object* v_init_2522_, lean_object* v_as_2523_, lean_object* v_start_2524_, lean_object* v_stop_2525_){
_start:
{
lean_object* v___f_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___f_2526_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2526_, 0, v_f_2521_);
v___x_2527_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2528_ = lean_array_get_size(v_as_2523_);
v___x_2529_ = lean_nat_dec_le(v_start_2524_, v___x_2528_);
if (v___x_2529_ == 0)
{
uint8_t v___x_2530_; 
v___x_2530_ = lean_nat_dec_lt(v_stop_2525_, v___x_2528_);
if (v___x_2530_ == 0)
{
lean_dec_ref(v___f_2526_);
lean_dec_ref(v_as_2523_);
return v_init_2522_;
}
else
{
size_t v___x_2531_; size_t v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_usize_of_nat(v___x_2528_);
v___x_2532_ = lean_usize_of_nat(v_stop_2525_);
v___x_2533_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2527_, v___f_2526_, v_as_2523_, v___x_2531_, v___x_2532_, v_init_2522_);
return v___x_2533_;
}
}
else
{
uint8_t v___x_2534_; 
v___x_2534_ = lean_nat_dec_lt(v_stop_2525_, v_start_2524_);
if (v___x_2534_ == 0)
{
lean_dec_ref(v___f_2526_);
lean_dec_ref(v_as_2523_);
return v_init_2522_;
}
else
{
size_t v___x_2535_; size_t v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = lean_usize_of_nat(v_start_2524_);
v___x_2536_ = lean_usize_of_nat(v_stop_2525_);
v___x_2537_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2527_, v___f_2526_, v_as_2523_, v___x_2535_, v___x_2536_, v_init_2522_);
return v___x_2537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___boxed(lean_object* v_00_u03b1_2538_, lean_object* v_00_u03b2_2539_, lean_object* v_f_2540_, lean_object* v_init_2541_, lean_object* v_as_2542_, lean_object* v_start_2543_, lean_object* v_stop_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Array_foldr(v_00_u03b1_2538_, v_00_u03b2_2539_, v_f_2540_, v_init_2541_, v_as_2542_, v_start_2543_, v_stop_2544_);
lean_dec(v_stop_2544_);
lean_dec(v_start_2543_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg___lam__0(lean_object* v_inst_2546_, lean_object* v_x1_2547_, lean_object* v_x2_2548_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_apply_2(v_inst_2546_, v_x1_2547_, v_x2_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg(lean_object* v_inst_2550_, lean_object* v_inst_2551_, lean_object* v_as_2552_){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
v___x_2553_ = lean_array_get_size(v_as_2552_);
v___x_2554_ = lean_unsigned_to_nat(0u);
v___x_2555_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2556_ = lean_nat_dec_lt(v___x_2554_, v___x_2553_);
if (v___x_2556_ == 0)
{
lean_dec_ref(v_as_2552_);
lean_dec(v_inst_2550_);
return v_inst_2551_;
}
else
{
lean_object* v___f_2557_; size_t v___x_2558_; size_t v___x_2559_; lean_object* v___x_2560_; 
v___f_2557_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2557_, 0, v_inst_2550_);
v___x_2558_ = lean_usize_of_nat(v___x_2553_);
v___x_2559_ = ((size_t)0ULL);
v___x_2560_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2555_, v___f_2557_, v_as_2552_, v___x_2558_, v___x_2559_, v_inst_2551_);
return v___x_2560_;
}
}
}
LEAN_EXPORT lean_object* l_Array_sum(lean_object* v_00_u03b1_2561_, lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_as_2564_){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2565_ = lean_array_get_size(v_as_2564_);
v___x_2566_ = lean_unsigned_to_nat(0u);
v___x_2567_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2568_ = lean_nat_dec_lt(v___x_2566_, v___x_2565_);
if (v___x_2568_ == 0)
{
lean_dec_ref(v_as_2564_);
lean_dec(v_inst_2562_);
return v_inst_2563_;
}
else
{
lean_object* v___f_2569_; size_t v___x_2570_; size_t v___x_2571_; lean_object* v___x_2572_; 
v___f_2569_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2569_, 0, v_inst_2562_);
v___x_2570_ = lean_usize_of_nat(v___x_2565_);
v___x_2571_ = ((size_t)0ULL);
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2567_, v___f_2569_, v_as_2564_, v___x_2570_, v___x_2571_, v_inst_2563_);
return v___x_2572_;
}
}
}
LEAN_EXPORT lean_object* l_Array_prod___redArg(lean_object* v_inst_2573_, lean_object* v_inst_2574_, lean_object* v_as_2575_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; 
v___x_2576_ = lean_array_get_size(v_as_2575_);
v___x_2577_ = lean_unsigned_to_nat(0u);
v___x_2578_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2579_ = lean_nat_dec_lt(v___x_2577_, v___x_2576_);
if (v___x_2579_ == 0)
{
lean_dec_ref(v_as_2575_);
lean_dec(v_inst_2573_);
return v_inst_2574_;
}
else
{
lean_object* v___f_2580_; size_t v___x_2581_; size_t v___x_2582_; lean_object* v___x_2583_; 
v___f_2580_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2580_, 0, v_inst_2573_);
v___x_2581_ = lean_usize_of_nat(v___x_2576_);
v___x_2582_ = ((size_t)0ULL);
v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2578_, v___f_2580_, v_as_2575_, v___x_2581_, v___x_2582_, v_inst_2574_);
return v___x_2583_;
}
}
}
LEAN_EXPORT lean_object* l_Array_prod(lean_object* v_00_u03b1_2584_, lean_object* v_inst_2585_, lean_object* v_inst_2586_, lean_object* v_as_2587_){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; 
v___x_2588_ = lean_array_get_size(v_as_2587_);
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2591_ = lean_nat_dec_lt(v___x_2589_, v___x_2588_);
if (v___x_2591_ == 0)
{
lean_dec_ref(v_as_2587_);
lean_dec(v_inst_2585_);
return v_inst_2586_;
}
else
{
lean_object* v___f_2592_; size_t v___x_2593_; size_t v___x_2594_; lean_object* v___x_2595_; 
v___f_2592_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2592_, 0, v_inst_2585_);
v___x_2593_ = lean_usize_of_nat(v___x_2588_);
v___x_2594_ = ((size_t)0ULL);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2590_, v___f_2592_, v_as_2587_, v___x_2593_, v___x_2594_, v_inst_2586_);
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0(lean_object* v_p_2596_, lean_object* v_x1_2597_, lean_object* v_x2_2598_){
_start:
{
lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2599_ = lean_apply_1(v_p_2596_, v_x1_2597_);
v___x_2600_ = lean_unbox(v___x_2599_);
if (v___x_2600_ == 0)
{
lean_inc(v_x2_2598_);
return v_x2_2598_;
}
else
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = lean_unsigned_to_nat(1u);
v___x_2602_ = lean_nat_add(v_x2_2598_, v___x_2601_);
return v___x_2602_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0___boxed(lean_object* v_p_2603_, lean_object* v_x1_2604_, lean_object* v_x2_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Array_countP___redArg___lam__0(v_p_2603_, v_x1_2604_, v_x2_2605_);
lean_dec(v_x2_2605_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg(lean_object* v_p_2607_, lean_object* v_as_2608_){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = lean_array_get_size(v_as_2608_);
v___x_2611_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2612_ = lean_nat_dec_lt(v___x_2609_, v___x_2610_);
if (v___x_2612_ == 0)
{
lean_dec_ref(v_as_2608_);
lean_dec_ref(v_p_2607_);
return v___x_2609_;
}
else
{
lean_object* v___f_2613_; size_t v___x_2614_; size_t v___x_2615_; lean_object* v___x_2616_; 
v___f_2613_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2613_, 0, v_p_2607_);
v___x_2614_ = lean_usize_of_nat(v___x_2610_);
v___x_2615_ = ((size_t)0ULL);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2611_, v___f_2613_, v_as_2608_, v___x_2614_, v___x_2615_, v___x_2609_);
return v___x_2616_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP(lean_object* v_00_u03b1_2617_, lean_object* v_p_2618_, lean_object* v_as_2619_){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = lean_array_get_size(v_as_2619_);
v___x_2622_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2623_ = lean_nat_dec_lt(v___x_2620_, v___x_2621_);
if (v___x_2623_ == 0)
{
lean_dec_ref(v_as_2619_);
lean_dec_ref(v_p_2618_);
return v___x_2620_;
}
else
{
lean_object* v___f_2624_; size_t v___x_2625_; size_t v___x_2626_; lean_object* v___x_2627_; 
v___f_2624_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2624_, 0, v_p_2618_);
v___x_2625_ = lean_usize_of_nat(v___x_2621_);
v___x_2626_ = ((size_t)0ULL);
v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2622_, v___f_2624_, v_as_2619_, v___x_2625_, v___x_2626_, v___x_2620_);
return v___x_2627_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0(lean_object* v_inst_2628_, lean_object* v_a_2629_, lean_object* v_x1_2630_, lean_object* v_x2_2631_){
_start:
{
lean_object* v___x_2632_; uint8_t v___x_2633_; 
v___x_2632_ = lean_apply_2(v_inst_2628_, v_x1_2630_, v_a_2629_);
v___x_2633_ = lean_unbox(v___x_2632_);
if (v___x_2633_ == 0)
{
lean_inc(v_x2_2631_);
return v_x2_2631_;
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = lean_unsigned_to_nat(1u);
v___x_2635_ = lean_nat_add(v_x2_2631_, v___x_2634_);
return v___x_2635_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0___boxed(lean_object* v_inst_2636_, lean_object* v_a_2637_, lean_object* v_x1_2638_, lean_object* v_x2_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Array_count___redArg___lam__0(v_inst_2636_, v_a_2637_, v_x1_2638_, v_x2_2639_);
lean_dec(v_x2_2639_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg(lean_object* v_inst_2641_, lean_object* v_a_2642_, lean_object* v_as_2643_){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2644_ = lean_unsigned_to_nat(0u);
v___x_2645_ = lean_array_get_size(v_as_2643_);
v___x_2646_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2647_ = lean_nat_dec_lt(v___x_2644_, v___x_2645_);
if (v___x_2647_ == 0)
{
lean_dec_ref(v_as_2643_);
lean_dec(v_a_2642_);
lean_dec_ref(v_inst_2641_);
return v___x_2644_;
}
else
{
lean_object* v___f_2648_; size_t v___x_2649_; size_t v___x_2650_; lean_object* v___x_2651_; 
v___f_2648_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2648_, 0, v_inst_2641_);
lean_closure_set(v___f_2648_, 1, v_a_2642_);
v___x_2649_ = lean_usize_of_nat(v___x_2645_);
v___x_2650_ = ((size_t)0ULL);
v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2646_, v___f_2648_, v_as_2643_, v___x_2649_, v___x_2650_, v___x_2644_);
return v___x_2651_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count(lean_object* v_00_u03b1_2652_, lean_object* v_inst_2653_, lean_object* v_a_2654_, lean_object* v_as_2655_){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v___x_2656_ = lean_unsigned_to_nat(0u);
v___x_2657_ = lean_array_get_size(v_as_2655_);
v___x_2658_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2659_ = lean_nat_dec_lt(v___x_2656_, v___x_2657_);
if (v___x_2659_ == 0)
{
lean_dec_ref(v_as_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_inst_2653_);
return v___x_2656_;
}
else
{
lean_object* v___f_2660_; size_t v___x_2661_; size_t v___x_2662_; lean_object* v___x_2663_; 
v___f_2660_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2660_, 0, v_inst_2653_);
lean_closure_set(v___f_2660_, 1, v_a_2654_);
v___x_2661_ = lean_usize_of_nat(v___x_2657_);
v___x_2662_ = ((size_t)0ULL);
v___x_2663_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2658_, v___f_2660_, v_as_2655_, v___x_2661_, v___x_2662_, v___x_2656_);
return v___x_2663_;
}
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg___lam__0(lean_object* v_f_2664_, lean_object* v_x_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_apply_1(v_f_2664_, v_x_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg(lean_object* v_f_2667_, lean_object* v_as_2668_){
_start:
{
lean_object* v___f_2669_; lean_object* v___x_2670_; size_t v_sz_2671_; size_t v___x_2672_; lean_object* v___x_2673_; 
v___f_2669_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2669_, 0, v_f_2667_);
v___x_2670_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2671_ = lean_array_size(v_as_2668_);
v___x_2672_ = ((size_t)0ULL);
v___x_2673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2670_, v___f_2669_, v_sz_2671_, v___x_2672_, v_as_2668_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Array_map(lean_object* v_00_u03b1_2674_, lean_object* v_00_u03b2_2675_, lean_object* v_f_2676_, lean_object* v_as_2677_){
_start:
{
lean_object* v___f_2678_; lean_object* v___x_2679_; size_t v_sz_2680_; size_t v___x_2681_; lean_object* v___x_2682_; 
v___f_2678_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2678_, 0, v_f_2676_);
v___x_2679_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2680_ = lean_array_size(v_as_2677_);
v___x_2681_ = ((size_t)0ULL);
v___x_2682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2679_, v___f_2678_, v_sz_2680_, v___x_2681_, v_as_2677_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0(lean_object* v___y_2683_, lean_object* v_x_2684_){
_start:
{
lean_inc(v___y_2683_);
return v___y_2683_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0___boxed(lean_object* v___y_2685_, lean_object* v_x_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Array_instFunctor___lam__0(v___y_2685_, v_x_2686_);
lean_dec(v_x_2686_);
lean_dec(v___y_2685_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__1(lean_object* v_00_u03b1_2688_, lean_object* v_00_u03b2_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v___f_2692_; lean_object* v___x_2693_; size_t v_sz_2694_; size_t v___x_2695_; lean_object* v___x_2696_; 
v___f_2692_ = lean_alloc_closure((void*)(l_Array_instFunctor___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2692_, 0, v___y_2690_);
v___x_2693_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2694_ = lean_array_size(v___y_2691_);
v___x_2695_ = ((size_t)0ULL);
v___x_2696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2693_, v___f_2692_, v_sz_2694_, v___x_2695_, v___y_2691_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg___lam__0(lean_object* v_f_2703_, lean_object* v_x1_2704_, lean_object* v_x2_2705_, lean_object* v_x3_2706_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = lean_apply_3(v_f_2703_, v_x1_2704_, v_x2_2705_, lean_box(0));
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg(lean_object* v_as_2708_, lean_object* v_f_2709_){
_start:
{
lean_object* v___f_2710_; lean_object* v___x_2711_; size_t v_sz_2712_; size_t v___x_2713_; lean_object* v___x_2714_; 
v___f_2710_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2710_, 0, v_f_2709_);
v___x_2711_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2712_ = lean_array_size(v_as_2708_);
v___x_2713_ = ((size_t)0ULL);
v___x_2714_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2711_, v___f_2710_, v_sz_2712_, v___x_2713_, v_as_2708_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx(lean_object* v_00_u03b1_2715_, lean_object* v_00_u03b2_2716_, lean_object* v_as_2717_, lean_object* v_f_2718_){
_start:
{
lean_object* v___f_2719_; lean_object* v___x_2720_; size_t v_sz_2721_; size_t v___x_2722_; lean_object* v___x_2723_; 
v___f_2719_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2719_, 0, v_f_2718_);
v___x_2720_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2721_ = lean_array_size(v_as_2717_);
v___x_2722_ = ((size_t)0ULL);
v___x_2723_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2720_, v___f_2719_, v_sz_2721_, v___x_2722_, v_as_2717_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx___redArg(lean_object* v_f_2724_, lean_object* v_as_2725_){
_start:
{
lean_object* v___f_2726_; lean_object* v___x_2727_; size_t v_sz_2728_; size_t v___x_2729_; lean_object* v___x_2730_; 
v___f_2726_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2726_, 0, v_f_2724_);
v___x_2727_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2728_ = lean_array_size(v_as_2725_);
v___x_2729_ = ((size_t)0ULL);
v___x_2730_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2727_, v___f_2726_, v_sz_2728_, v___x_2729_, v_as_2725_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx(lean_object* v_00_u03b1_2731_, lean_object* v_00_u03b2_2732_, lean_object* v_f_2733_, lean_object* v_as_2734_){
_start:
{
lean_object* v___f_2735_; lean_object* v___x_2736_; size_t v_sz_2737_; size_t v___x_2738_; lean_object* v___x_2739_; 
v___f_2735_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2735_, 0, v_f_2733_);
v___x_2736_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2737_ = lean_array_size(v_as_2734_);
v___x_2738_ = ((size_t)0ULL);
v___x_2739_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2736_, v___f_2735_, v_sz_2737_, v___x_2738_, v_as_2734_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(lean_object* v_start_2740_, size_t v_sz_2741_, size_t v_i_2742_, lean_object* v_bs_2743_){
_start:
{
uint8_t v___x_2744_; 
v___x_2744_ = lean_usize_dec_lt(v_i_2742_, v_sz_2741_);
if (v___x_2744_ == 0)
{
return v_bs_2743_;
}
else
{
lean_object* v_v_2745_; lean_object* v___x_2746_; lean_object* v_bs_x27_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; size_t v___x_2751_; size_t v___x_2752_; lean_object* v___x_2753_; 
v_v_2745_ = lean_array_uget(v_bs_2743_, v_i_2742_);
v___x_2746_ = lean_unsigned_to_nat(0u);
v_bs_x27_2747_ = lean_array_uset(v_bs_2743_, v_i_2742_, v___x_2746_);
v___x_2748_ = lean_usize_to_nat(v_i_2742_);
v___x_2749_ = lean_nat_add(v_start_2740_, v___x_2748_);
lean_dec(v___x_2748_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v_v_2745_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = ((size_t)1ULL);
v___x_2752_ = lean_usize_add(v_i_2742_, v___x_2751_);
v___x_2753_ = lean_array_uset(v_bs_x27_2747_, v_i_2742_, v___x_2750_);
v_i_2742_ = v___x_2752_;
v_bs_2743_ = v___x_2753_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg___boxed(lean_object* v_start_2755_, lean_object* v_sz_2756_, lean_object* v_i_2757_, lean_object* v_bs_2758_){
_start:
{
size_t v_sz_boxed_2759_; size_t v_i_boxed_2760_; lean_object* v_res_2761_; 
v_sz_boxed_2759_ = lean_unbox_usize(v_sz_2756_);
lean_dec(v_sz_2756_);
v_i_boxed_2760_ = lean_unbox_usize(v_i_2757_);
lean_dec(v_i_2757_);
v_res_2761_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2755_, v_sz_boxed_2759_, v_i_boxed_2760_, v_bs_2758_);
lean_dec(v_start_2755_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg(lean_object* v_xs_2762_, lean_object* v_start_2763_){
_start:
{
size_t v_sz_2764_; size_t v___x_2765_; lean_object* v___x_2766_; 
v_sz_2764_ = lean_array_size(v_xs_2762_);
v___x_2765_ = ((size_t)0ULL);
v___x_2766_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2763_, v_sz_2764_, v___x_2765_, v_xs_2762_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg___boxed(lean_object* v_xs_2767_, lean_object* v_start_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Array_zipIdx___redArg(v_xs_2767_, v_start_2768_);
lean_dec(v_start_2768_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx(lean_object* v_00_u03b1_2770_, lean_object* v_xs_2771_, lean_object* v_start_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Array_zipIdx___redArg(v_xs_2771_, v_start_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___boxed(lean_object* v_00_u03b1_2774_, lean_object* v_xs_2775_, lean_object* v_start_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Array_zipIdx(v_00_u03b1_2774_, v_xs_2775_, v_start_2776_);
lean_dec(v_start_2776_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(lean_object* v_00_u03b1_2778_, lean_object* v_start_2779_, lean_object* v_as_2780_, size_t v_sz_2781_, size_t v_i_2782_, lean_object* v_bs_2783_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2779_, v_sz_2781_, v_i_2782_, v_bs_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___boxed(lean_object* v_00_u03b1_2785_, lean_object* v_start_2786_, lean_object* v_as_2787_, lean_object* v_sz_2788_, lean_object* v_i_2789_, lean_object* v_bs_2790_){
_start:
{
size_t v_sz_boxed_2791_; size_t v_i_boxed_2792_; lean_object* v_res_2793_; 
v_sz_boxed_2791_ = lean_unbox_usize(v_sz_2788_);
lean_dec(v_sz_2788_);
v_i_boxed_2792_ = lean_unbox_usize(v_i_2789_);
lean_dec(v_i_2789_);
v_res_2793_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(v_00_u03b1_2785_, v_start_2786_, v_as_2787_, v_sz_boxed_2791_, v_i_boxed_2792_, v_bs_2790_);
lean_dec_ref(v_as_2787_);
lean_dec(v_start_2786_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0(lean_object* v_p_2794_, lean_object* v___x_2795_, lean_object* v___x_2796_, lean_object* v_a_2797_, lean_object* v_x_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___x_2800_; uint8_t v___x_2801_; 
lean_inc(v_a_2797_);
v___x_2800_ = lean_apply_1(v_p_2794_, v_a_2797_);
v___x_2801_ = lean_unbox(v___x_2800_);
if (v___x_2801_ == 0)
{
lean_object* v___x_2802_; 
lean_dec(v_a_2797_);
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2795_);
return v___x_2802_;
}
else
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
lean_dec_ref(v___x_2795_);
v___x_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2803_, 0, v_a_2797_);
v___x_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
v___x_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
lean_ctor_set(v___x_2805_, 1, v___x_2796_);
v___x_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
return v___x_2806_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0___boxed(lean_object* v_p_2807_, lean_object* v___x_2808_, lean_object* v___x_2809_, lean_object* v_a_2810_, lean_object* v_x_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Array_find_x3f___redArg___lam__0(v_p_2807_, v___x_2808_, v___x_2809_, v_a_2810_, v_x_2811_, v___y_2812_);
lean_dec_ref(v___y_2812_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg(lean_object* v_p_2814_, lean_object* v_as_2815_){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___f_2820_; size_t v_sz_2821_; size_t v___x_2822_; lean_object* v___x_2823_; lean_object* v_fst_2824_; 
v___x_2816_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2817_ = lean_box(0);
v___x_2818_ = lean_box(0);
v___x_2819_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2820_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2820_, 0, v_p_2814_);
lean_closure_set(v___f_2820_, 1, v___x_2819_);
lean_closure_set(v___f_2820_, 2, v___x_2818_);
v_sz_2821_ = lean_array_size(v_as_2815_);
v___x_2822_ = ((size_t)0ULL);
v___x_2823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2816_, v_as_2815_, v___f_2820_, v_sz_2821_, v___x_2822_, v___x_2819_);
v_fst_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_fst_2824_);
lean_dec(v___x_2823_);
if (lean_obj_tag(v_fst_2824_) == 0)
{
return v___x_2817_;
}
else
{
lean_object* v_val_2825_; 
v_val_2825_ = lean_ctor_get(v_fst_2824_, 0);
lean_inc(v_val_2825_);
lean_dec_ref_known(v_fst_2824_, 1);
return v_val_2825_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f(lean_object* v_00_u03b1_2826_, lean_object* v_p_2827_, lean_object* v_as_2828_){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___f_2833_; size_t v_sz_2834_; size_t v___x_2835_; lean_object* v___x_2836_; lean_object* v_fst_2837_; 
v___x_2829_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2830_ = lean_box(0);
v___x_2831_ = lean_box(0);
v___x_2832_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2833_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2833_, 0, v_p_2827_);
lean_closure_set(v___f_2833_, 1, v___x_2832_);
lean_closure_set(v___f_2833_, 2, v___x_2831_);
v_sz_2834_ = lean_array_size(v_as_2828_);
v___x_2835_ = ((size_t)0ULL);
v___x_2836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2829_, v_as_2828_, v___f_2833_, v_sz_2834_, v___x_2835_, v___x_2832_);
v_fst_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_fst_2837_);
lean_dec(v___x_2836_);
if (lean_obj_tag(v_fst_2837_) == 0)
{
return v___x_2830_;
}
else
{
lean_object* v_val_2838_; 
v_val_2838_ = lean_ctor_get(v_fst_2837_, 0);
lean_inc(v_val_2838_);
lean_dec_ref_known(v_fst_2837_, 1);
return v_val_2838_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0(lean_object* v_f_2839_, lean_object* v___x_2840_, lean_object* v___x_2841_, lean_object* v_a_2842_, lean_object* v_x_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = lean_apply_1(v_f_2839_, v_a_2842_);
if (lean_obj_tag(v___x_2845_) == 1)
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
lean_dec_ref(v___x_2841_);
v___x_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
v___x_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
lean_ctor_set(v___x_2847_, 1, v___x_2840_);
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
return v___x_2848_;
}
else
{
lean_object* v___x_2849_; 
lean_dec(v___x_2845_);
v___x_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2841_);
return v___x_2849_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2850_, lean_object* v___x_2851_, lean_object* v___x_2852_, lean_object* v_a_2853_, lean_object* v_x_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Array_findSome_x3f___redArg___lam__0(v_f_2850_, v___x_2851_, v___x_2852_, v_a_2853_, v_x_2854_, v___y_2855_);
lean_dec_ref(v___y_2855_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg(lean_object* v_f_2857_, lean_object* v_as_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___f_2863_; size_t v_sz_2864_; size_t v___x_2865_; lean_object* v___x_2866_; lean_object* v_fst_2867_; 
v___x_2859_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2860_ = lean_box(0);
v___x_2861_ = lean_box(0);
v___x_2862_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2863_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2863_, 0, v_f_2857_);
lean_closure_set(v___f_2863_, 1, v___x_2861_);
lean_closure_set(v___f_2863_, 2, v___x_2862_);
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
LEAN_EXPORT lean_object* l_Array_findSome_x3f(lean_object* v_00_u03b1_2869_, lean_object* v_00_u03b2_2870_, lean_object* v_f_2871_, lean_object* v_as_2872_){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___f_2877_; size_t v_sz_2878_; size_t v___x_2879_; lean_object* v___x_2880_; lean_object* v_fst_2881_; 
v___x_2873_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2874_ = lean_box(0);
v___x_2875_ = lean_box(0);
v___x_2876_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2877_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2877_, 0, v_f_2871_);
lean_closure_set(v___f_2877_, 1, v___x_2875_);
lean_closure_set(v___f_2877_, 2, v___x_2876_);
v_sz_2878_ = lean_array_size(v_as_2872_);
v___x_2879_ = ((size_t)0ULL);
v___x_2880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2873_, v_as_2872_, v___f_2877_, v_sz_2878_, v___x_2879_, v___x_2876_);
v_fst_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_fst_2881_);
lean_dec(v___x_2880_);
if (lean_obj_tag(v_fst_2881_) == 0)
{
return v___x_2874_;
}
else
{
lean_object* v_val_2882_; 
v_val_2882_ = lean_ctor_get(v_fst_2881_, 0);
lean_inc(v_val_2882_);
lean_dec_ref_known(v_fst_2881_, 1);
return v_val_2882_;
}
}
}
static lean_object* _init_l_Array_findSome_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2885_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__1));
v___x_2886_ = lean_unsigned_to_nat(14u);
v___x_2887_ = lean_unsigned_to_nat(1279u);
v___x_2888_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__0));
v___x_2889_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_2890_ = l_mkPanicMessageWithDecl(v___x_2889_, v___x_2888_, v___x_2887_, v___x_2886_, v___x_2885_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg(lean_object* v_inst_2891_, lean_object* v_f_2892_, lean_object* v_xs_2893_){
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
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg___boxed(lean_object* v_inst_2907_, lean_object* v_f_2908_, lean_object* v_xs_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Array_findSome_x21___redArg(v_inst_2907_, v_f_2908_, v_xs_2909_);
lean_dec(v_inst_2907_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21(lean_object* v_00_u03b1_2911_, lean_object* v_00_u03b2_2912_, lean_object* v_inst_2913_, lean_object* v_f_2914_, lean_object* v_xs_2915_){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___f_2922_; size_t v_sz_2923_; size_t v___x_2924_; lean_object* v___x_2925_; lean_object* v_fst_2926_; 
v___x_2919_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2920_ = lean_box(0);
v___x_2921_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2922_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2922_, 0, v_f_2914_);
lean_closure_set(v___f_2922_, 1, v___x_2920_);
lean_closure_set(v___f_2922_, 2, v___x_2921_);
v_sz_2923_ = lean_array_size(v_xs_2915_);
v___x_2924_ = ((size_t)0ULL);
v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2919_, v_xs_2915_, v___f_2922_, v_sz_2923_, v___x_2924_, v___x_2921_);
v_fst_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_fst_2926_);
lean_dec(v___x_2925_);
if (lean_obj_tag(v_fst_2926_) == 0)
{
goto v___jp_2916_;
}
else
{
lean_object* v_val_2927_; 
v_val_2927_ = lean_ctor_get(v_fst_2926_, 0);
lean_inc(v_val_2927_);
lean_dec_ref_known(v_fst_2926_, 1);
if (lean_obj_tag(v_val_2927_) == 0)
{
goto v___jp_2916_;
}
else
{
lean_object* v_val_2928_; 
v_val_2928_ = lean_ctor_get(v_val_2927_, 0);
lean_inc(v_val_2928_);
lean_dec_ref_known(v_val_2927_, 1);
return v_val_2928_;
}
}
v___jp_2916_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2918_ = l_panic___redArg(v_inst_2913_, v___x_2917_);
return v___x_2918_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___boxed(lean_object* v_00_u03b1_2929_, lean_object* v_00_u03b2_2930_, lean_object* v_inst_2931_, lean_object* v_f_2932_, lean_object* v_xs_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Array_findSome_x21(v_00_u03b1_2929_, v_00_u03b2_2930_, v_inst_2931_, v_f_2932_, v_xs_2933_);
lean_dec(v_inst_2931_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2935_, lean_object* v_x_2936_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_apply_1(v_f_2935_, v_x_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg(lean_object* v_f_2938_, lean_object* v_as_2939_){
_start:
{
lean_object* v___f_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___f_2940_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2940_, 0, v_f_2938_);
v___x_2941_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2942_ = lean_array_get_size(v_as_2939_);
v___x_2943_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2941_, v___f_2940_, v_as_2939_, v___x_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f(lean_object* v_00_u03b1_2944_, lean_object* v_00_u03b2_2945_, lean_object* v_f_2946_, lean_object* v_as_2947_){
_start:
{
lean_object* v___f_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___f_2948_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2948_, 0, v_f_2946_);
v___x_2949_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2950_ = lean_array_get_size(v_as_2947_);
v___x_2951_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2949_, v___f_2948_, v_as_2947_, v___x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg___lam__0(lean_object* v_p_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v___x_2954_; uint8_t v___x_2955_; 
lean_inc(v_a_2953_);
v___x_2954_ = lean_apply_1(v_p_2952_, v_a_2953_);
v___x_2955_ = lean_unbox(v___x_2954_);
if (v___x_2955_ == 0)
{
lean_object* v___x_2956_; 
lean_dec(v_a_2953_);
v___x_2956_ = lean_box(0);
return v___x_2956_;
}
else
{
lean_object* v___x_2957_; 
v___x_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2957_, 0, v_a_2953_);
return v___x_2957_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg(lean_object* v_p_2958_, lean_object* v_as_2959_){
_start:
{
lean_object* v___f_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___f_2960_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2960_, 0, v_p_2958_);
v___x_2961_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2962_ = lean_array_get_size(v_as_2959_);
v___x_2963_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2961_, v___f_2960_, v_as_2959_, v___x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f(lean_object* v_00_u03b1_2964_, lean_object* v_p_2965_, lean_object* v_as_2966_){
_start:
{
lean_object* v___f_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___f_2967_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2967_, 0, v_p_2965_);
v___x_2968_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2969_ = lean_array_get_size(v_as_2966_);
v___x_2970_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2968_, v___f_2967_, v_as_2966_, v___x_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object* v_p_2971_, lean_object* v_as_2972_, lean_object* v_j_2973_){
_start:
{
lean_object* v___x_2974_; uint8_t v___x_2975_; 
v___x_2974_ = lean_array_get_size(v_as_2972_);
v___x_2975_ = lean_nat_dec_lt(v_j_2973_, v___x_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; 
lean_dec(v_j_2973_);
lean_dec_ref(v_p_2971_);
v___x_2976_ = lean_box(0);
return v___x_2976_;
}
else
{
lean_object* v___x_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; 
v___x_2977_ = lean_array_fget_borrowed(v_as_2972_, v_j_2973_);
lean_inc_ref(v_p_2971_);
lean_inc(v___x_2977_);
v___x_2978_ = lean_apply_1(v_p_2971_, v___x_2977_);
v___x_2979_ = lean_unbox(v___x_2978_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2980_ = lean_unsigned_to_nat(1u);
v___x_2981_ = lean_nat_add(v_j_2973_, v___x_2980_);
lean_dec(v_j_2973_);
v_j_2973_ = v___x_2981_;
goto _start;
}
else
{
lean_object* v___x_2983_; 
lean_dec_ref(v_p_2971_);
v___x_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2983_, 0, v_j_2973_);
return v___x_2983_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg___boxed(lean_object* v_p_2984_, lean_object* v_as_2985_, lean_object* v_j_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Array_findIdx_x3f_loop___redArg(v_p_2984_, v_as_2985_, v_j_2986_);
lean_dec_ref(v_as_2985_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop(lean_object* v_00_u03b1_2988_, lean_object* v_p_2989_, lean_object* v_as_2990_, lean_object* v_j_2991_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = l_Array_findIdx_x3f_loop___redArg(v_p_2989_, v_as_2990_, v_j_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___boxed(lean_object* v_00_u03b1_2993_, lean_object* v_p_2994_, lean_object* v_as_2995_, lean_object* v_j_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Array_findIdx_x3f_loop(v_00_u03b1_2993_, v_p_2994_, v_as_2995_, v_j_2996_);
lean_dec_ref(v_as_2995_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg(lean_object* v_p_2998_, lean_object* v_as_2999_){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = lean_unsigned_to_nat(0u);
v___x_3001_ = l_Array_findIdx_x3f_loop___redArg(v_p_2998_, v_as_2999_, v___x_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg___boxed(lean_object* v_p_3002_, lean_object* v_as_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Array_findIdx_x3f___redArg(v_p_3002_, v_as_3003_);
lean_dec_ref(v_as_3003_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f(lean_object* v_00_u03b1_3005_, lean_object* v_p_3006_, lean_object* v_as_3007_){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = lean_unsigned_to_nat(0u);
v___x_3009_ = l_Array_findIdx_x3f_loop___redArg(v_p_3006_, v_as_3007_, v___x_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___boxed(lean_object* v_00_u03b1_3010_, lean_object* v_p_3011_, lean_object* v_as_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Array_findIdx_x3f(v_00_u03b1_3010_, v_p_3011_, v_as_3012_);
lean_dec_ref(v_as_3012_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(lean_object* v_p_3014_, lean_object* v_as_3015_, lean_object* v_j_3016_){
_start:
{
lean_object* v___x_3017_; uint8_t v___x_3018_; 
v___x_3017_ = lean_array_get_size(v_as_3015_);
v___x_3018_ = lean_nat_dec_lt(v_j_3016_, v___x_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; 
lean_dec(v_j_3016_);
lean_dec_ref(v_p_3014_);
v___x_3019_ = lean_box(0);
return v___x_3019_;
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; 
v___x_3020_ = lean_array_fget_borrowed(v_as_3015_, v_j_3016_);
lean_inc_ref(v_p_3014_);
lean_inc(v___x_3020_);
v___x_3021_ = lean_apply_1(v_p_3014_, v___x_3020_);
v___x_3022_ = lean_unbox(v___x_3021_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = lean_unsigned_to_nat(1u);
v___x_3024_ = lean_nat_add(v_j_3016_, v___x_3023_);
lean_dec(v_j_3016_);
v_j_3016_ = v___x_3024_;
goto _start;
}
else
{
lean_object* v___x_3026_; 
lean_dec_ref(v_p_3014_);
v___x_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3026_, 0, v_j_3016_);
return v___x_3026_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg___boxed(lean_object* v_p_3027_, lean_object* v_as_3028_, lean_object* v_j_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3027_, v_as_3028_, v_j_3029_);
lean_dec_ref(v_as_3028_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object* v_00_u03b1_3031_, lean_object* v_p_3032_, lean_object* v_as_3033_, lean_object* v_j_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3032_, v_as_3033_, v_j_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___boxed(lean_object* v_00_u03b1_3036_, lean_object* v_p_3037_, lean_object* v_as_3038_, lean_object* v_j_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(v_00_u03b1_3036_, v_p_3037_, v_as_3038_, v_j_3039_);
lean_dec_ref(v_as_3038_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg(lean_object* v_p_3041_, lean_object* v_as_3042_){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = lean_unsigned_to_nat(0u);
v___x_3044_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3041_, v_as_3042_, v___x_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg___boxed(lean_object* v_p_3045_, lean_object* v_as_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Array_findFinIdx_x3f___redArg(v_p_3045_, v_as_3046_);
lean_dec_ref(v_as_3046_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f(lean_object* v_00_u03b1_3048_, lean_object* v_p_3049_, lean_object* v_as_3050_){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = lean_unsigned_to_nat(0u);
v___x_3052_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3049_, v_as_3050_, v___x_3051_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_3053_, lean_object* v_p_3054_, lean_object* v_as_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Array_findFinIdx_x3f(v_00_u03b1_3053_, v_p_3054_, v_as_3055_);
lean_dec_ref(v_as_3055_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg(lean_object* v_p_3057_, lean_object* v_as_3058_){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = lean_unsigned_to_nat(0u);
v___x_3060_ = l_Array_findIdx_x3f_loop___redArg(v_p_3057_, v_as_3058_, v___x_3059_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v___x_3061_; 
v___x_3061_ = lean_array_get_size(v_as_3058_);
return v___x_3061_;
}
else
{
lean_object* v_val_3062_; 
v_val_3062_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_val_3062_);
lean_dec_ref_known(v___x_3060_, 1);
return v_val_3062_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg___boxed(lean_object* v_p_3063_, lean_object* v_as_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Array_findIdx___redArg(v_p_3063_, v_as_3064_);
lean_dec_ref(v_as_3064_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx(lean_object* v_00_u03b1_3066_, lean_object* v_p_3067_, lean_object* v_as_3068_){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_unsigned_to_nat(0u);
v___x_3070_ = l_Array_findIdx_x3f_loop___redArg(v_p_3067_, v_as_3068_, v___x_3069_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v___x_3071_; 
v___x_3071_ = lean_array_get_size(v_as_3068_);
return v___x_3071_;
}
else
{
lean_object* v_val_3072_; 
v_val_3072_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_val_3072_);
lean_dec_ref_known(v___x_3070_, 1);
return v_val_3072_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___boxed(lean_object* v_00_u03b1_3073_, lean_object* v_p_3074_, lean_object* v_as_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Array_findIdx(v_00_u03b1_3073_, v_p_3074_, v_as_3075_);
lean_dec_ref(v_as_3075_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg(lean_object* v_inst_3077_, lean_object* v_xs_3078_, lean_object* v_v_3079_, lean_object* v_i_3080_){
_start:
{
lean_object* v___x_3081_; uint8_t v___x_3082_; 
v___x_3081_ = lean_array_get_size(v_xs_3078_);
v___x_3082_ = lean_nat_dec_lt(v_i_3080_, v___x_3081_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; 
lean_dec(v_i_3080_);
lean_dec(v_v_3079_);
lean_dec_ref(v_inst_3077_);
v___x_3083_ = lean_box(0);
return v___x_3083_;
}
else
{
lean_object* v___x_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3084_ = lean_array_fget_borrowed(v_xs_3078_, v_i_3080_);
lean_inc_ref(v_inst_3077_);
lean_inc(v_v_3079_);
lean_inc(v___x_3084_);
v___x_3085_ = lean_apply_2(v_inst_3077_, v___x_3084_, v_v_3079_);
v___x_3086_ = lean_unbox(v___x_3085_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = lean_unsigned_to_nat(1u);
v___x_3088_ = lean_nat_add(v_i_3080_, v___x_3087_);
lean_dec(v_i_3080_);
v_i_3080_ = v___x_3088_;
goto _start;
}
else
{
lean_object* v___x_3090_; 
lean_dec(v_v_3079_);
lean_dec_ref(v_inst_3077_);
v___x_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3090_, 0, v_i_3080_);
return v___x_3090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg___boxed(lean_object* v_inst_3091_, lean_object* v_xs_3092_, lean_object* v_v_3093_, lean_object* v_i_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Array_idxOfAux___redArg(v_inst_3091_, v_xs_3092_, v_v_3093_, v_i_3094_);
lean_dec_ref(v_xs_3092_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux(lean_object* v_00_u03b1_3096_, lean_object* v_inst_3097_, lean_object* v_xs_3098_, lean_object* v_v_3099_, lean_object* v_i_3100_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Array_idxOfAux___redArg(v_inst_3097_, v_xs_3098_, v_v_3099_, v_i_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___boxed(lean_object* v_00_u03b1_3102_, lean_object* v_inst_3103_, lean_object* v_xs_3104_, lean_object* v_v_3105_, lean_object* v_i_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Array_idxOfAux(v_00_u03b1_3102_, v_inst_3103_, v_xs_3104_, v_v_3105_, v_i_3106_);
lean_dec_ref(v_xs_3104_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg(lean_object* v_inst_3108_, lean_object* v_xs_3109_, lean_object* v_v_3110_){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = lean_unsigned_to_nat(0u);
v___x_3112_ = l_Array_idxOfAux___redArg(v_inst_3108_, v_xs_3109_, v_v_3110_, v___x_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_3113_, lean_object* v_xs_3114_, lean_object* v_v_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Array_finIdxOf_x3f___redArg(v_inst_3113_, v_xs_3114_, v_v_3115_);
lean_dec_ref(v_xs_3114_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f(lean_object* v_00_u03b1_3117_, lean_object* v_inst_3118_, lean_object* v_xs_3119_, lean_object* v_v_3120_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Array_finIdxOf_x3f___redArg(v_inst_3118_, v_xs_3119_, v_v_3120_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_3122_, lean_object* v_inst_3123_, lean_object* v_xs_3124_, lean_object* v_v_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Array_finIdxOf_x3f(v_00_u03b1_3122_, v_inst_3123_, v_xs_3124_, v_v_3125_);
lean_dec_ref(v_xs_3124_);
return v_res_3126_;
}
}
LEAN_EXPORT uint8_t l_Array_idxOf___redArg___lam__0(lean_object* v_inst_3127_, lean_object* v_a_3128_, lean_object* v_x_3129_){
_start:
{
lean_object* v___x_3130_; uint8_t v___x_3131_; 
v___x_3130_ = lean_apply_2(v_inst_3127_, v_x_3129_, v_a_3128_);
v___x_3131_ = lean_unbox(v___x_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___lam__0___boxed(lean_object* v_inst_3132_, lean_object* v_a_3133_, lean_object* v_x_3134_){
_start:
{
uint8_t v_res_3135_; lean_object* v_r_3136_; 
v_res_3135_ = l_Array_idxOf___redArg___lam__0(v_inst_3132_, v_a_3133_, v_x_3134_);
v_r_3136_ = lean_box(v_res_3135_);
return v_r_3136_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg(lean_object* v_inst_3137_, lean_object* v_a_3138_, lean_object* v_as_3139_){
_start:
{
lean_object* v___f_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___f_3140_ = lean_alloc_closure((void*)(l_Array_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3140_, 0, v_inst_3137_);
lean_closure_set(v___f_3140_, 1, v_a_3138_);
v___x_3141_ = lean_unsigned_to_nat(0u);
v___x_3142_ = l_Array_findIdx_x3f_loop___redArg(v___f_3140_, v_as_3139_, v___x_3141_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v___x_3143_; 
v___x_3143_ = lean_array_get_size(v_as_3139_);
return v___x_3143_;
}
else
{
lean_object* v_val_3144_; 
v_val_3144_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_val_3144_);
lean_dec_ref_known(v___x_3142_, 1);
return v_val_3144_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___boxed(lean_object* v_inst_3145_, lean_object* v_a_3146_, lean_object* v_as_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Array_idxOf___redArg(v_inst_3145_, v_a_3146_, v_as_3147_);
lean_dec_ref(v_as_3147_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf(lean_object* v_00_u03b1_3149_, lean_object* v_inst_3150_, lean_object* v_a_3151_, lean_object* v_as_3152_){
_start:
{
lean_object* v___x_3153_; 
v___x_3153_ = l_Array_idxOf___redArg(v_inst_3150_, v_a_3151_, v_as_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___boxed(lean_object* v_00_u03b1_3154_, lean_object* v_inst_3155_, lean_object* v_a_3156_, lean_object* v_as_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l_Array_idxOf(v_00_u03b1_3154_, v_inst_3155_, v_a_3156_, v_as_3157_);
lean_dec_ref(v_as_3157_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg(lean_object* v_inst_3159_, lean_object* v_xs_3160_, lean_object* v_v_3161_){
_start:
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Array_finIdxOf_x3f___redArg(v_inst_3159_, v_xs_3160_, v_v_3161_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v___x_3163_; 
v___x_3163_ = lean_box(0);
return v___x_3163_;
}
else
{
lean_object* v_val_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
v_val_3164_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3162_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_val_3164_);
lean_dec(v___x_3162_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_val_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg___boxed(lean_object* v_inst_3172_, lean_object* v_xs_3173_, lean_object* v_v_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_Array_idxOf_x3f___redArg(v_inst_3172_, v_xs_3173_, v_v_3174_);
lean_dec_ref(v_xs_3173_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f(lean_object* v_00_u03b1_3176_, lean_object* v_inst_3177_, lean_object* v_xs_3178_, lean_object* v_v_3179_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Array_idxOf_x3f___redArg(v_inst_3177_, v_xs_3178_, v_v_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___boxed(lean_object* v_00_u03b1_3181_, lean_object* v_inst_3182_, lean_object* v_xs_3183_, lean_object* v_v_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Array_idxOf_x3f(v_00_u03b1_3181_, v_inst_3182_, v_xs_3183_, v_v_3184_);
lean_dec_ref(v_xs_3183_);
return v_res_3185_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg___lam__0(lean_object* v_p_3186_, lean_object* v_x_3187_){
_start:
{
lean_object* v___x_3188_; uint8_t v___x_3189_; 
v___x_3188_ = lean_apply_1(v_p_3186_, v_x_3187_);
v___x_3189_ = lean_unbox(v___x_3188_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___lam__0___boxed(lean_object* v_p_3190_, lean_object* v_x_3191_){
_start:
{
uint8_t v_res_3192_; lean_object* v_r_3193_; 
v_res_3192_ = l_Array_any___redArg___lam__0(v_p_3190_, v_x_3191_);
v_r_3193_ = lean_box(v_res_3192_);
return v_r_3193_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg(lean_object* v_as_3194_, lean_object* v_p_3195_, lean_object* v_start_3196_, lean_object* v_stop_3197_){
_start:
{
lean_object* v___x_3198_; uint8_t v___x_3199_; 
v___x_3198_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3199_ = lean_nat_dec_lt(v_start_3196_, v_stop_3197_);
if (v___x_3199_ == 0)
{
lean_dec(v_stop_3197_);
lean_dec_ref(v_p_3195_);
lean_dec_ref(v_as_3194_);
return v___x_3199_;
}
else
{
lean_object* v___f_3200_; lean_object* v___y_3202_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v___f_3200_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3200_, 0, v_p_3195_);
v___x_3208_ = lean_array_get_size(v_as_3194_);
v___x_3209_ = lean_nat_dec_le(v_stop_3197_, v___x_3208_);
if (v___x_3209_ == 0)
{
lean_dec(v_stop_3197_);
v___y_3202_ = v___x_3208_;
goto v___jp_3201_;
}
else
{
v___y_3202_ = v_stop_3197_;
goto v___jp_3201_;
}
v___jp_3201_:
{
uint8_t v___x_3203_; 
v___x_3203_ = lean_nat_dec_lt(v_start_3196_, v___y_3202_);
if (v___x_3203_ == 0)
{
lean_dec(v___y_3202_);
lean_dec_ref(v___f_3200_);
lean_dec_ref(v_as_3194_);
return v___x_3203_;
}
else
{
size_t v___x_3204_; size_t v___x_3205_; lean_object* v___x_3206_; uint8_t v___x_3207_; 
v___x_3204_ = lean_usize_of_nat(v_start_3196_);
v___x_3205_ = lean_usize_of_nat(v___y_3202_);
lean_dec(v___y_3202_);
v___x_3206_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3198_, v___f_3200_, v_as_3194_, v___x_3204_, v___x_3205_);
v___x_3207_ = lean_unbox(v___x_3206_);
lean_dec(v___x_3206_);
return v___x_3207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___boxed(lean_object* v_as_3210_, lean_object* v_p_3211_, lean_object* v_start_3212_, lean_object* v_stop_3213_){
_start:
{
uint8_t v_res_3214_; lean_object* v_r_3215_; 
v_res_3214_ = l_Array_any___redArg(v_as_3210_, v_p_3211_, v_start_3212_, v_stop_3213_);
lean_dec(v_start_3212_);
v_r_3215_ = lean_box(v_res_3214_);
return v_r_3215_;
}
}
LEAN_EXPORT uint8_t l_Array_any(lean_object* v_00_u03b1_3216_, lean_object* v_as_3217_, lean_object* v_p_3218_, lean_object* v_start_3219_, lean_object* v_stop_3220_){
_start:
{
lean_object* v___x_3221_; uint8_t v___x_3222_; 
v___x_3221_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3222_ = lean_nat_dec_lt(v_start_3219_, v_stop_3220_);
if (v___x_3222_ == 0)
{
lean_dec(v_stop_3220_);
lean_dec_ref(v_p_3218_);
lean_dec_ref(v_as_3217_);
return v___x_3222_;
}
else
{
lean_object* v___f_3223_; lean_object* v___y_3225_; lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___f_3223_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3223_, 0, v_p_3218_);
v___x_3231_ = lean_array_get_size(v_as_3217_);
v___x_3232_ = lean_nat_dec_le(v_stop_3220_, v___x_3231_);
if (v___x_3232_ == 0)
{
lean_dec(v_stop_3220_);
v___y_3225_ = v___x_3231_;
goto v___jp_3224_;
}
else
{
v___y_3225_ = v_stop_3220_;
goto v___jp_3224_;
}
v___jp_3224_:
{
uint8_t v___x_3226_; 
v___x_3226_ = lean_nat_dec_lt(v_start_3219_, v___y_3225_);
if (v___x_3226_ == 0)
{
lean_dec(v___y_3225_);
lean_dec_ref(v___f_3223_);
lean_dec_ref(v_as_3217_);
return v___x_3226_;
}
else
{
size_t v___x_3227_; size_t v___x_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3227_ = lean_usize_of_nat(v_start_3219_);
v___x_3228_ = lean_usize_of_nat(v___y_3225_);
lean_dec(v___y_3225_);
v___x_3229_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3221_, v___f_3223_, v_as_3217_, v___x_3227_, v___x_3228_);
v___x_3230_ = lean_unbox(v___x_3229_);
lean_dec(v___x_3229_);
return v___x_3230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___boxed(lean_object* v_00_u03b1_3233_, lean_object* v_as_3234_, lean_object* v_p_3235_, lean_object* v_start_3236_, lean_object* v_stop_3237_){
_start:
{
uint8_t v_res_3238_; lean_object* v_r_3239_; 
v_res_3238_ = l_Array_any(v_00_u03b1_3233_, v_as_3234_, v_p_3235_, v_start_3236_, v_stop_3237_);
lean_dec(v_start_3236_);
v_r_3239_ = lean_box(v_res_3238_);
return v_r_3239_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg___lam__0(lean_object* v_p_3240_, uint8_t v___x_3241_, lean_object* v_v_3242_){
_start:
{
lean_object* v___x_3243_; uint8_t v___x_3244_; 
v___x_3243_ = lean_apply_1(v_p_3240_, v_v_3242_);
v___x_3244_ = lean_unbox(v___x_3243_);
if (v___x_3244_ == 0)
{
return v___x_3241_;
}
else
{
uint8_t v___x_3245_; 
v___x_3245_ = 0;
return v___x_3245_;
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___lam__0___boxed(lean_object* v_p_3246_, lean_object* v___x_3247_, lean_object* v_v_3248_){
_start:
{
uint8_t v___x_335__boxed_3249_; uint8_t v_res_3250_; lean_object* v_r_3251_; 
v___x_335__boxed_3249_ = lean_unbox(v___x_3247_);
v_res_3250_ = l_Array_all___redArg___lam__0(v_p_3246_, v___x_335__boxed_3249_, v_v_3248_);
v_r_3251_ = lean_box(v_res_3250_);
return v_r_3251_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg(lean_object* v_as_3252_, lean_object* v_p_3253_, lean_object* v_start_3254_, lean_object* v_stop_3255_){
_start:
{
lean_object* v___x_3256_; uint8_t v___x_3257_; 
v___x_3256_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3257_ = lean_nat_dec_lt(v_start_3254_, v_stop_3255_);
if (v___x_3257_ == 0)
{
uint8_t v___x_3258_; 
lean_dec(v_stop_3255_);
lean_dec_ref(v_p_3253_);
lean_dec_ref(v_as_3252_);
v___x_3258_ = 1;
return v___x_3258_;
}
else
{
lean_object* v___x_3259_; lean_object* v___f_3260_; lean_object* v___y_3262_; lean_object* v___x_3269_; uint8_t v___x_3270_; 
v___x_3259_ = lean_box(v___x_3257_);
v___f_3260_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3260_, 0, v_p_3253_);
lean_closure_set(v___f_3260_, 1, v___x_3259_);
v___x_3269_ = lean_array_get_size(v_as_3252_);
v___x_3270_ = lean_nat_dec_le(v_stop_3255_, v___x_3269_);
if (v___x_3270_ == 0)
{
lean_dec(v_stop_3255_);
v___y_3262_ = v___x_3269_;
goto v___jp_3261_;
}
else
{
v___y_3262_ = v_stop_3255_;
goto v___jp_3261_;
}
v___jp_3261_:
{
uint8_t v___x_3263_; 
v___x_3263_ = lean_nat_dec_lt(v_start_3254_, v___y_3262_);
if (v___x_3263_ == 0)
{
lean_dec(v___y_3262_);
lean_dec_ref(v___f_3260_);
lean_dec_ref(v_as_3252_);
return v___x_3257_;
}
else
{
size_t v___x_3264_; size_t v___x_3265_; lean_object* v___x_3266_; uint8_t v___x_3267_; 
v___x_3264_ = lean_usize_of_nat(v_start_3254_);
v___x_3265_ = lean_usize_of_nat(v___y_3262_);
lean_dec(v___y_3262_);
v___x_3266_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3256_, v___f_3260_, v_as_3252_, v___x_3264_, v___x_3265_);
v___x_3267_ = lean_unbox(v___x_3266_);
lean_dec(v___x_3266_);
if (v___x_3267_ == 0)
{
return v___x_3263_;
}
else
{
uint8_t v___x_3268_; 
v___x_3268_ = 0;
return v___x_3268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___boxed(lean_object* v_as_3271_, lean_object* v_p_3272_, lean_object* v_start_3273_, lean_object* v_stop_3274_){
_start:
{
uint8_t v_res_3275_; lean_object* v_r_3276_; 
v_res_3275_ = l_Array_all___redArg(v_as_3271_, v_p_3272_, v_start_3273_, v_stop_3274_);
lean_dec(v_start_3273_);
v_r_3276_ = lean_box(v_res_3275_);
return v_r_3276_;
}
}
LEAN_EXPORT uint8_t l_Array_all(lean_object* v_00_u03b1_3277_, lean_object* v_as_3278_, lean_object* v_p_3279_, lean_object* v_start_3280_, lean_object* v_stop_3281_){
_start:
{
lean_object* v___x_3282_; uint8_t v___x_3283_; 
v___x_3282_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3283_ = lean_nat_dec_lt(v_start_3280_, v_stop_3281_);
if (v___x_3283_ == 0)
{
uint8_t v___x_3284_; 
lean_dec(v_stop_3281_);
lean_dec_ref(v_p_3279_);
lean_dec_ref(v_as_3278_);
v___x_3284_ = 1;
return v___x_3284_;
}
else
{
lean_object* v___x_3285_; lean_object* v___f_3286_; lean_object* v___y_3288_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
v___x_3285_ = lean_box(v___x_3283_);
v___f_3286_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3286_, 0, v_p_3279_);
lean_closure_set(v___f_3286_, 1, v___x_3285_);
v___x_3295_ = lean_array_get_size(v_as_3278_);
v___x_3296_ = lean_nat_dec_le(v_stop_3281_, v___x_3295_);
if (v___x_3296_ == 0)
{
lean_dec(v_stop_3281_);
v___y_3288_ = v___x_3295_;
goto v___jp_3287_;
}
else
{
v___y_3288_ = v_stop_3281_;
goto v___jp_3287_;
}
v___jp_3287_:
{
uint8_t v___x_3289_; 
v___x_3289_ = lean_nat_dec_lt(v_start_3280_, v___y_3288_);
if (v___x_3289_ == 0)
{
lean_dec(v___y_3288_);
lean_dec_ref(v___f_3286_);
lean_dec_ref(v_as_3278_);
return v___x_3283_;
}
else
{
size_t v___x_3290_; size_t v___x_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; 
v___x_3290_ = lean_usize_of_nat(v_start_3280_);
v___x_3291_ = lean_usize_of_nat(v___y_3288_);
lean_dec(v___y_3288_);
v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3282_, v___f_3286_, v_as_3278_, v___x_3290_, v___x_3291_);
v___x_3293_ = lean_unbox(v___x_3292_);
lean_dec(v___x_3292_);
if (v___x_3293_ == 0)
{
return v___x_3289_;
}
else
{
uint8_t v___x_3294_; 
v___x_3294_ = 0;
return v___x_3294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___boxed(lean_object* v_00_u03b1_3297_, lean_object* v_as_3298_, lean_object* v_p_3299_, lean_object* v_start_3300_, lean_object* v_stop_3301_){
_start:
{
uint8_t v_res_3302_; lean_object* v_r_3303_; 
v_res_3302_ = l_Array_all(v_00_u03b1_3297_, v_as_3298_, v_p_3299_, v_start_3300_, v_stop_3301_);
lean_dec(v_start_3300_);
v_r_3303_ = lean_box(v_res_3302_);
return v_r_3303_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg___lam__0(lean_object* v_inst_3304_, lean_object* v_a_3305_, lean_object* v_x_3306_){
_start:
{
lean_object* v___x_3307_; uint8_t v___x_3308_; 
v___x_3307_ = lean_apply_2(v_inst_3304_, v_a_3305_, v_x_3306_);
v___x_3308_ = lean_unbox(v___x_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___lam__0___boxed(lean_object* v_inst_3309_, lean_object* v_a_3310_, lean_object* v_x_3311_){
_start:
{
uint8_t v_res_3312_; lean_object* v_r_3313_; 
v_res_3312_ = l_Array_contains___redArg___lam__0(v_inst_3309_, v_a_3310_, v_x_3311_);
v_r_3313_ = lean_box(v_res_3312_);
return v_r_3313_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg(lean_object* v_inst_3314_, lean_object* v_as_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___x_3317_ = lean_unsigned_to_nat(0u);
v___x_3318_ = lean_array_get_size(v_as_3315_);
v___x_3319_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3320_ = lean_nat_dec_lt(v___x_3317_, v___x_3318_);
if (v___x_3320_ == 0)
{
lean_dec(v_a_3316_);
lean_dec_ref(v_as_3315_);
lean_dec_ref(v_inst_3314_);
return v___x_3320_;
}
else
{
if (v___x_3320_ == 0)
{
lean_dec(v_a_3316_);
lean_dec_ref(v_as_3315_);
lean_dec_ref(v_inst_3314_);
return v___x_3320_;
}
else
{
lean_object* v___f_3321_; size_t v___x_3322_; size_t v___x_3323_; lean_object* v___x_3324_; uint8_t v___x_3325_; 
v___f_3321_ = lean_alloc_closure((void*)(l_Array_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3321_, 0, v_inst_3314_);
lean_closure_set(v___f_3321_, 1, v_a_3316_);
v___x_3322_ = ((size_t)0ULL);
v___x_3323_ = lean_usize_of_nat(v___x_3318_);
v___x_3324_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3319_, v___f_3321_, v_as_3315_, v___x_3322_, v___x_3323_);
v___x_3325_ = lean_unbox(v___x_3324_);
lean_dec(v___x_3324_);
return v___x_3325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___boxed(lean_object* v_inst_3326_, lean_object* v_as_3327_, lean_object* v_a_3328_){
_start:
{
uint8_t v_res_3329_; lean_object* v_r_3330_; 
v_res_3329_ = l_Array_contains___redArg(v_inst_3326_, v_as_3327_, v_a_3328_);
v_r_3330_ = lean_box(v_res_3329_);
return v_r_3330_;
}
}
LEAN_EXPORT uint8_t l_Array_contains(lean_object* v_00_u03b1_3331_, lean_object* v_inst_3332_, lean_object* v_as_3333_, lean_object* v_a_3334_){
_start:
{
uint8_t v___x_3335_; 
v___x_3335_ = l_Array_contains___redArg(v_inst_3332_, v_as_3333_, v_a_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___boxed(lean_object* v_00_u03b1_3336_, lean_object* v_inst_3337_, lean_object* v_as_3338_, lean_object* v_a_3339_){
_start:
{
uint8_t v_res_3340_; lean_object* v_r_3341_; 
v_res_3340_ = l_Array_contains(v_00_u03b1_3336_, v_inst_3337_, v_as_3338_, v_a_3339_);
v_r_3341_ = lean_box(v_res_3340_);
return v_r_3341_;
}
}
LEAN_EXPORT uint8_t l_Array_elem___redArg(lean_object* v_inst_3342_, lean_object* v_a_3343_, lean_object* v_as_3344_){
_start:
{
uint8_t v___x_3345_; 
v___x_3345_ = l_Array_contains___redArg(v_inst_3342_, v_as_3344_, v_a_3343_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___redArg___boxed(lean_object* v_inst_3346_, lean_object* v_a_3347_, lean_object* v_as_3348_){
_start:
{
uint8_t v_res_3349_; lean_object* v_r_3350_; 
v_res_3349_ = l_Array_elem___redArg(v_inst_3346_, v_a_3347_, v_as_3348_);
v_r_3350_ = lean_box(v_res_3349_);
return v_r_3350_;
}
}
LEAN_EXPORT uint8_t l_Array_elem(lean_object* v_00_u03b1_3351_, lean_object* v_inst_3352_, lean_object* v_a_3353_, lean_object* v_as_3354_){
_start:
{
uint8_t v___x_3355_; 
v___x_3355_ = l_Array_contains___redArg(v_inst_3352_, v_as_3354_, v_a_3353_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___boxed(lean_object* v_00_u03b1_3356_, lean_object* v_inst_3357_, lean_object* v_a_3358_, lean_object* v_as_3359_){
_start:
{
uint8_t v_res_3360_; lean_object* v_r_3361_; 
v_res_3360_ = l_Array_elem(v_00_u03b1_3356_, v_inst_3357_, v_a_3358_, v_as_3359_);
v_r_3361_ = lean_box(v_res_3360_);
return v_r_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(lean_object* v_as_3362_, size_t v_i_3363_, size_t v_stop_3364_, lean_object* v_b_3365_){
_start:
{
uint8_t v___x_3366_; 
v___x_3366_ = lean_usize_dec_eq(v_i_3363_, v_stop_3364_);
if (v___x_3366_ == 0)
{
size_t v___x_3367_; size_t v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3367_ = ((size_t)1ULL);
v___x_3368_ = lean_usize_sub(v_i_3363_, v___x_3367_);
v___x_3369_ = lean_array_uget_borrowed(v_as_3362_, v___x_3368_);
lean_inc(v___x_3369_);
v___x_3370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
lean_ctor_set(v___x_3370_, 1, v_b_3365_);
v_i_3363_ = v___x_3368_;
v_b_3365_ = v___x_3370_;
goto _start;
}
else
{
return v_b_3365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg___boxed(lean_object* v_as_3372_, lean_object* v_i_3373_, lean_object* v_stop_3374_, lean_object* v_b_3375_){
_start:
{
size_t v_i_boxed_3376_; size_t v_stop_boxed_3377_; lean_object* v_res_3378_; 
v_i_boxed_3376_ = lean_unbox_usize(v_i_3373_);
lean_dec(v_i_3373_);
v_stop_boxed_3377_ = lean_unbox_usize(v_stop_3374_);
lean_dec(v_stop_3374_);
v_res_3378_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3372_, v_i_boxed_3376_, v_stop_boxed_3377_, v_b_3375_);
lean_dec_ref(v_as_3372_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg(lean_object* v_as_3379_){
_start:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v___x_3380_ = lean_box(0);
v___x_3381_ = lean_array_get_size(v_as_3379_);
v___x_3382_ = lean_unsigned_to_nat(0u);
v___x_3383_ = lean_nat_dec_lt(v___x_3382_, v___x_3381_);
if (v___x_3383_ == 0)
{
return v___x_3380_;
}
else
{
size_t v___x_3384_; size_t v___x_3385_; lean_object* v___x_3386_; 
v___x_3384_ = lean_usize_of_nat(v___x_3381_);
v___x_3385_ = ((size_t)0ULL);
v___x_3386_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3379_, v___x_3384_, v___x_3385_, v___x_3380_);
return v___x_3386_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg___boxed(lean_object* v_as_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Array_toListImpl___redArg(v_as_3387_);
lean_dec_ref(v_as_3387_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* lean_array_to_list_impl(lean_object* v_00_u03b1_3389_, lean_object* v_as_3390_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Array_toListImpl___redArg(v_as_3390_);
lean_dec_ref(v_as_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(lean_object* v_00_u03b1_3392_, lean_object* v_as_3393_, size_t v_i_3394_, size_t v_stop_3395_, lean_object* v_b_3396_){
_start:
{
lean_object* v___x_3397_; 
v___x_3397_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3393_, v_i_3394_, v_stop_3395_, v_b_3396_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___boxed(lean_object* v_00_u03b1_3398_, lean_object* v_as_3399_, lean_object* v_i_3400_, lean_object* v_stop_3401_, lean_object* v_b_3402_){
_start:
{
size_t v_i_boxed_3403_; size_t v_stop_boxed_3404_; lean_object* v_res_3405_; 
v_i_boxed_3403_ = lean_unbox_usize(v_i_3400_);
lean_dec(v_i_3400_);
v_stop_boxed_3404_ = lean_unbox_usize(v_stop_3401_);
lean_dec(v_stop_3401_);
v_res_3405_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(v_00_u03b1_3398_, v_as_3399_, v_i_boxed_3403_, v_stop_boxed_3404_, v_b_3402_);
lean_dec_ref(v_as_3399_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg___lam__0(lean_object* v_x1_3406_, lean_object* v_x2_3407_){
_start:
{
lean_object* v___x_3408_; 
v___x_3408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3408_, 0, v_x1_3406_);
lean_ctor_set(v___x_3408_, 1, v_x2_3407_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg(lean_object* v_as_3410_, lean_object* v_l_3411_){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; uint8_t v___x_3415_; 
v___x_3412_ = lean_array_get_size(v_as_3410_);
v___x_3413_ = lean_unsigned_to_nat(0u);
v___x_3414_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3415_ = lean_nat_dec_lt(v___x_3413_, v___x_3412_);
if (v___x_3415_ == 0)
{
lean_dec_ref(v_as_3410_);
return v_l_3411_;
}
else
{
lean_object* v___f_3416_; size_t v___x_3417_; size_t v___x_3418_; lean_object* v___x_3419_; 
v___f_3416_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3417_ = lean_usize_of_nat(v___x_3412_);
v___x_3418_ = ((size_t)0ULL);
v___x_3419_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3414_, v___f_3416_, v_as_3410_, v___x_3417_, v___x_3418_, v_l_3411_);
return v___x_3419_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend(lean_object* v_00_u03b1_3420_, lean_object* v_as_3421_, lean_object* v_l_3422_){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v___x_3423_ = lean_array_get_size(v_as_3421_);
v___x_3424_ = lean_unsigned_to_nat(0u);
v___x_3425_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3426_ = lean_nat_dec_lt(v___x_3424_, v___x_3423_);
if (v___x_3426_ == 0)
{
lean_dec_ref(v_as_3421_);
return v_l_3422_;
}
else
{
lean_object* v___f_3427_; size_t v___x_3428_; size_t v___x_3429_; lean_object* v___x_3430_; 
v___f_3427_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3428_ = lean_usize_of_nat(v___x_3423_);
v___x_3429_ = ((size_t)0ULL);
v___x_3430_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3425_, v___f_3427_, v_as_3421_, v___x_3428_, v___x_3429_, v_l_3422_);
return v___x_3430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(lean_object* v_as_3431_, size_t v_i_3432_, size_t v_stop_3433_, lean_object* v_b_3434_){
_start:
{
uint8_t v___x_3435_; 
v___x_3435_ = lean_usize_dec_eq(v_i_3432_, v_stop_3433_);
if (v___x_3435_ == 0)
{
lean_object* v___x_3436_; lean_object* v___x_3437_; size_t v___x_3438_; size_t v___x_3439_; 
v___x_3436_ = lean_array_uget_borrowed(v_as_3431_, v_i_3432_);
lean_inc(v___x_3436_);
v___x_3437_ = lean_array_push(v_b_3434_, v___x_3436_);
v___x_3438_ = ((size_t)1ULL);
v___x_3439_ = lean_usize_add(v_i_3432_, v___x_3438_);
v_i_3432_ = v___x_3439_;
v_b_3434_ = v___x_3437_;
goto _start;
}
else
{
return v_b_3434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg___boxed(lean_object* v_as_3441_, lean_object* v_i_3442_, lean_object* v_stop_3443_, lean_object* v_b_3444_){
_start:
{
size_t v_i_boxed_3445_; size_t v_stop_boxed_3446_; lean_object* v_res_3447_; 
v_i_boxed_3445_ = lean_unbox_usize(v_i_3442_);
lean_dec(v_i_3442_);
v_stop_boxed_3446_ = lean_unbox_usize(v_stop_3443_);
lean_dec(v_stop_3443_);
v_res_3447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3441_, v_i_boxed_3445_, v_stop_boxed_3446_, v_b_3444_);
lean_dec_ref(v_as_3441_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg(lean_object* v_as_3448_, lean_object* v_bs_3449_){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; uint8_t v___x_3452_; 
v___x_3450_ = lean_unsigned_to_nat(0u);
v___x_3451_ = lean_array_get_size(v_bs_3449_);
v___x_3452_ = lean_nat_dec_lt(v___x_3450_, v___x_3451_);
if (v___x_3452_ == 0)
{
return v_as_3448_;
}
else
{
uint8_t v___x_3453_; 
v___x_3453_ = lean_nat_dec_le(v___x_3451_, v___x_3451_);
if (v___x_3453_ == 0)
{
if (v___x_3452_ == 0)
{
return v_as_3448_;
}
else
{
size_t v___x_3454_; size_t v___x_3455_; lean_object* v___x_3456_; 
v___x_3454_ = ((size_t)0ULL);
v___x_3455_ = lean_usize_of_nat(v___x_3451_);
v___x_3456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3449_, v___x_3454_, v___x_3455_, v_as_3448_);
return v___x_3456_;
}
}
else
{
size_t v___x_3457_; size_t v___x_3458_; lean_object* v___x_3459_; 
v___x_3457_ = ((size_t)0ULL);
v___x_3458_ = lean_usize_of_nat(v___x_3451_);
v___x_3459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3449_, v___x_3457_, v___x_3458_, v_as_3448_);
return v___x_3459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg___boxed(lean_object* v_as_3460_, lean_object* v_bs_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Array_append___redArg(v_as_3460_, v_bs_3461_);
lean_dec_ref(v_bs_3461_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Array_append(lean_object* v_00_u03b1_3463_, lean_object* v_as_3464_, lean_object* v_bs_3465_){
_start:
{
lean_object* v___x_3466_; 
v___x_3466_ = l_Array_append___redArg(v_as_3464_, v_bs_3465_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l_Array_append___boxed(lean_object* v_00_u03b1_3467_, lean_object* v_as_3468_, lean_object* v_bs_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Array_append(v_00_u03b1_3467_, v_as_3468_, v_bs_3469_);
lean_dec_ref(v_bs_3469_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(lean_object* v_00_u03b1_3471_, lean_object* v_as_3472_, size_t v_i_3473_, size_t v_stop_3474_, lean_object* v_b_3475_){
_start:
{
lean_object* v___x_3476_; 
v___x_3476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3472_, v_i_3473_, v_stop_3474_, v_b_3475_);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___boxed(lean_object* v_00_u03b1_3477_, lean_object* v_as_3478_, lean_object* v_i_3479_, lean_object* v_stop_3480_, lean_object* v_b_3481_){
_start:
{
size_t v_i_boxed_3482_; size_t v_stop_boxed_3483_; lean_object* v_res_3484_; 
v_i_boxed_3482_ = lean_unbox_usize(v_i_3479_);
lean_dec(v_i_3479_);
v_stop_boxed_3483_ = lean_unbox_usize(v_stop_3480_);
lean_dec(v_stop_3480_);
v_res_3484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(v_00_u03b1_3477_, v_as_3478_, v_i_boxed_3482_, v_stop_boxed_3483_, v_b_3481_);
lean_dec_ref(v_as_3478_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend___redArg(){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = ((lean_object*)(l_Array_instAppend___redArg___closed__0));
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend___redArg___boxed(lean_object* v___dummy_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Array_instAppend___redArg();
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend(lean_object* v_00_u03b1_3490_){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = ((lean_object*)(l_Array_instAppend___redArg___closed__0));
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object* v_x_3492_, lean_object* v_x_3493_){
_start:
{
if (lean_obj_tag(v_x_3493_) == 0)
{
return v_x_3492_;
}
else
{
lean_object* v_head_3494_; lean_object* v_tail_3495_; lean_object* v___x_3496_; 
v_head_3494_ = lean_ctor_get(v_x_3493_, 0);
lean_inc(v_head_3494_);
v_tail_3495_ = lean_ctor_get(v_x_3493_, 1);
lean_inc(v_tail_3495_);
lean_dec_ref_known(v_x_3493_, 2);
v___x_3496_ = lean_array_push(v_x_3492_, v_head_3494_);
v_x_3492_ = v___x_3496_;
v_x_3493_ = v_tail_3495_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_appendList___redArg(lean_object* v_as_3498_, lean_object* v_bs_3499_){
_start:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3498_, v_bs_3499_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Array_appendList(lean_object* v_00_u03b1_3501_, lean_object* v_as_3502_, lean_object* v_bs_3503_){
_start:
{
lean_object* v___x_3504_; 
v___x_3504_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3502_, v_bs_3503_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0(lean_object* v_00_u03b1_3505_, lean_object* v_x_3506_, lean_object* v_x_3507_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_3506_, v_x_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList___redArg(){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = ((lean_object*)(l_Array_instHAppendList___redArg___closed__0));
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList___redArg___boxed(lean_object* v___dummy_3512_){
_start:
{
lean_object* v_res_3513_; 
v_res_3513_ = l_Array_instHAppendList___redArg();
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList(lean_object* v_00_u03b1_3514_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = ((lean_object*)(l_Array_instHAppendList___redArg___closed__0));
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0(lean_object* v_bs_3516_, lean_object* v_toPure_3517_, lean_object* v_____do__lift_3518_){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = l_Array_append___redArg(v_bs_3516_, v_____do__lift_3518_);
v___x_3520_ = lean_apply_2(v_toPure_3517_, lean_box(0), v___x_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0___boxed(lean_object* v_bs_3521_, lean_object* v_toPure_3522_, lean_object* v_____do__lift_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Array_flatMapM___redArg___lam__0(v_bs_3521_, v_toPure_3522_, v_____do__lift_3523_);
lean_dec_ref(v_____do__lift_3523_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__1(lean_object* v_toPure_3525_, lean_object* v_f_3526_, lean_object* v_toBind_3527_, lean_object* v_bs_3528_, lean_object* v_a_3529_){
_start:
{
lean_object* v___f_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___f_3530_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3530_, 0, v_bs_3528_);
lean_closure_set(v___f_3530_, 1, v_toPure_3525_);
v___x_3531_ = lean_apply_1(v_f_3526_, v_a_3529_);
v___x_3532_ = lean_apply_4(v_toBind_3527_, lean_box(0), lean_box(0), v___x_3531_, v___f_3530_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg(lean_object* v_inst_3533_, lean_object* v_f_3534_, lean_object* v_as_3535_){
_start:
{
lean_object* v_toApplicative_3536_; lean_object* v_toBind_3537_; lean_object* v_toPure_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v_toApplicative_3536_ = lean_ctor_get(v_inst_3533_, 0);
v_toBind_3537_ = lean_ctor_get(v_inst_3533_, 1);
v_toPure_3538_ = lean_ctor_get(v_toApplicative_3536_, 1);
v___x_3539_ = lean_unsigned_to_nat(0u);
v___x_3540_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3541_ = lean_array_get_size(v_as_3535_);
v___x_3542_ = lean_nat_dec_lt(v___x_3539_, v___x_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; 
lean_inc(v_toPure_3538_);
lean_dec_ref(v_as_3535_);
lean_dec(v_f_3534_);
lean_dec_ref(v_inst_3533_);
v___x_3543_ = lean_apply_2(v_toPure_3538_, lean_box(0), v___x_3540_);
return v___x_3543_;
}
else
{
lean_object* v___f_3544_; uint8_t v___x_3545_; 
lean_inc(v_toBind_3537_);
lean_inc(v_toPure_3538_);
v___f_3544_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3544_, 0, v_toPure_3538_);
lean_closure_set(v___f_3544_, 1, v_f_3534_);
lean_closure_set(v___f_3544_, 2, v_toBind_3537_);
v___x_3545_ = lean_nat_dec_le(v___x_3541_, v___x_3541_);
if (v___x_3545_ == 0)
{
if (v___x_3542_ == 0)
{
lean_object* v___x_3546_; 
lean_inc(v_toPure_3538_);
lean_dec_ref(v___f_3544_);
lean_dec_ref(v_as_3535_);
lean_dec_ref(v_inst_3533_);
v___x_3546_ = lean_apply_2(v_toPure_3538_, lean_box(0), v___x_3540_);
return v___x_3546_;
}
else
{
size_t v___x_3547_; size_t v___x_3548_; lean_object* v___x_3549_; 
v___x_3547_ = ((size_t)0ULL);
v___x_3548_ = lean_usize_of_nat(v___x_3541_);
v___x_3549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3533_, v___f_3544_, v_as_3535_, v___x_3547_, v___x_3548_, v___x_3540_);
return v___x_3549_;
}
}
else
{
size_t v___x_3550_; size_t v___x_3551_; lean_object* v___x_3552_; 
v___x_3550_ = ((size_t)0ULL);
v___x_3551_ = lean_usize_of_nat(v___x_3541_);
v___x_3552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3533_, v___f_3544_, v_as_3535_, v___x_3550_, v___x_3551_, v___x_3540_);
return v___x_3552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM(lean_object* v_00_u03b1_3553_, lean_object* v_m_3554_, lean_object* v_00_u03b2_3555_, lean_object* v_inst_3556_, lean_object* v_f_3557_, lean_object* v_as_3558_){
_start:
{
lean_object* v_toApplicative_3559_; lean_object* v_toBind_3560_; lean_object* v_toPure_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
v_toApplicative_3559_ = lean_ctor_get(v_inst_3556_, 0);
v_toBind_3560_ = lean_ctor_get(v_inst_3556_, 1);
v_toPure_3561_ = lean_ctor_get(v_toApplicative_3559_, 1);
v___x_3562_ = lean_unsigned_to_nat(0u);
v___x_3563_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3564_ = lean_array_get_size(v_as_3558_);
v___x_3565_ = lean_nat_dec_lt(v___x_3562_, v___x_3564_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; 
lean_inc(v_toPure_3561_);
lean_dec_ref(v_as_3558_);
lean_dec(v_f_3557_);
lean_dec_ref(v_inst_3556_);
v___x_3566_ = lean_apply_2(v_toPure_3561_, lean_box(0), v___x_3563_);
return v___x_3566_;
}
else
{
lean_object* v___f_3567_; uint8_t v___x_3568_; 
lean_inc(v_toBind_3560_);
lean_inc(v_toPure_3561_);
v___f_3567_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3567_, 0, v_toPure_3561_);
lean_closure_set(v___f_3567_, 1, v_f_3557_);
lean_closure_set(v___f_3567_, 2, v_toBind_3560_);
v___x_3568_ = lean_nat_dec_le(v___x_3564_, v___x_3564_);
if (v___x_3568_ == 0)
{
if (v___x_3565_ == 0)
{
lean_object* v___x_3569_; 
lean_inc(v_toPure_3561_);
lean_dec_ref(v___f_3567_);
lean_dec_ref(v_as_3558_);
lean_dec_ref(v_inst_3556_);
v___x_3569_ = lean_apply_2(v_toPure_3561_, lean_box(0), v___x_3563_);
return v___x_3569_;
}
else
{
size_t v___x_3570_; size_t v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = ((size_t)0ULL);
v___x_3571_ = lean_usize_of_nat(v___x_3564_);
v___x_3572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3556_, v___f_3567_, v_as_3558_, v___x_3570_, v___x_3571_, v___x_3563_);
return v___x_3572_;
}
}
else
{
size_t v___x_3573_; size_t v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = ((size_t)0ULL);
v___x_3574_ = lean_usize_of_nat(v___x_3564_);
v___x_3575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3556_, v___f_3567_, v_as_3558_, v___x_3573_, v___x_3574_, v___x_3563_);
return v___x_3575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg___lam__0(lean_object* v_f_3576_, lean_object* v_x1_3577_, lean_object* v_x2_3578_){
_start:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3579_ = lean_apply_1(v_f_3576_, v_x2_3578_);
v___x_3580_ = l_Array_append___redArg(v_x1_3577_, v___x_3579_);
lean_dec_ref(v___x_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg(lean_object* v_f_3581_, lean_object* v_as_3582_){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; uint8_t v___x_3587_; 
v___x_3583_ = lean_unsigned_to_nat(0u);
v___x_3584_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3585_ = lean_array_get_size(v_as_3582_);
v___x_3586_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3587_ = lean_nat_dec_lt(v___x_3583_, v___x_3585_);
if (v___x_3587_ == 0)
{
lean_dec_ref(v_as_3582_);
lean_dec_ref(v_f_3581_);
return v___x_3584_;
}
else
{
lean_object* v___f_3588_; uint8_t v___x_3589_; 
v___f_3588_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3588_, 0, v_f_3581_);
v___x_3589_ = lean_nat_dec_le(v___x_3585_, v___x_3585_);
if (v___x_3589_ == 0)
{
if (v___x_3587_ == 0)
{
lean_dec_ref(v___f_3588_);
lean_dec_ref(v_as_3582_);
return v___x_3584_;
}
else
{
size_t v___x_3590_; size_t v___x_3591_; lean_object* v___x_3592_; 
v___x_3590_ = ((size_t)0ULL);
v___x_3591_ = lean_usize_of_nat(v___x_3585_);
v___x_3592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3586_, v___f_3588_, v_as_3582_, v___x_3590_, v___x_3591_, v___x_3584_);
return v___x_3592_;
}
}
else
{
size_t v___x_3593_; size_t v___x_3594_; lean_object* v___x_3595_; 
v___x_3593_ = ((size_t)0ULL);
v___x_3594_ = lean_usize_of_nat(v___x_3585_);
v___x_3595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3586_, v___f_3588_, v_as_3582_, v___x_3593_, v___x_3594_, v___x_3584_);
return v___x_3595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap(lean_object* v_00_u03b1_3596_, lean_object* v_00_u03b2_3597_, lean_object* v_f_3598_, lean_object* v_as_3599_){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; uint8_t v___x_3604_; 
v___x_3600_ = lean_unsigned_to_nat(0u);
v___x_3601_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3602_ = lean_array_get_size(v_as_3599_);
v___x_3603_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3604_ = lean_nat_dec_lt(v___x_3600_, v___x_3602_);
if (v___x_3604_ == 0)
{
lean_dec_ref(v_as_3599_);
lean_dec_ref(v_f_3598_);
return v___x_3601_;
}
else
{
lean_object* v___f_3605_; uint8_t v___x_3606_; 
v___f_3605_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3605_, 0, v_f_3598_);
v___x_3606_ = lean_nat_dec_le(v___x_3602_, v___x_3602_);
if (v___x_3606_ == 0)
{
if (v___x_3604_ == 0)
{
lean_dec_ref(v___f_3605_);
lean_dec_ref(v_as_3599_);
return v___x_3601_;
}
else
{
size_t v___x_3607_; size_t v___x_3608_; lean_object* v___x_3609_; 
v___x_3607_ = ((size_t)0ULL);
v___x_3608_ = lean_usize_of_nat(v___x_3602_);
v___x_3609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3603_, v___f_3605_, v_as_3599_, v___x_3607_, v___x_3608_, v___x_3601_);
return v___x_3609_;
}
}
else
{
size_t v___x_3610_; size_t v___x_3611_; lean_object* v___x_3612_; 
v___x_3610_ = ((size_t)0ULL);
v___x_3611_ = lean_usize_of_nat(v___x_3602_);
v___x_3612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3603_, v___f_3605_, v_as_3599_, v___x_3610_, v___x_3611_, v___x_3601_);
return v___x_3612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten___redArg(lean_object* v_xss_3614_){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; uint8_t v___x_3619_; 
v___x_3615_ = lean_unsigned_to_nat(0u);
v___x_3616_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3617_ = lean_array_get_size(v_xss_3614_);
v___x_3618_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3619_ = lean_nat_dec_lt(v___x_3615_, v___x_3617_);
if (v___x_3619_ == 0)
{
lean_dec_ref(v_xss_3614_);
return v___x_3616_;
}
else
{
lean_object* v___f_3620_; uint8_t v___x_3621_; 
v___f_3620_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3621_ = lean_nat_dec_le(v___x_3617_, v___x_3617_);
if (v___x_3621_ == 0)
{
if (v___x_3619_ == 0)
{
lean_dec_ref(v_xss_3614_);
return v___x_3616_;
}
else
{
size_t v___x_3622_; size_t v___x_3623_; lean_object* v___x_3624_; 
v___x_3622_ = ((size_t)0ULL);
v___x_3623_ = lean_usize_of_nat(v___x_3617_);
v___x_3624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3618_, v___f_3620_, v_xss_3614_, v___x_3622_, v___x_3623_, v___x_3616_);
return v___x_3624_;
}
}
else
{
size_t v___x_3625_; size_t v___x_3626_; lean_object* v___x_3627_; 
v___x_3625_ = ((size_t)0ULL);
v___x_3626_ = lean_usize_of_nat(v___x_3617_);
v___x_3627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3618_, v___f_3620_, v_xss_3614_, v___x_3625_, v___x_3626_, v___x_3616_);
return v___x_3627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten(lean_object* v_00_u03b1_3628_, lean_object* v_xss_3629_){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; uint8_t v___x_3634_; 
v___x_3630_ = lean_unsigned_to_nat(0u);
v___x_3631_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3632_ = lean_array_get_size(v_xss_3629_);
v___x_3633_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3634_ = lean_nat_dec_lt(v___x_3630_, v___x_3632_);
if (v___x_3634_ == 0)
{
lean_dec_ref(v_xss_3629_);
return v___x_3631_;
}
else
{
lean_object* v___f_3635_; uint8_t v___x_3636_; 
v___f_3635_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3636_ = lean_nat_dec_le(v___x_3632_, v___x_3632_);
if (v___x_3636_ == 0)
{
if (v___x_3634_ == 0)
{
lean_dec_ref(v_xss_3629_);
return v___x_3631_;
}
else
{
size_t v___x_3637_; size_t v___x_3638_; lean_object* v___x_3639_; 
v___x_3637_ = ((size_t)0ULL);
v___x_3638_ = lean_usize_of_nat(v___x_3632_);
v___x_3639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3633_, v___f_3635_, v_xss_3629_, v___x_3637_, v___x_3638_, v___x_3631_);
return v___x_3639_;
}
}
else
{
size_t v___x_3640_; size_t v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = ((size_t)0ULL);
v___x_3641_ = lean_usize_of_nat(v___x_3632_);
v___x_3642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3633_, v___f_3635_, v_xss_3629_, v___x_3640_, v___x_3641_, v___x_3631_);
return v___x_3642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop___redArg(lean_object* v_as_3643_, lean_object* v_i_3644_, lean_object* v_j_3645_){
_start:
{
uint8_t v___x_3646_; 
v___x_3646_ = lean_nat_dec_lt(v_i_3644_, v_j_3645_);
if (v___x_3646_ == 0)
{
lean_dec(v_j_3645_);
lean_dec(v_i_3644_);
return v_as_3643_;
}
else
{
lean_object* v_as_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v_as_3647_ = lean_array_fswap(v_as_3643_, v_i_3644_, v_j_3645_);
v___x_3648_ = lean_unsigned_to_nat(1u);
v___x_3649_ = lean_nat_add(v_i_3644_, v___x_3648_);
lean_dec(v_i_3644_);
v___x_3650_ = lean_nat_sub(v_j_3645_, v___x_3648_);
lean_dec(v_j_3645_);
v_as_3643_ = v_as_3647_;
v_i_3644_ = v___x_3649_;
v_j_3645_ = v___x_3650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop(lean_object* v_00_u03b1_3652_, lean_object* v_as_3653_, lean_object* v_i_3654_, lean_object* v_j_3655_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = l_Array_reverse_loop___redArg(v_as_3653_, v_i_3654_, v_j_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Array_reverse___redArg(lean_object* v_as_3657_){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; uint8_t v___x_3660_; 
v___x_3658_ = lean_array_get_size(v_as_3657_);
v___x_3659_ = lean_unsigned_to_nat(1u);
v___x_3660_ = lean_nat_dec_le(v___x_3658_, v___x_3659_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3661_ = lean_unsigned_to_nat(0u);
v___x_3662_ = lean_nat_sub(v___x_3658_, v___x_3659_);
v___x_3663_ = l_Array_reverse_loop___redArg(v_as_3657_, v___x_3661_, v___x_3662_);
return v___x_3663_;
}
else
{
return v_as_3657_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse(lean_object* v_00_u03b1_3664_, lean_object* v_as_3665_){
_start:
{
lean_object* v___x_3666_; 
v___x_3666_ = l_Array_reverse___redArg(v_as_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___lam__0(lean_object* v_p_3667_, lean_object* v_x1_3668_, lean_object* v_x2_3669_){
_start:
{
lean_object* v___x_3670_; uint8_t v___x_3671_; 
lean_inc(v_x2_3669_);
v___x_3670_ = lean_apply_1(v_p_3667_, v_x2_3669_);
v___x_3671_ = lean_unbox(v___x_3670_);
if (v___x_3671_ == 0)
{
lean_dec(v_x2_3669_);
return v_x1_3668_;
}
else
{
lean_object* v___x_3672_; 
v___x_3672_ = lean_array_push(v_x1_3668_, v_x2_3669_);
return v___x_3672_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg(lean_object* v_p_3675_, lean_object* v_as_3676_, lean_object* v_start_3677_, lean_object* v_stop_3678_){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; 
v___x_3679_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3680_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3681_ = lean_nat_dec_lt(v_start_3677_, v_stop_3678_);
if (v___x_3681_ == 0)
{
lean_dec_ref(v_as_3676_);
lean_dec_ref(v_p_3675_);
return v___x_3679_;
}
else
{
lean_object* v___f_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
v___f_3682_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3682_, 0, v_p_3675_);
v___x_3683_ = lean_array_get_size(v_as_3676_);
v___x_3684_ = lean_nat_dec_le(v_stop_3678_, v___x_3683_);
if (v___x_3684_ == 0)
{
uint8_t v___x_3685_; 
v___x_3685_ = lean_nat_dec_lt(v_start_3677_, v___x_3683_);
if (v___x_3685_ == 0)
{
lean_dec_ref(v___f_3682_);
lean_dec_ref(v_as_3676_);
return v___x_3679_;
}
else
{
size_t v___x_3686_; size_t v___x_3687_; lean_object* v___x_3688_; 
v___x_3686_ = lean_usize_of_nat(v_start_3677_);
v___x_3687_ = lean_usize_of_nat(v___x_3683_);
v___x_3688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3680_, v___f_3682_, v_as_3676_, v___x_3686_, v___x_3687_, v___x_3679_);
return v___x_3688_;
}
}
else
{
size_t v___x_3689_; size_t v___x_3690_; lean_object* v___x_3691_; 
v___x_3689_ = lean_usize_of_nat(v_start_3677_);
v___x_3690_ = lean_usize_of_nat(v_stop_3678_);
v___x_3691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3680_, v___f_3682_, v_as_3676_, v___x_3689_, v___x_3690_, v___x_3679_);
return v___x_3691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___boxed(lean_object* v_p_3692_, lean_object* v_as_3693_, lean_object* v_start_3694_, lean_object* v_stop_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l_Array_filter___redArg(v_p_3692_, v_as_3693_, v_start_3694_, v_stop_3695_);
lean_dec(v_stop_3695_);
lean_dec(v_start_3694_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l_Array_filter(lean_object* v_00_u03b1_3697_, lean_object* v_p_3698_, lean_object* v_as_3699_, lean_object* v_start_3700_, lean_object* v_stop_3701_){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; 
v___x_3702_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3703_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3704_ = lean_nat_dec_lt(v_start_3700_, v_stop_3701_);
if (v___x_3704_ == 0)
{
lean_dec_ref(v_as_3699_);
lean_dec_ref(v_p_3698_);
return v___x_3702_;
}
else
{
lean_object* v___f_3705_; lean_object* v___x_3706_; uint8_t v___x_3707_; 
v___f_3705_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3705_, 0, v_p_3698_);
v___x_3706_ = lean_array_get_size(v_as_3699_);
v___x_3707_ = lean_nat_dec_le(v_stop_3701_, v___x_3706_);
if (v___x_3707_ == 0)
{
uint8_t v___x_3708_; 
v___x_3708_ = lean_nat_dec_lt(v_start_3700_, v___x_3706_);
if (v___x_3708_ == 0)
{
lean_dec_ref(v___f_3705_);
lean_dec_ref(v_as_3699_);
return v___x_3702_;
}
else
{
size_t v___x_3709_; size_t v___x_3710_; lean_object* v___x_3711_; 
v___x_3709_ = lean_usize_of_nat(v_start_3700_);
v___x_3710_ = lean_usize_of_nat(v___x_3706_);
v___x_3711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3703_, v___f_3705_, v_as_3699_, v___x_3709_, v___x_3710_, v___x_3702_);
return v___x_3711_;
}
}
else
{
size_t v___x_3712_; size_t v___x_3713_; lean_object* v___x_3714_; 
v___x_3712_ = lean_usize_of_nat(v_start_3700_);
v___x_3713_ = lean_usize_of_nat(v_stop_3701_);
v___x_3714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3703_, v___f_3705_, v_as_3699_, v___x_3712_, v___x_3713_, v___x_3702_);
return v___x_3714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___boxed(lean_object* v_00_u03b1_3715_, lean_object* v_p_3716_, lean_object* v_as_3717_, lean_object* v_start_3718_, lean_object* v_stop_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Array_filter(v_00_u03b1_3715_, v_p_3716_, v_as_3717_, v_start_3718_, v_stop_3719_);
lean_dec(v_stop_3719_);
lean_dec(v_start_3718_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0(lean_object* v_toPure_3721_, lean_object* v_acc_3722_, lean_object* v_a_3723_, uint8_t v_____do__lift_3724_){
_start:
{
if (v_____do__lift_3724_ == 0)
{
lean_object* v___x_3725_; 
lean_dec(v_a_3723_);
v___x_3725_ = lean_apply_2(v_toPure_3721_, lean_box(0), v_acc_3722_);
return v___x_3725_;
}
else
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = lean_array_push(v_acc_3722_, v_a_3723_);
v___x_3727_ = lean_apply_2(v_toPure_3721_, lean_box(0), v___x_3726_);
return v___x_3727_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0___boxed(lean_object* v_toPure_3728_, lean_object* v_acc_3729_, lean_object* v_a_3730_, lean_object* v_____do__lift_3731_){
_start:
{
uint8_t v_____do__lift_91__boxed_3732_; lean_object* v_res_3733_; 
v_____do__lift_91__boxed_3732_ = lean_unbox(v_____do__lift_3731_);
v_res_3733_ = l_Array_filterM___redArg___lam__0(v_toPure_3728_, v_acc_3729_, v_a_3730_, v_____do__lift_91__boxed_3732_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__1(lean_object* v_toPure_3734_, lean_object* v_p_3735_, lean_object* v_toBind_3736_, lean_object* v_acc_3737_, lean_object* v_a_3738_){
_start:
{
lean_object* v___f_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_inc(v_a_3738_);
v___f_3739_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3739_, 0, v_toPure_3734_);
lean_closure_set(v___f_3739_, 1, v_acc_3737_);
lean_closure_set(v___f_3739_, 2, v_a_3738_);
v___x_3740_ = lean_apply_1(v_p_3735_, v_a_3738_);
v___x_3741_ = lean_apply_4(v_toBind_3736_, lean_box(0), lean_box(0), v___x_3740_, v___f_3739_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg(lean_object* v_inst_3742_, lean_object* v_p_3743_, lean_object* v_as_3744_, lean_object* v_start_3745_, lean_object* v_stop_3746_){
_start:
{
lean_object* v_toApplicative_3747_; lean_object* v_toBind_3748_; lean_object* v_toPure_3749_; lean_object* v___x_3750_; uint8_t v___x_3751_; 
v_toApplicative_3747_ = lean_ctor_get(v_inst_3742_, 0);
v_toBind_3748_ = lean_ctor_get(v_inst_3742_, 1);
v_toPure_3749_ = lean_ctor_get(v_toApplicative_3747_, 1);
v___x_3750_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3751_ = lean_nat_dec_lt(v_start_3745_, v_stop_3746_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; 
lean_inc(v_toPure_3749_);
lean_dec_ref(v_as_3744_);
lean_dec(v_p_3743_);
lean_dec_ref(v_inst_3742_);
v___x_3752_ = lean_apply_2(v_toPure_3749_, lean_box(0), v___x_3750_);
return v___x_3752_;
}
else
{
lean_object* v___f_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
lean_inc(v_toBind_3748_);
lean_inc(v_toPure_3749_);
v___f_3753_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3753_, 0, v_toPure_3749_);
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
lean_object* v___x_3757_; 
lean_inc(v_toPure_3749_);
lean_dec_ref(v___f_3753_);
lean_dec_ref(v_as_3744_);
lean_dec_ref(v_inst_3742_);
v___x_3757_ = lean_apply_2(v_toPure_3749_, lean_box(0), v___x_3750_);
return v___x_3757_;
}
else
{
size_t v___x_3758_; size_t v___x_3759_; lean_object* v___x_3760_; 
v___x_3758_ = lean_usize_of_nat(v_start_3745_);
v___x_3759_ = lean_usize_of_nat(v___x_3754_);
v___x_3760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3742_, v___f_3753_, v_as_3744_, v___x_3758_, v___x_3759_, v___x_3750_);
return v___x_3760_;
}
}
else
{
size_t v___x_3761_; size_t v___x_3762_; lean_object* v___x_3763_; 
v___x_3761_ = lean_usize_of_nat(v_start_3745_);
v___x_3762_ = lean_usize_of_nat(v_stop_3746_);
v___x_3763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3742_, v___f_3753_, v_as_3744_, v___x_3761_, v___x_3762_, v___x_3750_);
return v___x_3763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___boxed(lean_object* v_inst_3764_, lean_object* v_p_3765_, lean_object* v_as_3766_, lean_object* v_start_3767_, lean_object* v_stop_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Array_filterM___redArg(v_inst_3764_, v_p_3765_, v_as_3766_, v_start_3767_, v_stop_3768_);
lean_dec(v_stop_3768_);
lean_dec(v_start_3767_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM(lean_object* v_m_3770_, lean_object* v_00_u03b1_3771_, lean_object* v_inst_3772_, lean_object* v_p_3773_, lean_object* v_as_3774_, lean_object* v_start_3775_, lean_object* v_stop_3776_){
_start:
{
lean_object* v_toApplicative_3777_; lean_object* v_toBind_3778_; lean_object* v_toPure_3779_; lean_object* v___x_3780_; uint8_t v___x_3781_; 
v_toApplicative_3777_ = lean_ctor_get(v_inst_3772_, 0);
v_toBind_3778_ = lean_ctor_get(v_inst_3772_, 1);
v_toPure_3779_ = lean_ctor_get(v_toApplicative_3777_, 1);
v___x_3780_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3781_ = lean_nat_dec_lt(v_start_3775_, v_stop_3776_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; 
lean_inc(v_toPure_3779_);
lean_dec_ref(v_as_3774_);
lean_dec(v_p_3773_);
lean_dec_ref(v_inst_3772_);
v___x_3782_ = lean_apply_2(v_toPure_3779_, lean_box(0), v___x_3780_);
return v___x_3782_;
}
else
{
lean_object* v___f_3783_; lean_object* v___x_3784_; uint8_t v___x_3785_; 
lean_inc(v_toBind_3778_);
lean_inc(v_toPure_3779_);
v___f_3783_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3783_, 0, v_toPure_3779_);
lean_closure_set(v___f_3783_, 1, v_p_3773_);
lean_closure_set(v___f_3783_, 2, v_toBind_3778_);
v___x_3784_ = lean_array_get_size(v_as_3774_);
v___x_3785_ = lean_nat_dec_le(v_stop_3776_, v___x_3784_);
if (v___x_3785_ == 0)
{
uint8_t v___x_3786_; 
v___x_3786_ = lean_nat_dec_lt(v_start_3775_, v___x_3784_);
if (v___x_3786_ == 0)
{
lean_object* v___x_3787_; 
lean_inc(v_toPure_3779_);
lean_dec_ref(v___f_3783_);
lean_dec_ref(v_as_3774_);
lean_dec_ref(v_inst_3772_);
v___x_3787_ = lean_apply_2(v_toPure_3779_, lean_box(0), v___x_3780_);
return v___x_3787_;
}
else
{
size_t v___x_3788_; size_t v___x_3789_; lean_object* v___x_3790_; 
v___x_3788_ = lean_usize_of_nat(v_start_3775_);
v___x_3789_ = lean_usize_of_nat(v___x_3784_);
v___x_3790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3772_, v___f_3783_, v_as_3774_, v___x_3788_, v___x_3789_, v___x_3780_);
return v___x_3790_;
}
}
else
{
size_t v___x_3791_; size_t v___x_3792_; lean_object* v___x_3793_; 
v___x_3791_ = lean_usize_of_nat(v_start_3775_);
v___x_3792_ = lean_usize_of_nat(v_stop_3776_);
v___x_3793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3772_, v___f_3783_, v_as_3774_, v___x_3791_, v___x_3792_, v___x_3780_);
return v___x_3793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___boxed(lean_object* v_m_3794_, lean_object* v_00_u03b1_3795_, lean_object* v_inst_3796_, lean_object* v_p_3797_, lean_object* v_as_3798_, lean_object* v_start_3799_, lean_object* v_stop_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Array_filterM(v_m_3794_, v_00_u03b1_3795_, v_inst_3796_, v_p_3797_, v_as_3798_, v_start_3799_, v_stop_3800_);
lean_dec(v_stop_3800_);
lean_dec(v_start_3799_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__1(lean_object* v_toPure_3802_, lean_object* v_p_3803_, lean_object* v_toBind_3804_, lean_object* v_a_3805_, lean_object* v_acc_3806_){
_start:
{
lean_object* v___f_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
lean_inc(v_a_3805_);
v___f_3807_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3807_, 0, v_toPure_3802_);
lean_closure_set(v___f_3807_, 1, v_acc_3806_);
lean_closure_set(v___f_3807_, 2, v_a_3805_);
v___x_3808_ = lean_apply_1(v_p_3803_, v_a_3805_);
v___x_3809_ = lean_apply_4(v_toBind_3804_, lean_box(0), lean_box(0), v___x_3808_, v___f_3807_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg(lean_object* v_inst_3811_, lean_object* v_p_3812_, lean_object* v_as_3813_, lean_object* v_start_3814_, lean_object* v_stop_3815_){
_start:
{
lean_object* v_toApplicative_3816_; lean_object* v_toFunctor_3817_; lean_object* v_toBind_3818_; lean_object* v_toPure_3819_; lean_object* v_map_3820_; lean_object* v___f_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
v_toApplicative_3816_ = lean_ctor_get(v_inst_3811_, 0);
v_toFunctor_3817_ = lean_ctor_get(v_toApplicative_3816_, 0);
v_toBind_3818_ = lean_ctor_get(v_inst_3811_, 1);
v_toPure_3819_ = lean_ctor_get(v_toApplicative_3816_, 1);
v_map_3820_ = lean_ctor_get(v_toFunctor_3817_, 0);
lean_inc(v_map_3820_);
lean_inc(v_toBind_3818_);
lean_inc(v_toPure_3819_);
v___f_3821_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3821_, 0, v_toPure_3819_);
lean_closure_set(v___f_3821_, 1, v_p_3812_);
lean_closure_set(v___f_3821_, 2, v_toBind_3818_);
v___x_3822_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3823_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3824_ = lean_array_get_size(v_as_3813_);
v___x_3825_ = lean_nat_dec_le(v_start_3814_, v___x_3824_);
if (v___x_3825_ == 0)
{
uint8_t v___x_3826_; 
v___x_3826_ = lean_nat_dec_lt(v_stop_3815_, v___x_3824_);
if (v___x_3826_ == 0)
{
lean_object* v___x_3827_; lean_object* v___x_3828_; 
lean_inc(v_toPure_3819_);
lean_dec_ref(v___f_3821_);
lean_dec_ref(v_as_3813_);
lean_dec_ref(v_inst_3811_);
v___x_3827_ = lean_apply_2(v_toPure_3819_, lean_box(0), v___x_3823_);
v___x_3828_ = lean_apply_4(v_map_3820_, lean_box(0), lean_box(0), v___x_3822_, v___x_3827_);
return v___x_3828_;
}
else
{
size_t v___x_3829_; size_t v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3829_ = lean_usize_of_nat(v___x_3824_);
v___x_3830_ = lean_usize_of_nat(v_stop_3815_);
v___x_3831_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3811_, v___f_3821_, v_as_3813_, v___x_3829_, v___x_3830_, v___x_3823_);
v___x_3832_ = lean_apply_4(v_map_3820_, lean_box(0), lean_box(0), v___x_3822_, v___x_3831_);
return v___x_3832_;
}
}
else
{
uint8_t v___x_3833_; 
v___x_3833_ = lean_nat_dec_lt(v_stop_3815_, v_start_3814_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
lean_inc(v_toPure_3819_);
lean_dec_ref(v___f_3821_);
lean_dec_ref(v_as_3813_);
lean_dec_ref(v_inst_3811_);
v___x_3834_ = lean_apply_2(v_toPure_3819_, lean_box(0), v___x_3823_);
v___x_3835_ = lean_apply_4(v_map_3820_, lean_box(0), lean_box(0), v___x_3822_, v___x_3834_);
return v___x_3835_;
}
else
{
size_t v___x_3836_; size_t v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3836_ = lean_usize_of_nat(v_start_3814_);
v___x_3837_ = lean_usize_of_nat(v_stop_3815_);
v___x_3838_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3811_, v___f_3821_, v_as_3813_, v___x_3836_, v___x_3837_, v___x_3823_);
v___x_3839_ = lean_apply_4(v_map_3820_, lean_box(0), lean_box(0), v___x_3822_, v___x_3838_);
return v___x_3839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___boxed(lean_object* v_inst_3840_, lean_object* v_p_3841_, lean_object* v_as_3842_, lean_object* v_start_3843_, lean_object* v_stop_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Array_filterRevM___redArg(v_inst_3840_, v_p_3841_, v_as_3842_, v_start_3843_, v_stop_3844_);
lean_dec(v_stop_3844_);
lean_dec(v_start_3843_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM(lean_object* v_m_3846_, lean_object* v_00_u03b1_3847_, lean_object* v_inst_3848_, lean_object* v_p_3849_, lean_object* v_as_3850_, lean_object* v_start_3851_, lean_object* v_stop_3852_){
_start:
{
lean_object* v_toApplicative_3853_; lean_object* v_toFunctor_3854_; lean_object* v_toBind_3855_; lean_object* v_toPure_3856_; lean_object* v_map_3857_; lean_object* v___f_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; uint8_t v___x_3862_; 
v_toApplicative_3853_ = lean_ctor_get(v_inst_3848_, 0);
v_toFunctor_3854_ = lean_ctor_get(v_toApplicative_3853_, 0);
v_toBind_3855_ = lean_ctor_get(v_inst_3848_, 1);
v_toPure_3856_ = lean_ctor_get(v_toApplicative_3853_, 1);
v_map_3857_ = lean_ctor_get(v_toFunctor_3854_, 0);
lean_inc(v_map_3857_);
lean_inc(v_toBind_3855_);
lean_inc(v_toPure_3856_);
v___f_3858_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3858_, 0, v_toPure_3856_);
lean_closure_set(v___f_3858_, 1, v_p_3849_);
lean_closure_set(v___f_3858_, 2, v_toBind_3855_);
v___x_3859_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3860_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3861_ = lean_array_get_size(v_as_3850_);
v___x_3862_ = lean_nat_dec_le(v_start_3851_, v___x_3861_);
if (v___x_3862_ == 0)
{
uint8_t v___x_3863_; 
v___x_3863_ = lean_nat_dec_lt(v_stop_3852_, v___x_3861_);
if (v___x_3863_ == 0)
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
lean_inc(v_toPure_3856_);
lean_dec_ref(v___f_3858_);
lean_dec_ref(v_as_3850_);
lean_dec_ref(v_inst_3848_);
v___x_3864_ = lean_apply_2(v_toPure_3856_, lean_box(0), v___x_3860_);
v___x_3865_ = lean_apply_4(v_map_3857_, lean_box(0), lean_box(0), v___x_3859_, v___x_3864_);
return v___x_3865_;
}
else
{
size_t v___x_3866_; size_t v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3866_ = lean_usize_of_nat(v___x_3861_);
v___x_3867_ = lean_usize_of_nat(v_stop_3852_);
v___x_3868_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3848_, v___f_3858_, v_as_3850_, v___x_3866_, v___x_3867_, v___x_3860_);
v___x_3869_ = lean_apply_4(v_map_3857_, lean_box(0), lean_box(0), v___x_3859_, v___x_3868_);
return v___x_3869_;
}
}
else
{
uint8_t v___x_3870_; 
v___x_3870_ = lean_nat_dec_lt(v_stop_3852_, v_start_3851_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; lean_object* v___x_3872_; 
lean_inc(v_toPure_3856_);
lean_dec_ref(v___f_3858_);
lean_dec_ref(v_as_3850_);
lean_dec_ref(v_inst_3848_);
v___x_3871_ = lean_apply_2(v_toPure_3856_, lean_box(0), v___x_3860_);
v___x_3872_ = lean_apply_4(v_map_3857_, lean_box(0), lean_box(0), v___x_3859_, v___x_3871_);
return v___x_3872_;
}
else
{
size_t v___x_3873_; size_t v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3873_ = lean_usize_of_nat(v_start_3851_);
v___x_3874_ = lean_usize_of_nat(v_stop_3852_);
v___x_3875_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3848_, v___f_3858_, v_as_3850_, v___x_3873_, v___x_3874_, v___x_3860_);
v___x_3876_ = lean_apply_4(v_map_3857_, lean_box(0), lean_box(0), v___x_3859_, v___x_3875_);
return v___x_3876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___boxed(lean_object* v_m_3877_, lean_object* v_00_u03b1_3878_, lean_object* v_inst_3879_, lean_object* v_p_3880_, lean_object* v_as_3881_, lean_object* v_start_3882_, lean_object* v_stop_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Array_filterRevM(v_m_3877_, v_00_u03b1_3878_, v_inst_3879_, v_p_3880_, v_as_3881_, v_start_3882_, v_stop_3883_);
lean_dec(v_stop_3883_);
lean_dec(v_start_3882_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__0(lean_object* v_toPure_3885_, lean_object* v_bs_3886_, lean_object* v_____do__lift_3887_){
_start:
{
if (lean_obj_tag(v_____do__lift_3887_) == 0)
{
lean_object* v___x_3888_; 
v___x_3888_ = lean_apply_2(v_toPure_3885_, lean_box(0), v_bs_3886_);
return v___x_3888_;
}
else
{
lean_object* v_val_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v_val_3889_ = lean_ctor_get(v_____do__lift_3887_, 0);
lean_inc(v_val_3889_);
lean_dec_ref_known(v_____do__lift_3887_, 1);
v___x_3890_ = lean_array_push(v_bs_3886_, v_val_3889_);
v___x_3891_ = lean_apply_2(v_toPure_3885_, lean_box(0), v___x_3890_);
return v___x_3891_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__1(lean_object* v_toPure_3892_, lean_object* v_f_3893_, lean_object* v_toBind_3894_, lean_object* v_bs_3895_, lean_object* v_a_3896_){
_start:
{
lean_object* v___f_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___f_3897_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3897_, 0, v_toPure_3892_);
lean_closure_set(v___f_3897_, 1, v_bs_3895_);
v___x_3898_ = lean_apply_1(v_f_3893_, v_a_3896_);
v___x_3899_ = lean_apply_4(v_toBind_3894_, lean_box(0), lean_box(0), v___x_3898_, v___f_3897_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg(lean_object* v_inst_3900_, lean_object* v_f_3901_, lean_object* v_as_3902_, lean_object* v_start_3903_, lean_object* v_stop_3904_){
_start:
{
lean_object* v_toApplicative_3905_; lean_object* v_toBind_3906_; lean_object* v_toPure_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
v_toApplicative_3905_ = lean_ctor_get(v_inst_3900_, 0);
v_toBind_3906_ = lean_ctor_get(v_inst_3900_, 1);
v_toPure_3907_ = lean_ctor_get(v_toApplicative_3905_, 1);
v___x_3908_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3909_ = lean_nat_dec_lt(v_start_3903_, v_stop_3904_);
if (v___x_3909_ == 0)
{
lean_object* v___x_3910_; 
lean_inc(v_toPure_3907_);
lean_dec_ref(v_as_3902_);
lean_dec(v_f_3901_);
lean_dec_ref(v_inst_3900_);
v___x_3910_ = lean_apply_2(v_toPure_3907_, lean_box(0), v___x_3908_);
return v___x_3910_;
}
else
{
lean_object* v___f_3911_; lean_object* v___x_3912_; uint8_t v___x_3913_; 
lean_inc(v_toBind_3906_);
lean_inc(v_toPure_3907_);
v___f_3911_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3911_, 0, v_toPure_3907_);
lean_closure_set(v___f_3911_, 1, v_f_3901_);
lean_closure_set(v___f_3911_, 2, v_toBind_3906_);
v___x_3912_ = lean_array_get_size(v_as_3902_);
v___x_3913_ = lean_nat_dec_le(v_stop_3904_, v___x_3912_);
if (v___x_3913_ == 0)
{
uint8_t v___x_3914_; 
v___x_3914_ = lean_nat_dec_lt(v_start_3903_, v___x_3912_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3915_; 
lean_inc(v_toPure_3907_);
lean_dec_ref(v___f_3911_);
lean_dec_ref(v_as_3902_);
lean_dec_ref(v_inst_3900_);
v___x_3915_ = lean_apply_2(v_toPure_3907_, lean_box(0), v___x_3908_);
return v___x_3915_;
}
else
{
size_t v___x_3916_; size_t v___x_3917_; lean_object* v___x_3918_; 
v___x_3916_ = lean_usize_of_nat(v_start_3903_);
v___x_3917_ = lean_usize_of_nat(v___x_3912_);
v___x_3918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3900_, v___f_3911_, v_as_3902_, v___x_3916_, v___x_3917_, v___x_3908_);
return v___x_3918_;
}
}
else
{
size_t v___x_3919_; size_t v___x_3920_; lean_object* v___x_3921_; 
v___x_3919_ = lean_usize_of_nat(v_start_3903_);
v___x_3920_ = lean_usize_of_nat(v_stop_3904_);
v___x_3921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3900_, v___f_3911_, v_as_3902_, v___x_3919_, v___x_3920_, v___x_3908_);
return v___x_3921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___boxed(lean_object* v_inst_3922_, lean_object* v_f_3923_, lean_object* v_as_3924_, lean_object* v_start_3925_, lean_object* v_stop_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Array_filterMapM___redArg(v_inst_3922_, v_f_3923_, v_as_3924_, v_start_3925_, v_stop_3926_);
lean_dec(v_stop_3926_);
lean_dec(v_start_3925_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM(lean_object* v_00_u03b1_3928_, lean_object* v_m_3929_, lean_object* v_00_u03b2_3930_, lean_object* v_inst_3931_, lean_object* v_f_3932_, lean_object* v_as_3933_, lean_object* v_start_3934_, lean_object* v_stop_3935_){
_start:
{
lean_object* v___x_3936_; 
v___x_3936_ = l_Array_filterMapM___redArg(v_inst_3931_, v_f_3932_, v_as_3933_, v_start_3934_, v_stop_3935_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___boxed(lean_object* v_00_u03b1_3937_, lean_object* v_m_3938_, lean_object* v_00_u03b2_3939_, lean_object* v_inst_3940_, lean_object* v_f_3941_, lean_object* v_as_3942_, lean_object* v_start_3943_, lean_object* v_stop_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l_Array_filterMapM(v_00_u03b1_3937_, v_m_3938_, v_00_u03b2_3939_, v_inst_3940_, v_f_3941_, v_as_3942_, v_start_3943_, v_stop_3944_);
lean_dec(v_stop_3944_);
lean_dec(v_start_3943_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg(lean_object* v_f_3946_, lean_object* v_as_3947_, lean_object* v_start_3948_, lean_object* v_stop_3949_){
_start:
{
lean_object* v___f_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___f_3950_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3950_, 0, v_f_3946_);
v___x_3951_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3952_ = l_Array_filterMapM___redArg(v___x_3951_, v___f_3950_, v_as_3947_, v_start_3948_, v_stop_3949_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg___boxed(lean_object* v_f_3953_, lean_object* v_as_3954_, lean_object* v_start_3955_, lean_object* v_stop_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l_Array_filterMap___redArg(v_f_3953_, v_as_3954_, v_start_3955_, v_stop_3956_);
lean_dec(v_stop_3956_);
lean_dec(v_start_3955_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap(lean_object* v_00_u03b1_3958_, lean_object* v_00_u03b2_3959_, lean_object* v_f_3960_, lean_object* v_as_3961_, lean_object* v_start_3962_, lean_object* v_stop_3963_){
_start:
{
lean_object* v___f_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___f_3964_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3964_, 0, v_f_3960_);
v___x_3965_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3966_ = l_Array_filterMapM___redArg(v___x_3965_, v___f_3964_, v_as_3961_, v_start_3962_, v_stop_3963_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___boxed(lean_object* v_00_u03b1_3967_, lean_object* v_00_u03b2_3968_, lean_object* v_f_3969_, lean_object* v_as_3970_, lean_object* v_start_3971_, lean_object* v_stop_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_Array_filterMap(v_00_u03b1_3967_, v_00_u03b2_3968_, v_f_3969_, v_as_3970_, v_start_3971_, v_stop_3972_);
lean_dec(v_stop_3972_);
lean_dec(v_start_3971_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg___lam__0(lean_object* v_lt_3974_, lean_object* v_x1_3975_, lean_object* v_x2_3976_){
_start:
{
lean_object* v___x_3977_; uint8_t v___x_3978_; 
lean_inc(v_x2_3976_);
lean_inc(v_x1_3975_);
v___x_3977_ = lean_apply_2(v_lt_3974_, v_x1_3975_, v_x2_3976_);
v___x_3978_ = lean_unbox(v___x_3977_);
if (v___x_3978_ == 0)
{
lean_dec(v_x2_3976_);
return v_x1_3975_;
}
else
{
lean_dec(v_x1_3975_);
return v_x2_3976_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg(lean_object* v_as_3979_, lean_object* v_lt_3980_){
_start:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; 
v___x_3981_ = lean_unsigned_to_nat(0u);
v___x_3982_ = lean_array_get_size(v_as_3979_);
v___x_3983_ = lean_nat_dec_lt(v___x_3981_, v___x_3982_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; 
lean_dec_ref(v_lt_3980_);
lean_dec_ref(v_as_3979_);
v___x_3984_ = lean_box(0);
return v___x_3984_;
}
else
{
lean_object* v_a0_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; uint8_t v___x_3988_; 
v_a0_3985_ = lean_array_fget(v_as_3979_, v___x_3981_);
v___x_3986_ = lean_unsigned_to_nat(1u);
v___x_3987_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3988_ = lean_nat_dec_lt(v___x_3986_, v___x_3982_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; 
lean_dec_ref(v_lt_3980_);
lean_dec_ref(v_as_3979_);
v___x_3989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3989_, 0, v_a0_3985_);
return v___x_3989_;
}
else
{
lean_object* v___f_3990_; uint8_t v___x_3991_; 
v___f_3990_ = lean_alloc_closure((void*)(l_Array_getMax_x3f___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3990_, 0, v_lt_3980_);
v___x_3991_ = lean_nat_dec_le(v___x_3982_, v___x_3982_);
if (v___x_3991_ == 0)
{
if (v___x_3988_ == 0)
{
lean_object* v___x_3992_; 
lean_dec_ref(v___f_3990_);
lean_dec_ref(v_as_3979_);
v___x_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3992_, 0, v_a0_3985_);
return v___x_3992_;
}
else
{
size_t v___x_3993_; size_t v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3993_ = ((size_t)1ULL);
v___x_3994_ = lean_usize_of_nat(v___x_3982_);
v___x_3995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3987_, v___f_3990_, v_as_3979_, v___x_3993_, v___x_3994_, v_a0_3985_);
v___x_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3995_);
return v___x_3996_;
}
}
else
{
size_t v___x_3997_; size_t v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3997_ = ((size_t)1ULL);
v___x_3998_ = lean_usize_of_nat(v___x_3982_);
v___x_3999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3987_, v___f_3990_, v_as_3979_, v___x_3997_, v___x_3998_, v_a0_3985_);
v___x_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
return v___x_4000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f(lean_object* v_00_u03b1_4001_, lean_object* v_as_4002_, lean_object* v_lt_4003_){
_start:
{
lean_object* v___x_4004_; 
v___x_4004_ = l_Array_getMax_x3f___redArg(v_as_4002_, v_lt_4003_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg___lam__0(lean_object* v_p_4005_, lean_object* v_a_4006_, lean_object* v_x_4007_, lean_object* v___y_4008_){
_start:
{
lean_object* v_fst_4009_; lean_object* v_snd_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4026_; 
v_fst_4009_ = lean_ctor_get(v___y_4008_, 0);
v_snd_4010_ = lean_ctor_get(v___y_4008_, 1);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___y_4008_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4012_ = v___y_4008_;
v_isShared_4013_ = v_isSharedCheck_4026_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_snd_4010_);
lean_inc(v_fst_4009_);
lean_dec(v___y_4008_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4026_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4014_; uint8_t v___x_4015_; 
lean_inc(v_a_4006_);
v___x_4014_ = lean_apply_1(v_p_4005_, v_a_4006_);
v___x_4015_ = lean_unbox(v___x_4014_);
if (v___x_4015_ == 0)
{
lean_object* v___x_4016_; lean_object* v___x_4018_; 
v___x_4016_ = lean_array_push(v_snd_4010_, v_a_4006_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 1, v___x_4016_);
v___x_4018_ = v___x_4012_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_fst_4009_);
lean_ctor_set(v_reuseFailAlloc_4020_, 1, v___x_4016_);
v___x_4018_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
lean_object* v___x_4019_; 
v___x_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4018_);
return v___x_4019_;
}
}
else
{
lean_object* v___x_4021_; lean_object* v___x_4023_; 
v___x_4021_ = lean_array_push(v_fst_4009_, v_a_4006_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v___x_4021_);
v___x_4023_ = v___x_4012_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4021_);
lean_ctor_set(v_reuseFailAlloc_4025_, 1, v_snd_4010_);
v___x_4023_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
lean_object* v___x_4024_; 
v___x_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
return v___x_4024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg(lean_object* v_p_4029_, lean_object* v_as_4030_){
_start:
{
lean_object* v___f_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; size_t v_sz_4034_; size_t v___x_4035_; lean_object* v___x_4036_; lean_object* v_fst_4037_; lean_object* v_snd_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
v___f_4031_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4031_, 0, v_p_4029_);
v___x_4032_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4033_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_4034_ = lean_array_size(v_as_4030_);
v___x_4035_ = ((size_t)0ULL);
v___x_4036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_4032_, v_as_4030_, v___f_4031_, v_sz_4034_, v___x_4035_, v___x_4033_);
v_fst_4037_ = lean_ctor_get(v___x_4036_, 0);
v_snd_4038_ = lean_ctor_get(v___x_4036_, 1);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4036_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_snd_4038_);
lean_inc(v_fst_4037_);
lean_dec(v___x_4036_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_fst_4037_);
lean_ctor_set(v_reuseFailAlloc_4044_, 1, v_snd_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition(lean_object* v_00_u03b1_4046_, lean_object* v_p_4047_, lean_object* v_as_4048_){
_start:
{
lean_object* v___f_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; size_t v_sz_4052_; size_t v___x_4053_; lean_object* v___x_4054_; lean_object* v_fst_4055_; lean_object* v_snd_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
v___f_4049_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4049_, 0, v_p_4047_);
v___x_4050_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4051_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_4052_ = lean_array_size(v_as_4048_);
v___x_4053_ = ((size_t)0ULL);
v___x_4054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_4050_, v_as_4048_, v___f_4049_, v_sz_4052_, v___x_4053_, v___x_4051_);
v_fst_4055_ = lean_ctor_get(v___x_4054_, 0);
v_snd_4056_ = lean_ctor_get(v___x_4054_, 1);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4054_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_snd_4056_);
lean_inc(v_fst_4055_);
lean_dec(v___x_4054_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_fst_4055_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v_snd_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile___redArg(lean_object* v_p_4064_, lean_object* v_as_4065_){
_start:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; uint8_t v___x_4068_; 
v___x_4066_ = lean_unsigned_to_nat(0u);
v___x_4067_ = lean_array_get_size(v_as_4065_);
v___x_4068_ = lean_nat_dec_lt(v___x_4066_, v___x_4067_);
if (v___x_4068_ == 0)
{
lean_dec_ref(v_p_4064_);
return v_as_4065_;
}
else
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; uint8_t v___x_4073_; 
v___x_4069_ = lean_unsigned_to_nat(1u);
v___x_4070_ = lean_nat_sub(v___x_4067_, v___x_4069_);
v___x_4071_ = lean_array_fget_borrowed(v_as_4065_, v___x_4070_);
lean_dec(v___x_4070_);
lean_inc_ref(v_p_4064_);
lean_inc(v___x_4071_);
v___x_4072_ = lean_apply_1(v_p_4064_, v___x_4071_);
v___x_4073_ = lean_unbox(v___x_4072_);
if (v___x_4073_ == 0)
{
lean_dec_ref(v_p_4064_);
return v_as_4065_;
}
else
{
lean_object* v___x_4074_; 
v___x_4074_ = lean_array_pop(v_as_4065_);
v_as_4065_ = v___x_4074_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile(lean_object* v_00_u03b1_4076_, lean_object* v_p_4077_, lean_object* v_as_4078_){
_start:
{
lean_object* v___x_4079_; 
v___x_4079_ = l_Array_popWhile___redArg(v_p_4077_, v_as_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(lean_object* v_p_4080_, lean_object* v_as_4081_, lean_object* v_i_4082_, lean_object* v_acc_4083_){
_start:
{
lean_object* v___x_4084_; uint8_t v___x_4085_; 
v___x_4084_ = lean_array_get_size(v_as_4081_);
v___x_4085_ = lean_nat_dec_lt(v_i_4082_, v___x_4084_);
if (v___x_4085_ == 0)
{
lean_dec(v_i_4082_);
lean_dec_ref(v_p_4080_);
return v_acc_4083_;
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4087_; uint8_t v___x_4088_; 
v_a_4086_ = lean_array_fget_borrowed(v_as_4081_, v_i_4082_);
lean_inc_ref(v_p_4080_);
lean_inc(v_a_4086_);
v___x_4087_ = lean_apply_1(v_p_4080_, v_a_4086_);
v___x_4088_ = lean_unbox(v___x_4087_);
if (v___x_4088_ == 0)
{
lean_dec(v_i_4082_);
lean_dec_ref(v_p_4080_);
return v_acc_4083_;
}
else
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4089_ = lean_unsigned_to_nat(1u);
v___x_4090_ = lean_nat_add(v_i_4082_, v___x_4089_);
lean_dec(v_i_4082_);
lean_inc(v_a_4086_);
v___x_4091_ = lean_array_push(v_acc_4083_, v_a_4086_);
v_i_4082_ = v___x_4090_;
v_acc_4083_ = v___x_4091_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg___boxed(lean_object* v_p_4093_, lean_object* v_as_4094_, lean_object* v_i_4095_, lean_object* v_acc_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4093_, v_as_4094_, v_i_4095_, v_acc_4096_);
lean_dec_ref(v_as_4094_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(lean_object* v_00_u03b1_4098_, lean_object* v_p_4099_, lean_object* v_as_4100_, lean_object* v_i_4101_, lean_object* v_acc_4102_){
_start:
{
lean_object* v___x_4103_; 
v___x_4103_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4099_, v_as_4100_, v_i_4101_, v_acc_4102_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___boxed(lean_object* v_00_u03b1_4104_, lean_object* v_p_4105_, lean_object* v_as_4106_, lean_object* v_i_4107_, lean_object* v_acc_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(v_00_u03b1_4104_, v_p_4105_, v_as_4106_, v_i_4107_, v_acc_4108_);
lean_dec_ref(v_as_4106_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg(lean_object* v_p_4110_, lean_object* v_as_4111_){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4112_ = lean_unsigned_to_nat(0u);
v___x_4113_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4114_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4110_, v_as_4111_, v___x_4112_, v___x_4113_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg___boxed(lean_object* v_p_4115_, lean_object* v_as_4116_){
_start:
{
lean_object* v_res_4117_; 
v_res_4117_ = l_Array_takeWhile___redArg(v_p_4115_, v_as_4116_);
lean_dec_ref(v_as_4116_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile(lean_object* v_00_u03b1_4118_, lean_object* v_p_4119_, lean_object* v_as_4120_){
_start:
{
lean_object* v___x_4121_; 
v___x_4121_ = l_Array_takeWhile___redArg(v_p_4119_, v_as_4120_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___boxed(lean_object* v_00_u03b1_4122_, lean_object* v_p_4123_, lean_object* v_as_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l_Array_takeWhile(v_00_u03b1_4122_, v_p_4123_, v_as_4124_);
lean_dec_ref(v_as_4124_);
return v_res_4125_;
}
}
static lean_object* _init_l_Array_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_4126_; 
v___x_4126_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx___redArg(lean_object* v_xs_4127_, lean_object* v_i_4128_){
_start:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
v___x_4129_ = lean_unsigned_to_nat(1u);
v___x_4130_ = lean_nat_add(v_i_4128_, v___x_4129_);
v___x_4131_ = lean_array_get_size(v_xs_4127_);
v___x_4132_ = lean_nat_dec_lt(v___x_4130_, v___x_4131_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4133_; 
lean_dec(v___x_4130_);
lean_dec(v_i_4128_);
v___x_4133_ = lean_array_pop(v_xs_4127_);
return v___x_4133_;
}
else
{
lean_object* v_xs_x27_4134_; 
v_xs_x27_4134_ = lean_array_fswap(v_xs_4127_, v___x_4130_, v_i_4128_);
lean_dec(v_i_4128_);
v_xs_4127_ = v_xs_x27_4134_;
v_i_4128_ = v___x_4130_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx(lean_object* v_00_u03b1_4136_, lean_object* v_xs_4137_, lean_object* v_i_4138_, lean_object* v_h_4139_){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = l_Array_eraseIdx___redArg(v_xs_4137_, v_i_4138_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds___redArg(lean_object* v_xs_4141_, lean_object* v_i_4142_){
_start:
{
lean_object* v___x_4143_; uint8_t v___x_4144_; 
v___x_4143_ = lean_array_get_size(v_xs_4141_);
v___x_4144_ = lean_nat_dec_lt(v_i_4142_, v___x_4143_);
if (v___x_4144_ == 0)
{
lean_dec(v_i_4142_);
return v_xs_4141_;
}
else
{
lean_object* v___x_4145_; 
v___x_4145_ = l_Array_eraseIdx___redArg(v_xs_4141_, v_i_4142_);
return v___x_4145_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds(lean_object* v_00_u03b1_4146_, lean_object* v_xs_4147_, lean_object* v_i_4148_){
_start:
{
lean_object* v___x_4149_; 
v___x_4149_ = l_Array_eraseIdxIfInBounds___redArg(v_xs_4147_, v_i_4148_);
return v___x_4149_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(lean_object* v_msg_4150_){
_start:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4151_ = lean_obj_once(&l_Array_instInhabited___closed__0, &l_Array_instInhabited___closed__0_once, _init_l_Array_instInhabited___closed__0);
v___x_4152_ = lean_panic_fn_borrowed(v___x_4151_, v_msg_4150_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0(lean_object* v_00_u03b1_4153_, lean_object* v_msg_4154_){
_start:
{
lean_object* v___x_4155_; 
v___x_4155_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v_msg_4154_);
return v___x_4155_;
}
}
static lean_object* _init_l_Array_eraseIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4158_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4159_ = lean_unsigned_to_nat(47u);
v___x_4160_ = lean_unsigned_to_nat(1867u);
v___x_4161_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__0));
v___x_4162_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4163_ = l_mkPanicMessageWithDecl(v___x_4162_, v___x_4161_, v___x_4160_, v___x_4159_, v___x_4158_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21___redArg(lean_object* v_xs_4164_, lean_object* v_i_4165_){
_start:
{
lean_object* v___x_4166_; uint8_t v___x_4167_; 
v___x_4166_ = lean_array_get_size(v_xs_4164_);
v___x_4167_ = lean_nat_dec_lt(v_i_4165_, v___x_4166_);
if (v___x_4167_ == 0)
{
lean_object* v___x_4168_; lean_object* v___x_4169_; 
lean_dec(v_i_4165_);
lean_dec_ref(v_xs_4164_);
v___x_4168_ = lean_obj_once(&l_Array_eraseIdx_x21___redArg___closed__2, &l_Array_eraseIdx_x21___redArg___closed__2_once, _init_l_Array_eraseIdx_x21___redArg___closed__2);
v___x_4169_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4168_);
return v___x_4169_;
}
else
{
lean_object* v___x_4170_; 
v___x_4170_ = l_Array_eraseIdx___redArg(v_xs_4164_, v_i_4165_);
return v___x_4170_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21(lean_object* v_00_u03b1_4171_, lean_object* v_xs_4172_, lean_object* v_i_4173_){
_start:
{
lean_object* v___x_4174_; 
v___x_4174_ = l_Array_eraseIdx_x21___redArg(v_xs_4172_, v_i_4173_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l_Array_erase___redArg(lean_object* v_inst_4175_, lean_object* v_as_4176_, lean_object* v_a_4177_){
_start:
{
lean_object* v___x_4178_; 
v___x_4178_ = l_Array_finIdxOf_x3f___redArg(v_inst_4175_, v_as_4176_, v_a_4177_);
if (lean_obj_tag(v___x_4178_) == 0)
{
return v_as_4176_;
}
else
{
lean_object* v_val_4179_; lean_object* v___x_4180_; 
v_val_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_val_4179_);
lean_dec_ref_known(v___x_4178_, 1);
v___x_4180_ = l_Array_eraseIdx___redArg(v_as_4176_, v_val_4179_);
return v___x_4180_;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase(lean_object* v_00_u03b1_4181_, lean_object* v_inst_4182_, lean_object* v_as_4183_, lean_object* v_a_4184_){
_start:
{
lean_object* v___x_4185_; 
v___x_4185_ = l_Array_erase___redArg(v_inst_4182_, v_as_4183_, v_a_4184_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseP___redArg(lean_object* v_as_4186_, lean_object* v_p_4187_){
_start:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4188_ = lean_unsigned_to_nat(0u);
v___x_4189_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_4187_, v_as_4186_, v___x_4188_);
if (lean_obj_tag(v___x_4189_) == 0)
{
return v_as_4186_;
}
else
{
lean_object* v_val_4190_; lean_object* v___x_4191_; 
v_val_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_val_4190_);
lean_dec_ref_known(v___x_4189_, 1);
v___x_4191_ = l_Array_eraseIdx___redArg(v_as_4186_, v_val_4190_);
return v___x_4191_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseP(lean_object* v_00_u03b1_4192_, lean_object* v_as_4193_, lean_object* v_p_4194_){
_start:
{
lean_object* v___x_4195_; 
v___x_4195_ = l_Array_eraseP___redArg(v_as_4193_, v_p_4194_);
return v___x_4195_;
}
}
static lean_object* _init_l_Array_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(lean_object* v_i_4197_, lean_object* v_as_4198_, lean_object* v_j_4199_){
_start:
{
uint8_t v___x_4200_; 
v___x_4200_ = lean_nat_dec_lt(v_i_4197_, v_j_4199_);
if (v___x_4200_ == 0)
{
lean_dec(v_j_4199_);
return v_as_4198_;
}
else
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v_as_4203_; 
v___x_4201_ = lean_unsigned_to_nat(1u);
v___x_4202_ = lean_nat_sub(v_j_4199_, v___x_4201_);
v_as_4203_ = lean_array_fswap(v_as_4198_, v___x_4202_, v_j_4199_);
lean_dec(v_j_4199_);
v_as_4198_ = v_as_4203_;
v_j_4199_ = v___x_4202_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg___boxed(lean_object* v_i_4205_, lean_object* v_as_4206_, lean_object* v_j_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4205_, v_as_4206_, v_j_4207_);
lean_dec(v_i_4205_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object* v_00_u03b1_4209_, lean_object* v_i_4210_, lean_object* v_as_4211_, lean_object* v_j_4212_){
_start:
{
lean_object* v___x_4213_; 
v___x_4213_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4210_, v_as_4211_, v_j_4212_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___boxed(lean_object* v_00_u03b1_4214_, lean_object* v_i_4215_, lean_object* v_as_4216_, lean_object* v_j_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(v_00_u03b1_4214_, v_i_4215_, v_as_4216_, v_j_4217_);
lean_dec(v_i_4215_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg(lean_object* v_as_4219_, lean_object* v_i_4220_, lean_object* v_a_4221_){
_start:
{
lean_object* v_j_4222_; lean_object* v_as_4223_; lean_object* v___x_4224_; 
v_j_4222_ = lean_array_get_size(v_as_4219_);
v_as_4223_ = lean_array_push(v_as_4219_, v_a_4221_);
v___x_4224_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4220_, v_as_4223_, v_j_4222_);
return v___x_4224_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg___boxed(lean_object* v_as_4225_, lean_object* v_i_4226_, lean_object* v_a_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l_Array_insertIdx___redArg(v_as_4225_, v_i_4226_, v_a_4227_);
lean_dec(v_i_4226_);
return v_res_4228_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx(lean_object* v_00_u03b1_4229_, lean_object* v_as_4230_, lean_object* v_i_4231_, lean_object* v_a_4232_, lean_object* v_x_4233_){
_start:
{
lean_object* v_j_4234_; lean_object* v_as_4235_; lean_object* v___x_4236_; 
v_j_4234_ = lean_array_get_size(v_as_4230_);
v_as_4235_ = lean_array_push(v_as_4230_, v_a_4232_);
v___x_4236_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4231_, v_as_4235_, v_j_4234_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___boxed(lean_object* v_00_u03b1_4237_, lean_object* v_as_4238_, lean_object* v_i_4239_, lean_object* v_a_4240_, lean_object* v_x_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Array_insertIdx(v_00_u03b1_4237_, v_as_4238_, v_i_4239_, v_a_4240_, v_x_4241_);
lean_dec(v_i_4239_);
return v_res_4242_;
}
}
static lean_object* _init_l_Array_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4244_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4245_ = lean_unsigned_to_nat(7u);
v___x_4246_ = lean_unsigned_to_nat(1949u);
v___x_4247_ = ((lean_object*)(l_Array_insertIdx_x21___redArg___closed__0));
v___x_4248_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4249_ = l_mkPanicMessageWithDecl(v___x_4248_, v___x_4247_, v___x_4246_, v___x_4245_, v___x_4244_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg(lean_object* v_as_4250_, lean_object* v_i_4251_, lean_object* v_a_4252_){
_start:
{
lean_object* v___x_4253_; uint8_t v___x_4254_; 
v___x_4253_ = lean_array_get_size(v_as_4250_);
v___x_4254_ = lean_nat_dec_le(v_i_4251_, v___x_4253_);
if (v___x_4254_ == 0)
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
lean_dec(v_a_4252_);
lean_dec_ref(v_as_4250_);
v___x_4255_ = lean_obj_once(&l_Array_insertIdx_x21___redArg___closed__1, &l_Array_insertIdx_x21___redArg___closed__1_once, _init_l_Array_insertIdx_x21___redArg___closed__1);
v___x_4256_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4255_);
return v___x_4256_;
}
else
{
lean_object* v_as_4257_; lean_object* v___x_4258_; 
v_as_4257_ = lean_array_push(v_as_4250_, v_a_4252_);
v___x_4258_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4251_, v_as_4257_, v___x_4253_);
return v___x_4258_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg___boxed(lean_object* v_as_4259_, lean_object* v_i_4260_, lean_object* v_a_4261_){
_start:
{
lean_object* v_res_4262_; 
v_res_4262_ = l_Array_insertIdx_x21___redArg(v_as_4259_, v_i_4260_, v_a_4261_);
lean_dec(v_i_4260_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21(lean_object* v_00_u03b1_4263_, lean_object* v_as_4264_, lean_object* v_i_4265_, lean_object* v_a_4266_){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l_Array_insertIdx_x21___redArg(v_as_4264_, v_i_4265_, v_a_4266_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___boxed(lean_object* v_00_u03b1_4268_, lean_object* v_as_4269_, lean_object* v_i_4270_, lean_object* v_a_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l_Array_insertIdx_x21(v_00_u03b1_4268_, v_as_4269_, v_i_4270_, v_a_4271_);
lean_dec(v_i_4270_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg(lean_object* v_as_4273_, lean_object* v_i_4274_, lean_object* v_a_4275_){
_start:
{
lean_object* v___x_4276_; uint8_t v___x_4277_; 
v___x_4276_ = lean_array_get_size(v_as_4273_);
v___x_4277_ = lean_nat_dec_le(v_i_4274_, v___x_4276_);
if (v___x_4277_ == 0)
{
lean_dec(v_a_4275_);
return v_as_4273_;
}
else
{
lean_object* v_as_4278_; lean_object* v___x_4279_; 
v_as_4278_ = lean_array_push(v_as_4273_, v_a_4275_);
v___x_4279_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4274_, v_as_4278_, v___x_4276_);
return v___x_4279_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg___boxed(lean_object* v_as_4280_, lean_object* v_i_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Array_insertIdxIfInBounds___redArg(v_as_4280_, v_i_4281_, v_a_4282_);
lean_dec(v_i_4281_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds(lean_object* v_00_u03b1_4284_, lean_object* v_as_4285_, lean_object* v_i_4286_, lean_object* v_a_4287_){
_start:
{
lean_object* v___x_4288_; 
v___x_4288_ = l_Array_insertIdxIfInBounds___redArg(v_as_4285_, v_i_4286_, v_a_4287_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___boxed(lean_object* v_00_u03b1_4289_, lean_object* v_as_4290_, lean_object* v_i_4291_, lean_object* v_a_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l_Array_insertIdxIfInBounds(v_00_u03b1_4289_, v_as_4290_, v_i_4291_, v_a_4292_);
lean_dec(v_i_4291_);
return v_res_4293_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux___redArg(lean_object* v_inst_4294_, lean_object* v_as_4295_, lean_object* v_bs_4296_, lean_object* v_i_4297_){
_start:
{
lean_object* v___x_4298_; uint8_t v___x_4299_; 
v___x_4298_ = lean_array_get_size(v_as_4295_);
v___x_4299_ = lean_nat_dec_lt(v_i_4297_, v___x_4298_);
if (v___x_4299_ == 0)
{
uint8_t v___x_4300_; 
lean_dec(v_i_4297_);
lean_dec_ref(v_inst_4294_);
v___x_4300_ = 1;
return v___x_4300_;
}
else
{
lean_object* v_a_4301_; lean_object* v_b_4302_; lean_object* v___x_4303_; uint8_t v___x_4304_; 
v_a_4301_ = lean_array_fget_borrowed(v_as_4295_, v_i_4297_);
v_b_4302_ = lean_array_fget_borrowed(v_bs_4296_, v_i_4297_);
lean_inc_ref(v_inst_4294_);
lean_inc(v_b_4302_);
lean_inc(v_a_4301_);
v___x_4303_ = lean_apply_2(v_inst_4294_, v_a_4301_, v_b_4302_);
v___x_4304_ = lean_unbox(v___x_4303_);
if (v___x_4304_ == 0)
{
uint8_t v___x_4305_; 
lean_dec(v_i_4297_);
lean_dec_ref(v_inst_4294_);
v___x_4305_ = lean_unbox(v___x_4303_);
return v___x_4305_;
}
else
{
lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4306_ = lean_unsigned_to_nat(1u);
v___x_4307_ = lean_nat_add(v_i_4297_, v___x_4306_);
lean_dec(v_i_4297_);
v_i_4297_ = v___x_4307_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___redArg___boxed(lean_object* v_inst_4309_, lean_object* v_as_4310_, lean_object* v_bs_4311_, lean_object* v_i_4312_){
_start:
{
uint8_t v_res_4313_; lean_object* v_r_4314_; 
v_res_4313_ = l_Array_isPrefixOfAux___redArg(v_inst_4309_, v_as_4310_, v_bs_4311_, v_i_4312_);
lean_dec_ref(v_bs_4311_);
lean_dec_ref(v_as_4310_);
v_r_4314_ = lean_box(v_res_4313_);
return v_r_4314_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux(lean_object* v_00_u03b1_4315_, lean_object* v_inst_4316_, lean_object* v_as_4317_, lean_object* v_bs_4318_, lean_object* v_hle_4319_, lean_object* v_i_4320_){
_start:
{
uint8_t v___x_4321_; 
v___x_4321_ = l_Array_isPrefixOfAux___redArg(v_inst_4316_, v_as_4317_, v_bs_4318_, v_i_4320_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___boxed(lean_object* v_00_u03b1_4322_, lean_object* v_inst_4323_, lean_object* v_as_4324_, lean_object* v_bs_4325_, lean_object* v_hle_4326_, lean_object* v_i_4327_){
_start:
{
uint8_t v_res_4328_; lean_object* v_r_4329_; 
v_res_4328_ = l_Array_isPrefixOfAux(v_00_u03b1_4322_, v_inst_4323_, v_as_4324_, v_bs_4325_, v_hle_4326_, v_i_4327_);
lean_dec_ref(v_bs_4325_);
lean_dec_ref(v_as_4324_);
v_r_4329_ = lean_box(v_res_4328_);
return v_r_4329_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf___redArg(lean_object* v_inst_4330_, lean_object* v_as_4331_, lean_object* v_bs_4332_){
_start:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; uint8_t v___x_4335_; 
v___x_4333_ = lean_array_get_size(v_as_4331_);
v___x_4334_ = lean_array_get_size(v_bs_4332_);
v___x_4335_ = lean_nat_dec_le(v___x_4333_, v___x_4334_);
if (v___x_4335_ == 0)
{
lean_dec_ref(v_inst_4330_);
return v___x_4335_;
}
else
{
lean_object* v___x_4336_; uint8_t v___x_4337_; 
v___x_4336_ = lean_unsigned_to_nat(0u);
v___x_4337_ = l_Array_isPrefixOfAux___redArg(v_inst_4330_, v_as_4331_, v_bs_4332_, v___x_4336_);
return v___x_4337_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___redArg___boxed(lean_object* v_inst_4338_, lean_object* v_as_4339_, lean_object* v_bs_4340_){
_start:
{
uint8_t v_res_4341_; lean_object* v_r_4342_; 
v_res_4341_ = l_Array_isPrefixOf___redArg(v_inst_4338_, v_as_4339_, v_bs_4340_);
lean_dec_ref(v_bs_4340_);
lean_dec_ref(v_as_4339_);
v_r_4342_ = lean_box(v_res_4341_);
return v_r_4342_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf(lean_object* v_00_u03b1_4343_, lean_object* v_inst_4344_, lean_object* v_as_4345_, lean_object* v_bs_4346_){
_start:
{
uint8_t v___x_4347_; 
v___x_4347_ = l_Array_isPrefixOf___redArg(v_inst_4344_, v_as_4345_, v_bs_4346_);
return v___x_4347_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___boxed(lean_object* v_00_u03b1_4348_, lean_object* v_inst_4349_, lean_object* v_as_4350_, lean_object* v_bs_4351_){
_start:
{
uint8_t v_res_4352_; lean_object* v_r_4353_; 
v_res_4352_ = l_Array_isPrefixOf(v_00_u03b1_4348_, v_inst_4349_, v_as_4350_, v_bs_4351_);
lean_dec_ref(v_bs_4351_);
lean_dec_ref(v_as_4350_);
v_r_4353_ = lean_box(v_res_4352_);
return v_r_4353_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0___boxed(lean_object* v_i_4354_, lean_object* v_cs_4355_, lean_object* v_inst_4356_, lean_object* v_as_4357_, lean_object* v_bs_4358_, lean_object* v_f_4359_, lean_object* v_____do__lift_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l_Array_zipWithMAux___redArg___lam__0(v_i_4354_, v_cs_4355_, v_inst_4356_, v_as_4357_, v_bs_4358_, v_f_4359_, v_____do__lift_4360_);
lean_dec(v_i_4354_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg(lean_object* v_inst_4362_, lean_object* v_as_4363_, lean_object* v_bs_4364_, lean_object* v_f_4365_, lean_object* v_i_4366_, lean_object* v_cs_4367_){
_start:
{
lean_object* v_toApplicative_4368_; lean_object* v_toBind_4369_; lean_object* v_toPure_4370_; lean_object* v___x_4371_; uint8_t v___x_4372_; 
v_toApplicative_4368_ = lean_ctor_get(v_inst_4362_, 0);
v_toBind_4369_ = lean_ctor_get(v_inst_4362_, 1);
lean_inc(v_toBind_4369_);
v_toPure_4370_ = lean_ctor_get(v_toApplicative_4368_, 1);
v___x_4371_ = lean_array_get_size(v_as_4363_);
v___x_4372_ = lean_nat_dec_lt(v_i_4366_, v___x_4371_);
if (v___x_4372_ == 0)
{
lean_object* v___x_4373_; 
lean_inc(v_toPure_4370_);
lean_dec(v_toBind_4369_);
lean_dec(v_i_4366_);
lean_dec(v_f_4365_);
lean_dec_ref(v_bs_4364_);
lean_dec_ref(v_as_4363_);
lean_dec_ref(v_inst_4362_);
v___x_4373_ = lean_apply_2(v_toPure_4370_, lean_box(0), v_cs_4367_);
return v___x_4373_;
}
else
{
lean_object* v___x_4374_; uint8_t v___x_4375_; 
v___x_4374_ = lean_array_get_size(v_bs_4364_);
v___x_4375_ = lean_nat_dec_lt(v_i_4366_, v___x_4374_);
if (v___x_4375_ == 0)
{
lean_object* v___x_4376_; 
lean_inc(v_toPure_4370_);
lean_dec(v_toBind_4369_);
lean_dec(v_i_4366_);
lean_dec(v_f_4365_);
lean_dec_ref(v_bs_4364_);
lean_dec_ref(v_as_4363_);
lean_dec_ref(v_inst_4362_);
v___x_4376_ = lean_apply_2(v_toPure_4370_, lean_box(0), v_cs_4367_);
return v___x_4376_;
}
else
{
lean_object* v___f_4377_; lean_object* v_a_4378_; lean_object* v_b_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
lean_inc(v_f_4365_);
lean_inc_ref(v_bs_4364_);
lean_inc_ref(v_as_4363_);
lean_inc(v_i_4366_);
v___f_4377_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4377_, 0, v_i_4366_);
lean_closure_set(v___f_4377_, 1, v_cs_4367_);
lean_closure_set(v___f_4377_, 2, v_inst_4362_);
lean_closure_set(v___f_4377_, 3, v_as_4363_);
lean_closure_set(v___f_4377_, 4, v_bs_4364_);
lean_closure_set(v___f_4377_, 5, v_f_4365_);
v_a_4378_ = lean_array_fget(v_as_4363_, v_i_4366_);
lean_dec_ref(v_as_4363_);
v_b_4379_ = lean_array_fget(v_bs_4364_, v_i_4366_);
lean_dec(v_i_4366_);
lean_dec_ref(v_bs_4364_);
v___x_4380_ = lean_apply_2(v_f_4365_, v_a_4378_, v_b_4379_);
v___x_4381_ = lean_apply_4(v_toBind_4369_, lean_box(0), lean_box(0), v___x_4380_, v___f_4377_);
return v___x_4381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0(lean_object* v_i_4382_, lean_object* v_cs_4383_, lean_object* v_inst_4384_, lean_object* v_as_4385_, lean_object* v_bs_4386_, lean_object* v_f_4387_, lean_object* v_____do__lift_4388_){
_start:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4389_ = lean_unsigned_to_nat(1u);
v___x_4390_ = lean_nat_add(v_i_4382_, v___x_4389_);
v___x_4391_ = lean_array_push(v_cs_4383_, v_____do__lift_4388_);
v___x_4392_ = l_Array_zipWithMAux___redArg(v_inst_4384_, v_as_4385_, v_bs_4386_, v_f_4387_, v___x_4390_, v___x_4391_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux(lean_object* v_00_u03b1_4393_, lean_object* v_00_u03b2_4394_, lean_object* v_00_u03b3_4395_, lean_object* v_m_4396_, lean_object* v_inst_4397_, lean_object* v_as_4398_, lean_object* v_bs_4399_, lean_object* v_f_4400_, lean_object* v_i_4401_, lean_object* v_cs_4402_){
_start:
{
lean_object* v___x_4403_; 
v___x_4403_ = l_Array_zipWithMAux___redArg(v_inst_4397_, v_as_4398_, v_bs_4399_, v_f_4400_, v_i_4401_, v_cs_4402_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith___redArg(lean_object* v_f_4404_, lean_object* v_as_4405_, lean_object* v_bs_4406_){
_start:
{
lean_object* v___f_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___f_4407_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4407_, 0, v_f_4404_);
v___x_4408_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4409_ = lean_unsigned_to_nat(0u);
v___x_4410_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4411_ = l_Array_zipWithMAux___redArg(v___x_4408_, v_as_4405_, v_bs_4406_, v___f_4407_, v___x_4409_, v___x_4410_);
return v___x_4411_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith(lean_object* v_00_u03b1_4412_, lean_object* v_00_u03b2_4413_, lean_object* v_00_u03b3_4414_, lean_object* v_f_4415_, lean_object* v_as_4416_, lean_object* v_bs_4417_){
_start:
{
lean_object* v___f_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___f_4418_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4418_, 0, v_f_4415_);
v___x_4419_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4420_ = lean_unsigned_to_nat(0u);
v___x_4421_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4422_ = l_Array_zipWithMAux___redArg(v___x_4419_, v_as_4416_, v_bs_4417_, v___f_4418_, v___x_4420_, v___x_4421_);
return v___x_4422_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(lean_object* v_as_4423_, lean_object* v_bs_4424_, lean_object* v_i_4425_, lean_object* v_cs_4426_){
_start:
{
lean_object* v___x_4427_; uint8_t v___x_4428_; 
v___x_4427_ = lean_array_get_size(v_as_4423_);
v___x_4428_ = lean_nat_dec_lt(v_i_4425_, v___x_4427_);
if (v___x_4428_ == 0)
{
lean_dec(v_i_4425_);
return v_cs_4426_;
}
else
{
lean_object* v___x_4429_; uint8_t v___x_4430_; 
v___x_4429_ = lean_array_get_size(v_bs_4424_);
v___x_4430_ = lean_nat_dec_lt(v_i_4425_, v___x_4429_);
if (v___x_4430_ == 0)
{
lean_dec(v_i_4425_);
return v_cs_4426_;
}
else
{
lean_object* v_a_4431_; lean_object* v_b_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v_a_4431_ = lean_array_fget_borrowed(v_as_4423_, v_i_4425_);
v_b_4432_ = lean_array_fget_borrowed(v_bs_4424_, v_i_4425_);
lean_inc(v_b_4432_);
lean_inc(v_a_4431_);
v___x_4433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4433_, 0, v_a_4431_);
lean_ctor_set(v___x_4433_, 1, v_b_4432_);
v___x_4434_ = lean_unsigned_to_nat(1u);
v___x_4435_ = lean_nat_add(v_i_4425_, v___x_4434_);
lean_dec(v_i_4425_);
v___x_4436_ = lean_array_push(v_cs_4426_, v___x_4433_);
v_i_4425_ = v___x_4435_;
v_cs_4426_ = v___x_4436_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg___boxed(lean_object* v_as_4438_, lean_object* v_bs_4439_, lean_object* v_i_4440_, lean_object* v_cs_4441_){
_start:
{
lean_object* v_res_4442_; 
v_res_4442_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4438_, v_bs_4439_, v_i_4440_, v_cs_4441_);
lean_dec_ref(v_bs_4439_);
lean_dec_ref(v_as_4438_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg(lean_object* v_as_4445_, lean_object* v_bs_4446_){
_start:
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4447_ = lean_unsigned_to_nat(0u);
v___x_4448_ = ((lean_object*)(l_Array_zip___redArg___closed__0));
v___x_4449_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4445_, v_bs_4446_, v___x_4447_, v___x_4448_);
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg___boxed(lean_object* v_as_4450_, lean_object* v_bs_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l_Array_zip___redArg(v_as_4450_, v_bs_4451_);
lean_dec_ref(v_bs_4451_);
lean_dec_ref(v_as_4450_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l_Array_zip(lean_object* v_00_u03b1_4453_, lean_object* v_00_u03b2_4454_, lean_object* v_as_4455_, lean_object* v_bs_4456_){
_start:
{
lean_object* v___x_4457_; 
v___x_4457_ = l_Array_zip___redArg(v_as_4455_, v_bs_4456_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___boxed(lean_object* v_00_u03b1_4458_, lean_object* v_00_u03b2_4459_, lean_object* v_as_4460_, lean_object* v_bs_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l_Array_zip(v_00_u03b1_4458_, v_00_u03b2_4459_, v_as_4460_, v_bs_4461_);
lean_dec_ref(v_bs_4461_);
lean_dec_ref(v_as_4460_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0(lean_object* v_00_u03b1_4463_, lean_object* v_00_u03b2_4464_, lean_object* v_as_4465_, lean_object* v_bs_4466_, lean_object* v_i_4467_, lean_object* v_cs_4468_){
_start:
{
lean_object* v___x_4469_; 
v___x_4469_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4465_, v_bs_4466_, v_i_4467_, v_cs_4468_);
return v___x_4469_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___boxed(lean_object* v_00_u03b1_4470_, lean_object* v_00_u03b2_4471_, lean_object* v_as_4472_, lean_object* v_bs_4473_, lean_object* v_i_4474_, lean_object* v_cs_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l_Array_zipWithMAux___at___00Array_zip_spec__0(v_00_u03b1_4470_, v_00_u03b2_4471_, v_as_4472_, v_bs_4473_, v_i_4474_, v_cs_4475_);
lean_dec_ref(v_bs_4473_);
lean_dec_ref(v_as_4472_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(lean_object* v_f_4477_, lean_object* v_as_4478_, lean_object* v_bs_4479_, lean_object* v_i_4480_, lean_object* v_cs_4481_){
_start:
{
lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4491_; lean_object* v___y_4498_; lean_object* v___x_4505_; lean_object* v___x_4506_; uint8_t v___x_4507_; 
v___x_4505_ = lean_array_get_size(v_as_4478_);
v___x_4506_ = lean_array_get_size(v_bs_4479_);
v___x_4507_ = lean_nat_dec_le(v___x_4505_, v___x_4506_);
if (v___x_4507_ == 0)
{
v___y_4498_ = v___x_4505_;
goto v___jp_4497_;
}
else
{
v___y_4498_ = v___x_4506_;
goto v___jp_4497_;
}
v___jp_4482_:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4485_ = lean_unsigned_to_nat(1u);
v___x_4486_ = lean_nat_add(v_i_4480_, v___x_4485_);
lean_dec(v_i_4480_);
lean_inc(v_f_4477_);
v___x_4487_ = lean_apply_2(v_f_4477_, v___y_4483_, v___y_4484_);
v___x_4488_ = lean_array_push(v_cs_4481_, v___x_4487_);
v_i_4480_ = v___x_4486_;
v_cs_4481_ = v___x_4488_;
goto _start;
}
v___jp_4490_:
{
lean_object* v___x_4492_; uint8_t v___x_4493_; 
v___x_4492_ = lean_array_get_size(v_bs_4479_);
v___x_4493_ = lean_nat_dec_lt(v_i_4480_, v___x_4492_);
if (v___x_4493_ == 0)
{
lean_object* v___x_4494_; 
v___x_4494_ = lean_box(0);
v___y_4483_ = v___y_4491_;
v___y_4484_ = v___x_4494_;
goto v___jp_4482_;
}
else
{
lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4495_ = lean_array_fget_borrowed(v_bs_4479_, v_i_4480_);
lean_inc(v___x_4495_);
v___x_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
v___y_4483_ = v___y_4491_;
v___y_4484_ = v___x_4496_;
goto v___jp_4482_;
}
}
v___jp_4497_:
{
uint8_t v___x_4499_; 
v___x_4499_ = lean_nat_dec_lt(v_i_4480_, v___y_4498_);
lean_dec(v___y_4498_);
if (v___x_4499_ == 0)
{
lean_dec(v_i_4480_);
lean_dec(v_f_4477_);
return v_cs_4481_;
}
else
{
lean_object* v___x_4500_; uint8_t v___x_4501_; 
v___x_4500_ = lean_array_get_size(v_as_4478_);
v___x_4501_ = lean_nat_dec_lt(v_i_4480_, v___x_4500_);
if (v___x_4501_ == 0)
{
lean_object* v___x_4502_; 
v___x_4502_ = lean_box(0);
v___y_4491_ = v___x_4502_;
goto v___jp_4490_;
}
else
{
lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4503_ = lean_array_fget_borrowed(v_as_4478_, v_i_4480_);
lean_inc(v___x_4503_);
v___x_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4503_);
v___y_4491_ = v___x_4504_;
goto v___jp_4490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg___boxed(lean_object* v_f_4508_, lean_object* v_as_4509_, lean_object* v_bs_4510_, lean_object* v_i_4511_, lean_object* v_cs_4512_){
_start:
{
lean_object* v_res_4513_; 
v_res_4513_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4508_, v_as_4509_, v_bs_4510_, v_i_4511_, v_cs_4512_);
lean_dec_ref(v_bs_4510_);
lean_dec_ref(v_as_4509_);
return v_res_4513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(lean_object* v_00_u03b1_4514_, lean_object* v_00_u03b2_4515_, lean_object* v_00_u03b3_4516_, lean_object* v_f_4517_, lean_object* v_as_4518_, lean_object* v_bs_4519_, lean_object* v_i_4520_, lean_object* v_cs_4521_){
_start:
{
lean_object* v___x_4522_; 
v___x_4522_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4517_, v_as_4518_, v_bs_4519_, v_i_4520_, v_cs_4521_);
return v___x_4522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___boxed(lean_object* v_00_u03b1_4523_, lean_object* v_00_u03b2_4524_, lean_object* v_00_u03b3_4525_, lean_object* v_f_4526_, lean_object* v_as_4527_, lean_object* v_bs_4528_, lean_object* v_i_4529_, lean_object* v_cs_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(v_00_u03b1_4523_, v_00_u03b2_4524_, v_00_u03b3_4525_, v_f_4526_, v_as_4527_, v_bs_4528_, v_i_4529_, v_cs_4530_);
lean_dec_ref(v_bs_4528_);
lean_dec_ref(v_as_4527_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg(lean_object* v_f_4532_, lean_object* v_as_4533_, lean_object* v_bs_4534_){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4535_ = lean_unsigned_to_nat(0u);
v___x_4536_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4537_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4532_, v_as_4533_, v_bs_4534_, v___x_4535_, v___x_4536_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg___boxed(lean_object* v_f_4538_, lean_object* v_as_4539_, lean_object* v_bs_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l_Array_zipWithAll___redArg(v_f_4538_, v_as_4539_, v_bs_4540_);
lean_dec_ref(v_bs_4540_);
lean_dec_ref(v_as_4539_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll(lean_object* v_00_u03b1_4542_, lean_object* v_00_u03b2_4543_, lean_object* v_00_u03b3_4544_, lean_object* v_f_4545_, lean_object* v_as_4546_, lean_object* v_bs_4547_){
_start:
{
lean_object* v___x_4548_; 
v___x_4548_ = l_Array_zipWithAll___redArg(v_f_4545_, v_as_4546_, v_bs_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___boxed(lean_object* v_00_u03b1_4549_, lean_object* v_00_u03b2_4550_, lean_object* v_00_u03b3_4551_, lean_object* v_f_4552_, lean_object* v_as_4553_, lean_object* v_bs_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l_Array_zipWithAll(v_00_u03b1_4549_, v_00_u03b2_4550_, v_00_u03b3_4551_, v_f_4552_, v_as_4553_, v_bs_4554_);
lean_dec_ref(v_bs_4554_);
lean_dec_ref(v_as_4553_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM___redArg(lean_object* v_inst_4556_, lean_object* v_f_4557_, lean_object* v_as_4558_, lean_object* v_bs_4559_){
_start:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4560_ = lean_unsigned_to_nat(0u);
v___x_4561_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4562_ = l_Array_zipWithMAux___redArg(v_inst_4556_, v_as_4558_, v_bs_4559_, v_f_4557_, v___x_4560_, v___x_4561_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM(lean_object* v_00_u03b1_4563_, lean_object* v_00_u03b2_4564_, lean_object* v_00_u03b3_4565_, lean_object* v_m_4566_, lean_object* v_inst_4567_, lean_object* v_f_4568_, lean_object* v_as_4569_, lean_object* v_bs_4570_){
_start:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4571_ = lean_unsigned_to_nat(0u);
v___x_4572_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4573_ = l_Array_zipWithMAux___redArg(v_inst_4567_, v_as_4569_, v_bs_4570_, v_f_4568_, v___x_4571_, v___x_4572_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(lean_object* v_as_4574_, size_t v_i_4575_, size_t v_stop_4576_, lean_object* v_b_4577_){
_start:
{
uint8_t v___x_4578_; 
v___x_4578_ = lean_usize_dec_eq(v_i_4575_, v_stop_4576_);
if (v___x_4578_ == 0)
{
lean_object* v_fst_4579_; lean_object* v_snd_4580_; lean_object* v___x_4581_; lean_object* v_fst_4582_; lean_object* v_snd_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4595_; 
v_fst_4579_ = lean_ctor_get(v_b_4577_, 0);
lean_inc(v_fst_4579_);
v_snd_4580_ = lean_ctor_get(v_b_4577_, 1);
lean_inc(v_snd_4580_);
lean_dec_ref(v_b_4577_);
v___x_4581_ = lean_array_uget(v_as_4574_, v_i_4575_);
v_fst_4582_ = lean_ctor_get(v___x_4581_, 0);
v_snd_4583_ = lean_ctor_get(v___x_4581_, 1);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4585_ = v___x_4581_;
v_isShared_4586_ = v_isSharedCheck_4595_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_snd_4583_);
lean_inc(v_fst_4582_);
lean_dec(v___x_4581_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4595_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4590_; 
v___x_4587_ = lean_array_push(v_fst_4579_, v_fst_4582_);
v___x_4588_ = lean_array_push(v_snd_4580_, v_snd_4583_);
if (v_isShared_4586_ == 0)
{
lean_ctor_set(v___x_4585_, 1, v___x_4588_);
lean_ctor_set(v___x_4585_, 0, v___x_4587_);
v___x_4590_ = v___x_4585_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v___x_4587_);
lean_ctor_set(v_reuseFailAlloc_4594_, 1, v___x_4588_);
v___x_4590_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
size_t v___x_4591_; size_t v___x_4592_; 
v___x_4591_ = ((size_t)1ULL);
v___x_4592_ = lean_usize_add(v_i_4575_, v___x_4591_);
v_i_4575_ = v___x_4592_;
v_b_4577_ = v___x_4590_;
goto _start;
}
}
}
else
{
return v_b_4577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg___boxed(lean_object* v_as_4596_, lean_object* v_i_4597_, lean_object* v_stop_4598_, lean_object* v_b_4599_){
_start:
{
size_t v_i_boxed_4600_; size_t v_stop_boxed_4601_; lean_object* v_res_4602_; 
v_i_boxed_4600_ = lean_unbox_usize(v_i_4597_);
lean_dec(v_i_4597_);
v_stop_boxed_4601_ = lean_unbox_usize(v_stop_4598_);
lean_dec(v_stop_4598_);
v_res_4602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4596_, v_i_boxed_4600_, v_stop_boxed_4601_, v_b_4599_);
lean_dec_ref(v_as_4596_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg(lean_object* v_as_4603_){
_start:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; uint8_t v___x_4607_; 
v___x_4604_ = lean_unsigned_to_nat(0u);
v___x_4605_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v___x_4606_ = lean_array_get_size(v_as_4603_);
v___x_4607_ = lean_nat_dec_lt(v___x_4604_, v___x_4606_);
if (v___x_4607_ == 0)
{
return v___x_4605_;
}
else
{
uint8_t v___x_4608_; 
v___x_4608_ = lean_nat_dec_le(v___x_4606_, v___x_4606_);
if (v___x_4608_ == 0)
{
if (v___x_4607_ == 0)
{
return v___x_4605_;
}
else
{
size_t v___x_4609_; size_t v___x_4610_; lean_object* v___x_4611_; 
v___x_4609_ = ((size_t)0ULL);
v___x_4610_ = lean_usize_of_nat(v___x_4606_);
v___x_4611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4603_, v___x_4609_, v___x_4610_, v___x_4605_);
return v___x_4611_;
}
}
else
{
size_t v___x_4612_; size_t v___x_4613_; lean_object* v___x_4614_; 
v___x_4612_ = ((size_t)0ULL);
v___x_4613_ = lean_usize_of_nat(v___x_4606_);
v___x_4614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4603_, v___x_4612_, v___x_4613_, v___x_4605_);
return v___x_4614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg___boxed(lean_object* v_as_4615_){
_start:
{
lean_object* v_res_4616_; 
v_res_4616_ = l_Array_unzip___redArg(v_as_4615_);
lean_dec_ref(v_as_4615_);
return v_res_4616_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip(lean_object* v_00_u03b1_4617_, lean_object* v_00_u03b2_4618_, lean_object* v_as_4619_){
_start:
{
lean_object* v___x_4620_; 
v___x_4620_ = l_Array_unzip___redArg(v_as_4619_);
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___boxed(lean_object* v_00_u03b1_4621_, lean_object* v_00_u03b2_4622_, lean_object* v_as_4623_){
_start:
{
lean_object* v_res_4624_; 
v_res_4624_ = l_Array_unzip(v_00_u03b1_4621_, v_00_u03b2_4622_, v_as_4623_);
lean_dec_ref(v_as_4623_);
return v_res_4624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(lean_object* v_00_u03b1_4625_, lean_object* v_00_u03b2_4626_, lean_object* v_as_4627_, size_t v_i_4628_, size_t v_stop_4629_, lean_object* v_b_4630_){
_start:
{
lean_object* v___x_4631_; 
v___x_4631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4627_, v_i_4628_, v_stop_4629_, v_b_4630_);
return v___x_4631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___boxed(lean_object* v_00_u03b1_4632_, lean_object* v_00_u03b2_4633_, lean_object* v_as_4634_, lean_object* v_i_4635_, lean_object* v_stop_4636_, lean_object* v_b_4637_){
_start:
{
size_t v_i_boxed_4638_; size_t v_stop_boxed_4639_; lean_object* v_res_4640_; 
v_i_boxed_4638_ = lean_unbox_usize(v_i_4635_);
lean_dec(v_i_4635_);
v_stop_boxed_4639_ = lean_unbox_usize(v_stop_4636_);
lean_dec(v_stop_4636_);
v_res_4640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(v_00_u03b1_4632_, v_00_u03b2_4633_, v_as_4634_, v_i_boxed_4638_, v_stop_boxed_4639_, v_b_4637_);
lean_dec_ref(v_as_4634_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l_Array_replace___redArg(lean_object* v_inst_4641_, lean_object* v_xs_4642_, lean_object* v_a_4643_, lean_object* v_b_4644_){
_start:
{
lean_object* v___x_4645_; 
v___x_4645_ = l_Array_finIdxOf_x3f___redArg(v_inst_4641_, v_xs_4642_, v_a_4643_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_dec(v_b_4644_);
return v_xs_4642_;
}
else
{
lean_object* v_val_4646_; lean_object* v___x_4647_; 
v_val_4646_ = lean_ctor_get(v___x_4645_, 0);
lean_inc(v_val_4646_);
lean_dec_ref_known(v___x_4645_, 1);
v___x_4647_ = lean_array_fset(v_xs_4642_, v_val_4646_, v_b_4644_);
lean_dec(v_val_4646_);
return v___x_4647_;
}
}
}
LEAN_EXPORT lean_object* l_Array_replace(lean_object* v_00_u03b1_4648_, lean_object* v_inst_4649_, lean_object* v_xs_4650_, lean_object* v_a_4651_, lean_object* v_b_4652_){
_start:
{
lean_object* v___x_4653_; 
v___x_4653_ = l_Array_replace___redArg(v_inst_4649_, v_xs_4650_, v_a_4651_, v_b_4652_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Array_instLT___redArg(){
_start:
{
lean_object* v___x_4655_; 
v___x_4655_ = lean_box(0);
return v___x_4655_;
}
}
LEAN_EXPORT lean_object* l_Array_instLT___redArg___boxed(lean_object* v___dummy_4656_){
_start:
{
lean_object* v_res_4657_; 
v_res_4657_ = l_Array_instLT___redArg();
return v_res_4657_;
}
}
LEAN_EXPORT lean_object* l_Array_instLT(lean_object* v_00_u03b1_4658_, lean_object* v_inst_4659_){
_start:
{
lean_object* v___x_4660_; 
v___x_4660_ = lean_box(0);
return v___x_4660_;
}
}
LEAN_EXPORT lean_object* l_Array_instLE___redArg(){
_start:
{
lean_object* v___x_4662_; 
v___x_4662_ = lean_box(0);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Array_instLE___redArg___boxed(lean_object* v___dummy_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Array_instLE___redArg();
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_Array_instLE(lean_object* v_00_u03b1_4665_, lean_object* v_inst_4666_){
_start:
{
lean_object* v___x_4667_; 
v___x_4667_ = lean_box(0);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg(lean_object* v_n_4668_, lean_object* v_a_4669_, lean_object* v_xs_4670_){
_start:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4671_ = lean_array_get_size(v_xs_4670_);
v___x_4672_ = lean_nat_sub(v_n_4668_, v___x_4671_);
v___x_4673_ = lean_mk_array(v___x_4672_, v_a_4669_);
v___x_4674_ = l_Array_append___redArg(v___x_4673_, v_xs_4670_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg___boxed(lean_object* v_n_4675_, lean_object* v_a_4676_, lean_object* v_xs_4677_){
_start:
{
lean_object* v_res_4678_; 
v_res_4678_ = l_Array_leftpad___redArg(v_n_4675_, v_a_4676_, v_xs_4677_);
lean_dec_ref(v_xs_4677_);
lean_dec(v_n_4675_);
return v_res_4678_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad(lean_object* v_00_u03b1_4679_, lean_object* v_n_4680_, lean_object* v_a_4681_, lean_object* v_xs_4682_){
_start:
{
lean_object* v___x_4683_; 
v___x_4683_ = l_Array_leftpad___redArg(v_n_4680_, v_a_4681_, v_xs_4682_);
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___boxed(lean_object* v_00_u03b1_4684_, lean_object* v_n_4685_, lean_object* v_a_4686_, lean_object* v_xs_4687_){
_start:
{
lean_object* v_res_4688_; 
v_res_4688_ = l_Array_leftpad(v_00_u03b1_4684_, v_n_4685_, v_a_4686_, v_xs_4687_);
lean_dec_ref(v_xs_4687_);
lean_dec(v_n_4685_);
return v_res_4688_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg(lean_object* v_n_4689_, lean_object* v_a_4690_, lean_object* v_xs_4691_){
_start:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4692_ = lean_array_get_size(v_xs_4691_);
v___x_4693_ = lean_nat_sub(v_n_4689_, v___x_4692_);
v___x_4694_ = lean_mk_array(v___x_4693_, v_a_4690_);
v___x_4695_ = l_Array_append___redArg(v_xs_4691_, v___x_4694_);
lean_dec_ref(v___x_4694_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg___boxed(lean_object* v_n_4696_, lean_object* v_a_4697_, lean_object* v_xs_4698_){
_start:
{
lean_object* v_res_4699_; 
v_res_4699_ = l_Array_rightpad___redArg(v_n_4696_, v_a_4697_, v_xs_4698_);
lean_dec(v_n_4696_);
return v_res_4699_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad(lean_object* v_00_u03b1_4700_, lean_object* v_n_4701_, lean_object* v_a_4702_, lean_object* v_xs_4703_){
_start:
{
lean_object* v___x_4704_; 
v___x_4704_ = l_Array_rightpad___redArg(v_n_4701_, v_a_4702_, v_xs_4703_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___boxed(lean_object* v_00_u03b1_4705_, lean_object* v_n_4706_, lean_object* v_a_4707_, lean_object* v_xs_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l_Array_rightpad(v_00_u03b1_4705_, v_n_4706_, v_a_4707_, v_xs_4708_);
lean_dec(v_n_4706_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0(lean_object* v_x_4710_){
_start:
{
lean_inc(v_x_4710_);
return v_x_4710_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0___boxed(lean_object* v_x_4711_){
_start:
{
lean_object* v_res_4712_; 
v_res_4712_ = l_Array_reduceOption___redArg___lam__0(v_x_4711_);
lean_dec(v_x_4711_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg(lean_object* v_as_4714_){
_start:
{
lean_object* v___f_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; 
v___f_4715_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4716_ = lean_unsigned_to_nat(0u);
v___x_4717_ = lean_array_get_size(v_as_4714_);
v___x_4718_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4719_ = l_Array_filterMapM___redArg(v___x_4718_, v___f_4715_, v_as_4714_, v___x_4716_, v___x_4717_);
return v___x_4719_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption(lean_object* v_00_u03b1_4720_, lean_object* v_as_4721_){
_start:
{
lean_object* v___f_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; 
v___f_4722_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4723_ = lean_unsigned_to_nat(0u);
v___x_4724_ = lean_array_get_size(v_as_4721_);
v___x_4725_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4726_ = l_Array_filterMapM___redArg(v___x_4725_, v___f_4722_, v_as_4721_, v___x_4723_, v___x_4724_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg___lam__0(lean_object* v_inst_4727_, lean_object* v_x1_4728_, lean_object* v_x2_4729_){
_start:
{
lean_object* v_fst_4730_; lean_object* v_snd_4731_; lean_object* v___x_4732_; uint8_t v___x_4733_; 
v_fst_4730_ = lean_ctor_get(v_x1_4728_, 0);
v_snd_4731_ = lean_ctor_get(v_x1_4728_, 1);
lean_inc(v_fst_4730_);
lean_inc(v_x2_4729_);
v___x_4732_ = lean_apply_2(v_inst_4727_, v_x2_4729_, v_fst_4730_);
v___x_4733_ = lean_unbox(v___x_4732_);
if (v___x_4733_ == 0)
{
lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4741_; 
lean_inc(v_snd_4731_);
lean_inc(v_fst_4730_);
v_isSharedCheck_4741_ = !lean_is_exclusive(v_x1_4728_);
if (v_isSharedCheck_4741_ == 0)
{
lean_object* v_unused_4742_; lean_object* v_unused_4743_; 
v_unused_4742_ = lean_ctor_get(v_x1_4728_, 1);
lean_dec(v_unused_4742_);
v_unused_4743_ = lean_ctor_get(v_x1_4728_, 0);
lean_dec(v_unused_4743_);
v___x_4735_ = v_x1_4728_;
v_isShared_4736_ = v_isSharedCheck_4741_;
goto v_resetjp_4734_;
}
else
{
lean_dec(v_x1_4728_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4741_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4737_; lean_object* v___x_4739_; 
v___x_4737_ = lean_array_push(v_snd_4731_, v_fst_4730_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 1, v___x_4737_);
lean_ctor_set(v___x_4735_, 0, v_x2_4729_);
v___x_4739_ = v___x_4735_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_x2_4729_);
lean_ctor_set(v_reuseFailAlloc_4740_, 1, v___x_4737_);
v___x_4739_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
return v___x_4739_;
}
}
}
else
{
lean_dec(v_x2_4729_);
return v_x1_4728_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg(lean_object* v_inst_4744_, lean_object* v_as_4745_){
_start:
{
lean_object* v___y_4747_; lean_object* v___x_4751_; lean_object* v___x_4752_; uint8_t v___x_4753_; 
v___x_4751_ = lean_unsigned_to_nat(0u);
v___x_4752_ = lean_array_get_size(v_as_4745_);
v___x_4753_ = lean_nat_dec_lt(v___x_4751_, v___x_4752_);
if (v___x_4753_ == 0)
{
lean_object* v___x_4754_; 
lean_dec_ref(v_as_4745_);
lean_dec_ref(v_inst_4744_);
v___x_4754_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
return v___x_4754_;
}
else
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; 
v___x_4755_ = lean_array_fget_borrowed(v_as_4745_, v___x_4751_);
v___x_4756_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4757_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
if (v___x_4753_ == 0)
{
lean_object* v___x_4758_; 
lean_inc(v___x_4755_);
lean_dec_ref(v_as_4745_);
lean_dec_ref(v_inst_4744_);
v___x_4758_ = lean_array_push(v___x_4756_, v___x_4755_);
return v___x_4758_;
}
else
{
lean_object* v___f_4759_; lean_object* v___x_4760_; uint8_t v___x_4761_; 
v___f_4759_ = lean_alloc_closure((void*)(l_Array_eraseReps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4759_, 0, v_inst_4744_);
lean_inc(v___x_4755_);
v___x_4760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4755_);
lean_ctor_set(v___x_4760_, 1, v___x_4756_);
v___x_4761_ = lean_nat_dec_le(v___x_4752_, v___x_4752_);
if (v___x_4761_ == 0)
{
if (v___x_4753_ == 0)
{
lean_object* v___x_4762_; 
lean_inc(v___x_4755_);
lean_dec_ref_known(v___x_4760_, 2);
lean_dec_ref(v___f_4759_);
lean_dec_ref(v_as_4745_);
v___x_4762_ = lean_array_push(v___x_4756_, v___x_4755_);
return v___x_4762_;
}
else
{
size_t v___x_4763_; size_t v___x_4764_; lean_object* v___x_4765_; 
v___x_4763_ = ((size_t)0ULL);
v___x_4764_ = lean_usize_of_nat(v___x_4752_);
v___x_4765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4757_, v___f_4759_, v_as_4745_, v___x_4763_, v___x_4764_, v___x_4760_);
v___y_4747_ = v___x_4765_;
goto v___jp_4746_;
}
}
else
{
size_t v___x_4766_; size_t v___x_4767_; lean_object* v___x_4768_; 
v___x_4766_ = ((size_t)0ULL);
v___x_4767_ = lean_usize_of_nat(v___x_4752_);
v___x_4768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4757_, v___f_4759_, v_as_4745_, v___x_4766_, v___x_4767_, v___x_4760_);
v___y_4747_ = v___x_4768_;
goto v___jp_4746_;
}
}
}
v___jp_4746_:
{
lean_object* v_fst_4748_; lean_object* v_snd_4749_; lean_object* v___x_4750_; 
v_fst_4748_ = lean_ctor_get(v___y_4747_, 0);
lean_inc(v_fst_4748_);
v_snd_4749_ = lean_ctor_get(v___y_4747_, 1);
lean_inc(v_snd_4749_);
lean_dec_ref(v___y_4747_);
v___x_4750_ = lean_array_push(v_snd_4749_, v_fst_4748_);
return v___x_4750_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps(lean_object* v_00_u03b1_4769_, lean_object* v_inst_4770_, lean_object* v_as_4771_){
_start:
{
lean_object* v___x_4772_; 
v___x_4772_ = l_Array_eraseReps___redArg(v_inst_4770_, v_as_4771_);
return v___x_4772_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(lean_object* v_inst_4773_, lean_object* v_as_4774_, lean_object* v_a_4775_, lean_object* v_x_4776_){
_start:
{
lean_object* v_zero_4777_; uint8_t v_isZero_4778_; 
v_zero_4777_ = lean_unsigned_to_nat(0u);
v_isZero_4778_ = lean_nat_dec_eq(v_x_4776_, v_zero_4777_);
if (v_isZero_4778_ == 1)
{
lean_dec(v_x_4776_);
lean_dec(v_a_4775_);
lean_dec_ref(v_inst_4773_);
return v_isZero_4778_;
}
else
{
lean_object* v_one_4779_; lean_object* v_n_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; uint8_t v___x_4783_; 
v_one_4779_ = lean_unsigned_to_nat(1u);
v_n_4780_ = lean_nat_sub(v_x_4776_, v_one_4779_);
lean_dec(v_x_4776_);
v___x_4781_ = lean_array_fget_borrowed(v_as_4774_, v_n_4780_);
lean_inc_ref(v_inst_4773_);
lean_inc(v___x_4781_);
lean_inc(v_a_4775_);
v___x_4782_ = lean_apply_2(v_inst_4773_, v_a_4775_, v___x_4781_);
v___x_4783_ = lean_unbox(v___x_4782_);
if (v___x_4783_ == 0)
{
v_x_4776_ = v_n_4780_;
goto _start;
}
else
{
lean_dec(v_n_4780_);
lean_dec(v_a_4775_);
lean_dec_ref(v_inst_4773_);
return v_isZero_4778_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg___boxed(lean_object* v_inst_4785_, lean_object* v_as_4786_, lean_object* v_a_4787_, lean_object* v_x_4788_){
_start:
{
uint8_t v_res_4789_; lean_object* v_r_4790_; 
v_res_4789_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4785_, v_as_4786_, v_a_4787_, v_x_4788_);
lean_dec_ref(v_as_4786_);
v_r_4790_ = lean_box(v_res_4789_);
return v_r_4790_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(lean_object* v_00_u03b1_4791_, lean_object* v_inst_4792_, lean_object* v_as_4793_, lean_object* v_a_4794_, lean_object* v_x_4795_, lean_object* v_x_4796_){
_start:
{
uint8_t v___x_4797_; 
v___x_4797_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4792_, v_as_4793_, v_a_4794_, v_x_4795_);
return v___x_4797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___boxed(lean_object* v_00_u03b1_4798_, lean_object* v_inst_4799_, lean_object* v_as_4800_, lean_object* v_a_4801_, lean_object* v_x_4802_, lean_object* v_x_4803_){
_start:
{
uint8_t v_res_4804_; lean_object* v_r_4805_; 
v_res_4804_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(v_00_u03b1_4798_, v_inst_4799_, v_as_4800_, v_a_4801_, v_x_4802_, v_x_4803_);
lean_dec_ref(v_as_4800_);
v_r_4805_ = lean_box(v_res_4804_);
return v_r_4805_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(lean_object* v_inst_4806_, lean_object* v_as_4807_, lean_object* v_i_4808_){
_start:
{
lean_object* v___x_4809_; uint8_t v___x_4810_; 
v___x_4809_ = lean_array_get_size(v_as_4807_);
v___x_4810_ = lean_nat_dec_lt(v_i_4808_, v___x_4809_);
if (v___x_4810_ == 0)
{
uint8_t v___x_4811_; 
lean_dec(v_i_4808_);
lean_dec_ref(v_inst_4806_);
v___x_4811_ = 1;
return v___x_4811_;
}
else
{
lean_object* v___x_4812_; uint8_t v___x_4813_; 
v___x_4812_ = lean_array_fget_borrowed(v_as_4807_, v_i_4808_);
lean_inc(v_i_4808_);
lean_inc(v___x_4812_);
lean_inc_ref(v_inst_4806_);
v___x_4813_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4806_, v_as_4807_, v___x_4812_, v_i_4808_);
if (v___x_4813_ == 0)
{
lean_dec(v_i_4808_);
lean_dec_ref(v_inst_4806_);
return v___x_4813_;
}
else
{
lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4814_ = lean_unsigned_to_nat(1u);
v___x_4815_ = lean_nat_add(v_i_4808_, v___x_4814_);
lean_dec(v_i_4808_);
v_i_4808_ = v___x_4815_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg___boxed(lean_object* v_inst_4817_, lean_object* v_as_4818_, lean_object* v_i_4819_){
_start:
{
uint8_t v_res_4820_; lean_object* v_r_4821_; 
v_res_4820_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4817_, v_as_4818_, v_i_4819_);
lean_dec_ref(v_as_4818_);
v_r_4821_ = lean_box(v_res_4820_);
return v_r_4821_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux(lean_object* v_00_u03b1_4822_, lean_object* v_inst_4823_, lean_object* v_as_4824_, lean_object* v_i_4825_){
_start:
{
uint8_t v___x_4826_; 
v___x_4826_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4823_, v_as_4824_, v_i_4825_);
return v___x_4826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___boxed(lean_object* v_00_u03b1_4827_, lean_object* v_inst_4828_, lean_object* v_as_4829_, lean_object* v_i_4830_){
_start:
{
uint8_t v_res_4831_; lean_object* v_r_4832_; 
v_res_4831_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux(v_00_u03b1_4827_, v_inst_4828_, v_as_4829_, v_i_4830_);
lean_dec_ref(v_as_4829_);
v_r_4832_ = lean_box(v_res_4831_);
return v_r_4832_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___redArg(lean_object* v_inst_4833_, lean_object* v_as_4834_){
_start:
{
lean_object* v___x_4835_; uint8_t v___x_4836_; 
v___x_4835_ = lean_unsigned_to_nat(0u);
v___x_4836_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4833_, v_as_4834_, v___x_4835_);
return v___x_4836_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___redArg___boxed(lean_object* v_inst_4837_, lean_object* v_as_4838_){
_start:
{
uint8_t v_res_4839_; lean_object* v_r_4840_; 
v_res_4839_ = l_Array_allDiff___redArg(v_inst_4837_, v_as_4838_);
lean_dec_ref(v_as_4838_);
v_r_4840_ = lean_box(v_res_4839_);
return v_r_4840_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff(lean_object* v_00_u03b1_4841_, lean_object* v_inst_4842_, lean_object* v_as_4843_){
_start:
{
uint8_t v___x_4844_; 
v___x_4844_ = l_Array_allDiff___redArg(v_inst_4842_, v_as_4843_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___boxed(lean_object* v_00_u03b1_4845_, lean_object* v_inst_4846_, lean_object* v_as_4847_){
_start:
{
uint8_t v_res_4848_; lean_object* v_r_4849_; 
v_res_4848_ = l_Array_allDiff(v_00_u03b1_4845_, v_inst_4846_, v_as_4847_);
lean_dec_ref(v_as_4847_);
v_r_4849_ = lean_box(v_res_4848_);
return v_r_4849_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0(uint8_t v___x_4850_, lean_object* v_x1_4851_, lean_object* v_x2_4852_){
_start:
{
lean_object* v_fst_4853_; uint8_t v___x_4854_; 
v_fst_4853_ = lean_ctor_get(v_x1_4851_, 0);
v___x_4854_ = lean_unbox(v_fst_4853_);
if (v___x_4854_ == 0)
{
lean_object* v_snd_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4863_; 
lean_dec(v_x2_4852_);
v_snd_4855_ = lean_ctor_get(v_x1_4851_, 1);
v_isSharedCheck_4863_ = !lean_is_exclusive(v_x1_4851_);
if (v_isSharedCheck_4863_ == 0)
{
lean_object* v_unused_4864_; 
v_unused_4864_ = lean_ctor_get(v_x1_4851_, 0);
lean_dec(v_unused_4864_);
v___x_4857_ = v_x1_4851_;
v_isShared_4858_ = v_isSharedCheck_4863_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_snd_4855_);
lean_dec(v_x1_4851_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4863_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v___x_4859_; lean_object* v___x_4861_; 
v___x_4859_ = lean_box(v___x_4850_);
if (v_isShared_4858_ == 0)
{
lean_ctor_set(v___x_4857_, 0, v___x_4859_);
v___x_4861_ = v___x_4857_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v___x_4859_);
lean_ctor_set(v_reuseFailAlloc_4862_, 1, v_snd_4855_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
else
{
lean_object* v_snd_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4875_; 
v_snd_4865_ = lean_ctor_get(v_x1_4851_, 1);
v_isSharedCheck_4875_ = !lean_is_exclusive(v_x1_4851_);
if (v_isSharedCheck_4875_ == 0)
{
lean_object* v_unused_4876_; 
v_unused_4876_ = lean_ctor_get(v_x1_4851_, 0);
lean_dec(v_unused_4876_);
v___x_4867_ = v_x1_4851_;
v_isShared_4868_ = v_isSharedCheck_4875_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_snd_4865_);
lean_dec(v_x1_4851_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4875_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
uint8_t v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4873_; 
v___x_4869_ = 0;
v___x_4870_ = lean_array_push(v_snd_4865_, v_x2_4852_);
v___x_4871_ = lean_box(v___x_4869_);
if (v_isShared_4868_ == 0)
{
lean_ctor_set(v___x_4867_, 1, v___x_4870_);
lean_ctor_set(v___x_4867_, 0, v___x_4871_);
v___x_4873_ = v___x_4867_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v___x_4871_);
lean_ctor_set(v_reuseFailAlloc_4874_, 1, v___x_4870_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0___boxed(lean_object* v___x_4877_, lean_object* v_x1_4878_, lean_object* v_x2_4879_){
_start:
{
uint8_t v___x_141__boxed_4880_; lean_object* v_res_4881_; 
v___x_141__boxed_4880_ = lean_unbox(v___x_4877_);
v_res_4881_ = l_Array_getEvenElems___redArg___lam__0(v___x_141__boxed_4880_, v_x1_4878_, v_x2_4879_);
return v_res_4881_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg(lean_object* v_as_4882_){
_start:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; uint8_t v___x_4887_; 
v___x_4883_ = lean_unsigned_to_nat(0u);
v___x_4884_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
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
LEAN_EXPORT lean_object* l_Array_getEvenElems(lean_object* v_00_u03b1_4901_, lean_object* v_as_4902_){
_start:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; uint8_t v___x_4907_; 
v___x_4903_ = lean_unsigned_to_nat(0u);
v___x_4904_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_4905_ = lean_array_get_size(v_as_4902_);
v___x_4906_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4907_ = lean_nat_dec_lt(v___x_4903_, v___x_4905_);
if (v___x_4907_ == 0)
{
lean_dec_ref(v_as_4902_);
return v___x_4904_;
}
else
{
lean_object* v___x_4908_; lean_object* v___f_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; uint8_t v___x_4912_; 
v___x_4908_ = lean_box(v___x_4907_);
v___f_4909_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4909_, 0, v___x_4908_);
v___x_4910_ = lean_box(v___x_4907_);
v___x_4911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4911_, 0, v___x_4910_);
lean_ctor_set(v___x_4911_, 1, v___x_4904_);
v___x_4912_ = lean_nat_dec_le(v___x_4905_, v___x_4905_);
if (v___x_4912_ == 0)
{
if (v___x_4907_ == 0)
{
lean_dec_ref_known(v___x_4911_, 2);
lean_dec_ref(v___f_4909_);
lean_dec_ref(v_as_4902_);
return v___x_4904_;
}
else
{
size_t v___x_4913_; size_t v___x_4914_; lean_object* v___x_4915_; lean_object* v_snd_4916_; 
v___x_4913_ = ((size_t)0ULL);
v___x_4914_ = lean_usize_of_nat(v___x_4905_);
v___x_4915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4906_, v___f_4909_, v_as_4902_, v___x_4913_, v___x_4914_, v___x_4911_);
v_snd_4916_ = lean_ctor_get(v___x_4915_, 1);
lean_inc(v_snd_4916_);
lean_dec(v___x_4915_);
return v_snd_4916_;
}
}
else
{
size_t v___x_4917_; size_t v___x_4918_; lean_object* v___x_4919_; lean_object* v_snd_4920_; 
v___x_4917_ = ((size_t)0ULL);
v___x_4918_ = lean_usize_of_nat(v___x_4905_);
v___x_4919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4906_, v___f_4909_, v_as_4902_, v___x_4917_, v___x_4918_, v___x_4911_);
v_snd_4920_ = lean_ctor_get(v___x_4919_, 1);
lean_inc(v_snd_4920_);
lean_dec(v___x_4919_);
return v_snd_4920_;
}
}
}
}
static lean_object* _init_l_Array_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_4926_; lean_object* v___x_4927_; 
v___x_4926_ = ((lean_object*)(l_term_x23_x5b___x2c_x5d___closed__4));
v___x_4927_ = lean_string_length(v___x_4926_);
return v___x_4927_;
}
}
static lean_object* _init_l_Array_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; 
v___x_4928_ = lean_obj_once(&l_Array_repr___redArg___closed__2, &l_Array_repr___redArg___closed__2_once, _init_l_Array_repr___redArg___closed__2);
v___x_4929_ = lean_nat_to_int(v___x_4928_);
return v___x_4929_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___redArg(lean_object* v_inst_4937_, lean_object* v_xs_4938_){
_start:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; uint8_t v___x_4941_; 
v___x_4939_ = lean_array_get_size(v_xs_4938_);
v___x_4940_ = lean_unsigned_to_nat(0u);
v___x_4941_ = lean_nat_dec_eq(v___x_4939_, v___x_4940_);
if (v___x_4941_ == 0)
{
lean_object* v_x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
v_x_4942_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_4942_, 0, lean_box(0));
lean_closure_set(v_x_4942_, 1, v_inst_4937_);
v___x_4943_ = lean_array_to_list(v_xs_4938_);
v___x_4944_ = ((lean_object*)(l_Array_repr___redArg___closed__1));
v___x_4945_ = l_Std_Format_joinSep___redArg(v_x_4942_, v___x_4943_, v___x_4944_);
v___x_4946_ = lean_obj_once(&l_Array_repr___redArg___closed__3, &l_Array_repr___redArg___closed__3_once, _init_l_Array_repr___redArg___closed__3);
v___x_4947_ = ((lean_object*)(l_Array_repr___redArg___closed__4));
v___x_4948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4947_);
lean_ctor_set(v___x_4948_, 1, v___x_4945_);
v___x_4949_ = ((lean_object*)(l_Array_repr___redArg___closed__5));
v___x_4950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4948_);
lean_ctor_set(v___x_4950_, 1, v___x_4949_);
v___x_4951_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4951_, 0, v___x_4946_);
lean_ctor_set(v___x_4951_, 1, v___x_4950_);
v___x_4952_ = l_Std_Format_fill(v___x_4951_);
return v___x_4952_;
}
else
{
lean_object* v___x_4953_; 
lean_dec_ref(v_xs_4938_);
lean_dec_ref(v_inst_4937_);
v___x_4953_ = ((lean_object*)(l_Array_repr___redArg___closed__7));
return v___x_4953_;
}
}
}
LEAN_EXPORT lean_object* l_Array_repr(lean_object* v_00_u03b1_4954_, lean_object* v_inst_4955_, lean_object* v_xs_4956_){
_start:
{
lean_object* v___x_4957_; 
v___x_4957_ = l_Array_repr___redArg(v_inst_4955_, v_xs_4956_);
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0(lean_object* v_inst_4958_, lean_object* v_xs_4959_, lean_object* v_x_4960_){
_start:
{
lean_object* v___x_4961_; 
v___x_4961_ = l_Array_repr___redArg(v_inst_4958_, v_xs_4959_);
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object* v_inst_4962_, lean_object* v_xs_4963_, lean_object* v_x_4964_){
_start:
{
lean_object* v_res_4965_; 
v_res_4965_ = l_Array_instRepr___redArg___lam__0(v_inst_4962_, v_xs_4963_, v_x_4964_);
lean_dec(v_x_4964_);
return v_res_4965_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg(lean_object* v_inst_4966_){
_start:
{
lean_object* v___f_4967_; 
v___f_4967_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4967_, 0, v_inst_4966_);
return v___f_4967_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr(lean_object* v_00_u03b1_4968_, lean_object* v_inst_4969_){
_start:
{
lean_object* v___f_4970_; 
v___f_4970_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4970_, 0, v_inst_4969_);
return v___f_4970_;
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
