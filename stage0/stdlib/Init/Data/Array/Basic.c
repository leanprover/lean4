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
lean_object* v___f_2346_; size_t v___x_2347_; size_t v___x_2348_; lean_object* v___x_2349_; 
v___f_2346_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2346_, 0, v_f_2338_);
v___x_2347_ = ((size_t)0ULL);
v___x_2348_ = lean_usize_of_nat(v___x_2342_);
v___x_2349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2336_, v___f_2346_, v_xs_2337_, v___x_2347_, v___x_2348_, v___x_2343_);
return v___x_2349_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg(lean_object* v_inst_2350_){
_start:
{
lean_object* v___f_2351_; 
v___f_2351_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2351_, 0, v_inst_2350_);
return v___f_2351_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad(lean_object* v_00_u03b1_2352_, lean_object* v_m_2353_, lean_object* v_inst_2354_){
_start:
{
lean_object* v___f_2355_; 
v___f_2355_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2355_, 0, v_inst_2354_);
return v___f_2355_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___lam__0(lean_object* v_f_2356_, lean_object* v_a_2357_, lean_object* v_x_2358_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_apply_1(v_f_2356_, v_a_2357_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg(lean_object* v_inst_2360_, lean_object* v_f_2361_, lean_object* v_as_2362_, lean_object* v_start_2363_, lean_object* v_stop_2364_){
_start:
{
lean_object* v_toApplicative_2365_; lean_object* v_toPure_2366_; lean_object* v___f_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; 
v_toApplicative_2365_ = lean_ctor_get(v_inst_2360_, 0);
v_toPure_2366_ = lean_ctor_get(v_toApplicative_2365_, 1);
v___f_2367_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2367_, 0, v_f_2361_);
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_array_get_size(v_as_2362_);
v___x_2370_ = lean_nat_dec_le(v_start_2363_, v___x_2369_);
if (v___x_2370_ == 0)
{
uint8_t v___x_2371_; 
v___x_2371_ = lean_nat_dec_lt(v_stop_2364_, v___x_2369_);
if (v___x_2371_ == 0)
{
lean_object* v___x_2372_; 
lean_inc(v_toPure_2366_);
lean_dec_ref(v___f_2367_);
lean_dec_ref(v_as_2362_);
lean_dec_ref(v_inst_2360_);
v___x_2372_ = lean_apply_2(v_toPure_2366_, lean_box(0), v___x_2368_);
return v___x_2372_;
}
else
{
size_t v___x_2373_; size_t v___x_2374_; lean_object* v___x_2375_; 
v___x_2373_ = lean_usize_of_nat(v___x_2369_);
v___x_2374_ = lean_usize_of_nat(v_stop_2364_);
v___x_2375_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2360_, v___f_2367_, v_as_2362_, v___x_2373_, v___x_2374_, v___x_2368_);
return v___x_2375_;
}
}
else
{
uint8_t v___x_2376_; 
v___x_2376_ = lean_nat_dec_lt(v_stop_2364_, v_start_2363_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; 
lean_inc(v_toPure_2366_);
lean_dec_ref(v___f_2367_);
lean_dec_ref(v_as_2362_);
lean_dec_ref(v_inst_2360_);
v___x_2377_ = lean_apply_2(v_toPure_2366_, lean_box(0), v___x_2368_);
return v___x_2377_;
}
else
{
size_t v___x_2378_; size_t v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = lean_usize_of_nat(v_start_2363_);
v___x_2379_ = lean_usize_of_nat(v_stop_2364_);
v___x_2380_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2360_, v___f_2367_, v_as_2362_, v___x_2378_, v___x_2379_, v___x_2368_);
return v___x_2380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___boxed(lean_object* v_inst_2381_, lean_object* v_f_2382_, lean_object* v_as_2383_, lean_object* v_start_2384_, lean_object* v_stop_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Array_forRevM___redArg(v_inst_2381_, v_f_2382_, v_as_2383_, v_start_2384_, v_stop_2385_);
lean_dec(v_stop_2385_);
lean_dec(v_start_2384_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM(lean_object* v_00_u03b1_2387_, lean_object* v_m_2388_, lean_object* v_inst_2389_, lean_object* v_f_2390_, lean_object* v_as_2391_, lean_object* v_start_2392_, lean_object* v_stop_2393_){
_start:
{
lean_object* v_toApplicative_2394_; lean_object* v_toPure_2395_; lean_object* v___f_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v_toApplicative_2394_ = lean_ctor_get(v_inst_2389_, 0);
v_toPure_2395_ = lean_ctor_get(v_toApplicative_2394_, 1);
v___f_2396_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2396_, 0, v_f_2390_);
v___x_2397_ = lean_box(0);
v___x_2398_ = lean_array_get_size(v_as_2391_);
v___x_2399_ = lean_nat_dec_le(v_start_2392_, v___x_2398_);
if (v___x_2399_ == 0)
{
uint8_t v___x_2400_; 
v___x_2400_ = lean_nat_dec_lt(v_stop_2393_, v___x_2398_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; 
lean_inc(v_toPure_2395_);
lean_dec_ref(v___f_2396_);
lean_dec_ref(v_as_2391_);
lean_dec_ref(v_inst_2389_);
v___x_2401_ = lean_apply_2(v_toPure_2395_, lean_box(0), v___x_2397_);
return v___x_2401_;
}
else
{
size_t v___x_2402_; size_t v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = lean_usize_of_nat(v___x_2398_);
v___x_2403_ = lean_usize_of_nat(v_stop_2393_);
v___x_2404_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2389_, v___f_2396_, v_as_2391_, v___x_2402_, v___x_2403_, v___x_2397_);
return v___x_2404_;
}
}
else
{
uint8_t v___x_2405_; 
v___x_2405_ = lean_nat_dec_lt(v_stop_2393_, v_start_2392_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; 
lean_inc(v_toPure_2395_);
lean_dec_ref(v___f_2396_);
lean_dec_ref(v_as_2391_);
lean_dec_ref(v_inst_2389_);
v___x_2406_ = lean_apply_2(v_toPure_2395_, lean_box(0), v___x_2397_);
return v___x_2406_;
}
else
{
size_t v___x_2407_; size_t v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = lean_usize_of_nat(v_start_2392_);
v___x_2408_ = lean_usize_of_nat(v_stop_2393_);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2389_, v___f_2396_, v_as_2391_, v___x_2407_, v___x_2408_, v___x_2397_);
return v___x_2409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___boxed(lean_object* v_00_u03b1_2410_, lean_object* v_m_2411_, lean_object* v_inst_2412_, lean_object* v_f_2413_, lean_object* v_as_2414_, lean_object* v_start_2415_, lean_object* v_stop_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Array_forRevM(v_00_u03b1_2410_, v_m_2411_, v_inst_2412_, v_f_2413_, v_as_2414_, v_start_2415_, v_stop_2416_);
lean_dec(v_stop_2416_);
lean_dec(v_start_2415_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___lam__0(lean_object* v_f_2418_, lean_object* v_x1_2419_, lean_object* v_x2_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_apply_2(v_f_2418_, v_x1_2419_, v_x2_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg(lean_object* v_f_2441_, lean_object* v_init_2442_, lean_object* v_as_2443_, lean_object* v_start_2444_, lean_object* v_stop_2445_){
_start:
{
lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2446_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2447_ = lean_nat_dec_lt(v_start_2444_, v_stop_2445_);
if (v___x_2447_ == 0)
{
lean_dec_ref(v_as_2443_);
lean_dec(v_f_2441_);
return v_init_2442_;
}
else
{
lean_object* v___f_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___f_2448_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2448_, 0, v_f_2441_);
v___x_2449_ = lean_array_get_size(v_as_2443_);
v___x_2450_ = lean_nat_dec_le(v_stop_2445_, v___x_2449_);
if (v___x_2450_ == 0)
{
uint8_t v___x_2451_; 
v___x_2451_ = lean_nat_dec_lt(v_start_2444_, v___x_2449_);
if (v___x_2451_ == 0)
{
lean_dec_ref(v___f_2448_);
lean_dec_ref(v_as_2443_);
return v_init_2442_;
}
else
{
size_t v___x_2452_; size_t v___x_2453_; lean_object* v___x_2454_; 
v___x_2452_ = lean_usize_of_nat(v_start_2444_);
v___x_2453_ = lean_usize_of_nat(v___x_2449_);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2446_, v___f_2448_, v_as_2443_, v___x_2452_, v___x_2453_, v_init_2442_);
return v___x_2454_;
}
}
else
{
size_t v___x_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = lean_usize_of_nat(v_start_2444_);
v___x_2456_ = lean_usize_of_nat(v_stop_2445_);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2446_, v___f_2448_, v_as_2443_, v___x_2455_, v___x_2456_, v_init_2442_);
return v___x_2457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___boxed(lean_object* v_f_2458_, lean_object* v_init_2459_, lean_object* v_as_2460_, lean_object* v_start_2461_, lean_object* v_stop_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Array_foldl___redArg(v_f_2458_, v_init_2459_, v_as_2460_, v_start_2461_, v_stop_2462_);
lean_dec(v_stop_2462_);
lean_dec(v_start_2461_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl(lean_object* v_00_u03b1_2464_, lean_object* v_00_u03b2_2465_, lean_object* v_f_2466_, lean_object* v_init_2467_, lean_object* v_as_2468_, lean_object* v_start_2469_, lean_object* v_stop_2470_){
_start:
{
lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2471_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2472_ = lean_nat_dec_lt(v_start_2469_, v_stop_2470_);
if (v___x_2472_ == 0)
{
lean_dec_ref(v_as_2468_);
lean_dec(v_f_2466_);
return v_init_2467_;
}
else
{
lean_object* v___f_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___f_2473_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2473_, 0, v_f_2466_);
v___x_2474_ = lean_array_get_size(v_as_2468_);
v___x_2475_ = lean_nat_dec_le(v_stop_2470_, v___x_2474_);
if (v___x_2475_ == 0)
{
uint8_t v___x_2476_; 
v___x_2476_ = lean_nat_dec_lt(v_start_2469_, v___x_2474_);
if (v___x_2476_ == 0)
{
lean_dec_ref(v___f_2473_);
lean_dec_ref(v_as_2468_);
return v_init_2467_;
}
else
{
size_t v___x_2477_; size_t v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = lean_usize_of_nat(v_start_2469_);
v___x_2478_ = lean_usize_of_nat(v___x_2474_);
v___x_2479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2471_, v___f_2473_, v_as_2468_, v___x_2477_, v___x_2478_, v_init_2467_);
return v___x_2479_;
}
}
else
{
size_t v___x_2480_; size_t v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = lean_usize_of_nat(v_start_2469_);
v___x_2481_ = lean_usize_of_nat(v_stop_2470_);
v___x_2482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2471_, v___f_2473_, v_as_2468_, v___x_2480_, v___x_2481_, v_init_2467_);
return v___x_2482_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___boxed(lean_object* v_00_u03b1_2483_, lean_object* v_00_u03b2_2484_, lean_object* v_f_2485_, lean_object* v_init_2486_, lean_object* v_as_2487_, lean_object* v_start_2488_, lean_object* v_stop_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Array_foldl(v_00_u03b1_2483_, v_00_u03b2_2484_, v_f_2485_, v_init_2486_, v_as_2487_, v_start_2488_, v_stop_2489_);
lean_dec(v_stop_2489_);
lean_dec(v_start_2488_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg(lean_object* v_f_2491_, lean_object* v_init_2492_, lean_object* v_as_2493_, lean_object* v_start_2494_, lean_object* v_stop_2495_){
_start:
{
lean_object* v___f_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___f_2496_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2496_, 0, v_f_2491_);
v___x_2497_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2498_ = lean_array_get_size(v_as_2493_);
v___x_2499_ = lean_nat_dec_le(v_start_2494_, v___x_2498_);
if (v___x_2499_ == 0)
{
uint8_t v___x_2500_; 
v___x_2500_ = lean_nat_dec_lt(v_stop_2495_, v___x_2498_);
if (v___x_2500_ == 0)
{
lean_dec_ref(v___f_2496_);
lean_dec_ref(v_as_2493_);
return v_init_2492_;
}
else
{
size_t v___x_2501_; size_t v___x_2502_; lean_object* v___x_2503_; 
v___x_2501_ = lean_usize_of_nat(v___x_2498_);
v___x_2502_ = lean_usize_of_nat(v_stop_2495_);
v___x_2503_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2497_, v___f_2496_, v_as_2493_, v___x_2501_, v___x_2502_, v_init_2492_);
return v___x_2503_;
}
}
else
{
uint8_t v___x_2504_; 
v___x_2504_ = lean_nat_dec_lt(v_stop_2495_, v_start_2494_);
if (v___x_2504_ == 0)
{
lean_dec_ref(v___f_2496_);
lean_dec_ref(v_as_2493_);
return v_init_2492_;
}
else
{
size_t v___x_2505_; size_t v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = lean_usize_of_nat(v_start_2494_);
v___x_2506_ = lean_usize_of_nat(v_stop_2495_);
v___x_2507_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2497_, v___f_2496_, v_as_2493_, v___x_2505_, v___x_2506_, v_init_2492_);
return v___x_2507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg___boxed(lean_object* v_f_2508_, lean_object* v_init_2509_, lean_object* v_as_2510_, lean_object* v_start_2511_, lean_object* v_stop_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Array_foldr___redArg(v_f_2508_, v_init_2509_, v_as_2510_, v_start_2511_, v_stop_2512_);
lean_dec(v_stop_2512_);
lean_dec(v_start_2511_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr(lean_object* v_00_u03b1_2514_, lean_object* v_00_u03b2_2515_, lean_object* v_f_2516_, lean_object* v_init_2517_, lean_object* v_as_2518_, lean_object* v_start_2519_, lean_object* v_stop_2520_){
_start:
{
lean_object* v___f_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___f_2521_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2521_, 0, v_f_2516_);
v___x_2522_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2523_ = lean_array_get_size(v_as_2518_);
v___x_2524_ = lean_nat_dec_le(v_start_2519_, v___x_2523_);
if (v___x_2524_ == 0)
{
uint8_t v___x_2525_; 
v___x_2525_ = lean_nat_dec_lt(v_stop_2520_, v___x_2523_);
if (v___x_2525_ == 0)
{
lean_dec_ref(v___f_2521_);
lean_dec_ref(v_as_2518_);
return v_init_2517_;
}
else
{
size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = lean_usize_of_nat(v___x_2523_);
v___x_2527_ = lean_usize_of_nat(v_stop_2520_);
v___x_2528_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2522_, v___f_2521_, v_as_2518_, v___x_2526_, v___x_2527_, v_init_2517_);
return v___x_2528_;
}
}
else
{
uint8_t v___x_2529_; 
v___x_2529_ = lean_nat_dec_lt(v_stop_2520_, v_start_2519_);
if (v___x_2529_ == 0)
{
lean_dec_ref(v___f_2521_);
lean_dec_ref(v_as_2518_);
return v_init_2517_;
}
else
{
size_t v___x_2530_; size_t v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = lean_usize_of_nat(v_start_2519_);
v___x_2531_ = lean_usize_of_nat(v_stop_2520_);
v___x_2532_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2522_, v___f_2521_, v_as_2518_, v___x_2530_, v___x_2531_, v_init_2517_);
return v___x_2532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___boxed(lean_object* v_00_u03b1_2533_, lean_object* v_00_u03b2_2534_, lean_object* v_f_2535_, lean_object* v_init_2536_, lean_object* v_as_2537_, lean_object* v_start_2538_, lean_object* v_stop_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Array_foldr(v_00_u03b1_2533_, v_00_u03b2_2534_, v_f_2535_, v_init_2536_, v_as_2537_, v_start_2538_, v_stop_2539_);
lean_dec(v_stop_2539_);
lean_dec(v_start_2538_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg___lam__0(lean_object* v_inst_2541_, lean_object* v_x1_2542_, lean_object* v_x2_2543_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_apply_2(v_inst_2541_, v_x1_2542_, v_x2_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg(lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_as_2547_){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2548_ = lean_array_get_size(v_as_2547_);
v___x_2549_ = lean_unsigned_to_nat(0u);
v___x_2550_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2551_ = lean_nat_dec_lt(v___x_2549_, v___x_2548_);
if (v___x_2551_ == 0)
{
lean_dec_ref(v_as_2547_);
lean_dec(v_inst_2545_);
return v_inst_2546_;
}
else
{
lean_object* v___f_2552_; size_t v___x_2553_; size_t v___x_2554_; lean_object* v___x_2555_; 
v___f_2552_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2552_, 0, v_inst_2545_);
v___x_2553_ = lean_usize_of_nat(v___x_2548_);
v___x_2554_ = ((size_t)0ULL);
v___x_2555_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2550_, v___f_2552_, v_as_2547_, v___x_2553_, v___x_2554_, v_inst_2546_);
return v___x_2555_;
}
}
}
LEAN_EXPORT lean_object* l_Array_sum(lean_object* v_00_u03b1_2556_, lean_object* v_inst_2557_, lean_object* v_inst_2558_, lean_object* v_as_2559_){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; 
v___x_2560_ = lean_array_get_size(v_as_2559_);
v___x_2561_ = lean_unsigned_to_nat(0u);
v___x_2562_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2563_ = lean_nat_dec_lt(v___x_2561_, v___x_2560_);
if (v___x_2563_ == 0)
{
lean_dec_ref(v_as_2559_);
lean_dec(v_inst_2557_);
return v_inst_2558_;
}
else
{
lean_object* v___f_2564_; size_t v___x_2565_; size_t v___x_2566_; lean_object* v___x_2567_; 
v___f_2564_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2564_, 0, v_inst_2557_);
v___x_2565_ = lean_usize_of_nat(v___x_2560_);
v___x_2566_ = ((size_t)0ULL);
v___x_2567_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2562_, v___f_2564_, v_as_2559_, v___x_2565_, v___x_2566_, v_inst_2558_);
return v___x_2567_;
}
}
}
LEAN_EXPORT lean_object* l_Array_prod___redArg(lean_object* v_inst_2568_, lean_object* v_inst_2569_, lean_object* v_as_2570_){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; 
v___x_2571_ = lean_array_get_size(v_as_2570_);
v___x_2572_ = lean_unsigned_to_nat(0u);
v___x_2573_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2574_ = lean_nat_dec_lt(v___x_2572_, v___x_2571_);
if (v___x_2574_ == 0)
{
lean_dec_ref(v_as_2570_);
lean_dec(v_inst_2568_);
return v_inst_2569_;
}
else
{
lean_object* v___f_2575_; size_t v___x_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
v___f_2575_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2575_, 0, v_inst_2568_);
v___x_2576_ = lean_usize_of_nat(v___x_2571_);
v___x_2577_ = ((size_t)0ULL);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2573_, v___f_2575_, v_as_2570_, v___x_2576_, v___x_2577_, v_inst_2569_);
return v___x_2578_;
}
}
}
LEAN_EXPORT lean_object* l_Array_prod(lean_object* v_00_u03b1_2579_, lean_object* v_inst_2580_, lean_object* v_inst_2581_, lean_object* v_as_2582_){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v___x_2583_ = lean_array_get_size(v_as_2582_);
v___x_2584_ = lean_unsigned_to_nat(0u);
v___x_2585_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2586_ = lean_nat_dec_lt(v___x_2584_, v___x_2583_);
if (v___x_2586_ == 0)
{
lean_dec_ref(v_as_2582_);
lean_dec(v_inst_2580_);
return v_inst_2581_;
}
else
{
lean_object* v___f_2587_; size_t v___x_2588_; size_t v___x_2589_; lean_object* v___x_2590_; 
v___f_2587_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2587_, 0, v_inst_2580_);
v___x_2588_ = lean_usize_of_nat(v___x_2583_);
v___x_2589_ = ((size_t)0ULL);
v___x_2590_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2585_, v___f_2587_, v_as_2582_, v___x_2588_, v___x_2589_, v_inst_2581_);
return v___x_2590_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0(lean_object* v_p_2591_, lean_object* v_x1_2592_, lean_object* v_x2_2593_){
_start:
{
lean_object* v___x_2594_; uint8_t v___x_2595_; 
v___x_2594_ = lean_apply_1(v_p_2591_, v_x1_2592_);
v___x_2595_ = lean_unbox(v___x_2594_);
if (v___x_2595_ == 0)
{
lean_inc(v_x2_2593_);
return v_x2_2593_;
}
else
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_unsigned_to_nat(1u);
v___x_2597_ = lean_nat_add(v_x2_2593_, v___x_2596_);
return v___x_2597_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0___boxed(lean_object* v_p_2598_, lean_object* v_x1_2599_, lean_object* v_x2_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Array_countP___redArg___lam__0(v_p_2598_, v_x1_2599_, v_x2_2600_);
lean_dec(v_x2_2600_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg(lean_object* v_p_2602_, lean_object* v_as_2603_){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2604_ = lean_unsigned_to_nat(0u);
v___x_2605_ = lean_array_get_size(v_as_2603_);
v___x_2606_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2607_ = lean_nat_dec_lt(v___x_2604_, v___x_2605_);
if (v___x_2607_ == 0)
{
lean_dec_ref(v_as_2603_);
lean_dec_ref(v_p_2602_);
return v___x_2604_;
}
else
{
lean_object* v___f_2608_; size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___f_2608_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2608_, 0, v_p_2602_);
v___x_2609_ = lean_usize_of_nat(v___x_2605_);
v___x_2610_ = ((size_t)0ULL);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2606_, v___f_2608_, v_as_2603_, v___x_2609_, v___x_2610_, v___x_2604_);
return v___x_2611_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP(lean_object* v_00_u03b1_2612_, lean_object* v_p_2613_, lean_object* v_as_2614_){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2615_ = lean_unsigned_to_nat(0u);
v___x_2616_ = lean_array_get_size(v_as_2614_);
v___x_2617_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2618_ = lean_nat_dec_lt(v___x_2615_, v___x_2616_);
if (v___x_2618_ == 0)
{
lean_dec_ref(v_as_2614_);
lean_dec_ref(v_p_2613_);
return v___x_2615_;
}
else
{
lean_object* v___f_2619_; size_t v___x_2620_; size_t v___x_2621_; lean_object* v___x_2622_; 
v___f_2619_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2619_, 0, v_p_2613_);
v___x_2620_ = lean_usize_of_nat(v___x_2616_);
v___x_2621_ = ((size_t)0ULL);
v___x_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2617_, v___f_2619_, v_as_2614_, v___x_2620_, v___x_2621_, v___x_2615_);
return v___x_2622_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0(lean_object* v_inst_2623_, lean_object* v_a_2624_, lean_object* v_x1_2625_, lean_object* v_x2_2626_){
_start:
{
lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = lean_apply_2(v_inst_2623_, v_x1_2625_, v_a_2624_);
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
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0___boxed(lean_object* v_inst_2631_, lean_object* v_a_2632_, lean_object* v_x1_2633_, lean_object* v_x2_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Array_count___redArg___lam__0(v_inst_2631_, v_a_2632_, v_x1_2633_, v_x2_2634_);
lean_dec(v_x2_2634_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg(lean_object* v_inst_2636_, lean_object* v_a_2637_, lean_object* v_as_2638_){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2639_ = lean_unsigned_to_nat(0u);
v___x_2640_ = lean_array_get_size(v_as_2638_);
v___x_2641_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2642_ = lean_nat_dec_lt(v___x_2639_, v___x_2640_);
if (v___x_2642_ == 0)
{
lean_dec_ref(v_as_2638_);
lean_dec(v_a_2637_);
lean_dec_ref(v_inst_2636_);
return v___x_2639_;
}
else
{
lean_object* v___f_2643_; size_t v___x_2644_; size_t v___x_2645_; lean_object* v___x_2646_; 
v___f_2643_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2643_, 0, v_inst_2636_);
lean_closure_set(v___f_2643_, 1, v_a_2637_);
v___x_2644_ = lean_usize_of_nat(v___x_2640_);
v___x_2645_ = ((size_t)0ULL);
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2641_, v___f_2643_, v_as_2638_, v___x_2644_, v___x_2645_, v___x_2639_);
return v___x_2646_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count(lean_object* v_00_u03b1_2647_, lean_object* v_inst_2648_, lean_object* v_a_2649_, lean_object* v_as_2650_){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; 
v___x_2651_ = lean_unsigned_to_nat(0u);
v___x_2652_ = lean_array_get_size(v_as_2650_);
v___x_2653_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2654_ = lean_nat_dec_lt(v___x_2651_, v___x_2652_);
if (v___x_2654_ == 0)
{
lean_dec_ref(v_as_2650_);
lean_dec(v_a_2649_);
lean_dec_ref(v_inst_2648_);
return v___x_2651_;
}
else
{
lean_object* v___f_2655_; size_t v___x_2656_; size_t v___x_2657_; lean_object* v___x_2658_; 
v___f_2655_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2655_, 0, v_inst_2648_);
lean_closure_set(v___f_2655_, 1, v_a_2649_);
v___x_2656_ = lean_usize_of_nat(v___x_2652_);
v___x_2657_ = ((size_t)0ULL);
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2653_, v___f_2655_, v_as_2650_, v___x_2656_, v___x_2657_, v___x_2651_);
return v___x_2658_;
}
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg___lam__0(lean_object* v_f_2659_, lean_object* v_x_2660_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = lean_apply_1(v_f_2659_, v_x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg(lean_object* v_f_2662_, lean_object* v_as_2663_){
_start:
{
lean_object* v___f_2664_; lean_object* v___x_2665_; size_t v_sz_2666_; size_t v___x_2667_; lean_object* v___x_2668_; 
v___f_2664_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2664_, 0, v_f_2662_);
v___x_2665_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2666_ = lean_array_size(v_as_2663_);
v___x_2667_ = ((size_t)0ULL);
v___x_2668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2665_, v___f_2664_, v_sz_2666_, v___x_2667_, v_as_2663_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Array_map(lean_object* v_00_u03b1_2669_, lean_object* v_00_u03b2_2670_, lean_object* v_f_2671_, lean_object* v_as_2672_){
_start:
{
lean_object* v___f_2673_; lean_object* v___x_2674_; size_t v_sz_2675_; size_t v___x_2676_; lean_object* v___x_2677_; 
v___f_2673_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2673_, 0, v_f_2671_);
v___x_2674_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2675_ = lean_array_size(v_as_2672_);
v___x_2676_ = ((size_t)0ULL);
v___x_2677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2674_, v___f_2673_, v_sz_2675_, v___x_2676_, v_as_2672_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0(lean_object* v___y_2678_, lean_object* v_x_2679_){
_start:
{
lean_inc(v___y_2678_);
return v___y_2678_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0___boxed(lean_object* v___y_2680_, lean_object* v_x_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_Array_instFunctor___lam__0(v___y_2680_, v_x_2681_);
lean_dec(v_x_2681_);
lean_dec(v___y_2680_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__1(lean_object* v_00_u03b1_2683_, lean_object* v_00_u03b2_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v___f_2687_; lean_object* v___x_2688_; size_t v_sz_2689_; size_t v___x_2690_; lean_object* v___x_2691_; 
v___f_2687_ = lean_alloc_closure((void*)(l_Array_instFunctor___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2687_, 0, v___y_2685_);
v___x_2688_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2689_ = lean_array_size(v___y_2686_);
v___x_2690_ = ((size_t)0ULL);
v___x_2691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2688_, v___f_2687_, v_sz_2689_, v___x_2690_, v___y_2686_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg___lam__0(lean_object* v_f_2698_, lean_object* v_x1_2699_, lean_object* v_x2_2700_, lean_object* v_x3_2701_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = lean_apply_3(v_f_2698_, v_x1_2699_, v_x2_2700_, lean_box(0));
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg(lean_object* v_as_2703_, lean_object* v_f_2704_){
_start:
{
lean_object* v___f_2705_; lean_object* v___x_2706_; size_t v_sz_2707_; size_t v___x_2708_; lean_object* v___x_2709_; 
v___f_2705_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2705_, 0, v_f_2704_);
v___x_2706_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2707_ = lean_array_size(v_as_2703_);
v___x_2708_ = ((size_t)0ULL);
v___x_2709_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2706_, v___f_2705_, v_sz_2707_, v___x_2708_, v_as_2703_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx(lean_object* v_00_u03b1_2710_, lean_object* v_00_u03b2_2711_, lean_object* v_as_2712_, lean_object* v_f_2713_){
_start:
{
lean_object* v___f_2714_; lean_object* v___x_2715_; size_t v_sz_2716_; size_t v___x_2717_; lean_object* v___x_2718_; 
v___f_2714_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2714_, 0, v_f_2713_);
v___x_2715_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2716_ = lean_array_size(v_as_2712_);
v___x_2717_ = ((size_t)0ULL);
v___x_2718_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2715_, v___f_2714_, v_sz_2716_, v___x_2717_, v_as_2712_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx___redArg(lean_object* v_f_2719_, lean_object* v_as_2720_){
_start:
{
lean_object* v___f_2721_; lean_object* v___x_2722_; size_t v_sz_2723_; size_t v___x_2724_; lean_object* v___x_2725_; 
v___f_2721_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2721_, 0, v_f_2719_);
v___x_2722_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2723_ = lean_array_size(v_as_2720_);
v___x_2724_ = ((size_t)0ULL);
v___x_2725_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2722_, v___f_2721_, v_sz_2723_, v___x_2724_, v_as_2720_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx(lean_object* v_00_u03b1_2726_, lean_object* v_00_u03b2_2727_, lean_object* v_f_2728_, lean_object* v_as_2729_){
_start:
{
lean_object* v___f_2730_; lean_object* v___x_2731_; size_t v_sz_2732_; size_t v___x_2733_; lean_object* v___x_2734_; 
v___f_2730_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2730_, 0, v_f_2728_);
v___x_2731_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2732_ = lean_array_size(v_as_2729_);
v___x_2733_ = ((size_t)0ULL);
v___x_2734_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2731_, v___f_2730_, v_sz_2732_, v___x_2733_, v_as_2729_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(lean_object* v_start_2735_, size_t v_sz_2736_, size_t v_i_2737_, lean_object* v_bs_2738_){
_start:
{
uint8_t v___x_2739_; 
v___x_2739_ = lean_usize_dec_lt(v_i_2737_, v_sz_2736_);
if (v___x_2739_ == 0)
{
return v_bs_2738_;
}
else
{
lean_object* v_v_2740_; lean_object* v___x_2741_; lean_object* v_bs_x27_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; size_t v___x_2746_; size_t v___x_2747_; lean_object* v___x_2748_; 
v_v_2740_ = lean_array_uget(v_bs_2738_, v_i_2737_);
v___x_2741_ = lean_unsigned_to_nat(0u);
v_bs_x27_2742_ = lean_array_uset(v_bs_2738_, v_i_2737_, v___x_2741_);
v___x_2743_ = lean_usize_to_nat(v_i_2737_);
v___x_2744_ = lean_nat_add(v_start_2735_, v___x_2743_);
lean_dec(v___x_2743_);
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v_v_2740_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = ((size_t)1ULL);
v___x_2747_ = lean_usize_add(v_i_2737_, v___x_2746_);
v___x_2748_ = lean_array_uset(v_bs_x27_2742_, v_i_2737_, v___x_2745_);
v_i_2737_ = v___x_2747_;
v_bs_2738_ = v___x_2748_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg___boxed(lean_object* v_start_2750_, lean_object* v_sz_2751_, lean_object* v_i_2752_, lean_object* v_bs_2753_){
_start:
{
size_t v_sz_boxed_2754_; size_t v_i_boxed_2755_; lean_object* v_res_2756_; 
v_sz_boxed_2754_ = lean_unbox_usize(v_sz_2751_);
lean_dec(v_sz_2751_);
v_i_boxed_2755_ = lean_unbox_usize(v_i_2752_);
lean_dec(v_i_2752_);
v_res_2756_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2750_, v_sz_boxed_2754_, v_i_boxed_2755_, v_bs_2753_);
lean_dec(v_start_2750_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg(lean_object* v_xs_2757_, lean_object* v_start_2758_){
_start:
{
size_t v_sz_2759_; size_t v___x_2760_; lean_object* v___x_2761_; 
v_sz_2759_ = lean_array_size(v_xs_2757_);
v___x_2760_ = ((size_t)0ULL);
v___x_2761_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2758_, v_sz_2759_, v___x_2760_, v_xs_2757_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg___boxed(lean_object* v_xs_2762_, lean_object* v_start_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Array_zipIdx___redArg(v_xs_2762_, v_start_2763_);
lean_dec(v_start_2763_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx(lean_object* v_00_u03b1_2765_, lean_object* v_xs_2766_, lean_object* v_start_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Array_zipIdx___redArg(v_xs_2766_, v_start_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___boxed(lean_object* v_00_u03b1_2769_, lean_object* v_xs_2770_, lean_object* v_start_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Array_zipIdx(v_00_u03b1_2769_, v_xs_2770_, v_start_2771_);
lean_dec(v_start_2771_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(lean_object* v_00_u03b1_2773_, lean_object* v_start_2774_, lean_object* v_as_2775_, size_t v_sz_2776_, size_t v_i_2777_, lean_object* v_bs_2778_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2774_, v_sz_2776_, v_i_2777_, v_bs_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___boxed(lean_object* v_00_u03b1_2780_, lean_object* v_start_2781_, lean_object* v_as_2782_, lean_object* v_sz_2783_, lean_object* v_i_2784_, lean_object* v_bs_2785_){
_start:
{
size_t v_sz_boxed_2786_; size_t v_i_boxed_2787_; lean_object* v_res_2788_; 
v_sz_boxed_2786_ = lean_unbox_usize(v_sz_2783_);
lean_dec(v_sz_2783_);
v_i_boxed_2787_ = lean_unbox_usize(v_i_2784_);
lean_dec(v_i_2784_);
v_res_2788_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(v_00_u03b1_2780_, v_start_2781_, v_as_2782_, v_sz_boxed_2786_, v_i_boxed_2787_, v_bs_2785_);
lean_dec_ref(v_as_2782_);
lean_dec(v_start_2781_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0(lean_object* v_p_2789_, lean_object* v___x_2790_, lean_object* v___x_2791_, lean_object* v_a_2792_, lean_object* v_x_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v___x_2795_; uint8_t v___x_2796_; 
lean_inc(v_a_2792_);
v___x_2795_ = lean_apply_1(v_p_2789_, v_a_2792_);
v___x_2796_ = lean_unbox(v___x_2795_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; 
lean_dec(v_a_2792_);
v___x_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2790_);
return v___x_2797_;
}
else
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
lean_dec_ref(v___x_2790_);
v___x_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2798_, 0, v_a_2792_);
v___x_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
v___x_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
lean_ctor_set(v___x_2800_, 1, v___x_2791_);
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
return v___x_2801_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0___boxed(lean_object* v_p_2802_, lean_object* v___x_2803_, lean_object* v___x_2804_, lean_object* v_a_2805_, lean_object* v_x_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Array_find_x3f___redArg___lam__0(v_p_2802_, v___x_2803_, v___x_2804_, v_a_2805_, v_x_2806_, v___y_2807_);
lean_dec_ref(v___y_2807_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg(lean_object* v_p_2809_, lean_object* v_as_2810_){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___f_2815_; size_t v_sz_2816_; size_t v___x_2817_; lean_object* v___x_2818_; lean_object* v_fst_2819_; 
v___x_2811_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2812_ = lean_box(0);
v___x_2813_ = lean_box(0);
v___x_2814_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2815_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2815_, 0, v_p_2809_);
lean_closure_set(v___f_2815_, 1, v___x_2814_);
lean_closure_set(v___f_2815_, 2, v___x_2813_);
v_sz_2816_ = lean_array_size(v_as_2810_);
v___x_2817_ = ((size_t)0ULL);
v___x_2818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2811_, v_as_2810_, v___f_2815_, v_sz_2816_, v___x_2817_, v___x_2814_);
v_fst_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_fst_2819_);
lean_dec(v___x_2818_);
if (lean_obj_tag(v_fst_2819_) == 0)
{
return v___x_2812_;
}
else
{
lean_object* v_val_2820_; 
v_val_2820_ = lean_ctor_get(v_fst_2819_, 0);
lean_inc(v_val_2820_);
lean_dec_ref_known(v_fst_2819_, 1);
return v_val_2820_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f(lean_object* v_00_u03b1_2821_, lean_object* v_p_2822_, lean_object* v_as_2823_){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___f_2828_; size_t v_sz_2829_; size_t v___x_2830_; lean_object* v___x_2831_; lean_object* v_fst_2832_; 
v___x_2824_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2825_ = lean_box(0);
v___x_2826_ = lean_box(0);
v___x_2827_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2828_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2828_, 0, v_p_2822_);
lean_closure_set(v___f_2828_, 1, v___x_2827_);
lean_closure_set(v___f_2828_, 2, v___x_2826_);
v_sz_2829_ = lean_array_size(v_as_2823_);
v___x_2830_ = ((size_t)0ULL);
v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2824_, v_as_2823_, v___f_2828_, v_sz_2829_, v___x_2830_, v___x_2827_);
v_fst_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_fst_2832_);
lean_dec(v___x_2831_);
if (lean_obj_tag(v_fst_2832_) == 0)
{
return v___x_2825_;
}
else
{
lean_object* v_val_2833_; 
v_val_2833_ = lean_ctor_get(v_fst_2832_, 0);
lean_inc(v_val_2833_);
lean_dec_ref_known(v_fst_2832_, 1);
return v_val_2833_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0(lean_object* v_f_2834_, lean_object* v___x_2835_, lean_object* v___x_2836_, lean_object* v_a_2837_, lean_object* v_x_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = lean_apply_1(v_f_2834_, v_a_2837_);
if (lean_obj_tag(v___x_2840_) == 1)
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
lean_dec_ref(v___x_2836_);
v___x_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
v___x_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
lean_ctor_set(v___x_2842_, 1, v___x_2835_);
v___x_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
return v___x_2843_;
}
else
{
lean_object* v___x_2844_; 
lean_dec(v___x_2840_);
v___x_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2836_);
return v___x_2844_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2845_, lean_object* v___x_2846_, lean_object* v___x_2847_, lean_object* v_a_2848_, lean_object* v_x_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Array_findSome_x3f___redArg___lam__0(v_f_2845_, v___x_2846_, v___x_2847_, v_a_2848_, v_x_2849_, v___y_2850_);
lean_dec_ref(v___y_2850_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg(lean_object* v_f_2852_, lean_object* v_as_2853_){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___f_2858_; size_t v_sz_2859_; size_t v___x_2860_; lean_object* v___x_2861_; lean_object* v_fst_2862_; 
v___x_2854_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2855_ = lean_box(0);
v___x_2856_ = lean_box(0);
v___x_2857_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2858_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2858_, 0, v_f_2852_);
lean_closure_set(v___f_2858_, 1, v___x_2856_);
lean_closure_set(v___f_2858_, 2, v___x_2857_);
v_sz_2859_ = lean_array_size(v_as_2853_);
v___x_2860_ = ((size_t)0ULL);
v___x_2861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2854_, v_as_2853_, v___f_2858_, v_sz_2859_, v___x_2860_, v___x_2857_);
v_fst_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_fst_2862_);
lean_dec(v___x_2861_);
if (lean_obj_tag(v_fst_2862_) == 0)
{
return v___x_2855_;
}
else
{
lean_object* v_val_2863_; 
v_val_2863_ = lean_ctor_get(v_fst_2862_, 0);
lean_inc(v_val_2863_);
lean_dec_ref_known(v_fst_2862_, 1);
return v_val_2863_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f(lean_object* v_00_u03b1_2864_, lean_object* v_00_u03b2_2865_, lean_object* v_f_2866_, lean_object* v_as_2867_){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___f_2872_; size_t v_sz_2873_; size_t v___x_2874_; lean_object* v___x_2875_; lean_object* v_fst_2876_; 
v___x_2868_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2869_ = lean_box(0);
v___x_2870_ = lean_box(0);
v___x_2871_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2872_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2872_, 0, v_f_2866_);
lean_closure_set(v___f_2872_, 1, v___x_2870_);
lean_closure_set(v___f_2872_, 2, v___x_2871_);
v_sz_2873_ = lean_array_size(v_as_2867_);
v___x_2874_ = ((size_t)0ULL);
v___x_2875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2868_, v_as_2867_, v___f_2872_, v_sz_2873_, v___x_2874_, v___x_2871_);
v_fst_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_fst_2876_);
lean_dec(v___x_2875_);
if (lean_obj_tag(v_fst_2876_) == 0)
{
return v___x_2869_;
}
else
{
lean_object* v_val_2877_; 
v_val_2877_ = lean_ctor_get(v_fst_2876_, 0);
lean_inc(v_val_2877_);
lean_dec_ref_known(v_fst_2876_, 1);
return v_val_2877_;
}
}
}
static lean_object* _init_l_Array_findSome_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2880_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__1));
v___x_2881_ = lean_unsigned_to_nat(14u);
v___x_2882_ = lean_unsigned_to_nat(1286u);
v___x_2883_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__0));
v___x_2884_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_2885_ = l_mkPanicMessageWithDecl(v___x_2884_, v___x_2883_, v___x_2882_, v___x_2881_, v___x_2880_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg(lean_object* v_inst_2886_, lean_object* v_f_2887_, lean_object* v_xs_2888_){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___f_2895_; size_t v_sz_2896_; size_t v___x_2897_; lean_object* v___x_2898_; lean_object* v_fst_2899_; 
v___x_2892_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2893_ = lean_box(0);
v___x_2894_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2895_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2895_, 0, v_f_2887_);
lean_closure_set(v___f_2895_, 1, v___x_2893_);
lean_closure_set(v___f_2895_, 2, v___x_2894_);
v_sz_2896_ = lean_array_size(v_xs_2888_);
v___x_2897_ = ((size_t)0ULL);
v___x_2898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2892_, v_xs_2888_, v___f_2895_, v_sz_2896_, v___x_2897_, v___x_2894_);
v_fst_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_fst_2899_);
lean_dec(v___x_2898_);
if (lean_obj_tag(v_fst_2899_) == 0)
{
goto v___jp_2889_;
}
else
{
lean_object* v_val_2900_; 
v_val_2900_ = lean_ctor_get(v_fst_2899_, 0);
lean_inc(v_val_2900_);
lean_dec_ref_known(v_fst_2899_, 1);
if (lean_obj_tag(v_val_2900_) == 0)
{
goto v___jp_2889_;
}
else
{
lean_object* v_val_2901_; 
v_val_2901_ = lean_ctor_get(v_val_2900_, 0);
lean_inc(v_val_2901_);
lean_dec_ref_known(v_val_2900_, 1);
return v_val_2901_;
}
}
v___jp_2889_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2891_ = l_panic___redArg(v_inst_2886_, v___x_2890_);
return v___x_2891_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg___boxed(lean_object* v_inst_2902_, lean_object* v_f_2903_, lean_object* v_xs_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Array_findSome_x21___redArg(v_inst_2902_, v_f_2903_, v_xs_2904_);
lean_dec(v_inst_2902_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21(lean_object* v_00_u03b1_2906_, lean_object* v_00_u03b2_2907_, lean_object* v_inst_2908_, lean_object* v_f_2909_, lean_object* v_xs_2910_){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___f_2917_; size_t v_sz_2918_; size_t v___x_2919_; lean_object* v___x_2920_; lean_object* v_fst_2921_; 
v___x_2914_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2915_ = lean_box(0);
v___x_2916_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2917_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2917_, 0, v_f_2909_);
lean_closure_set(v___f_2917_, 1, v___x_2915_);
lean_closure_set(v___f_2917_, 2, v___x_2916_);
v_sz_2918_ = lean_array_size(v_xs_2910_);
v___x_2919_ = ((size_t)0ULL);
v___x_2920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2914_, v_xs_2910_, v___f_2917_, v_sz_2918_, v___x_2919_, v___x_2916_);
v_fst_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_fst_2921_);
lean_dec(v___x_2920_);
if (lean_obj_tag(v_fst_2921_) == 0)
{
goto v___jp_2911_;
}
else
{
lean_object* v_val_2922_; 
v_val_2922_ = lean_ctor_get(v_fst_2921_, 0);
lean_inc(v_val_2922_);
lean_dec_ref_known(v_fst_2921_, 1);
if (lean_obj_tag(v_val_2922_) == 0)
{
goto v___jp_2911_;
}
else
{
lean_object* v_val_2923_; 
v_val_2923_ = lean_ctor_get(v_val_2922_, 0);
lean_inc(v_val_2923_);
lean_dec_ref_known(v_val_2922_, 1);
return v_val_2923_;
}
}
v___jp_2911_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2913_ = l_panic___redArg(v_inst_2908_, v___x_2912_);
return v___x_2913_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___boxed(lean_object* v_00_u03b1_2924_, lean_object* v_00_u03b2_2925_, lean_object* v_inst_2926_, lean_object* v_f_2927_, lean_object* v_xs_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Array_findSome_x21(v_00_u03b1_2924_, v_00_u03b2_2925_, v_inst_2926_, v_f_2927_, v_xs_2928_);
lean_dec(v_inst_2926_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2930_, lean_object* v_x_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = lean_apply_1(v_f_2930_, v_x_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg(lean_object* v_f_2933_, lean_object* v_as_2934_){
_start:
{
lean_object* v___f_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___f_2935_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2935_, 0, v_f_2933_);
v___x_2936_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2937_ = lean_array_get_size(v_as_2934_);
v___x_2938_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2936_, v___f_2935_, v_as_2934_, v___x_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f(lean_object* v_00_u03b1_2939_, lean_object* v_00_u03b2_2940_, lean_object* v_f_2941_, lean_object* v_as_2942_){
_start:
{
lean_object* v___f_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___f_2943_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2943_, 0, v_f_2941_);
v___x_2944_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2945_ = lean_array_get_size(v_as_2942_);
v___x_2946_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2944_, v___f_2943_, v_as_2942_, v___x_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg___lam__0(lean_object* v_p_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v___x_2949_; uint8_t v___x_2950_; 
lean_inc(v_a_2948_);
v___x_2949_ = lean_apply_1(v_p_2947_, v_a_2948_);
v___x_2950_ = lean_unbox(v___x_2949_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; 
lean_dec(v_a_2948_);
v___x_2951_ = lean_box(0);
return v___x_2951_;
}
else
{
lean_object* v___x_2952_; 
v___x_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2952_, 0, v_a_2948_);
return v___x_2952_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg(lean_object* v_p_2953_, lean_object* v_as_2954_){
_start:
{
lean_object* v___f_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___f_2955_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2955_, 0, v_p_2953_);
v___x_2956_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2957_ = lean_array_get_size(v_as_2954_);
v___x_2958_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2956_, v___f_2955_, v_as_2954_, v___x_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f(lean_object* v_00_u03b1_2959_, lean_object* v_p_2960_, lean_object* v_as_2961_){
_start:
{
lean_object* v___f_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___f_2962_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2962_, 0, v_p_2960_);
v___x_2963_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2964_ = lean_array_get_size(v_as_2961_);
v___x_2965_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2963_, v___f_2962_, v_as_2961_, v___x_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object* v_p_2966_, lean_object* v_as_2967_, lean_object* v_j_2968_){
_start:
{
lean_object* v___x_2969_; uint8_t v___x_2970_; 
v___x_2969_ = lean_array_get_size(v_as_2967_);
v___x_2970_ = lean_nat_dec_lt(v_j_2968_, v___x_2969_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; 
lean_dec(v_j_2968_);
lean_dec_ref(v_p_2966_);
v___x_2971_ = lean_box(0);
return v___x_2971_;
}
else
{
lean_object* v___x_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2972_ = lean_array_fget_borrowed(v_as_2967_, v_j_2968_);
lean_inc_ref(v_p_2966_);
lean_inc(v___x_2972_);
v___x_2973_ = lean_apply_1(v_p_2966_, v___x_2972_);
v___x_2974_ = lean_unbox(v___x_2973_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = lean_unsigned_to_nat(1u);
v___x_2976_ = lean_nat_add(v_j_2968_, v___x_2975_);
lean_dec(v_j_2968_);
v_j_2968_ = v___x_2976_;
goto _start;
}
else
{
lean_object* v___x_2978_; 
lean_dec_ref(v_p_2966_);
v___x_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2978_, 0, v_j_2968_);
return v___x_2978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg___boxed(lean_object* v_p_2979_, lean_object* v_as_2980_, lean_object* v_j_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Array_findIdx_x3f_loop___redArg(v_p_2979_, v_as_2980_, v_j_2981_);
lean_dec_ref(v_as_2980_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop(lean_object* v_00_u03b1_2983_, lean_object* v_p_2984_, lean_object* v_as_2985_, lean_object* v_j_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Array_findIdx_x3f_loop___redArg(v_p_2984_, v_as_2985_, v_j_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___boxed(lean_object* v_00_u03b1_2988_, lean_object* v_p_2989_, lean_object* v_as_2990_, lean_object* v_j_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Array_findIdx_x3f_loop(v_00_u03b1_2988_, v_p_2989_, v_as_2990_, v_j_2991_);
lean_dec_ref(v_as_2990_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg(lean_object* v_p_2993_, lean_object* v_as_2994_){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = lean_unsigned_to_nat(0u);
v___x_2996_ = l_Array_findIdx_x3f_loop___redArg(v_p_2993_, v_as_2994_, v___x_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg___boxed(lean_object* v_p_2997_, lean_object* v_as_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Array_findIdx_x3f___redArg(v_p_2997_, v_as_2998_);
lean_dec_ref(v_as_2998_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f(lean_object* v_00_u03b1_3000_, lean_object* v_p_3001_, lean_object* v_as_3002_){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = lean_unsigned_to_nat(0u);
v___x_3004_ = l_Array_findIdx_x3f_loop___redArg(v_p_3001_, v_as_3002_, v___x_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___boxed(lean_object* v_00_u03b1_3005_, lean_object* v_p_3006_, lean_object* v_as_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l_Array_findIdx_x3f(v_00_u03b1_3005_, v_p_3006_, v_as_3007_);
lean_dec_ref(v_as_3007_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(lean_object* v_p_3009_, lean_object* v_as_3010_, lean_object* v_j_3011_){
_start:
{
lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3012_ = lean_array_get_size(v_as_3010_);
v___x_3013_ = lean_nat_dec_lt(v_j_3011_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; 
lean_dec(v_j_3011_);
lean_dec_ref(v_p_3009_);
v___x_3014_ = lean_box(0);
return v___x_3014_;
}
else
{
lean_object* v___x_3015_; lean_object* v___x_3016_; uint8_t v___x_3017_; 
v___x_3015_ = lean_array_fget_borrowed(v_as_3010_, v_j_3011_);
lean_inc_ref(v_p_3009_);
lean_inc(v___x_3015_);
v___x_3016_ = lean_apply_1(v_p_3009_, v___x_3015_);
v___x_3017_ = lean_unbox(v___x_3016_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_unsigned_to_nat(1u);
v___x_3019_ = lean_nat_add(v_j_3011_, v___x_3018_);
lean_dec(v_j_3011_);
v_j_3011_ = v___x_3019_;
goto _start;
}
else
{
lean_object* v___x_3021_; 
lean_dec_ref(v_p_3009_);
v___x_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3021_, 0, v_j_3011_);
return v___x_3021_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg___boxed(lean_object* v_p_3022_, lean_object* v_as_3023_, lean_object* v_j_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3022_, v_as_3023_, v_j_3024_);
lean_dec_ref(v_as_3023_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object* v_00_u03b1_3026_, lean_object* v_p_3027_, lean_object* v_as_3028_, lean_object* v_j_3029_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3027_, v_as_3028_, v_j_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___boxed(lean_object* v_00_u03b1_3031_, lean_object* v_p_3032_, lean_object* v_as_3033_, lean_object* v_j_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(v_00_u03b1_3031_, v_p_3032_, v_as_3033_, v_j_3034_);
lean_dec_ref(v_as_3033_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg(lean_object* v_p_3036_, lean_object* v_as_3037_){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3038_ = lean_unsigned_to_nat(0u);
v___x_3039_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3036_, v_as_3037_, v___x_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg___boxed(lean_object* v_p_3040_, lean_object* v_as_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Array_findFinIdx_x3f___redArg(v_p_3040_, v_as_3041_);
lean_dec_ref(v_as_3041_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f(lean_object* v_00_u03b1_3043_, lean_object* v_p_3044_, lean_object* v_as_3045_){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_unsigned_to_nat(0u);
v___x_3047_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3044_, v_as_3045_, v___x_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_3048_, lean_object* v_p_3049_, lean_object* v_as_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Array_findFinIdx_x3f(v_00_u03b1_3048_, v_p_3049_, v_as_3050_);
lean_dec_ref(v_as_3050_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg(lean_object* v_p_3052_, lean_object* v_as_3053_){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = lean_unsigned_to_nat(0u);
v___x_3055_ = l_Array_findIdx_x3f_loop___redArg(v_p_3052_, v_as_3053_, v___x_3054_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_array_get_size(v_as_3053_);
return v___x_3056_;
}
else
{
lean_object* v_val_3057_; 
v_val_3057_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_val_3057_);
lean_dec_ref_known(v___x_3055_, 1);
return v_val_3057_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg___boxed(lean_object* v_p_3058_, lean_object* v_as_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Array_findIdx___redArg(v_p_3058_, v_as_3059_);
lean_dec_ref(v_as_3059_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx(lean_object* v_00_u03b1_3061_, lean_object* v_p_3062_, lean_object* v_as_3063_){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = lean_unsigned_to_nat(0u);
v___x_3065_ = l_Array_findIdx_x3f_loop___redArg(v_p_3062_, v_as_3063_, v___x_3064_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v___x_3066_; 
v___x_3066_ = lean_array_get_size(v_as_3063_);
return v___x_3066_;
}
else
{
lean_object* v_val_3067_; 
v_val_3067_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_val_3067_);
lean_dec_ref_known(v___x_3065_, 1);
return v_val_3067_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___boxed(lean_object* v_00_u03b1_3068_, lean_object* v_p_3069_, lean_object* v_as_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Array_findIdx(v_00_u03b1_3068_, v_p_3069_, v_as_3070_);
lean_dec_ref(v_as_3070_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg(lean_object* v_inst_3072_, lean_object* v_xs_3073_, lean_object* v_v_3074_, lean_object* v_i_3075_){
_start:
{
lean_object* v___x_3076_; uint8_t v___x_3077_; 
v___x_3076_ = lean_array_get_size(v_xs_3073_);
v___x_3077_ = lean_nat_dec_lt(v_i_3075_, v___x_3076_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; 
lean_dec(v_i_3075_);
lean_dec(v_v_3074_);
lean_dec_ref(v_inst_3072_);
v___x_3078_ = lean_box(0);
return v___x_3078_;
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3079_ = lean_array_fget_borrowed(v_xs_3073_, v_i_3075_);
lean_inc_ref(v_inst_3072_);
lean_inc(v_v_3074_);
lean_inc(v___x_3079_);
v___x_3080_ = lean_apply_2(v_inst_3072_, v___x_3079_, v_v_3074_);
v___x_3081_ = lean_unbox(v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_unsigned_to_nat(1u);
v___x_3083_ = lean_nat_add(v_i_3075_, v___x_3082_);
lean_dec(v_i_3075_);
v_i_3075_ = v___x_3083_;
goto _start;
}
else
{
lean_object* v___x_3085_; 
lean_dec(v_v_3074_);
lean_dec_ref(v_inst_3072_);
v___x_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3085_, 0, v_i_3075_);
return v___x_3085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg___boxed(lean_object* v_inst_3086_, lean_object* v_xs_3087_, lean_object* v_v_3088_, lean_object* v_i_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Array_idxOfAux___redArg(v_inst_3086_, v_xs_3087_, v_v_3088_, v_i_3089_);
lean_dec_ref(v_xs_3087_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux(lean_object* v_00_u03b1_3091_, lean_object* v_inst_3092_, lean_object* v_xs_3093_, lean_object* v_v_3094_, lean_object* v_i_3095_){
_start:
{
lean_object* v___x_3096_; 
v___x_3096_ = l_Array_idxOfAux___redArg(v_inst_3092_, v_xs_3093_, v_v_3094_, v_i_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___boxed(lean_object* v_00_u03b1_3097_, lean_object* v_inst_3098_, lean_object* v_xs_3099_, lean_object* v_v_3100_, lean_object* v_i_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Array_idxOfAux(v_00_u03b1_3097_, v_inst_3098_, v_xs_3099_, v_v_3100_, v_i_3101_);
lean_dec_ref(v_xs_3099_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg(lean_object* v_inst_3103_, lean_object* v_xs_3104_, lean_object* v_v_3105_){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = lean_unsigned_to_nat(0u);
v___x_3107_ = l_Array_idxOfAux___redArg(v_inst_3103_, v_xs_3104_, v_v_3105_, v___x_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_3108_, lean_object* v_xs_3109_, lean_object* v_v_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Array_finIdxOf_x3f___redArg(v_inst_3108_, v_xs_3109_, v_v_3110_);
lean_dec_ref(v_xs_3109_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f(lean_object* v_00_u03b1_3112_, lean_object* v_inst_3113_, lean_object* v_xs_3114_, lean_object* v_v_3115_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Array_finIdxOf_x3f___redArg(v_inst_3113_, v_xs_3114_, v_v_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_3117_, lean_object* v_inst_3118_, lean_object* v_xs_3119_, lean_object* v_v_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Array_finIdxOf_x3f(v_00_u03b1_3117_, v_inst_3118_, v_xs_3119_, v_v_3120_);
lean_dec_ref(v_xs_3119_);
return v_res_3121_;
}
}
LEAN_EXPORT uint8_t l_Array_idxOf___redArg___lam__0(lean_object* v_inst_3122_, lean_object* v_a_3123_, lean_object* v_x_3124_){
_start:
{
lean_object* v___x_3125_; uint8_t v___x_3126_; 
v___x_3125_ = lean_apply_2(v_inst_3122_, v_x_3124_, v_a_3123_);
v___x_3126_ = lean_unbox(v___x_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___lam__0___boxed(lean_object* v_inst_3127_, lean_object* v_a_3128_, lean_object* v_x_3129_){
_start:
{
uint8_t v_res_3130_; lean_object* v_r_3131_; 
v_res_3130_ = l_Array_idxOf___redArg___lam__0(v_inst_3127_, v_a_3128_, v_x_3129_);
v_r_3131_ = lean_box(v_res_3130_);
return v_r_3131_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg(lean_object* v_inst_3132_, lean_object* v_a_3133_, lean_object* v_as_3134_){
_start:
{
lean_object* v___f_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___f_3135_ = lean_alloc_closure((void*)(l_Array_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3135_, 0, v_inst_3132_);
lean_closure_set(v___f_3135_, 1, v_a_3133_);
v___x_3136_ = lean_unsigned_to_nat(0u);
v___x_3137_ = l_Array_findIdx_x3f_loop___redArg(v___f_3135_, v_as_3134_, v___x_3136_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v___x_3138_; 
v___x_3138_ = lean_array_get_size(v_as_3134_);
return v___x_3138_;
}
else
{
lean_object* v_val_3139_; 
v_val_3139_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_val_3139_);
lean_dec_ref_known(v___x_3137_, 1);
return v_val_3139_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___boxed(lean_object* v_inst_3140_, lean_object* v_a_3141_, lean_object* v_as_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Array_idxOf___redArg(v_inst_3140_, v_a_3141_, v_as_3142_);
lean_dec_ref(v_as_3142_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf(lean_object* v_00_u03b1_3144_, lean_object* v_inst_3145_, lean_object* v_a_3146_, lean_object* v_as_3147_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Array_idxOf___redArg(v_inst_3145_, v_a_3146_, v_as_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___boxed(lean_object* v_00_u03b1_3149_, lean_object* v_inst_3150_, lean_object* v_a_3151_, lean_object* v_as_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Array_idxOf(v_00_u03b1_3149_, v_inst_3150_, v_a_3151_, v_as_3152_);
lean_dec_ref(v_as_3152_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg(lean_object* v_inst_3154_, lean_object* v_xs_3155_, lean_object* v_v_3156_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_Array_finIdxOf_x3f___redArg(v_inst_3154_, v_xs_3155_, v_v_3156_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v___x_3158_; 
v___x_3158_ = lean_box(0);
return v___x_3158_;
}
else
{
lean_object* v_val_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
v_val_3159_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3157_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_val_3159_);
lean_dec(v___x_3157_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_val_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg___boxed(lean_object* v_inst_3167_, lean_object* v_xs_3168_, lean_object* v_v_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Array_idxOf_x3f___redArg(v_inst_3167_, v_xs_3168_, v_v_3169_);
lean_dec_ref(v_xs_3168_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f(lean_object* v_00_u03b1_3171_, lean_object* v_inst_3172_, lean_object* v_xs_3173_, lean_object* v_v_3174_){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Array_idxOf_x3f___redArg(v_inst_3172_, v_xs_3173_, v_v_3174_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___boxed(lean_object* v_00_u03b1_3176_, lean_object* v_inst_3177_, lean_object* v_xs_3178_, lean_object* v_v_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l_Array_idxOf_x3f(v_00_u03b1_3176_, v_inst_3177_, v_xs_3178_, v_v_3179_);
lean_dec_ref(v_xs_3178_);
return v_res_3180_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg___lam__0(lean_object* v_p_3181_, lean_object* v_x_3182_){
_start:
{
lean_object* v___x_3183_; uint8_t v___x_3184_; 
v___x_3183_ = lean_apply_1(v_p_3181_, v_x_3182_);
v___x_3184_ = lean_unbox(v___x_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___lam__0___boxed(lean_object* v_p_3185_, lean_object* v_x_3186_){
_start:
{
uint8_t v_res_3187_; lean_object* v_r_3188_; 
v_res_3187_ = l_Array_any___redArg___lam__0(v_p_3185_, v_x_3186_);
v_r_3188_ = lean_box(v_res_3187_);
return v_r_3188_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg(lean_object* v_as_3189_, lean_object* v_p_3190_, lean_object* v_start_3191_, lean_object* v_stop_3192_){
_start:
{
lean_object* v___x_3193_; uint8_t v___x_3194_; 
v___x_3193_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3194_ = lean_nat_dec_lt(v_start_3191_, v_stop_3192_);
if (v___x_3194_ == 0)
{
lean_dec(v_stop_3192_);
lean_dec_ref(v_p_3190_);
lean_dec_ref(v_as_3189_);
return v___x_3194_;
}
else
{
lean_object* v___f_3195_; lean_object* v___y_3197_; lean_object* v___x_3203_; uint8_t v___x_3204_; 
v___f_3195_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3195_, 0, v_p_3190_);
v___x_3203_ = lean_array_get_size(v_as_3189_);
v___x_3204_ = lean_nat_dec_le(v_stop_3192_, v___x_3203_);
if (v___x_3204_ == 0)
{
lean_dec(v_stop_3192_);
v___y_3197_ = v___x_3203_;
goto v___jp_3196_;
}
else
{
v___y_3197_ = v_stop_3192_;
goto v___jp_3196_;
}
v___jp_3196_:
{
uint8_t v___x_3198_; 
v___x_3198_ = lean_nat_dec_lt(v_start_3191_, v___y_3197_);
if (v___x_3198_ == 0)
{
lean_dec(v___y_3197_);
lean_dec_ref(v___f_3195_);
lean_dec_ref(v_as_3189_);
return v___x_3198_;
}
else
{
size_t v___x_3199_; size_t v___x_3200_; lean_object* v___x_3201_; uint8_t v___x_3202_; 
v___x_3199_ = lean_usize_of_nat(v_start_3191_);
v___x_3200_ = lean_usize_of_nat(v___y_3197_);
lean_dec(v___y_3197_);
v___x_3201_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3193_, v___f_3195_, v_as_3189_, v___x_3199_, v___x_3200_);
v___x_3202_ = lean_unbox(v___x_3201_);
lean_dec(v___x_3201_);
return v___x_3202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___boxed(lean_object* v_as_3205_, lean_object* v_p_3206_, lean_object* v_start_3207_, lean_object* v_stop_3208_){
_start:
{
uint8_t v_res_3209_; lean_object* v_r_3210_; 
v_res_3209_ = l_Array_any___redArg(v_as_3205_, v_p_3206_, v_start_3207_, v_stop_3208_);
lean_dec(v_start_3207_);
v_r_3210_ = lean_box(v_res_3209_);
return v_r_3210_;
}
}
LEAN_EXPORT uint8_t l_Array_any(lean_object* v_00_u03b1_3211_, lean_object* v_as_3212_, lean_object* v_p_3213_, lean_object* v_start_3214_, lean_object* v_stop_3215_){
_start:
{
lean_object* v___x_3216_; uint8_t v___x_3217_; 
v___x_3216_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3217_ = lean_nat_dec_lt(v_start_3214_, v_stop_3215_);
if (v___x_3217_ == 0)
{
lean_dec(v_stop_3215_);
lean_dec_ref(v_p_3213_);
lean_dec_ref(v_as_3212_);
return v___x_3217_;
}
else
{
lean_object* v___f_3218_; lean_object* v___y_3220_; lean_object* v___x_3226_; uint8_t v___x_3227_; 
v___f_3218_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3218_, 0, v_p_3213_);
v___x_3226_ = lean_array_get_size(v_as_3212_);
v___x_3227_ = lean_nat_dec_le(v_stop_3215_, v___x_3226_);
if (v___x_3227_ == 0)
{
lean_dec(v_stop_3215_);
v___y_3220_ = v___x_3226_;
goto v___jp_3219_;
}
else
{
v___y_3220_ = v_stop_3215_;
goto v___jp_3219_;
}
v___jp_3219_:
{
uint8_t v___x_3221_; 
v___x_3221_ = lean_nat_dec_lt(v_start_3214_, v___y_3220_);
if (v___x_3221_ == 0)
{
lean_dec(v___y_3220_);
lean_dec_ref(v___f_3218_);
lean_dec_ref(v_as_3212_);
return v___x_3221_;
}
else
{
size_t v___x_3222_; size_t v___x_3223_; lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3222_ = lean_usize_of_nat(v_start_3214_);
v___x_3223_ = lean_usize_of_nat(v___y_3220_);
lean_dec(v___y_3220_);
v___x_3224_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3216_, v___f_3218_, v_as_3212_, v___x_3222_, v___x_3223_);
v___x_3225_ = lean_unbox(v___x_3224_);
lean_dec(v___x_3224_);
return v___x_3225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___boxed(lean_object* v_00_u03b1_3228_, lean_object* v_as_3229_, lean_object* v_p_3230_, lean_object* v_start_3231_, lean_object* v_stop_3232_){
_start:
{
uint8_t v_res_3233_; lean_object* v_r_3234_; 
v_res_3233_ = l_Array_any(v_00_u03b1_3228_, v_as_3229_, v_p_3230_, v_start_3231_, v_stop_3232_);
lean_dec(v_start_3231_);
v_r_3234_ = lean_box(v_res_3233_);
return v_r_3234_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg___lam__0(lean_object* v_p_3235_, uint8_t v___x_3236_, lean_object* v_v_3237_){
_start:
{
lean_object* v___x_3238_; uint8_t v___x_3239_; 
v___x_3238_ = lean_apply_1(v_p_3235_, v_v_3237_);
v___x_3239_ = lean_unbox(v___x_3238_);
if (v___x_3239_ == 0)
{
return v___x_3236_;
}
else
{
uint8_t v___x_3240_; 
v___x_3240_ = 0;
return v___x_3240_;
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___lam__0___boxed(lean_object* v_p_3241_, lean_object* v___x_3242_, lean_object* v_v_3243_){
_start:
{
uint8_t v___x_335__boxed_3244_; uint8_t v_res_3245_; lean_object* v_r_3246_; 
v___x_335__boxed_3244_ = lean_unbox(v___x_3242_);
v_res_3245_ = l_Array_all___redArg___lam__0(v_p_3241_, v___x_335__boxed_3244_, v_v_3243_);
v_r_3246_ = lean_box(v_res_3245_);
return v_r_3246_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg(lean_object* v_as_3247_, lean_object* v_p_3248_, lean_object* v_start_3249_, lean_object* v_stop_3250_){
_start:
{
lean_object* v___x_3251_; uint8_t v___x_3252_; 
v___x_3251_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3252_ = lean_nat_dec_lt(v_start_3249_, v_stop_3250_);
if (v___x_3252_ == 0)
{
uint8_t v___x_3253_; 
lean_dec(v_stop_3250_);
lean_dec_ref(v_p_3248_);
lean_dec_ref(v_as_3247_);
v___x_3253_ = 1;
return v___x_3253_;
}
else
{
lean_object* v___x_3254_; lean_object* v___f_3255_; lean_object* v___y_3257_; lean_object* v___x_3264_; uint8_t v___x_3265_; 
v___x_3254_ = lean_box(v___x_3252_);
v___f_3255_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3255_, 0, v_p_3248_);
lean_closure_set(v___f_3255_, 1, v___x_3254_);
v___x_3264_ = lean_array_get_size(v_as_3247_);
v___x_3265_ = lean_nat_dec_le(v_stop_3250_, v___x_3264_);
if (v___x_3265_ == 0)
{
lean_dec(v_stop_3250_);
v___y_3257_ = v___x_3264_;
goto v___jp_3256_;
}
else
{
v___y_3257_ = v_stop_3250_;
goto v___jp_3256_;
}
v___jp_3256_:
{
uint8_t v___x_3258_; 
v___x_3258_ = lean_nat_dec_lt(v_start_3249_, v___y_3257_);
if (v___x_3258_ == 0)
{
lean_dec(v___y_3257_);
lean_dec_ref(v___f_3255_);
lean_dec_ref(v_as_3247_);
return v___x_3252_;
}
else
{
size_t v___x_3259_; size_t v___x_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; 
v___x_3259_ = lean_usize_of_nat(v_start_3249_);
v___x_3260_ = lean_usize_of_nat(v___y_3257_);
lean_dec(v___y_3257_);
v___x_3261_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3251_, v___f_3255_, v_as_3247_, v___x_3259_, v___x_3260_);
v___x_3262_ = lean_unbox(v___x_3261_);
lean_dec(v___x_3261_);
if (v___x_3262_ == 0)
{
return v___x_3258_;
}
else
{
uint8_t v___x_3263_; 
v___x_3263_ = 0;
return v___x_3263_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___boxed(lean_object* v_as_3266_, lean_object* v_p_3267_, lean_object* v_start_3268_, lean_object* v_stop_3269_){
_start:
{
uint8_t v_res_3270_; lean_object* v_r_3271_; 
v_res_3270_ = l_Array_all___redArg(v_as_3266_, v_p_3267_, v_start_3268_, v_stop_3269_);
lean_dec(v_start_3268_);
v_r_3271_ = lean_box(v_res_3270_);
return v_r_3271_;
}
}
LEAN_EXPORT uint8_t l_Array_all(lean_object* v_00_u03b1_3272_, lean_object* v_as_3273_, lean_object* v_p_3274_, lean_object* v_start_3275_, lean_object* v_stop_3276_){
_start:
{
lean_object* v___x_3277_; uint8_t v___x_3278_; 
v___x_3277_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3278_ = lean_nat_dec_lt(v_start_3275_, v_stop_3276_);
if (v___x_3278_ == 0)
{
uint8_t v___x_3279_; 
lean_dec(v_stop_3276_);
lean_dec_ref(v_p_3274_);
lean_dec_ref(v_as_3273_);
v___x_3279_ = 1;
return v___x_3279_;
}
else
{
lean_object* v___x_3280_; lean_object* v___f_3281_; lean_object* v___y_3283_; lean_object* v___x_3290_; uint8_t v___x_3291_; 
v___x_3280_ = lean_box(v___x_3278_);
v___f_3281_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3281_, 0, v_p_3274_);
lean_closure_set(v___f_3281_, 1, v___x_3280_);
v___x_3290_ = lean_array_get_size(v_as_3273_);
v___x_3291_ = lean_nat_dec_le(v_stop_3276_, v___x_3290_);
if (v___x_3291_ == 0)
{
lean_dec(v_stop_3276_);
v___y_3283_ = v___x_3290_;
goto v___jp_3282_;
}
else
{
v___y_3283_ = v_stop_3276_;
goto v___jp_3282_;
}
v___jp_3282_:
{
uint8_t v___x_3284_; 
v___x_3284_ = lean_nat_dec_lt(v_start_3275_, v___y_3283_);
if (v___x_3284_ == 0)
{
lean_dec(v___y_3283_);
lean_dec_ref(v___f_3281_);
lean_dec_ref(v_as_3273_);
return v___x_3278_;
}
else
{
size_t v___x_3285_; size_t v___x_3286_; lean_object* v___x_3287_; uint8_t v___x_3288_; 
v___x_3285_ = lean_usize_of_nat(v_start_3275_);
v___x_3286_ = lean_usize_of_nat(v___y_3283_);
lean_dec(v___y_3283_);
v___x_3287_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3277_, v___f_3281_, v_as_3273_, v___x_3285_, v___x_3286_);
v___x_3288_ = lean_unbox(v___x_3287_);
lean_dec(v___x_3287_);
if (v___x_3288_ == 0)
{
return v___x_3284_;
}
else
{
uint8_t v___x_3289_; 
v___x_3289_ = 0;
return v___x_3289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___boxed(lean_object* v_00_u03b1_3292_, lean_object* v_as_3293_, lean_object* v_p_3294_, lean_object* v_start_3295_, lean_object* v_stop_3296_){
_start:
{
uint8_t v_res_3297_; lean_object* v_r_3298_; 
v_res_3297_ = l_Array_all(v_00_u03b1_3292_, v_as_3293_, v_p_3294_, v_start_3295_, v_stop_3296_);
lean_dec(v_start_3295_);
v_r_3298_ = lean_box(v_res_3297_);
return v_r_3298_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg___lam__0(lean_object* v_inst_3299_, lean_object* v_a_3300_, lean_object* v_x_3301_){
_start:
{
lean_object* v___x_3302_; uint8_t v___x_3303_; 
v___x_3302_ = lean_apply_2(v_inst_3299_, v_a_3300_, v_x_3301_);
v___x_3303_ = lean_unbox(v___x_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___lam__0___boxed(lean_object* v_inst_3304_, lean_object* v_a_3305_, lean_object* v_x_3306_){
_start:
{
uint8_t v_res_3307_; lean_object* v_r_3308_; 
v_res_3307_ = l_Array_contains___redArg___lam__0(v_inst_3304_, v_a_3305_, v_x_3306_);
v_r_3308_ = lean_box(v_res_3307_);
return v_r_3308_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg(lean_object* v_inst_3309_, lean_object* v_as_3310_, lean_object* v_a_3311_){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; uint8_t v___x_3315_; 
v___x_3312_ = lean_unsigned_to_nat(0u);
v___x_3313_ = lean_array_get_size(v_as_3310_);
v___x_3314_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3315_ = lean_nat_dec_lt(v___x_3312_, v___x_3313_);
if (v___x_3315_ == 0)
{
lean_dec(v_a_3311_);
lean_dec_ref(v_as_3310_);
lean_dec_ref(v_inst_3309_);
return v___x_3315_;
}
else
{
if (v___x_3315_ == 0)
{
lean_dec(v_a_3311_);
lean_dec_ref(v_as_3310_);
lean_dec_ref(v_inst_3309_);
return v___x_3315_;
}
else
{
lean_object* v___f_3316_; size_t v___x_3317_; size_t v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___f_3316_ = lean_alloc_closure((void*)(l_Array_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3316_, 0, v_inst_3309_);
lean_closure_set(v___f_3316_, 1, v_a_3311_);
v___x_3317_ = ((size_t)0ULL);
v___x_3318_ = lean_usize_of_nat(v___x_3313_);
v___x_3319_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3314_, v___f_3316_, v_as_3310_, v___x_3317_, v___x_3318_);
v___x_3320_ = lean_unbox(v___x_3319_);
lean_dec(v___x_3319_);
return v___x_3320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___boxed(lean_object* v_inst_3321_, lean_object* v_as_3322_, lean_object* v_a_3323_){
_start:
{
uint8_t v_res_3324_; lean_object* v_r_3325_; 
v_res_3324_ = l_Array_contains___redArg(v_inst_3321_, v_as_3322_, v_a_3323_);
v_r_3325_ = lean_box(v_res_3324_);
return v_r_3325_;
}
}
LEAN_EXPORT uint8_t l_Array_contains(lean_object* v_00_u03b1_3326_, lean_object* v_inst_3327_, lean_object* v_as_3328_, lean_object* v_a_3329_){
_start:
{
uint8_t v___x_3330_; 
v___x_3330_ = l_Array_contains___redArg(v_inst_3327_, v_as_3328_, v_a_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___boxed(lean_object* v_00_u03b1_3331_, lean_object* v_inst_3332_, lean_object* v_as_3333_, lean_object* v_a_3334_){
_start:
{
uint8_t v_res_3335_; lean_object* v_r_3336_; 
v_res_3335_ = l_Array_contains(v_00_u03b1_3331_, v_inst_3332_, v_as_3333_, v_a_3334_);
v_r_3336_ = lean_box(v_res_3335_);
return v_r_3336_;
}
}
LEAN_EXPORT uint8_t l_Array_elem___redArg(lean_object* v_inst_3337_, lean_object* v_a_3338_, lean_object* v_as_3339_){
_start:
{
uint8_t v___x_3340_; 
v___x_3340_ = l_Array_contains___redArg(v_inst_3337_, v_as_3339_, v_a_3338_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___redArg___boxed(lean_object* v_inst_3341_, lean_object* v_a_3342_, lean_object* v_as_3343_){
_start:
{
uint8_t v_res_3344_; lean_object* v_r_3345_; 
v_res_3344_ = l_Array_elem___redArg(v_inst_3341_, v_a_3342_, v_as_3343_);
v_r_3345_ = lean_box(v_res_3344_);
return v_r_3345_;
}
}
LEAN_EXPORT uint8_t l_Array_elem(lean_object* v_00_u03b1_3346_, lean_object* v_inst_3347_, lean_object* v_a_3348_, lean_object* v_as_3349_){
_start:
{
uint8_t v___x_3350_; 
v___x_3350_ = l_Array_contains___redArg(v_inst_3347_, v_as_3349_, v_a_3348_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___boxed(lean_object* v_00_u03b1_3351_, lean_object* v_inst_3352_, lean_object* v_a_3353_, lean_object* v_as_3354_){
_start:
{
uint8_t v_res_3355_; lean_object* v_r_3356_; 
v_res_3355_ = l_Array_elem(v_00_u03b1_3351_, v_inst_3352_, v_a_3353_, v_as_3354_);
v_r_3356_ = lean_box(v_res_3355_);
return v_r_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(lean_object* v_as_3357_, size_t v_i_3358_, size_t v_stop_3359_, lean_object* v_b_3360_){
_start:
{
uint8_t v___x_3361_; 
v___x_3361_ = lean_usize_dec_eq(v_i_3358_, v_stop_3359_);
if (v___x_3361_ == 0)
{
size_t v___x_3362_; size_t v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3362_ = ((size_t)1ULL);
v___x_3363_ = lean_usize_sub(v_i_3358_, v___x_3362_);
v___x_3364_ = lean_array_uget_borrowed(v_as_3357_, v___x_3363_);
lean_inc(v___x_3364_);
v___x_3365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
lean_ctor_set(v___x_3365_, 1, v_b_3360_);
v_i_3358_ = v___x_3363_;
v_b_3360_ = v___x_3365_;
goto _start;
}
else
{
return v_b_3360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg___boxed(lean_object* v_as_3367_, lean_object* v_i_3368_, lean_object* v_stop_3369_, lean_object* v_b_3370_){
_start:
{
size_t v_i_boxed_3371_; size_t v_stop_boxed_3372_; lean_object* v_res_3373_; 
v_i_boxed_3371_ = lean_unbox_usize(v_i_3368_);
lean_dec(v_i_3368_);
v_stop_boxed_3372_ = lean_unbox_usize(v_stop_3369_);
lean_dec(v_stop_3369_);
v_res_3373_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3367_, v_i_boxed_3371_, v_stop_boxed_3372_, v_b_3370_);
lean_dec_ref(v_as_3367_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg(lean_object* v_as_3374_){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; uint8_t v___x_3378_; 
v___x_3375_ = lean_box(0);
v___x_3376_ = lean_array_get_size(v_as_3374_);
v___x_3377_ = lean_unsigned_to_nat(0u);
v___x_3378_ = lean_nat_dec_lt(v___x_3377_, v___x_3376_);
if (v___x_3378_ == 0)
{
return v___x_3375_;
}
else
{
size_t v___x_3379_; size_t v___x_3380_; lean_object* v___x_3381_; 
v___x_3379_ = lean_usize_of_nat(v___x_3376_);
v___x_3380_ = ((size_t)0ULL);
v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3374_, v___x_3379_, v___x_3380_, v___x_3375_);
return v___x_3381_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg___boxed(lean_object* v_as_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Array_toListImpl___redArg(v_as_3382_);
lean_dec_ref(v_as_3382_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* lean_array_to_list_impl(lean_object* v_00_u03b1_3384_, lean_object* v_as_3385_){
_start:
{
lean_object* v___x_3386_; 
v___x_3386_ = l_Array_toListImpl___redArg(v_as_3385_);
lean_dec_ref(v_as_3385_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(lean_object* v_00_u03b1_3387_, lean_object* v_as_3388_, size_t v_i_3389_, size_t v_stop_3390_, lean_object* v_b_3391_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3388_, v_i_3389_, v_stop_3390_, v_b_3391_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___boxed(lean_object* v_00_u03b1_3393_, lean_object* v_as_3394_, lean_object* v_i_3395_, lean_object* v_stop_3396_, lean_object* v_b_3397_){
_start:
{
size_t v_i_boxed_3398_; size_t v_stop_boxed_3399_; lean_object* v_res_3400_; 
v_i_boxed_3398_ = lean_unbox_usize(v_i_3395_);
lean_dec(v_i_3395_);
v_stop_boxed_3399_ = lean_unbox_usize(v_stop_3396_);
lean_dec(v_stop_3396_);
v_res_3400_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(v_00_u03b1_3393_, v_as_3394_, v_i_boxed_3398_, v_stop_boxed_3399_, v_b_3397_);
lean_dec_ref(v_as_3394_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg___lam__0(lean_object* v_x1_3401_, lean_object* v_x2_3402_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3403_, 0, v_x1_3401_);
lean_ctor_set(v___x_3403_, 1, v_x2_3402_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg(lean_object* v_as_3405_, lean_object* v_l_3406_){
_start:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; uint8_t v___x_3410_; 
v___x_3407_ = lean_array_get_size(v_as_3405_);
v___x_3408_ = lean_unsigned_to_nat(0u);
v___x_3409_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3410_ = lean_nat_dec_lt(v___x_3408_, v___x_3407_);
if (v___x_3410_ == 0)
{
lean_dec_ref(v_as_3405_);
return v_l_3406_;
}
else
{
lean_object* v___f_3411_; size_t v___x_3412_; size_t v___x_3413_; lean_object* v___x_3414_; 
v___f_3411_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3412_ = lean_usize_of_nat(v___x_3407_);
v___x_3413_ = ((size_t)0ULL);
v___x_3414_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3409_, v___f_3411_, v_as_3405_, v___x_3412_, v___x_3413_, v_l_3406_);
return v___x_3414_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend(lean_object* v_00_u03b1_3415_, lean_object* v_as_3416_, lean_object* v_l_3417_){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; uint8_t v___x_3421_; 
v___x_3418_ = lean_array_get_size(v_as_3416_);
v___x_3419_ = lean_unsigned_to_nat(0u);
v___x_3420_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3421_ = lean_nat_dec_lt(v___x_3419_, v___x_3418_);
if (v___x_3421_ == 0)
{
lean_dec_ref(v_as_3416_);
return v_l_3417_;
}
else
{
lean_object* v___f_3422_; size_t v___x_3423_; size_t v___x_3424_; lean_object* v___x_3425_; 
v___f_3422_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3423_ = lean_usize_of_nat(v___x_3418_);
v___x_3424_ = ((size_t)0ULL);
v___x_3425_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3420_, v___f_3422_, v_as_3416_, v___x_3423_, v___x_3424_, v_l_3417_);
return v___x_3425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(lean_object* v_as_3426_, size_t v_i_3427_, size_t v_stop_3428_, lean_object* v_b_3429_){
_start:
{
uint8_t v___x_3430_; 
v___x_3430_ = lean_usize_dec_eq(v_i_3427_, v_stop_3428_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; lean_object* v___x_3432_; size_t v___x_3433_; size_t v___x_3434_; 
v___x_3431_ = lean_array_uget_borrowed(v_as_3426_, v_i_3427_);
lean_inc(v___x_3431_);
v___x_3432_ = lean_array_push(v_b_3429_, v___x_3431_);
v___x_3433_ = ((size_t)1ULL);
v___x_3434_ = lean_usize_add(v_i_3427_, v___x_3433_);
v_i_3427_ = v___x_3434_;
v_b_3429_ = v___x_3432_;
goto _start;
}
else
{
return v_b_3429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg___boxed(lean_object* v_as_3436_, lean_object* v_i_3437_, lean_object* v_stop_3438_, lean_object* v_b_3439_){
_start:
{
size_t v_i_boxed_3440_; size_t v_stop_boxed_3441_; lean_object* v_res_3442_; 
v_i_boxed_3440_ = lean_unbox_usize(v_i_3437_);
lean_dec(v_i_3437_);
v_stop_boxed_3441_ = lean_unbox_usize(v_stop_3438_);
lean_dec(v_stop_3438_);
v_res_3442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3436_, v_i_boxed_3440_, v_stop_boxed_3441_, v_b_3439_);
lean_dec_ref(v_as_3436_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg(lean_object* v_as_3443_, lean_object* v_bs_3444_){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; 
v___x_3445_ = lean_unsigned_to_nat(0u);
v___x_3446_ = lean_array_get_size(v_bs_3444_);
v___x_3447_ = lean_nat_dec_lt(v___x_3445_, v___x_3446_);
if (v___x_3447_ == 0)
{
return v_as_3443_;
}
else
{
size_t v___x_3448_; size_t v___x_3449_; lean_object* v___x_3450_; 
v___x_3448_ = ((size_t)0ULL);
v___x_3449_ = lean_usize_of_nat(v___x_3446_);
v___x_3450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3444_, v___x_3448_, v___x_3449_, v_as_3443_);
return v___x_3450_;
}
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg___boxed(lean_object* v_as_3451_, lean_object* v_bs_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l_Array_append___redArg(v_as_3451_, v_bs_3452_);
lean_dec_ref(v_bs_3452_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Array_append(lean_object* v_00_u03b1_3454_, lean_object* v_as_3455_, lean_object* v_bs_3456_){
_start:
{
lean_object* v___x_3457_; 
v___x_3457_ = l_Array_append___redArg(v_as_3455_, v_bs_3456_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l_Array_append___boxed(lean_object* v_00_u03b1_3458_, lean_object* v_as_3459_, lean_object* v_bs_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Array_append(v_00_u03b1_3458_, v_as_3459_, v_bs_3460_);
lean_dec_ref(v_bs_3460_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(lean_object* v_00_u03b1_3462_, lean_object* v_as_3463_, size_t v_i_3464_, size_t v_stop_3465_, lean_object* v_b_3466_){
_start:
{
lean_object* v___x_3467_; 
v___x_3467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3463_, v_i_3464_, v_stop_3465_, v_b_3466_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___boxed(lean_object* v_00_u03b1_3468_, lean_object* v_as_3469_, lean_object* v_i_3470_, lean_object* v_stop_3471_, lean_object* v_b_3472_){
_start:
{
size_t v_i_boxed_3473_; size_t v_stop_boxed_3474_; lean_object* v_res_3475_; 
v_i_boxed_3473_ = lean_unbox_usize(v_i_3470_);
lean_dec(v_i_3470_);
v_stop_boxed_3474_ = lean_unbox_usize(v_stop_3471_);
lean_dec(v_stop_3471_);
v_res_3475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(v_00_u03b1_3468_, v_as_3469_, v_i_boxed_3473_, v_stop_boxed_3474_, v_b_3472_);
lean_dec_ref(v_as_3469_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend___redArg(){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = ((lean_object*)(l_Array_instAppend___redArg___closed__0));
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend___redArg___boxed(lean_object* v___dummy_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Array_instAppend___redArg();
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend(lean_object* v_00_u03b1_3481_){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = ((lean_object*)(l_Array_instAppend___redArg___closed__0));
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object* v_x_3483_, lean_object* v_x_3484_){
_start:
{
if (lean_obj_tag(v_x_3484_) == 0)
{
return v_x_3483_;
}
else
{
lean_object* v_head_3485_; lean_object* v_tail_3486_; lean_object* v___x_3487_; 
v_head_3485_ = lean_ctor_get(v_x_3484_, 0);
lean_inc(v_head_3485_);
v_tail_3486_ = lean_ctor_get(v_x_3484_, 1);
lean_inc(v_tail_3486_);
lean_dec_ref_known(v_x_3484_, 2);
v___x_3487_ = lean_array_push(v_x_3483_, v_head_3485_);
v_x_3483_ = v___x_3487_;
v_x_3484_ = v_tail_3486_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_appendList___redArg(lean_object* v_as_3489_, lean_object* v_bs_3490_){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3489_, v_bs_3490_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Array_appendList(lean_object* v_00_u03b1_3492_, lean_object* v_as_3493_, lean_object* v_bs_3494_){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3493_, v_bs_3494_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0(lean_object* v_00_u03b1_3496_, lean_object* v_x_3497_, lean_object* v_x_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_3497_, v_x_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList___redArg(){
_start:
{
lean_object* v___x_3502_; 
v___x_3502_ = ((lean_object*)(l_Array_instHAppendList___redArg___closed__0));
return v___x_3502_;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList___redArg___boxed(lean_object* v___dummy_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_Array_instHAppendList___redArg();
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList(lean_object* v_00_u03b1_3505_){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = ((lean_object*)(l_Array_instHAppendList___redArg___closed__0));
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0(lean_object* v_bs_3507_, lean_object* v_toPure_3508_, lean_object* v_____do__lift_3509_){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = l_Array_append___redArg(v_bs_3507_, v_____do__lift_3509_);
v___x_3511_ = lean_apply_2(v_toPure_3508_, lean_box(0), v___x_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0___boxed(lean_object* v_bs_3512_, lean_object* v_toPure_3513_, lean_object* v_____do__lift_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Array_flatMapM___redArg___lam__0(v_bs_3512_, v_toPure_3513_, v_____do__lift_3514_);
lean_dec_ref(v_____do__lift_3514_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__1(lean_object* v_toPure_3516_, lean_object* v_f_3517_, lean_object* v_toBind_3518_, lean_object* v_bs_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v___f_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___f_3521_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3521_, 0, v_bs_3519_);
lean_closure_set(v___f_3521_, 1, v_toPure_3516_);
v___x_3522_ = lean_apply_1(v_f_3517_, v_a_3520_);
v___x_3523_ = lean_apply_4(v_toBind_3518_, lean_box(0), lean_box(0), v___x_3522_, v___f_3521_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg(lean_object* v_inst_3524_, lean_object* v_f_3525_, lean_object* v_as_3526_){
_start:
{
lean_object* v_toApplicative_3527_; lean_object* v_toBind_3528_; lean_object* v_toPure_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; uint8_t v___x_3533_; 
v_toApplicative_3527_ = lean_ctor_get(v_inst_3524_, 0);
v_toBind_3528_ = lean_ctor_get(v_inst_3524_, 1);
v_toPure_3529_ = lean_ctor_get(v_toApplicative_3527_, 1);
v___x_3530_ = lean_unsigned_to_nat(0u);
v___x_3531_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3532_ = lean_array_get_size(v_as_3526_);
v___x_3533_ = lean_nat_dec_lt(v___x_3530_, v___x_3532_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3534_; 
lean_inc(v_toPure_3529_);
lean_dec_ref(v_as_3526_);
lean_dec(v_f_3525_);
lean_dec_ref(v_inst_3524_);
v___x_3534_ = lean_apply_2(v_toPure_3529_, lean_box(0), v___x_3531_);
return v___x_3534_;
}
else
{
lean_object* v___f_3535_; size_t v___x_3536_; size_t v___x_3537_; lean_object* v___x_3538_; 
lean_inc(v_toBind_3528_);
lean_inc(v_toPure_3529_);
v___f_3535_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3535_, 0, v_toPure_3529_);
lean_closure_set(v___f_3535_, 1, v_f_3525_);
lean_closure_set(v___f_3535_, 2, v_toBind_3528_);
v___x_3536_ = ((size_t)0ULL);
v___x_3537_ = lean_usize_of_nat(v___x_3532_);
v___x_3538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3524_, v___f_3535_, v_as_3526_, v___x_3536_, v___x_3537_, v___x_3531_);
return v___x_3538_;
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM(lean_object* v_00_u03b1_3539_, lean_object* v_m_3540_, lean_object* v_00_u03b2_3541_, lean_object* v_inst_3542_, lean_object* v_f_3543_, lean_object* v_as_3544_){
_start:
{
lean_object* v_toApplicative_3545_; lean_object* v_toBind_3546_; lean_object* v_toPure_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; 
v_toApplicative_3545_ = lean_ctor_get(v_inst_3542_, 0);
v_toBind_3546_ = lean_ctor_get(v_inst_3542_, 1);
v_toPure_3547_ = lean_ctor_get(v_toApplicative_3545_, 1);
v___x_3548_ = lean_unsigned_to_nat(0u);
v___x_3549_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3550_ = lean_array_get_size(v_as_3544_);
v___x_3551_ = lean_nat_dec_lt(v___x_3548_, v___x_3550_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; 
lean_inc(v_toPure_3547_);
lean_dec_ref(v_as_3544_);
lean_dec(v_f_3543_);
lean_dec_ref(v_inst_3542_);
v___x_3552_ = lean_apply_2(v_toPure_3547_, lean_box(0), v___x_3549_);
return v___x_3552_;
}
else
{
lean_object* v___f_3553_; size_t v___x_3554_; size_t v___x_3555_; lean_object* v___x_3556_; 
lean_inc(v_toBind_3546_);
lean_inc(v_toPure_3547_);
v___f_3553_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3553_, 0, v_toPure_3547_);
lean_closure_set(v___f_3553_, 1, v_f_3543_);
lean_closure_set(v___f_3553_, 2, v_toBind_3546_);
v___x_3554_ = ((size_t)0ULL);
v___x_3555_ = lean_usize_of_nat(v___x_3550_);
v___x_3556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3542_, v___f_3553_, v_as_3544_, v___x_3554_, v___x_3555_, v___x_3549_);
return v___x_3556_;
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg___lam__0(lean_object* v_f_3557_, lean_object* v_x1_3558_, lean_object* v_x2_3559_){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = lean_apply_1(v_f_3557_, v_x2_3559_);
v___x_3561_ = l_Array_append___redArg(v_x1_3558_, v___x_3560_);
lean_dec_ref(v___x_3560_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg(lean_object* v_f_3562_, lean_object* v_as_3563_){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; uint8_t v___x_3568_; 
v___x_3564_ = lean_unsigned_to_nat(0u);
v___x_3565_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3566_ = lean_array_get_size(v_as_3563_);
v___x_3567_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3568_ = lean_nat_dec_lt(v___x_3564_, v___x_3566_);
if (v___x_3568_ == 0)
{
lean_dec_ref(v_as_3563_);
lean_dec_ref(v_f_3562_);
return v___x_3565_;
}
else
{
lean_object* v___f_3569_; size_t v___x_3570_; size_t v___x_3571_; lean_object* v___x_3572_; 
v___f_3569_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3569_, 0, v_f_3562_);
v___x_3570_ = ((size_t)0ULL);
v___x_3571_ = lean_usize_of_nat(v___x_3566_);
v___x_3572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3567_, v___f_3569_, v_as_3563_, v___x_3570_, v___x_3571_, v___x_3565_);
return v___x_3572_;
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap(lean_object* v_00_u03b1_3573_, lean_object* v_00_u03b2_3574_, lean_object* v_f_3575_, lean_object* v_as_3576_){
_start:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; 
v___x_3577_ = lean_unsigned_to_nat(0u);
v___x_3578_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3579_ = lean_array_get_size(v_as_3576_);
v___x_3580_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3581_ = lean_nat_dec_lt(v___x_3577_, v___x_3579_);
if (v___x_3581_ == 0)
{
lean_dec_ref(v_as_3576_);
lean_dec_ref(v_f_3575_);
return v___x_3578_;
}
else
{
lean_object* v___f_3582_; size_t v___x_3583_; size_t v___x_3584_; lean_object* v___x_3585_; 
v___f_3582_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3582_, 0, v_f_3575_);
v___x_3583_ = ((size_t)0ULL);
v___x_3584_ = lean_usize_of_nat(v___x_3579_);
v___x_3585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3580_, v___f_3582_, v_as_3576_, v___x_3583_, v___x_3584_, v___x_3578_);
return v___x_3585_;
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten___redArg(lean_object* v_xss_3587_){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; uint8_t v___x_3592_; 
v___x_3588_ = lean_unsigned_to_nat(0u);
v___x_3589_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3590_ = lean_array_get_size(v_xss_3587_);
v___x_3591_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3592_ = lean_nat_dec_lt(v___x_3588_, v___x_3590_);
if (v___x_3592_ == 0)
{
lean_dec_ref(v_xss_3587_);
return v___x_3589_;
}
else
{
lean_object* v___f_3593_; size_t v___x_3594_; size_t v___x_3595_; lean_object* v___x_3596_; 
v___f_3593_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3594_ = ((size_t)0ULL);
v___x_3595_ = lean_usize_of_nat(v___x_3590_);
v___x_3596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3591_, v___f_3593_, v_xss_3587_, v___x_3594_, v___x_3595_, v___x_3589_);
return v___x_3596_;
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten(lean_object* v_00_u03b1_3597_, lean_object* v_xss_3598_){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; uint8_t v___x_3603_; 
v___x_3599_ = lean_unsigned_to_nat(0u);
v___x_3600_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_3601_ = lean_array_get_size(v_xss_3598_);
v___x_3602_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3603_ = lean_nat_dec_lt(v___x_3599_, v___x_3601_);
if (v___x_3603_ == 0)
{
lean_dec_ref(v_xss_3598_);
return v___x_3600_;
}
else
{
lean_object* v___f_3604_; size_t v___x_3605_; size_t v___x_3606_; lean_object* v___x_3607_; 
v___f_3604_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3605_ = ((size_t)0ULL);
v___x_3606_ = lean_usize_of_nat(v___x_3601_);
v___x_3607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3602_, v___f_3604_, v_xss_3598_, v___x_3605_, v___x_3606_, v___x_3600_);
return v___x_3607_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop___redArg(lean_object* v_as_3608_, lean_object* v_i_3609_, lean_object* v_j_3610_){
_start:
{
uint8_t v___x_3611_; 
v___x_3611_ = lean_nat_dec_lt(v_i_3609_, v_j_3610_);
if (v___x_3611_ == 0)
{
lean_dec(v_j_3610_);
lean_dec(v_i_3609_);
return v_as_3608_;
}
else
{
lean_object* v_as_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v_as_3612_ = lean_array_fswap(v_as_3608_, v_i_3609_, v_j_3610_);
v___x_3613_ = lean_unsigned_to_nat(1u);
v___x_3614_ = lean_nat_add(v_i_3609_, v___x_3613_);
lean_dec(v_i_3609_);
v___x_3615_ = lean_nat_sub(v_j_3610_, v___x_3613_);
lean_dec(v_j_3610_);
v_as_3608_ = v_as_3612_;
v_i_3609_ = v___x_3614_;
v_j_3610_ = v___x_3615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop(lean_object* v_00_u03b1_3617_, lean_object* v_as_3618_, lean_object* v_i_3619_, lean_object* v_j_3620_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_Array_reverse_loop___redArg(v_as_3618_, v_i_3619_, v_j_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Array_reverse___redArg(lean_object* v_as_3622_){
_start:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; 
v___x_3623_ = lean_array_get_size(v_as_3622_);
v___x_3624_ = lean_unsigned_to_nat(1u);
v___x_3625_ = lean_nat_dec_le(v___x_3623_, v___x_3624_);
if (v___x_3625_ == 0)
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3626_ = lean_unsigned_to_nat(0u);
v___x_3627_ = lean_nat_sub(v___x_3623_, v___x_3624_);
v___x_3628_ = l_Array_reverse_loop___redArg(v_as_3622_, v___x_3626_, v___x_3627_);
return v___x_3628_;
}
else
{
return v_as_3622_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse(lean_object* v_00_u03b1_3629_, lean_object* v_as_3630_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l_Array_reverse___redArg(v_as_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___lam__0(lean_object* v_p_3632_, lean_object* v_x1_3633_, lean_object* v_x2_3634_){
_start:
{
lean_object* v___x_3635_; uint8_t v___x_3636_; 
lean_inc(v_x2_3634_);
v___x_3635_ = lean_apply_1(v_p_3632_, v_x2_3634_);
v___x_3636_ = lean_unbox(v___x_3635_);
if (v___x_3636_ == 0)
{
lean_dec(v_x2_3634_);
return v_x1_3633_;
}
else
{
lean_object* v___x_3637_; 
v___x_3637_ = lean_array_push(v_x1_3633_, v_x2_3634_);
return v___x_3637_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg(lean_object* v_p_3640_, lean_object* v_as_3641_, lean_object* v_start_3642_, lean_object* v_stop_3643_){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
v___x_3644_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3645_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3646_ = lean_nat_dec_lt(v_start_3642_, v_stop_3643_);
if (v___x_3646_ == 0)
{
lean_dec_ref(v_as_3641_);
lean_dec_ref(v_p_3640_);
return v___x_3644_;
}
else
{
lean_object* v___f_3647_; lean_object* v___x_3648_; uint8_t v___x_3649_; 
v___f_3647_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3647_, 0, v_p_3640_);
v___x_3648_ = lean_array_get_size(v_as_3641_);
v___x_3649_ = lean_nat_dec_le(v_stop_3643_, v___x_3648_);
if (v___x_3649_ == 0)
{
uint8_t v___x_3650_; 
v___x_3650_ = lean_nat_dec_lt(v_start_3642_, v___x_3648_);
if (v___x_3650_ == 0)
{
lean_dec_ref(v___f_3647_);
lean_dec_ref(v_as_3641_);
return v___x_3644_;
}
else
{
size_t v___x_3651_; size_t v___x_3652_; lean_object* v___x_3653_; 
v___x_3651_ = lean_usize_of_nat(v_start_3642_);
v___x_3652_ = lean_usize_of_nat(v___x_3648_);
v___x_3653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3645_, v___f_3647_, v_as_3641_, v___x_3651_, v___x_3652_, v___x_3644_);
return v___x_3653_;
}
}
else
{
size_t v___x_3654_; size_t v___x_3655_; lean_object* v___x_3656_; 
v___x_3654_ = lean_usize_of_nat(v_start_3642_);
v___x_3655_ = lean_usize_of_nat(v_stop_3643_);
v___x_3656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3645_, v___f_3647_, v_as_3641_, v___x_3654_, v___x_3655_, v___x_3644_);
return v___x_3656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___boxed(lean_object* v_p_3657_, lean_object* v_as_3658_, lean_object* v_start_3659_, lean_object* v_stop_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l_Array_filter___redArg(v_p_3657_, v_as_3658_, v_start_3659_, v_stop_3660_);
lean_dec(v_stop_3660_);
lean_dec(v_start_3659_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_Array_filter(lean_object* v_00_u03b1_3662_, lean_object* v_p_3663_, lean_object* v_as_3664_, lean_object* v_start_3665_, lean_object* v_stop_3666_){
_start:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; 
v___x_3667_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3668_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3669_ = lean_nat_dec_lt(v_start_3665_, v_stop_3666_);
if (v___x_3669_ == 0)
{
lean_dec_ref(v_as_3664_);
lean_dec_ref(v_p_3663_);
return v___x_3667_;
}
else
{
lean_object* v___f_3670_; lean_object* v___x_3671_; uint8_t v___x_3672_; 
v___f_3670_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3670_, 0, v_p_3663_);
v___x_3671_ = lean_array_get_size(v_as_3664_);
v___x_3672_ = lean_nat_dec_le(v_stop_3666_, v___x_3671_);
if (v___x_3672_ == 0)
{
uint8_t v___x_3673_; 
v___x_3673_ = lean_nat_dec_lt(v_start_3665_, v___x_3671_);
if (v___x_3673_ == 0)
{
lean_dec_ref(v___f_3670_);
lean_dec_ref(v_as_3664_);
return v___x_3667_;
}
else
{
size_t v___x_3674_; size_t v___x_3675_; lean_object* v___x_3676_; 
v___x_3674_ = lean_usize_of_nat(v_start_3665_);
v___x_3675_ = lean_usize_of_nat(v___x_3671_);
v___x_3676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3668_, v___f_3670_, v_as_3664_, v___x_3674_, v___x_3675_, v___x_3667_);
return v___x_3676_;
}
}
else
{
size_t v___x_3677_; size_t v___x_3678_; lean_object* v___x_3679_; 
v___x_3677_ = lean_usize_of_nat(v_start_3665_);
v___x_3678_ = lean_usize_of_nat(v_stop_3666_);
v___x_3679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3668_, v___f_3670_, v_as_3664_, v___x_3677_, v___x_3678_, v___x_3667_);
return v___x_3679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___boxed(lean_object* v_00_u03b1_3680_, lean_object* v_p_3681_, lean_object* v_as_3682_, lean_object* v_start_3683_, lean_object* v_stop_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Array_filter(v_00_u03b1_3680_, v_p_3681_, v_as_3682_, v_start_3683_, v_stop_3684_);
lean_dec(v_stop_3684_);
lean_dec(v_start_3683_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0(lean_object* v_toPure_3686_, lean_object* v_acc_3687_, lean_object* v_a_3688_, uint8_t v_____do__lift_3689_){
_start:
{
if (v_____do__lift_3689_ == 0)
{
lean_object* v___x_3690_; 
lean_dec(v_a_3688_);
v___x_3690_ = lean_apply_2(v_toPure_3686_, lean_box(0), v_acc_3687_);
return v___x_3690_;
}
else
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3691_ = lean_array_push(v_acc_3687_, v_a_3688_);
v___x_3692_ = lean_apply_2(v_toPure_3686_, lean_box(0), v___x_3691_);
return v___x_3692_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0___boxed(lean_object* v_toPure_3693_, lean_object* v_acc_3694_, lean_object* v_a_3695_, lean_object* v_____do__lift_3696_){
_start:
{
uint8_t v_____do__lift_91__boxed_3697_; lean_object* v_res_3698_; 
v_____do__lift_91__boxed_3697_ = lean_unbox(v_____do__lift_3696_);
v_res_3698_ = l_Array_filterM___redArg___lam__0(v_toPure_3693_, v_acc_3694_, v_a_3695_, v_____do__lift_91__boxed_3697_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__1(lean_object* v_toPure_3699_, lean_object* v_p_3700_, lean_object* v_toBind_3701_, lean_object* v_acc_3702_, lean_object* v_a_3703_){
_start:
{
lean_object* v___f_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
lean_inc(v_a_3703_);
v___f_3704_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3704_, 0, v_toPure_3699_);
lean_closure_set(v___f_3704_, 1, v_acc_3702_);
lean_closure_set(v___f_3704_, 2, v_a_3703_);
v___x_3705_ = lean_apply_1(v_p_3700_, v_a_3703_);
v___x_3706_ = lean_apply_4(v_toBind_3701_, lean_box(0), lean_box(0), v___x_3705_, v___f_3704_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg(lean_object* v_inst_3707_, lean_object* v_p_3708_, lean_object* v_as_3709_, lean_object* v_start_3710_, lean_object* v_stop_3711_){
_start:
{
lean_object* v_toApplicative_3712_; lean_object* v_toBind_3713_; lean_object* v_toPure_3714_; lean_object* v___x_3715_; uint8_t v___x_3716_; 
v_toApplicative_3712_ = lean_ctor_get(v_inst_3707_, 0);
v_toBind_3713_ = lean_ctor_get(v_inst_3707_, 1);
v_toPure_3714_ = lean_ctor_get(v_toApplicative_3712_, 1);
v___x_3715_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3716_ = lean_nat_dec_lt(v_start_3710_, v_stop_3711_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; 
lean_inc(v_toPure_3714_);
lean_dec_ref(v_as_3709_);
lean_dec(v_p_3708_);
lean_dec_ref(v_inst_3707_);
v___x_3717_ = lean_apply_2(v_toPure_3714_, lean_box(0), v___x_3715_);
return v___x_3717_;
}
else
{
lean_object* v___f_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; 
lean_inc(v_toBind_3713_);
lean_inc(v_toPure_3714_);
v___f_3718_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3718_, 0, v_toPure_3714_);
lean_closure_set(v___f_3718_, 1, v_p_3708_);
lean_closure_set(v___f_3718_, 2, v_toBind_3713_);
v___x_3719_ = lean_array_get_size(v_as_3709_);
v___x_3720_ = lean_nat_dec_le(v_stop_3711_, v___x_3719_);
if (v___x_3720_ == 0)
{
uint8_t v___x_3721_; 
v___x_3721_ = lean_nat_dec_lt(v_start_3710_, v___x_3719_);
if (v___x_3721_ == 0)
{
lean_object* v___x_3722_; 
lean_inc(v_toPure_3714_);
lean_dec_ref(v___f_3718_);
lean_dec_ref(v_as_3709_);
lean_dec_ref(v_inst_3707_);
v___x_3722_ = lean_apply_2(v_toPure_3714_, lean_box(0), v___x_3715_);
return v___x_3722_;
}
else
{
size_t v___x_3723_; size_t v___x_3724_; lean_object* v___x_3725_; 
v___x_3723_ = lean_usize_of_nat(v_start_3710_);
v___x_3724_ = lean_usize_of_nat(v___x_3719_);
v___x_3725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3707_, v___f_3718_, v_as_3709_, v___x_3723_, v___x_3724_, v___x_3715_);
return v___x_3725_;
}
}
else
{
size_t v___x_3726_; size_t v___x_3727_; lean_object* v___x_3728_; 
v___x_3726_ = lean_usize_of_nat(v_start_3710_);
v___x_3727_ = lean_usize_of_nat(v_stop_3711_);
v___x_3728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3707_, v___f_3718_, v_as_3709_, v___x_3726_, v___x_3727_, v___x_3715_);
return v___x_3728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___boxed(lean_object* v_inst_3729_, lean_object* v_p_3730_, lean_object* v_as_3731_, lean_object* v_start_3732_, lean_object* v_stop_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_Array_filterM___redArg(v_inst_3729_, v_p_3730_, v_as_3731_, v_start_3732_, v_stop_3733_);
lean_dec(v_stop_3733_);
lean_dec(v_start_3732_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM(lean_object* v_m_3735_, lean_object* v_00_u03b1_3736_, lean_object* v_inst_3737_, lean_object* v_p_3738_, lean_object* v_as_3739_, lean_object* v_start_3740_, lean_object* v_stop_3741_){
_start:
{
lean_object* v_toApplicative_3742_; lean_object* v_toBind_3743_; lean_object* v_toPure_3744_; lean_object* v___x_3745_; uint8_t v___x_3746_; 
v_toApplicative_3742_ = lean_ctor_get(v_inst_3737_, 0);
v_toBind_3743_ = lean_ctor_get(v_inst_3737_, 1);
v_toPure_3744_ = lean_ctor_get(v_toApplicative_3742_, 1);
v___x_3745_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3746_ = lean_nat_dec_lt(v_start_3740_, v_stop_3741_);
if (v___x_3746_ == 0)
{
lean_object* v___x_3747_; 
lean_inc(v_toPure_3744_);
lean_dec_ref(v_as_3739_);
lean_dec(v_p_3738_);
lean_dec_ref(v_inst_3737_);
v___x_3747_ = lean_apply_2(v_toPure_3744_, lean_box(0), v___x_3745_);
return v___x_3747_;
}
else
{
lean_object* v___f_3748_; lean_object* v___x_3749_; uint8_t v___x_3750_; 
lean_inc(v_toBind_3743_);
lean_inc(v_toPure_3744_);
v___f_3748_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3748_, 0, v_toPure_3744_);
lean_closure_set(v___f_3748_, 1, v_p_3738_);
lean_closure_set(v___f_3748_, 2, v_toBind_3743_);
v___x_3749_ = lean_array_get_size(v_as_3739_);
v___x_3750_ = lean_nat_dec_le(v_stop_3741_, v___x_3749_);
if (v___x_3750_ == 0)
{
uint8_t v___x_3751_; 
v___x_3751_ = lean_nat_dec_lt(v_start_3740_, v___x_3749_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; 
lean_inc(v_toPure_3744_);
lean_dec_ref(v___f_3748_);
lean_dec_ref(v_as_3739_);
lean_dec_ref(v_inst_3737_);
v___x_3752_ = lean_apply_2(v_toPure_3744_, lean_box(0), v___x_3745_);
return v___x_3752_;
}
else
{
size_t v___x_3753_; size_t v___x_3754_; lean_object* v___x_3755_; 
v___x_3753_ = lean_usize_of_nat(v_start_3740_);
v___x_3754_ = lean_usize_of_nat(v___x_3749_);
v___x_3755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3737_, v___f_3748_, v_as_3739_, v___x_3753_, v___x_3754_, v___x_3745_);
return v___x_3755_;
}
}
else
{
size_t v___x_3756_; size_t v___x_3757_; lean_object* v___x_3758_; 
v___x_3756_ = lean_usize_of_nat(v_start_3740_);
v___x_3757_ = lean_usize_of_nat(v_stop_3741_);
v___x_3758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3737_, v___f_3748_, v_as_3739_, v___x_3756_, v___x_3757_, v___x_3745_);
return v___x_3758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___boxed(lean_object* v_m_3759_, lean_object* v_00_u03b1_3760_, lean_object* v_inst_3761_, lean_object* v_p_3762_, lean_object* v_as_3763_, lean_object* v_start_3764_, lean_object* v_stop_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l_Array_filterM(v_m_3759_, v_00_u03b1_3760_, v_inst_3761_, v_p_3762_, v_as_3763_, v_start_3764_, v_stop_3765_);
lean_dec(v_stop_3765_);
lean_dec(v_start_3764_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__1(lean_object* v_toPure_3767_, lean_object* v_p_3768_, lean_object* v_toBind_3769_, lean_object* v_a_3770_, lean_object* v_acc_3771_){
_start:
{
lean_object* v___f_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
lean_inc(v_a_3770_);
v___f_3772_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3772_, 0, v_toPure_3767_);
lean_closure_set(v___f_3772_, 1, v_acc_3771_);
lean_closure_set(v___f_3772_, 2, v_a_3770_);
v___x_3773_ = lean_apply_1(v_p_3768_, v_a_3770_);
v___x_3774_ = lean_apply_4(v_toBind_3769_, lean_box(0), lean_box(0), v___x_3773_, v___f_3772_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg(lean_object* v_inst_3776_, lean_object* v_p_3777_, lean_object* v_as_3778_, lean_object* v_start_3779_, lean_object* v_stop_3780_){
_start:
{
lean_object* v_toApplicative_3781_; lean_object* v_toFunctor_3782_; lean_object* v_toBind_3783_; lean_object* v_toPure_3784_; lean_object* v_map_3785_; lean_object* v___f_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; uint8_t v___x_3790_; 
v_toApplicative_3781_ = lean_ctor_get(v_inst_3776_, 0);
v_toFunctor_3782_ = lean_ctor_get(v_toApplicative_3781_, 0);
v_toBind_3783_ = lean_ctor_get(v_inst_3776_, 1);
v_toPure_3784_ = lean_ctor_get(v_toApplicative_3781_, 1);
v_map_3785_ = lean_ctor_get(v_toFunctor_3782_, 0);
lean_inc(v_map_3785_);
lean_inc(v_toBind_3783_);
lean_inc(v_toPure_3784_);
v___f_3786_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3786_, 0, v_toPure_3784_);
lean_closure_set(v___f_3786_, 1, v_p_3777_);
lean_closure_set(v___f_3786_, 2, v_toBind_3783_);
v___x_3787_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3788_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3789_ = lean_array_get_size(v_as_3778_);
v___x_3790_ = lean_nat_dec_le(v_start_3779_, v___x_3789_);
if (v___x_3790_ == 0)
{
uint8_t v___x_3791_; 
v___x_3791_ = lean_nat_dec_lt(v_stop_3780_, v___x_3789_);
if (v___x_3791_ == 0)
{
lean_object* v___x_3792_; lean_object* v___x_3793_; 
lean_inc(v_toPure_3784_);
lean_dec_ref(v___f_3786_);
lean_dec_ref(v_as_3778_);
lean_dec_ref(v_inst_3776_);
v___x_3792_ = lean_apply_2(v_toPure_3784_, lean_box(0), v___x_3788_);
v___x_3793_ = lean_apply_4(v_map_3785_, lean_box(0), lean_box(0), v___x_3787_, v___x_3792_);
return v___x_3793_;
}
else
{
size_t v___x_3794_; size_t v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3794_ = lean_usize_of_nat(v___x_3789_);
v___x_3795_ = lean_usize_of_nat(v_stop_3780_);
v___x_3796_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3776_, v___f_3786_, v_as_3778_, v___x_3794_, v___x_3795_, v___x_3788_);
v___x_3797_ = lean_apply_4(v_map_3785_, lean_box(0), lean_box(0), v___x_3787_, v___x_3796_);
return v___x_3797_;
}
}
else
{
uint8_t v___x_3798_; 
v___x_3798_ = lean_nat_dec_lt(v_stop_3780_, v_start_3779_);
if (v___x_3798_ == 0)
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
lean_inc(v_toPure_3784_);
lean_dec_ref(v___f_3786_);
lean_dec_ref(v_as_3778_);
lean_dec_ref(v_inst_3776_);
v___x_3799_ = lean_apply_2(v_toPure_3784_, lean_box(0), v___x_3788_);
v___x_3800_ = lean_apply_4(v_map_3785_, lean_box(0), lean_box(0), v___x_3787_, v___x_3799_);
return v___x_3800_;
}
else
{
size_t v___x_3801_; size_t v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3801_ = lean_usize_of_nat(v_start_3779_);
v___x_3802_ = lean_usize_of_nat(v_stop_3780_);
v___x_3803_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3776_, v___f_3786_, v_as_3778_, v___x_3801_, v___x_3802_, v___x_3788_);
v___x_3804_ = lean_apply_4(v_map_3785_, lean_box(0), lean_box(0), v___x_3787_, v___x_3803_);
return v___x_3804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___boxed(lean_object* v_inst_3805_, lean_object* v_p_3806_, lean_object* v_as_3807_, lean_object* v_start_3808_, lean_object* v_stop_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_Array_filterRevM___redArg(v_inst_3805_, v_p_3806_, v_as_3807_, v_start_3808_, v_stop_3809_);
lean_dec(v_stop_3809_);
lean_dec(v_start_3808_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM(lean_object* v_m_3811_, lean_object* v_00_u03b1_3812_, lean_object* v_inst_3813_, lean_object* v_p_3814_, lean_object* v_as_3815_, lean_object* v_start_3816_, lean_object* v_stop_3817_){
_start:
{
lean_object* v_toApplicative_3818_; lean_object* v_toFunctor_3819_; lean_object* v_toBind_3820_; lean_object* v_toPure_3821_; lean_object* v_map_3822_; lean_object* v___f_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v_toApplicative_3818_ = lean_ctor_get(v_inst_3813_, 0);
v_toFunctor_3819_ = lean_ctor_get(v_toApplicative_3818_, 0);
v_toBind_3820_ = lean_ctor_get(v_inst_3813_, 1);
v_toPure_3821_ = lean_ctor_get(v_toApplicative_3818_, 1);
v_map_3822_ = lean_ctor_get(v_toFunctor_3819_, 0);
lean_inc(v_map_3822_);
lean_inc(v_toBind_3820_);
lean_inc(v_toPure_3821_);
v___f_3823_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3823_, 0, v_toPure_3821_);
lean_closure_set(v___f_3823_, 1, v_p_3814_);
lean_closure_set(v___f_3823_, 2, v_toBind_3820_);
v___x_3824_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3825_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3826_ = lean_array_get_size(v_as_3815_);
v___x_3827_ = lean_nat_dec_le(v_start_3816_, v___x_3826_);
if (v___x_3827_ == 0)
{
uint8_t v___x_3828_; 
v___x_3828_ = lean_nat_dec_lt(v_stop_3817_, v___x_3826_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
lean_inc(v_toPure_3821_);
lean_dec_ref(v___f_3823_);
lean_dec_ref(v_as_3815_);
lean_dec_ref(v_inst_3813_);
v___x_3829_ = lean_apply_2(v_toPure_3821_, lean_box(0), v___x_3825_);
v___x_3830_ = lean_apply_4(v_map_3822_, lean_box(0), lean_box(0), v___x_3824_, v___x_3829_);
return v___x_3830_;
}
else
{
size_t v___x_3831_; size_t v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3831_ = lean_usize_of_nat(v___x_3826_);
v___x_3832_ = lean_usize_of_nat(v_stop_3817_);
v___x_3833_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3813_, v___f_3823_, v_as_3815_, v___x_3831_, v___x_3832_, v___x_3825_);
v___x_3834_ = lean_apply_4(v_map_3822_, lean_box(0), lean_box(0), v___x_3824_, v___x_3833_);
return v___x_3834_;
}
}
else
{
uint8_t v___x_3835_; 
v___x_3835_ = lean_nat_dec_lt(v_stop_3817_, v_start_3816_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
lean_inc(v_toPure_3821_);
lean_dec_ref(v___f_3823_);
lean_dec_ref(v_as_3815_);
lean_dec_ref(v_inst_3813_);
v___x_3836_ = lean_apply_2(v_toPure_3821_, lean_box(0), v___x_3825_);
v___x_3837_ = lean_apply_4(v_map_3822_, lean_box(0), lean_box(0), v___x_3824_, v___x_3836_);
return v___x_3837_;
}
else
{
size_t v___x_3838_; size_t v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3838_ = lean_usize_of_nat(v_start_3816_);
v___x_3839_ = lean_usize_of_nat(v_stop_3817_);
v___x_3840_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3813_, v___f_3823_, v_as_3815_, v___x_3838_, v___x_3839_, v___x_3825_);
v___x_3841_ = lean_apply_4(v_map_3822_, lean_box(0), lean_box(0), v___x_3824_, v___x_3840_);
return v___x_3841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___boxed(lean_object* v_m_3842_, lean_object* v_00_u03b1_3843_, lean_object* v_inst_3844_, lean_object* v_p_3845_, lean_object* v_as_3846_, lean_object* v_start_3847_, lean_object* v_stop_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_Array_filterRevM(v_m_3842_, v_00_u03b1_3843_, v_inst_3844_, v_p_3845_, v_as_3846_, v_start_3847_, v_stop_3848_);
lean_dec(v_stop_3848_);
lean_dec(v_start_3847_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__0(lean_object* v_toPure_3850_, lean_object* v_bs_3851_, lean_object* v_____do__lift_3852_){
_start:
{
if (lean_obj_tag(v_____do__lift_3852_) == 0)
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_apply_2(v_toPure_3850_, lean_box(0), v_bs_3851_);
return v___x_3853_;
}
else
{
lean_object* v_val_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v_val_3854_ = lean_ctor_get(v_____do__lift_3852_, 0);
lean_inc(v_val_3854_);
lean_dec_ref_known(v_____do__lift_3852_, 1);
v___x_3855_ = lean_array_push(v_bs_3851_, v_val_3854_);
v___x_3856_ = lean_apply_2(v_toPure_3850_, lean_box(0), v___x_3855_);
return v___x_3856_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__1(lean_object* v_toPure_3857_, lean_object* v_f_3858_, lean_object* v_toBind_3859_, lean_object* v_bs_3860_, lean_object* v_a_3861_){
_start:
{
lean_object* v___f_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___f_3862_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3862_, 0, v_toPure_3857_);
lean_closure_set(v___f_3862_, 1, v_bs_3860_);
v___x_3863_ = lean_apply_1(v_f_3858_, v_a_3861_);
v___x_3864_ = lean_apply_4(v_toBind_3859_, lean_box(0), lean_box(0), v___x_3863_, v___f_3862_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg(lean_object* v_inst_3865_, lean_object* v_f_3866_, lean_object* v_as_3867_, lean_object* v_start_3868_, lean_object* v_stop_3869_){
_start:
{
lean_object* v_toApplicative_3870_; lean_object* v_toBind_3871_; lean_object* v_toPure_3872_; lean_object* v___x_3873_; uint8_t v___x_3874_; 
v_toApplicative_3870_ = lean_ctor_get(v_inst_3865_, 0);
v_toBind_3871_ = lean_ctor_get(v_inst_3865_, 1);
v_toPure_3872_ = lean_ctor_get(v_toApplicative_3870_, 1);
v___x_3873_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3874_ = lean_nat_dec_lt(v_start_3868_, v_stop_3869_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3875_; 
lean_inc(v_toPure_3872_);
lean_dec_ref(v_as_3867_);
lean_dec(v_f_3866_);
lean_dec_ref(v_inst_3865_);
v___x_3875_ = lean_apply_2(v_toPure_3872_, lean_box(0), v___x_3873_);
return v___x_3875_;
}
else
{
lean_object* v___f_3876_; lean_object* v___x_3877_; uint8_t v___x_3878_; 
lean_inc(v_toBind_3871_);
lean_inc(v_toPure_3872_);
v___f_3876_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3876_, 0, v_toPure_3872_);
lean_closure_set(v___f_3876_, 1, v_f_3866_);
lean_closure_set(v___f_3876_, 2, v_toBind_3871_);
v___x_3877_ = lean_array_get_size(v_as_3867_);
v___x_3878_ = lean_nat_dec_le(v_stop_3869_, v___x_3877_);
if (v___x_3878_ == 0)
{
uint8_t v___x_3879_; 
v___x_3879_ = lean_nat_dec_lt(v_start_3868_, v___x_3877_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; 
lean_inc(v_toPure_3872_);
lean_dec_ref(v___f_3876_);
lean_dec_ref(v_as_3867_);
lean_dec_ref(v_inst_3865_);
v___x_3880_ = lean_apply_2(v_toPure_3872_, lean_box(0), v___x_3873_);
return v___x_3880_;
}
else
{
size_t v___x_3881_; size_t v___x_3882_; lean_object* v___x_3883_; 
v___x_3881_ = lean_usize_of_nat(v_start_3868_);
v___x_3882_ = lean_usize_of_nat(v___x_3877_);
v___x_3883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3865_, v___f_3876_, v_as_3867_, v___x_3881_, v___x_3882_, v___x_3873_);
return v___x_3883_;
}
}
else
{
size_t v___x_3884_; size_t v___x_3885_; lean_object* v___x_3886_; 
v___x_3884_ = lean_usize_of_nat(v_start_3868_);
v___x_3885_ = lean_usize_of_nat(v_stop_3869_);
v___x_3886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3865_, v___f_3876_, v_as_3867_, v___x_3884_, v___x_3885_, v___x_3873_);
return v___x_3886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___boxed(lean_object* v_inst_3887_, lean_object* v_f_3888_, lean_object* v_as_3889_, lean_object* v_start_3890_, lean_object* v_stop_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Array_filterMapM___redArg(v_inst_3887_, v_f_3888_, v_as_3889_, v_start_3890_, v_stop_3891_);
lean_dec(v_stop_3891_);
lean_dec(v_start_3890_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM(lean_object* v_00_u03b1_3893_, lean_object* v_m_3894_, lean_object* v_00_u03b2_3895_, lean_object* v_inst_3896_, lean_object* v_f_3897_, lean_object* v_as_3898_, lean_object* v_start_3899_, lean_object* v_stop_3900_){
_start:
{
lean_object* v___x_3901_; 
v___x_3901_ = l_Array_filterMapM___redArg(v_inst_3896_, v_f_3897_, v_as_3898_, v_start_3899_, v_stop_3900_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___boxed(lean_object* v_00_u03b1_3902_, lean_object* v_m_3903_, lean_object* v_00_u03b2_3904_, lean_object* v_inst_3905_, lean_object* v_f_3906_, lean_object* v_as_3907_, lean_object* v_start_3908_, lean_object* v_stop_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Array_filterMapM(v_00_u03b1_3902_, v_m_3903_, v_00_u03b2_3904_, v_inst_3905_, v_f_3906_, v_as_3907_, v_start_3908_, v_stop_3909_);
lean_dec(v_stop_3909_);
lean_dec(v_start_3908_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg(lean_object* v_f_3911_, lean_object* v_as_3912_, lean_object* v_start_3913_, lean_object* v_stop_3914_){
_start:
{
lean_object* v___f_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___f_3915_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3915_, 0, v_f_3911_);
v___x_3916_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3917_ = l_Array_filterMapM___redArg(v___x_3916_, v___f_3915_, v_as_3912_, v_start_3913_, v_stop_3914_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg___boxed(lean_object* v_f_3918_, lean_object* v_as_3919_, lean_object* v_start_3920_, lean_object* v_stop_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l_Array_filterMap___redArg(v_f_3918_, v_as_3919_, v_start_3920_, v_stop_3921_);
lean_dec(v_stop_3921_);
lean_dec(v_start_3920_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap(lean_object* v_00_u03b1_3923_, lean_object* v_00_u03b2_3924_, lean_object* v_f_3925_, lean_object* v_as_3926_, lean_object* v_start_3927_, lean_object* v_stop_3928_){
_start:
{
lean_object* v___f_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___f_3929_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3929_, 0, v_f_3925_);
v___x_3930_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3931_ = l_Array_filterMapM___redArg(v___x_3930_, v___f_3929_, v_as_3926_, v_start_3927_, v_stop_3928_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___boxed(lean_object* v_00_u03b1_3932_, lean_object* v_00_u03b2_3933_, lean_object* v_f_3934_, lean_object* v_as_3935_, lean_object* v_start_3936_, lean_object* v_stop_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l_Array_filterMap(v_00_u03b1_3932_, v_00_u03b2_3933_, v_f_3934_, v_as_3935_, v_start_3936_, v_stop_3937_);
lean_dec(v_stop_3937_);
lean_dec(v_start_3936_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg___lam__0(lean_object* v_lt_3939_, lean_object* v_x1_3940_, lean_object* v_x2_3941_){
_start:
{
lean_object* v___x_3942_; uint8_t v___x_3943_; 
lean_inc(v_x2_3941_);
lean_inc(v_x1_3940_);
v___x_3942_ = lean_apply_2(v_lt_3939_, v_x1_3940_, v_x2_3941_);
v___x_3943_ = lean_unbox(v___x_3942_);
if (v___x_3943_ == 0)
{
lean_dec(v_x2_3941_);
return v_x1_3940_;
}
else
{
lean_dec(v_x1_3940_);
return v_x2_3941_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg(lean_object* v_as_3944_, lean_object* v_lt_3945_){
_start:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; uint8_t v___x_3948_; 
v___x_3946_ = lean_unsigned_to_nat(0u);
v___x_3947_ = lean_array_get_size(v_as_3944_);
v___x_3948_ = lean_nat_dec_lt(v___x_3946_, v___x_3947_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; 
lean_dec_ref(v_lt_3945_);
lean_dec_ref(v_as_3944_);
v___x_3949_ = lean_box(0);
return v___x_3949_;
}
else
{
lean_object* v_a0_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; uint8_t v___x_3953_; 
v_a0_3950_ = lean_array_fget(v_as_3944_, v___x_3946_);
v___x_3951_ = lean_unsigned_to_nat(1u);
v___x_3952_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3953_ = lean_nat_dec_lt(v___x_3951_, v___x_3947_);
if (v___x_3953_ == 0)
{
lean_object* v___x_3954_; 
lean_dec_ref(v_lt_3945_);
lean_dec_ref(v_as_3944_);
v___x_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3954_, 0, v_a0_3950_);
return v___x_3954_;
}
else
{
lean_object* v___f_3955_; size_t v___x_3956_; size_t v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___f_3955_ = lean_alloc_closure((void*)(l_Array_getMax_x3f___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3955_, 0, v_lt_3945_);
v___x_3956_ = ((size_t)1ULL);
v___x_3957_ = lean_usize_of_nat(v___x_3947_);
v___x_3958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3952_, v___f_3955_, v_as_3944_, v___x_3956_, v___x_3957_, v_a0_3950_);
v___x_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
return v___x_3959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f(lean_object* v_00_u03b1_3960_, lean_object* v_as_3961_, lean_object* v_lt_3962_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l_Array_getMax_x3f___redArg(v_as_3961_, v_lt_3962_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg___lam__0(lean_object* v_p_3964_, lean_object* v_a_3965_, lean_object* v_x_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v_fst_3968_; lean_object* v_snd_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3985_; 
v_fst_3968_ = lean_ctor_get(v___y_3967_, 0);
v_snd_3969_ = lean_ctor_get(v___y_3967_, 1);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___y_3967_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3971_ = v___y_3967_;
v_isShared_3972_ = v_isSharedCheck_3985_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_snd_3969_);
lean_inc(v_fst_3968_);
lean_dec(v___y_3967_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3985_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3973_; uint8_t v___x_3974_; 
lean_inc(v_a_3965_);
v___x_3973_ = lean_apply_1(v_p_3964_, v_a_3965_);
v___x_3974_ = lean_unbox(v___x_3973_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3975_; lean_object* v___x_3977_; 
v___x_3975_ = lean_array_push(v_snd_3969_, v_a_3965_);
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 1, v___x_3975_);
v___x_3977_ = v___x_3971_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_fst_3968_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v___x_3975_);
v___x_3977_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
lean_object* v___x_3978_; 
v___x_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
return v___x_3978_;
}
}
else
{
lean_object* v___x_3980_; lean_object* v___x_3982_; 
v___x_3980_ = lean_array_push(v_fst_3968_, v_a_3965_);
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 0, v___x_3980_);
v___x_3982_ = v___x_3971_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3980_);
lean_ctor_set(v_reuseFailAlloc_3984_, 1, v_snd_3969_);
v___x_3982_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
lean_object* v___x_3983_; 
v___x_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3982_);
return v___x_3983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg(lean_object* v_p_3988_, lean_object* v_as_3989_){
_start:
{
lean_object* v___f_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; size_t v_sz_3993_; size_t v___x_3994_; lean_object* v___x_3995_; lean_object* v_fst_3996_; lean_object* v_snd_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
v___f_3990_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3990_, 0, v_p_3988_);
v___x_3991_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3992_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_3993_ = lean_array_size(v_as_3989_);
v___x_3994_ = ((size_t)0ULL);
v___x_3995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_3991_, v_as_3989_, v___f_3990_, v_sz_3993_, v___x_3994_, v___x_3992_);
v_fst_3996_ = lean_ctor_get(v___x_3995_, 0);
v_snd_3997_ = lean_ctor_get(v___x_3995_, 1);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3995_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_snd_3997_);
lean_inc(v_fst_3996_);
lean_dec(v___x_3995_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4002_; 
if (v_isShared_4000_ == 0)
{
v___x_4002_ = v___x_3999_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_fst_3996_);
lean_ctor_set(v_reuseFailAlloc_4003_, 1, v_snd_3997_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition(lean_object* v_00_u03b1_4005_, lean_object* v_p_4006_, lean_object* v_as_4007_){
_start:
{
lean_object* v___f_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; size_t v_sz_4011_; size_t v___x_4012_; lean_object* v___x_4013_; lean_object* v_fst_4014_; lean_object* v_snd_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
v___f_4008_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4008_, 0, v_p_4006_);
v___x_4009_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4010_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_4011_ = lean_array_size(v_as_4007_);
v___x_4012_ = ((size_t)0ULL);
v___x_4013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_4009_, v_as_4007_, v___f_4008_, v_sz_4011_, v___x_4012_, v___x_4010_);
v_fst_4014_ = lean_ctor_get(v___x_4013_, 0);
v_snd_4015_ = lean_ctor_get(v___x_4013_, 1);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_4013_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_snd_4015_);
lean_inc(v_fst_4014_);
lean_dec(v___x_4013_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_fst_4014_);
lean_ctor_set(v_reuseFailAlloc_4021_, 1, v_snd_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile___redArg(lean_object* v_p_4023_, lean_object* v_as_4024_){
_start:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; uint8_t v___x_4027_; 
v___x_4025_ = lean_unsigned_to_nat(0u);
v___x_4026_ = lean_array_get_size(v_as_4024_);
v___x_4027_ = lean_nat_dec_lt(v___x_4025_, v___x_4026_);
if (v___x_4027_ == 0)
{
lean_dec_ref(v_p_4023_);
return v_as_4024_;
}
else
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; uint8_t v___x_4032_; 
v___x_4028_ = lean_unsigned_to_nat(1u);
v___x_4029_ = lean_nat_sub(v___x_4026_, v___x_4028_);
v___x_4030_ = lean_array_fget_borrowed(v_as_4024_, v___x_4029_);
lean_dec(v___x_4029_);
lean_inc_ref(v_p_4023_);
lean_inc(v___x_4030_);
v___x_4031_ = lean_apply_1(v_p_4023_, v___x_4030_);
v___x_4032_ = lean_unbox(v___x_4031_);
if (v___x_4032_ == 0)
{
lean_dec_ref(v_p_4023_);
return v_as_4024_;
}
else
{
lean_object* v___x_4033_; 
v___x_4033_ = lean_array_pop(v_as_4024_);
v_as_4024_ = v___x_4033_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile(lean_object* v_00_u03b1_4035_, lean_object* v_p_4036_, lean_object* v_as_4037_){
_start:
{
lean_object* v___x_4038_; 
v___x_4038_ = l_Array_popWhile___redArg(v_p_4036_, v_as_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(lean_object* v_p_4039_, lean_object* v_as_4040_, lean_object* v_i_4041_, lean_object* v_acc_4042_){
_start:
{
lean_object* v___x_4043_; uint8_t v___x_4044_; 
v___x_4043_ = lean_array_get_size(v_as_4040_);
v___x_4044_ = lean_nat_dec_lt(v_i_4041_, v___x_4043_);
if (v___x_4044_ == 0)
{
lean_dec(v_i_4041_);
lean_dec_ref(v_p_4039_);
return v_acc_4042_;
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4046_; uint8_t v___x_4047_; 
v_a_4045_ = lean_array_fget_borrowed(v_as_4040_, v_i_4041_);
lean_inc_ref(v_p_4039_);
lean_inc(v_a_4045_);
v___x_4046_ = lean_apply_1(v_p_4039_, v_a_4045_);
v___x_4047_ = lean_unbox(v___x_4046_);
if (v___x_4047_ == 0)
{
lean_dec(v_i_4041_);
lean_dec_ref(v_p_4039_);
return v_acc_4042_;
}
else
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4048_ = lean_unsigned_to_nat(1u);
v___x_4049_ = lean_nat_add(v_i_4041_, v___x_4048_);
lean_dec(v_i_4041_);
lean_inc(v_a_4045_);
v___x_4050_ = lean_array_push(v_acc_4042_, v_a_4045_);
v_i_4041_ = v___x_4049_;
v_acc_4042_ = v___x_4050_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg___boxed(lean_object* v_p_4052_, lean_object* v_as_4053_, lean_object* v_i_4054_, lean_object* v_acc_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4052_, v_as_4053_, v_i_4054_, v_acc_4055_);
lean_dec_ref(v_as_4053_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(lean_object* v_00_u03b1_4057_, lean_object* v_p_4058_, lean_object* v_as_4059_, lean_object* v_i_4060_, lean_object* v_acc_4061_){
_start:
{
lean_object* v___x_4062_; 
v___x_4062_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4058_, v_as_4059_, v_i_4060_, v_acc_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___boxed(lean_object* v_00_u03b1_4063_, lean_object* v_p_4064_, lean_object* v_as_4065_, lean_object* v_i_4066_, lean_object* v_acc_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(v_00_u03b1_4063_, v_p_4064_, v_as_4065_, v_i_4066_, v_acc_4067_);
lean_dec_ref(v_as_4065_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg(lean_object* v_p_4069_, lean_object* v_as_4070_){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4071_ = lean_unsigned_to_nat(0u);
v___x_4072_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4073_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4069_, v_as_4070_, v___x_4071_, v___x_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg___boxed(lean_object* v_p_4074_, lean_object* v_as_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_Array_takeWhile___redArg(v_p_4074_, v_as_4075_);
lean_dec_ref(v_as_4075_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile(lean_object* v_00_u03b1_4077_, lean_object* v_p_4078_, lean_object* v_as_4079_){
_start:
{
lean_object* v___x_4080_; 
v___x_4080_ = l_Array_takeWhile___redArg(v_p_4078_, v_as_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___boxed(lean_object* v_00_u03b1_4081_, lean_object* v_p_4082_, lean_object* v_as_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Array_takeWhile(v_00_u03b1_4081_, v_p_4082_, v_as_4083_);
lean_dec_ref(v_as_4083_);
return v_res_4084_;
}
}
static lean_object* _init_l_Array_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx___redArg(lean_object* v_xs_4086_, lean_object* v_i_4087_){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; uint8_t v___x_4091_; 
v___x_4088_ = lean_unsigned_to_nat(1u);
v___x_4089_ = lean_nat_add(v_i_4087_, v___x_4088_);
v___x_4090_ = lean_array_get_size(v_xs_4086_);
v___x_4091_ = lean_nat_dec_lt(v___x_4089_, v___x_4090_);
if (v___x_4091_ == 0)
{
lean_object* v___x_4092_; 
lean_dec(v___x_4089_);
lean_dec(v_i_4087_);
v___x_4092_ = lean_array_pop(v_xs_4086_);
return v___x_4092_;
}
else
{
lean_object* v_xs_x27_4093_; 
v_xs_x27_4093_ = lean_array_fswap(v_xs_4086_, v___x_4089_, v_i_4087_);
lean_dec(v_i_4087_);
v_xs_4086_ = v_xs_x27_4093_;
v_i_4087_ = v___x_4089_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx(lean_object* v_00_u03b1_4095_, lean_object* v_xs_4096_, lean_object* v_i_4097_, lean_object* v_h_4098_){
_start:
{
lean_object* v___x_4099_; 
v___x_4099_ = l_Array_eraseIdx___redArg(v_xs_4096_, v_i_4097_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds___redArg(lean_object* v_xs_4100_, lean_object* v_i_4101_){
_start:
{
lean_object* v___x_4102_; uint8_t v___x_4103_; 
v___x_4102_ = lean_array_get_size(v_xs_4100_);
v___x_4103_ = lean_nat_dec_lt(v_i_4101_, v___x_4102_);
if (v___x_4103_ == 0)
{
lean_dec(v_i_4101_);
return v_xs_4100_;
}
else
{
lean_object* v___x_4104_; 
v___x_4104_ = l_Array_eraseIdx___redArg(v_xs_4100_, v_i_4101_);
return v___x_4104_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds(lean_object* v_00_u03b1_4105_, lean_object* v_xs_4106_, lean_object* v_i_4107_){
_start:
{
lean_object* v___x_4108_; 
v___x_4108_ = l_Array_eraseIdxIfInBounds___redArg(v_xs_4106_, v_i_4107_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(lean_object* v_msg_4109_){
_start:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4110_ = lean_obj_once(&l_Array_instInhabited___closed__0, &l_Array_instInhabited___closed__0_once, _init_l_Array_instInhabited___closed__0);
v___x_4111_ = lean_panic_fn_borrowed(v___x_4110_, v_msg_4109_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0(lean_object* v_00_u03b1_4112_, lean_object* v_msg_4113_){
_start:
{
lean_object* v___x_4114_; 
v___x_4114_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v_msg_4113_);
return v___x_4114_;
}
}
static lean_object* _init_l_Array_eraseIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4117_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4118_ = lean_unsigned_to_nat(47u);
v___x_4119_ = lean_unsigned_to_nat(1874u);
v___x_4120_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__0));
v___x_4121_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4122_ = l_mkPanicMessageWithDecl(v___x_4121_, v___x_4120_, v___x_4119_, v___x_4118_, v___x_4117_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21___redArg(lean_object* v_xs_4123_, lean_object* v_i_4124_){
_start:
{
lean_object* v___x_4125_; uint8_t v___x_4126_; 
v___x_4125_ = lean_array_get_size(v_xs_4123_);
v___x_4126_ = lean_nat_dec_lt(v_i_4124_, v___x_4125_);
if (v___x_4126_ == 0)
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
lean_dec(v_i_4124_);
lean_dec_ref(v_xs_4123_);
v___x_4127_ = lean_obj_once(&l_Array_eraseIdx_x21___redArg___closed__2, &l_Array_eraseIdx_x21___redArg___closed__2_once, _init_l_Array_eraseIdx_x21___redArg___closed__2);
v___x_4128_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4127_);
return v___x_4128_;
}
else
{
lean_object* v___x_4129_; 
v___x_4129_ = l_Array_eraseIdx___redArg(v_xs_4123_, v_i_4124_);
return v___x_4129_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21(lean_object* v_00_u03b1_4130_, lean_object* v_xs_4131_, lean_object* v_i_4132_){
_start:
{
lean_object* v___x_4133_; 
v___x_4133_ = l_Array_eraseIdx_x21___redArg(v_xs_4131_, v_i_4132_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Array_erase___redArg(lean_object* v_inst_4134_, lean_object* v_as_4135_, lean_object* v_a_4136_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Array_finIdxOf_x3f___redArg(v_inst_4134_, v_as_4135_, v_a_4136_);
if (lean_obj_tag(v___x_4137_) == 0)
{
return v_as_4135_;
}
else
{
lean_object* v_val_4138_; lean_object* v___x_4139_; 
v_val_4138_ = lean_ctor_get(v___x_4137_, 0);
lean_inc(v_val_4138_);
lean_dec_ref_known(v___x_4137_, 1);
v___x_4139_ = l_Array_eraseIdx___redArg(v_as_4135_, v_val_4138_);
return v___x_4139_;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase(lean_object* v_00_u03b1_4140_, lean_object* v_inst_4141_, lean_object* v_as_4142_, lean_object* v_a_4143_){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = l_Array_erase___redArg(v_inst_4141_, v_as_4142_, v_a_4143_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseP___redArg(lean_object* v_as_4145_, lean_object* v_p_4146_){
_start:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4147_ = lean_unsigned_to_nat(0u);
v___x_4148_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_4146_, v_as_4145_, v___x_4147_);
if (lean_obj_tag(v___x_4148_) == 0)
{
return v_as_4145_;
}
else
{
lean_object* v_val_4149_; lean_object* v___x_4150_; 
v_val_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_val_4149_);
lean_dec_ref_known(v___x_4148_, 1);
v___x_4150_ = l_Array_eraseIdx___redArg(v_as_4145_, v_val_4149_);
return v___x_4150_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseP(lean_object* v_00_u03b1_4151_, lean_object* v_as_4152_, lean_object* v_p_4153_){
_start:
{
lean_object* v___x_4154_; 
v___x_4154_ = l_Array_eraseP___redArg(v_as_4152_, v_p_4153_);
return v___x_4154_;
}
}
static lean_object* _init_l_Array_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_4155_; 
v___x_4155_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(lean_object* v_i_4156_, lean_object* v_as_4157_, lean_object* v_j_4158_){
_start:
{
uint8_t v___x_4159_; 
v___x_4159_ = lean_nat_dec_lt(v_i_4156_, v_j_4158_);
if (v___x_4159_ == 0)
{
lean_dec(v_j_4158_);
return v_as_4157_;
}
else
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v_as_4162_; 
v___x_4160_ = lean_unsigned_to_nat(1u);
v___x_4161_ = lean_nat_sub(v_j_4158_, v___x_4160_);
v_as_4162_ = lean_array_fswap(v_as_4157_, v___x_4161_, v_j_4158_);
lean_dec(v_j_4158_);
v_as_4157_ = v_as_4162_;
v_j_4158_ = v___x_4161_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg___boxed(lean_object* v_i_4164_, lean_object* v_as_4165_, lean_object* v_j_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4164_, v_as_4165_, v_j_4166_);
lean_dec(v_i_4164_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object* v_00_u03b1_4168_, lean_object* v_i_4169_, lean_object* v_as_4170_, lean_object* v_j_4171_){
_start:
{
lean_object* v___x_4172_; 
v___x_4172_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4169_, v_as_4170_, v_j_4171_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___boxed(lean_object* v_00_u03b1_4173_, lean_object* v_i_4174_, lean_object* v_as_4175_, lean_object* v_j_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(v_00_u03b1_4173_, v_i_4174_, v_as_4175_, v_j_4176_);
lean_dec(v_i_4174_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg(lean_object* v_as_4178_, lean_object* v_i_4179_, lean_object* v_a_4180_){
_start:
{
lean_object* v_j_4181_; lean_object* v_as_4182_; lean_object* v___x_4183_; 
v_j_4181_ = lean_array_get_size(v_as_4178_);
v_as_4182_ = lean_array_push(v_as_4178_, v_a_4180_);
v___x_4183_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4179_, v_as_4182_, v_j_4181_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg___boxed(lean_object* v_as_4184_, lean_object* v_i_4185_, lean_object* v_a_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l_Array_insertIdx___redArg(v_as_4184_, v_i_4185_, v_a_4186_);
lean_dec(v_i_4185_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx(lean_object* v_00_u03b1_4188_, lean_object* v_as_4189_, lean_object* v_i_4190_, lean_object* v_a_4191_, lean_object* v_x_4192_){
_start:
{
lean_object* v_j_4193_; lean_object* v_as_4194_; lean_object* v___x_4195_; 
v_j_4193_ = lean_array_get_size(v_as_4189_);
v_as_4194_ = lean_array_push(v_as_4189_, v_a_4191_);
v___x_4195_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4190_, v_as_4194_, v_j_4193_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___boxed(lean_object* v_00_u03b1_4196_, lean_object* v_as_4197_, lean_object* v_i_4198_, lean_object* v_a_4199_, lean_object* v_x_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Array_insertIdx(v_00_u03b1_4196_, v_as_4197_, v_i_4198_, v_a_4199_, v_x_4200_);
lean_dec(v_i_4198_);
return v_res_4201_;
}
}
static lean_object* _init_l_Array_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4203_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4204_ = lean_unsigned_to_nat(7u);
v___x_4205_ = lean_unsigned_to_nat(1956u);
v___x_4206_ = ((lean_object*)(l_Array_insertIdx_x21___redArg___closed__0));
v___x_4207_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4208_ = l_mkPanicMessageWithDecl(v___x_4207_, v___x_4206_, v___x_4205_, v___x_4204_, v___x_4203_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg(lean_object* v_as_4209_, lean_object* v_i_4210_, lean_object* v_a_4211_){
_start:
{
lean_object* v___x_4212_; uint8_t v___x_4213_; 
v___x_4212_ = lean_array_get_size(v_as_4209_);
v___x_4213_ = lean_nat_dec_le(v_i_4210_, v___x_4212_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
lean_dec(v_a_4211_);
lean_dec_ref(v_as_4209_);
v___x_4214_ = lean_obj_once(&l_Array_insertIdx_x21___redArg___closed__1, &l_Array_insertIdx_x21___redArg___closed__1_once, _init_l_Array_insertIdx_x21___redArg___closed__1);
v___x_4215_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4214_);
return v___x_4215_;
}
else
{
lean_object* v_as_4216_; lean_object* v___x_4217_; 
v_as_4216_ = lean_array_push(v_as_4209_, v_a_4211_);
v___x_4217_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4210_, v_as_4216_, v___x_4212_);
return v___x_4217_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg___boxed(lean_object* v_as_4218_, lean_object* v_i_4219_, lean_object* v_a_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l_Array_insertIdx_x21___redArg(v_as_4218_, v_i_4219_, v_a_4220_);
lean_dec(v_i_4219_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21(lean_object* v_00_u03b1_4222_, lean_object* v_as_4223_, lean_object* v_i_4224_, lean_object* v_a_4225_){
_start:
{
lean_object* v___x_4226_; 
v___x_4226_ = l_Array_insertIdx_x21___redArg(v_as_4223_, v_i_4224_, v_a_4225_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___boxed(lean_object* v_00_u03b1_4227_, lean_object* v_as_4228_, lean_object* v_i_4229_, lean_object* v_a_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l_Array_insertIdx_x21(v_00_u03b1_4227_, v_as_4228_, v_i_4229_, v_a_4230_);
lean_dec(v_i_4229_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg(lean_object* v_as_4232_, lean_object* v_i_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v___x_4235_; uint8_t v___x_4236_; 
v___x_4235_ = lean_array_get_size(v_as_4232_);
v___x_4236_ = lean_nat_dec_le(v_i_4233_, v___x_4235_);
if (v___x_4236_ == 0)
{
lean_dec(v_a_4234_);
return v_as_4232_;
}
else
{
lean_object* v_as_4237_; lean_object* v___x_4238_; 
v_as_4237_ = lean_array_push(v_as_4232_, v_a_4234_);
v___x_4238_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4233_, v_as_4237_, v___x_4235_);
return v___x_4238_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg___boxed(lean_object* v_as_4239_, lean_object* v_i_4240_, lean_object* v_a_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Array_insertIdxIfInBounds___redArg(v_as_4239_, v_i_4240_, v_a_4241_);
lean_dec(v_i_4240_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds(lean_object* v_00_u03b1_4243_, lean_object* v_as_4244_, lean_object* v_i_4245_, lean_object* v_a_4246_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Array_insertIdxIfInBounds___redArg(v_as_4244_, v_i_4245_, v_a_4246_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___boxed(lean_object* v_00_u03b1_4248_, lean_object* v_as_4249_, lean_object* v_i_4250_, lean_object* v_a_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_Array_insertIdxIfInBounds(v_00_u03b1_4248_, v_as_4249_, v_i_4250_, v_a_4251_);
lean_dec(v_i_4250_);
return v_res_4252_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux___redArg(lean_object* v_inst_4253_, lean_object* v_as_4254_, lean_object* v_bs_4255_, lean_object* v_i_4256_){
_start:
{
lean_object* v___x_4257_; uint8_t v___x_4258_; 
v___x_4257_ = lean_array_get_size(v_as_4254_);
v___x_4258_ = lean_nat_dec_lt(v_i_4256_, v___x_4257_);
if (v___x_4258_ == 0)
{
uint8_t v___x_4259_; 
lean_dec(v_i_4256_);
lean_dec_ref(v_inst_4253_);
v___x_4259_ = 1;
return v___x_4259_;
}
else
{
lean_object* v_a_4260_; lean_object* v_b_4261_; lean_object* v___x_4262_; uint8_t v___x_4263_; 
v_a_4260_ = lean_array_fget_borrowed(v_as_4254_, v_i_4256_);
v_b_4261_ = lean_array_fget_borrowed(v_bs_4255_, v_i_4256_);
lean_inc_ref(v_inst_4253_);
lean_inc(v_b_4261_);
lean_inc(v_a_4260_);
v___x_4262_ = lean_apply_2(v_inst_4253_, v_a_4260_, v_b_4261_);
v___x_4263_ = lean_unbox(v___x_4262_);
if (v___x_4263_ == 0)
{
uint8_t v___x_4264_; 
lean_dec(v_i_4256_);
lean_dec_ref(v_inst_4253_);
v___x_4264_ = lean_unbox(v___x_4262_);
return v___x_4264_;
}
else
{
lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4265_ = lean_unsigned_to_nat(1u);
v___x_4266_ = lean_nat_add(v_i_4256_, v___x_4265_);
lean_dec(v_i_4256_);
v_i_4256_ = v___x_4266_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___redArg___boxed(lean_object* v_inst_4268_, lean_object* v_as_4269_, lean_object* v_bs_4270_, lean_object* v_i_4271_){
_start:
{
uint8_t v_res_4272_; lean_object* v_r_4273_; 
v_res_4272_ = l_Array_isPrefixOfAux___redArg(v_inst_4268_, v_as_4269_, v_bs_4270_, v_i_4271_);
lean_dec_ref(v_bs_4270_);
lean_dec_ref(v_as_4269_);
v_r_4273_ = lean_box(v_res_4272_);
return v_r_4273_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux(lean_object* v_00_u03b1_4274_, lean_object* v_inst_4275_, lean_object* v_as_4276_, lean_object* v_bs_4277_, lean_object* v_hle_4278_, lean_object* v_i_4279_){
_start:
{
uint8_t v___x_4280_; 
v___x_4280_ = l_Array_isPrefixOfAux___redArg(v_inst_4275_, v_as_4276_, v_bs_4277_, v_i_4279_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___boxed(lean_object* v_00_u03b1_4281_, lean_object* v_inst_4282_, lean_object* v_as_4283_, lean_object* v_bs_4284_, lean_object* v_hle_4285_, lean_object* v_i_4286_){
_start:
{
uint8_t v_res_4287_; lean_object* v_r_4288_; 
v_res_4287_ = l_Array_isPrefixOfAux(v_00_u03b1_4281_, v_inst_4282_, v_as_4283_, v_bs_4284_, v_hle_4285_, v_i_4286_);
lean_dec_ref(v_bs_4284_);
lean_dec_ref(v_as_4283_);
v_r_4288_ = lean_box(v_res_4287_);
return v_r_4288_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf___redArg(lean_object* v_inst_4289_, lean_object* v_as_4290_, lean_object* v_bs_4291_){
_start:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; uint8_t v___x_4294_; 
v___x_4292_ = lean_array_get_size(v_as_4290_);
v___x_4293_ = lean_array_get_size(v_bs_4291_);
v___x_4294_ = lean_nat_dec_le(v___x_4292_, v___x_4293_);
if (v___x_4294_ == 0)
{
lean_dec_ref(v_inst_4289_);
return v___x_4294_;
}
else
{
lean_object* v___x_4295_; uint8_t v___x_4296_; 
v___x_4295_ = lean_unsigned_to_nat(0u);
v___x_4296_ = l_Array_isPrefixOfAux___redArg(v_inst_4289_, v_as_4290_, v_bs_4291_, v___x_4295_);
return v___x_4296_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___redArg___boxed(lean_object* v_inst_4297_, lean_object* v_as_4298_, lean_object* v_bs_4299_){
_start:
{
uint8_t v_res_4300_; lean_object* v_r_4301_; 
v_res_4300_ = l_Array_isPrefixOf___redArg(v_inst_4297_, v_as_4298_, v_bs_4299_);
lean_dec_ref(v_bs_4299_);
lean_dec_ref(v_as_4298_);
v_r_4301_ = lean_box(v_res_4300_);
return v_r_4301_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf(lean_object* v_00_u03b1_4302_, lean_object* v_inst_4303_, lean_object* v_as_4304_, lean_object* v_bs_4305_){
_start:
{
uint8_t v___x_4306_; 
v___x_4306_ = l_Array_isPrefixOf___redArg(v_inst_4303_, v_as_4304_, v_bs_4305_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___boxed(lean_object* v_00_u03b1_4307_, lean_object* v_inst_4308_, lean_object* v_as_4309_, lean_object* v_bs_4310_){
_start:
{
uint8_t v_res_4311_; lean_object* v_r_4312_; 
v_res_4311_ = l_Array_isPrefixOf(v_00_u03b1_4307_, v_inst_4308_, v_as_4309_, v_bs_4310_);
lean_dec_ref(v_bs_4310_);
lean_dec_ref(v_as_4309_);
v_r_4312_ = lean_box(v_res_4311_);
return v_r_4312_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0___boxed(lean_object* v_i_4313_, lean_object* v_cs_4314_, lean_object* v_inst_4315_, lean_object* v_as_4316_, lean_object* v_bs_4317_, lean_object* v_f_4318_, lean_object* v_____do__lift_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Array_zipWithMAux___redArg___lam__0(v_i_4313_, v_cs_4314_, v_inst_4315_, v_as_4316_, v_bs_4317_, v_f_4318_, v_____do__lift_4319_);
lean_dec(v_i_4313_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg(lean_object* v_inst_4321_, lean_object* v_as_4322_, lean_object* v_bs_4323_, lean_object* v_f_4324_, lean_object* v_i_4325_, lean_object* v_cs_4326_){
_start:
{
lean_object* v_toApplicative_4327_; lean_object* v_toBind_4328_; lean_object* v_toPure_4329_; lean_object* v___x_4330_; uint8_t v___x_4331_; 
v_toApplicative_4327_ = lean_ctor_get(v_inst_4321_, 0);
v_toBind_4328_ = lean_ctor_get(v_inst_4321_, 1);
lean_inc(v_toBind_4328_);
v_toPure_4329_ = lean_ctor_get(v_toApplicative_4327_, 1);
v___x_4330_ = lean_array_get_size(v_as_4322_);
v___x_4331_ = lean_nat_dec_lt(v_i_4325_, v___x_4330_);
if (v___x_4331_ == 0)
{
lean_object* v___x_4332_; 
lean_inc(v_toPure_4329_);
lean_dec(v_toBind_4328_);
lean_dec(v_i_4325_);
lean_dec(v_f_4324_);
lean_dec_ref(v_bs_4323_);
lean_dec_ref(v_as_4322_);
lean_dec_ref(v_inst_4321_);
v___x_4332_ = lean_apply_2(v_toPure_4329_, lean_box(0), v_cs_4326_);
return v___x_4332_;
}
else
{
lean_object* v___x_4333_; uint8_t v___x_4334_; 
v___x_4333_ = lean_array_get_size(v_bs_4323_);
v___x_4334_ = lean_nat_dec_lt(v_i_4325_, v___x_4333_);
if (v___x_4334_ == 0)
{
lean_object* v___x_4335_; 
lean_inc(v_toPure_4329_);
lean_dec(v_toBind_4328_);
lean_dec(v_i_4325_);
lean_dec(v_f_4324_);
lean_dec_ref(v_bs_4323_);
lean_dec_ref(v_as_4322_);
lean_dec_ref(v_inst_4321_);
v___x_4335_ = lean_apply_2(v_toPure_4329_, lean_box(0), v_cs_4326_);
return v___x_4335_;
}
else
{
lean_object* v___f_4336_; lean_object* v_a_4337_; lean_object* v_b_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
lean_inc(v_f_4324_);
lean_inc_ref(v_bs_4323_);
lean_inc_ref(v_as_4322_);
lean_inc(v_i_4325_);
v___f_4336_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4336_, 0, v_i_4325_);
lean_closure_set(v___f_4336_, 1, v_cs_4326_);
lean_closure_set(v___f_4336_, 2, v_inst_4321_);
lean_closure_set(v___f_4336_, 3, v_as_4322_);
lean_closure_set(v___f_4336_, 4, v_bs_4323_);
lean_closure_set(v___f_4336_, 5, v_f_4324_);
v_a_4337_ = lean_array_fget(v_as_4322_, v_i_4325_);
lean_dec_ref(v_as_4322_);
v_b_4338_ = lean_array_fget(v_bs_4323_, v_i_4325_);
lean_dec(v_i_4325_);
lean_dec_ref(v_bs_4323_);
v___x_4339_ = lean_apply_2(v_f_4324_, v_a_4337_, v_b_4338_);
v___x_4340_ = lean_apply_4(v_toBind_4328_, lean_box(0), lean_box(0), v___x_4339_, v___f_4336_);
return v___x_4340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0(lean_object* v_i_4341_, lean_object* v_cs_4342_, lean_object* v_inst_4343_, lean_object* v_as_4344_, lean_object* v_bs_4345_, lean_object* v_f_4346_, lean_object* v_____do__lift_4347_){
_start:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4348_ = lean_unsigned_to_nat(1u);
v___x_4349_ = lean_nat_add(v_i_4341_, v___x_4348_);
v___x_4350_ = lean_array_push(v_cs_4342_, v_____do__lift_4347_);
v___x_4351_ = l_Array_zipWithMAux___redArg(v_inst_4343_, v_as_4344_, v_bs_4345_, v_f_4346_, v___x_4349_, v___x_4350_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux(lean_object* v_00_u03b1_4352_, lean_object* v_00_u03b2_4353_, lean_object* v_00_u03b3_4354_, lean_object* v_m_4355_, lean_object* v_inst_4356_, lean_object* v_as_4357_, lean_object* v_bs_4358_, lean_object* v_f_4359_, lean_object* v_i_4360_, lean_object* v_cs_4361_){
_start:
{
lean_object* v___x_4362_; 
v___x_4362_ = l_Array_zipWithMAux___redArg(v_inst_4356_, v_as_4357_, v_bs_4358_, v_f_4359_, v_i_4360_, v_cs_4361_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith___redArg(lean_object* v_f_4363_, lean_object* v_as_4364_, lean_object* v_bs_4365_){
_start:
{
lean_object* v___f_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___f_4366_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4366_, 0, v_f_4363_);
v___x_4367_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4368_ = lean_unsigned_to_nat(0u);
v___x_4369_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4370_ = l_Array_zipWithMAux___redArg(v___x_4367_, v_as_4364_, v_bs_4365_, v___f_4366_, v___x_4368_, v___x_4369_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith(lean_object* v_00_u03b1_4371_, lean_object* v_00_u03b2_4372_, lean_object* v_00_u03b3_4373_, lean_object* v_f_4374_, lean_object* v_as_4375_, lean_object* v_bs_4376_){
_start:
{
lean_object* v___f_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___f_4377_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4377_, 0, v_f_4374_);
v___x_4378_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4379_ = lean_unsigned_to_nat(0u);
v___x_4380_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4381_ = l_Array_zipWithMAux___redArg(v___x_4378_, v_as_4375_, v_bs_4376_, v___f_4377_, v___x_4379_, v___x_4380_);
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(lean_object* v_as_4382_, lean_object* v_bs_4383_, lean_object* v_i_4384_, lean_object* v_cs_4385_){
_start:
{
lean_object* v___x_4386_; uint8_t v___x_4387_; 
v___x_4386_ = lean_array_get_size(v_as_4382_);
v___x_4387_ = lean_nat_dec_lt(v_i_4384_, v___x_4386_);
if (v___x_4387_ == 0)
{
lean_dec(v_i_4384_);
return v_cs_4385_;
}
else
{
lean_object* v___x_4388_; uint8_t v___x_4389_; 
v___x_4388_ = lean_array_get_size(v_bs_4383_);
v___x_4389_ = lean_nat_dec_lt(v_i_4384_, v___x_4388_);
if (v___x_4389_ == 0)
{
lean_dec(v_i_4384_);
return v_cs_4385_;
}
else
{
lean_object* v_a_4390_; lean_object* v_b_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v_a_4390_ = lean_array_fget_borrowed(v_as_4382_, v_i_4384_);
v_b_4391_ = lean_array_fget_borrowed(v_bs_4383_, v_i_4384_);
lean_inc(v_b_4391_);
lean_inc(v_a_4390_);
v___x_4392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4392_, 0, v_a_4390_);
lean_ctor_set(v___x_4392_, 1, v_b_4391_);
v___x_4393_ = lean_unsigned_to_nat(1u);
v___x_4394_ = lean_nat_add(v_i_4384_, v___x_4393_);
lean_dec(v_i_4384_);
v___x_4395_ = lean_array_push(v_cs_4385_, v___x_4392_);
v_i_4384_ = v___x_4394_;
v_cs_4385_ = v___x_4395_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg___boxed(lean_object* v_as_4397_, lean_object* v_bs_4398_, lean_object* v_i_4399_, lean_object* v_cs_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4397_, v_bs_4398_, v_i_4399_, v_cs_4400_);
lean_dec_ref(v_bs_4398_);
lean_dec_ref(v_as_4397_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg(lean_object* v_as_4404_, lean_object* v_bs_4405_){
_start:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4406_ = lean_unsigned_to_nat(0u);
v___x_4407_ = ((lean_object*)(l_Array_zip___redArg___closed__0));
v___x_4408_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4404_, v_bs_4405_, v___x_4406_, v___x_4407_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg___boxed(lean_object* v_as_4409_, lean_object* v_bs_4410_){
_start:
{
lean_object* v_res_4411_; 
v_res_4411_ = l_Array_zip___redArg(v_as_4409_, v_bs_4410_);
lean_dec_ref(v_bs_4410_);
lean_dec_ref(v_as_4409_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l_Array_zip(lean_object* v_00_u03b1_4412_, lean_object* v_00_u03b2_4413_, lean_object* v_as_4414_, lean_object* v_bs_4415_){
_start:
{
lean_object* v___x_4416_; 
v___x_4416_ = l_Array_zip___redArg(v_as_4414_, v_bs_4415_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___boxed(lean_object* v_00_u03b1_4417_, lean_object* v_00_u03b2_4418_, lean_object* v_as_4419_, lean_object* v_bs_4420_){
_start:
{
lean_object* v_res_4421_; 
v_res_4421_ = l_Array_zip(v_00_u03b1_4417_, v_00_u03b2_4418_, v_as_4419_, v_bs_4420_);
lean_dec_ref(v_bs_4420_);
lean_dec_ref(v_as_4419_);
return v_res_4421_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0(lean_object* v_00_u03b1_4422_, lean_object* v_00_u03b2_4423_, lean_object* v_as_4424_, lean_object* v_bs_4425_, lean_object* v_i_4426_, lean_object* v_cs_4427_){
_start:
{
lean_object* v___x_4428_; 
v___x_4428_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4424_, v_bs_4425_, v_i_4426_, v_cs_4427_);
return v___x_4428_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___boxed(lean_object* v_00_u03b1_4429_, lean_object* v_00_u03b2_4430_, lean_object* v_as_4431_, lean_object* v_bs_4432_, lean_object* v_i_4433_, lean_object* v_cs_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l_Array_zipWithMAux___at___00Array_zip_spec__0(v_00_u03b1_4429_, v_00_u03b2_4430_, v_as_4431_, v_bs_4432_, v_i_4433_, v_cs_4434_);
lean_dec_ref(v_bs_4432_);
lean_dec_ref(v_as_4431_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(lean_object* v_f_4436_, lean_object* v_as_4437_, lean_object* v_bs_4438_, lean_object* v_i_4439_, lean_object* v_cs_4440_){
_start:
{
lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4450_; lean_object* v___y_4457_; lean_object* v___x_4464_; lean_object* v___x_4465_; uint8_t v___x_4466_; 
v___x_4464_ = lean_array_get_size(v_as_4437_);
v___x_4465_ = lean_array_get_size(v_bs_4438_);
v___x_4466_ = lean_nat_dec_le(v___x_4464_, v___x_4465_);
if (v___x_4466_ == 0)
{
v___y_4457_ = v___x_4464_;
goto v___jp_4456_;
}
else
{
v___y_4457_ = v___x_4465_;
goto v___jp_4456_;
}
v___jp_4441_:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4444_ = lean_unsigned_to_nat(1u);
v___x_4445_ = lean_nat_add(v_i_4439_, v___x_4444_);
lean_dec(v_i_4439_);
lean_inc(v_f_4436_);
v___x_4446_ = lean_apply_2(v_f_4436_, v___y_4442_, v___y_4443_);
v___x_4447_ = lean_array_push(v_cs_4440_, v___x_4446_);
v_i_4439_ = v___x_4445_;
v_cs_4440_ = v___x_4447_;
goto _start;
}
v___jp_4449_:
{
lean_object* v___x_4451_; uint8_t v___x_4452_; 
v___x_4451_ = lean_array_get_size(v_bs_4438_);
v___x_4452_ = lean_nat_dec_lt(v_i_4439_, v___x_4451_);
if (v___x_4452_ == 0)
{
lean_object* v___x_4453_; 
v___x_4453_ = lean_box(0);
v___y_4442_ = v___y_4450_;
v___y_4443_ = v___x_4453_;
goto v___jp_4441_;
}
else
{
lean_object* v___x_4454_; lean_object* v___x_4455_; 
v___x_4454_ = lean_array_fget_borrowed(v_bs_4438_, v_i_4439_);
lean_inc(v___x_4454_);
v___x_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4455_, 0, v___x_4454_);
v___y_4442_ = v___y_4450_;
v___y_4443_ = v___x_4455_;
goto v___jp_4441_;
}
}
v___jp_4456_:
{
uint8_t v___x_4458_; 
v___x_4458_ = lean_nat_dec_lt(v_i_4439_, v___y_4457_);
lean_dec(v___y_4457_);
if (v___x_4458_ == 0)
{
lean_dec(v_i_4439_);
lean_dec(v_f_4436_);
return v_cs_4440_;
}
else
{
lean_object* v___x_4459_; uint8_t v___x_4460_; 
v___x_4459_ = lean_array_get_size(v_as_4437_);
v___x_4460_ = lean_nat_dec_lt(v_i_4439_, v___x_4459_);
if (v___x_4460_ == 0)
{
lean_object* v___x_4461_; 
v___x_4461_ = lean_box(0);
v___y_4450_ = v___x_4461_;
goto v___jp_4449_;
}
else
{
lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4462_ = lean_array_fget_borrowed(v_as_4437_, v_i_4439_);
lean_inc(v___x_4462_);
v___x_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4462_);
v___y_4450_ = v___x_4463_;
goto v___jp_4449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg___boxed(lean_object* v_f_4467_, lean_object* v_as_4468_, lean_object* v_bs_4469_, lean_object* v_i_4470_, lean_object* v_cs_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4467_, v_as_4468_, v_bs_4469_, v_i_4470_, v_cs_4471_);
lean_dec_ref(v_bs_4469_);
lean_dec_ref(v_as_4468_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(lean_object* v_00_u03b1_4473_, lean_object* v_00_u03b2_4474_, lean_object* v_00_u03b3_4475_, lean_object* v_f_4476_, lean_object* v_as_4477_, lean_object* v_bs_4478_, lean_object* v_i_4479_, lean_object* v_cs_4480_){
_start:
{
lean_object* v___x_4481_; 
v___x_4481_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4476_, v_as_4477_, v_bs_4478_, v_i_4479_, v_cs_4480_);
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___boxed(lean_object* v_00_u03b1_4482_, lean_object* v_00_u03b2_4483_, lean_object* v_00_u03b3_4484_, lean_object* v_f_4485_, lean_object* v_as_4486_, lean_object* v_bs_4487_, lean_object* v_i_4488_, lean_object* v_cs_4489_){
_start:
{
lean_object* v_res_4490_; 
v_res_4490_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(v_00_u03b1_4482_, v_00_u03b2_4483_, v_00_u03b3_4484_, v_f_4485_, v_as_4486_, v_bs_4487_, v_i_4488_, v_cs_4489_);
lean_dec_ref(v_bs_4487_);
lean_dec_ref(v_as_4486_);
return v_res_4490_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg(lean_object* v_f_4491_, lean_object* v_as_4492_, lean_object* v_bs_4493_){
_start:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4494_ = lean_unsigned_to_nat(0u);
v___x_4495_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4496_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4491_, v_as_4492_, v_bs_4493_, v___x_4494_, v___x_4495_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg___boxed(lean_object* v_f_4497_, lean_object* v_as_4498_, lean_object* v_bs_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l_Array_zipWithAll___redArg(v_f_4497_, v_as_4498_, v_bs_4499_);
lean_dec_ref(v_bs_4499_);
lean_dec_ref(v_as_4498_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll(lean_object* v_00_u03b1_4501_, lean_object* v_00_u03b2_4502_, lean_object* v_00_u03b3_4503_, lean_object* v_f_4504_, lean_object* v_as_4505_, lean_object* v_bs_4506_){
_start:
{
lean_object* v___x_4507_; 
v___x_4507_ = l_Array_zipWithAll___redArg(v_f_4504_, v_as_4505_, v_bs_4506_);
return v___x_4507_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___boxed(lean_object* v_00_u03b1_4508_, lean_object* v_00_u03b2_4509_, lean_object* v_00_u03b3_4510_, lean_object* v_f_4511_, lean_object* v_as_4512_, lean_object* v_bs_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l_Array_zipWithAll(v_00_u03b1_4508_, v_00_u03b2_4509_, v_00_u03b3_4510_, v_f_4511_, v_as_4512_, v_bs_4513_);
lean_dec_ref(v_bs_4513_);
lean_dec_ref(v_as_4512_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM___redArg(lean_object* v_inst_4515_, lean_object* v_f_4516_, lean_object* v_as_4517_, lean_object* v_bs_4518_){
_start:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; 
v___x_4519_ = lean_unsigned_to_nat(0u);
v___x_4520_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4521_ = l_Array_zipWithMAux___redArg(v_inst_4515_, v_as_4517_, v_bs_4518_, v_f_4516_, v___x_4519_, v___x_4520_);
return v___x_4521_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM(lean_object* v_00_u03b1_4522_, lean_object* v_00_u03b2_4523_, lean_object* v_00_u03b3_4524_, lean_object* v_m_4525_, lean_object* v_inst_4526_, lean_object* v_f_4527_, lean_object* v_as_4528_, lean_object* v_bs_4529_){
_start:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4530_ = lean_unsigned_to_nat(0u);
v___x_4531_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4532_ = l_Array_zipWithMAux___redArg(v_inst_4526_, v_as_4528_, v_bs_4529_, v_f_4527_, v___x_4530_, v___x_4531_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(lean_object* v_as_4533_, size_t v_i_4534_, size_t v_stop_4535_, lean_object* v_b_4536_){
_start:
{
uint8_t v___x_4537_; 
v___x_4537_ = lean_usize_dec_eq(v_i_4534_, v_stop_4535_);
if (v___x_4537_ == 0)
{
lean_object* v_fst_4538_; lean_object* v_snd_4539_; lean_object* v___x_4540_; lean_object* v_fst_4541_; lean_object* v_snd_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4554_; 
v_fst_4538_ = lean_ctor_get(v_b_4536_, 0);
lean_inc(v_fst_4538_);
v_snd_4539_ = lean_ctor_get(v_b_4536_, 1);
lean_inc(v_snd_4539_);
lean_dec_ref(v_b_4536_);
v___x_4540_ = lean_array_uget(v_as_4533_, v_i_4534_);
v_fst_4541_ = lean_ctor_get(v___x_4540_, 0);
v_snd_4542_ = lean_ctor_get(v___x_4540_, 1);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4544_ = v___x_4540_;
v_isShared_4545_ = v_isSharedCheck_4554_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_snd_4542_);
lean_inc(v_fst_4541_);
lean_dec(v___x_4540_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4554_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4549_; 
v___x_4546_ = lean_array_push(v_fst_4538_, v_fst_4541_);
v___x_4547_ = lean_array_push(v_snd_4539_, v_snd_4542_);
if (v_isShared_4545_ == 0)
{
lean_ctor_set(v___x_4544_, 1, v___x_4547_);
lean_ctor_set(v___x_4544_, 0, v___x_4546_);
v___x_4549_ = v___x_4544_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4546_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v___x_4547_);
v___x_4549_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
size_t v___x_4550_; size_t v___x_4551_; 
v___x_4550_ = ((size_t)1ULL);
v___x_4551_ = lean_usize_add(v_i_4534_, v___x_4550_);
v_i_4534_ = v___x_4551_;
v_b_4536_ = v___x_4549_;
goto _start;
}
}
}
else
{
return v_b_4536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg___boxed(lean_object* v_as_4555_, lean_object* v_i_4556_, lean_object* v_stop_4557_, lean_object* v_b_4558_){
_start:
{
size_t v_i_boxed_4559_; size_t v_stop_boxed_4560_; lean_object* v_res_4561_; 
v_i_boxed_4559_ = lean_unbox_usize(v_i_4556_);
lean_dec(v_i_4556_);
v_stop_boxed_4560_ = lean_unbox_usize(v_stop_4557_);
lean_dec(v_stop_4557_);
v_res_4561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4555_, v_i_boxed_4559_, v_stop_boxed_4560_, v_b_4558_);
lean_dec_ref(v_as_4555_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg(lean_object* v_as_4562_){
_start:
{
lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; uint8_t v___x_4566_; 
v___x_4563_ = lean_unsigned_to_nat(0u);
v___x_4564_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v___x_4565_ = lean_array_get_size(v_as_4562_);
v___x_4566_ = lean_nat_dec_lt(v___x_4563_, v___x_4565_);
if (v___x_4566_ == 0)
{
return v___x_4564_;
}
else
{
size_t v___x_4567_; size_t v___x_4568_; lean_object* v___x_4569_; 
v___x_4567_ = ((size_t)0ULL);
v___x_4568_ = lean_usize_of_nat(v___x_4565_);
v___x_4569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4562_, v___x_4567_, v___x_4568_, v___x_4564_);
return v___x_4569_;
}
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg___boxed(lean_object* v_as_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l_Array_unzip___redArg(v_as_4570_);
lean_dec_ref(v_as_4570_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip(lean_object* v_00_u03b1_4572_, lean_object* v_00_u03b2_4573_, lean_object* v_as_4574_){
_start:
{
lean_object* v___x_4575_; 
v___x_4575_ = l_Array_unzip___redArg(v_as_4574_);
return v___x_4575_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___boxed(lean_object* v_00_u03b1_4576_, lean_object* v_00_u03b2_4577_, lean_object* v_as_4578_){
_start:
{
lean_object* v_res_4579_; 
v_res_4579_ = l_Array_unzip(v_00_u03b1_4576_, v_00_u03b2_4577_, v_as_4578_);
lean_dec_ref(v_as_4578_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(lean_object* v_00_u03b1_4580_, lean_object* v_00_u03b2_4581_, lean_object* v_as_4582_, size_t v_i_4583_, size_t v_stop_4584_, lean_object* v_b_4585_){
_start:
{
lean_object* v___x_4586_; 
v___x_4586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4582_, v_i_4583_, v_stop_4584_, v_b_4585_);
return v___x_4586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___boxed(lean_object* v_00_u03b1_4587_, lean_object* v_00_u03b2_4588_, lean_object* v_as_4589_, lean_object* v_i_4590_, lean_object* v_stop_4591_, lean_object* v_b_4592_){
_start:
{
size_t v_i_boxed_4593_; size_t v_stop_boxed_4594_; lean_object* v_res_4595_; 
v_i_boxed_4593_ = lean_unbox_usize(v_i_4590_);
lean_dec(v_i_4590_);
v_stop_boxed_4594_ = lean_unbox_usize(v_stop_4591_);
lean_dec(v_stop_4591_);
v_res_4595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(v_00_u03b1_4587_, v_00_u03b2_4588_, v_as_4589_, v_i_boxed_4593_, v_stop_boxed_4594_, v_b_4592_);
lean_dec_ref(v_as_4589_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l_Array_replace___redArg(lean_object* v_inst_4596_, lean_object* v_xs_4597_, lean_object* v_a_4598_, lean_object* v_b_4599_){
_start:
{
lean_object* v___x_4600_; 
v___x_4600_ = l_Array_finIdxOf_x3f___redArg(v_inst_4596_, v_xs_4597_, v_a_4598_);
if (lean_obj_tag(v___x_4600_) == 0)
{
lean_dec(v_b_4599_);
return v_xs_4597_;
}
else
{
lean_object* v_val_4601_; lean_object* v___x_4602_; 
v_val_4601_ = lean_ctor_get(v___x_4600_, 0);
lean_inc(v_val_4601_);
lean_dec_ref_known(v___x_4600_, 1);
v___x_4602_ = lean_array_fset(v_xs_4597_, v_val_4601_, v_b_4599_);
lean_dec(v_val_4601_);
return v___x_4602_;
}
}
}
LEAN_EXPORT lean_object* l_Array_replace(lean_object* v_00_u03b1_4603_, lean_object* v_inst_4604_, lean_object* v_xs_4605_, lean_object* v_a_4606_, lean_object* v_b_4607_){
_start:
{
lean_object* v___x_4608_; 
v___x_4608_ = l_Array_replace___redArg(v_inst_4604_, v_xs_4605_, v_a_4606_, v_b_4607_);
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l_Array_instLT___redArg(){
_start:
{
lean_object* v___x_4610_; 
v___x_4610_ = lean_box(0);
return v___x_4610_;
}
}
LEAN_EXPORT lean_object* l_Array_instLT___redArg___boxed(lean_object* v___dummy_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l_Array_instLT___redArg();
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l_Array_instLT(lean_object* v_00_u03b1_4613_, lean_object* v_inst_4614_){
_start:
{
lean_object* v___x_4615_; 
v___x_4615_ = lean_box(0);
return v___x_4615_;
}
}
LEAN_EXPORT lean_object* l_Array_instLE___redArg(){
_start:
{
lean_object* v___x_4617_; 
v___x_4617_ = lean_box(0);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l_Array_instLE___redArg___boxed(lean_object* v___dummy_4618_){
_start:
{
lean_object* v_res_4619_; 
v_res_4619_ = l_Array_instLE___redArg();
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l_Array_instLE(lean_object* v_00_u03b1_4620_, lean_object* v_inst_4621_){
_start:
{
lean_object* v___x_4622_; 
v___x_4622_ = lean_box(0);
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg(lean_object* v_n_4623_, lean_object* v_a_4624_, lean_object* v_xs_4625_){
_start:
{
lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4626_ = lean_array_get_size(v_xs_4625_);
v___x_4627_ = lean_nat_sub(v_n_4623_, v___x_4626_);
v___x_4628_ = lean_mk_array(v___x_4627_, v_a_4624_);
v___x_4629_ = l_Array_append___redArg(v___x_4628_, v_xs_4625_);
return v___x_4629_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg___boxed(lean_object* v_n_4630_, lean_object* v_a_4631_, lean_object* v_xs_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l_Array_leftpad___redArg(v_n_4630_, v_a_4631_, v_xs_4632_);
lean_dec_ref(v_xs_4632_);
lean_dec(v_n_4630_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad(lean_object* v_00_u03b1_4634_, lean_object* v_n_4635_, lean_object* v_a_4636_, lean_object* v_xs_4637_){
_start:
{
lean_object* v___x_4638_; 
v___x_4638_ = l_Array_leftpad___redArg(v_n_4635_, v_a_4636_, v_xs_4637_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___boxed(lean_object* v_00_u03b1_4639_, lean_object* v_n_4640_, lean_object* v_a_4641_, lean_object* v_xs_4642_){
_start:
{
lean_object* v_res_4643_; 
v_res_4643_ = l_Array_leftpad(v_00_u03b1_4639_, v_n_4640_, v_a_4641_, v_xs_4642_);
lean_dec_ref(v_xs_4642_);
lean_dec(v_n_4640_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg(lean_object* v_n_4644_, lean_object* v_a_4645_, lean_object* v_xs_4646_){
_start:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; 
v___x_4647_ = lean_array_get_size(v_xs_4646_);
v___x_4648_ = lean_nat_sub(v_n_4644_, v___x_4647_);
v___x_4649_ = lean_mk_array(v___x_4648_, v_a_4645_);
v___x_4650_ = l_Array_append___redArg(v_xs_4646_, v___x_4649_);
lean_dec_ref(v___x_4649_);
return v___x_4650_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg___boxed(lean_object* v_n_4651_, lean_object* v_a_4652_, lean_object* v_xs_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l_Array_rightpad___redArg(v_n_4651_, v_a_4652_, v_xs_4653_);
lean_dec(v_n_4651_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad(lean_object* v_00_u03b1_4655_, lean_object* v_n_4656_, lean_object* v_a_4657_, lean_object* v_xs_4658_){
_start:
{
lean_object* v___x_4659_; 
v___x_4659_ = l_Array_rightpad___redArg(v_n_4656_, v_a_4657_, v_xs_4658_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___boxed(lean_object* v_00_u03b1_4660_, lean_object* v_n_4661_, lean_object* v_a_4662_, lean_object* v_xs_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Array_rightpad(v_00_u03b1_4660_, v_n_4661_, v_a_4662_, v_xs_4663_);
lean_dec(v_n_4661_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0(lean_object* v_x_4665_){
_start:
{
lean_inc(v_x_4665_);
return v_x_4665_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0___boxed(lean_object* v_x_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l_Array_reduceOption___redArg___lam__0(v_x_4666_);
lean_dec(v_x_4666_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg(lean_object* v_as_4669_){
_start:
{
lean_object* v___f_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___f_4670_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4671_ = lean_unsigned_to_nat(0u);
v___x_4672_ = lean_array_get_size(v_as_4669_);
v___x_4673_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4674_ = l_Array_filterMapM___redArg(v___x_4673_, v___f_4670_, v_as_4669_, v___x_4671_, v___x_4672_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption(lean_object* v_00_u03b1_4675_, lean_object* v_as_4676_){
_start:
{
lean_object* v___f_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___f_4677_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4678_ = lean_unsigned_to_nat(0u);
v___x_4679_ = lean_array_get_size(v_as_4676_);
v___x_4680_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4681_ = l_Array_filterMapM___redArg(v___x_4680_, v___f_4677_, v_as_4676_, v___x_4678_, v___x_4679_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg___lam__0(lean_object* v_inst_4682_, lean_object* v_x1_4683_, lean_object* v_x2_4684_){
_start:
{
lean_object* v_fst_4685_; lean_object* v_snd_4686_; lean_object* v___x_4687_; uint8_t v___x_4688_; 
v_fst_4685_ = lean_ctor_get(v_x1_4683_, 0);
v_snd_4686_ = lean_ctor_get(v_x1_4683_, 1);
lean_inc(v_fst_4685_);
lean_inc(v_x2_4684_);
v___x_4687_ = lean_apply_2(v_inst_4682_, v_x2_4684_, v_fst_4685_);
v___x_4688_ = lean_unbox(v___x_4687_);
if (v___x_4688_ == 0)
{
lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4696_; 
lean_inc(v_snd_4686_);
lean_inc(v_fst_4685_);
v_isSharedCheck_4696_ = !lean_is_exclusive(v_x1_4683_);
if (v_isSharedCheck_4696_ == 0)
{
lean_object* v_unused_4697_; lean_object* v_unused_4698_; 
v_unused_4697_ = lean_ctor_get(v_x1_4683_, 1);
lean_dec(v_unused_4697_);
v_unused_4698_ = lean_ctor_get(v_x1_4683_, 0);
lean_dec(v_unused_4698_);
v___x_4690_ = v_x1_4683_;
v_isShared_4691_ = v_isSharedCheck_4696_;
goto v_resetjp_4689_;
}
else
{
lean_dec(v_x1_4683_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4696_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4692_; lean_object* v___x_4694_; 
v___x_4692_ = lean_array_push(v_snd_4686_, v_fst_4685_);
if (v_isShared_4691_ == 0)
{
lean_ctor_set(v___x_4690_, 1, v___x_4692_);
lean_ctor_set(v___x_4690_, 0, v_x2_4684_);
v___x_4694_ = v___x_4690_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_x2_4684_);
lean_ctor_set(v_reuseFailAlloc_4695_, 1, v___x_4692_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
else
{
lean_dec(v_x2_4684_);
return v_x1_4683_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg(lean_object* v_inst_4699_, lean_object* v_as_4700_){
_start:
{
lean_object* v___x_4701_; lean_object* v___x_4702_; uint8_t v___x_4703_; 
v___x_4701_ = lean_unsigned_to_nat(0u);
v___x_4702_ = lean_array_get_size(v_as_4700_);
v___x_4703_ = lean_nat_dec_lt(v___x_4701_, v___x_4702_);
if (v___x_4703_ == 0)
{
lean_object* v___x_4704_; 
lean_dec_ref(v_as_4700_);
lean_dec_ref(v_inst_4699_);
v___x_4704_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
return v___x_4704_;
}
else
{
lean_object* v___f_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; size_t v___x_4710_; size_t v___x_4711_; lean_object* v___x_4712_; lean_object* v_fst_4713_; lean_object* v_snd_4714_; lean_object* v___x_4715_; 
v___f_4705_ = lean_alloc_closure((void*)(l_Array_eraseReps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4705_, 0, v_inst_4699_);
v___x_4706_ = lean_array_fget_borrowed(v_as_4700_, v___x_4701_);
v___x_4707_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4708_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
lean_inc(v___x_4706_);
v___x_4709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4706_);
lean_ctor_set(v___x_4709_, 1, v___x_4707_);
v___x_4710_ = ((size_t)0ULL);
v___x_4711_ = lean_usize_of_nat(v___x_4702_);
v___x_4712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4708_, v___f_4705_, v_as_4700_, v___x_4710_, v___x_4711_, v___x_4709_);
v_fst_4713_ = lean_ctor_get(v___x_4712_, 0);
lean_inc(v_fst_4713_);
v_snd_4714_ = lean_ctor_get(v___x_4712_, 1);
lean_inc(v_snd_4714_);
lean_dec(v___x_4712_);
v___x_4715_ = lean_array_push(v_snd_4714_, v_fst_4713_);
return v___x_4715_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps(lean_object* v_00_u03b1_4716_, lean_object* v_inst_4717_, lean_object* v_as_4718_){
_start:
{
lean_object* v___x_4719_; 
v___x_4719_ = l_Array_eraseReps___redArg(v_inst_4717_, v_as_4718_);
return v___x_4719_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(lean_object* v_inst_4720_, lean_object* v_as_4721_, lean_object* v_a_4722_, lean_object* v_x_4723_){
_start:
{
lean_object* v_zero_4724_; uint8_t v_isZero_4725_; 
v_zero_4724_ = lean_unsigned_to_nat(0u);
v_isZero_4725_ = lean_nat_dec_eq(v_x_4723_, v_zero_4724_);
if (v_isZero_4725_ == 1)
{
lean_dec(v_x_4723_);
lean_dec(v_a_4722_);
lean_dec_ref(v_inst_4720_);
return v_isZero_4725_;
}
else
{
lean_object* v_one_4726_; lean_object* v_n_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; uint8_t v___x_4730_; 
v_one_4726_ = lean_unsigned_to_nat(1u);
v_n_4727_ = lean_nat_sub(v_x_4723_, v_one_4726_);
lean_dec(v_x_4723_);
v___x_4728_ = lean_array_fget_borrowed(v_as_4721_, v_n_4727_);
lean_inc_ref(v_inst_4720_);
lean_inc(v___x_4728_);
lean_inc(v_a_4722_);
v___x_4729_ = lean_apply_2(v_inst_4720_, v_a_4722_, v___x_4728_);
v___x_4730_ = lean_unbox(v___x_4729_);
if (v___x_4730_ == 0)
{
v_x_4723_ = v_n_4727_;
goto _start;
}
else
{
lean_dec(v_n_4727_);
lean_dec(v_a_4722_);
lean_dec_ref(v_inst_4720_);
return v_isZero_4725_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg___boxed(lean_object* v_inst_4732_, lean_object* v_as_4733_, lean_object* v_a_4734_, lean_object* v_x_4735_){
_start:
{
uint8_t v_res_4736_; lean_object* v_r_4737_; 
v_res_4736_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4732_, v_as_4733_, v_a_4734_, v_x_4735_);
lean_dec_ref(v_as_4733_);
v_r_4737_ = lean_box(v_res_4736_);
return v_r_4737_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(lean_object* v_00_u03b1_4738_, lean_object* v_inst_4739_, lean_object* v_as_4740_, lean_object* v_a_4741_, lean_object* v_x_4742_, lean_object* v_x_4743_){
_start:
{
uint8_t v___x_4744_; 
v___x_4744_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4739_, v_as_4740_, v_a_4741_, v_x_4742_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___boxed(lean_object* v_00_u03b1_4745_, lean_object* v_inst_4746_, lean_object* v_as_4747_, lean_object* v_a_4748_, lean_object* v_x_4749_, lean_object* v_x_4750_){
_start:
{
uint8_t v_res_4751_; lean_object* v_r_4752_; 
v_res_4751_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(v_00_u03b1_4745_, v_inst_4746_, v_as_4747_, v_a_4748_, v_x_4749_, v_x_4750_);
lean_dec_ref(v_as_4747_);
v_r_4752_ = lean_box(v_res_4751_);
return v_r_4752_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(lean_object* v_inst_4753_, lean_object* v_as_4754_, lean_object* v_i_4755_){
_start:
{
lean_object* v___x_4756_; uint8_t v___x_4757_; 
v___x_4756_ = lean_array_get_size(v_as_4754_);
v___x_4757_ = lean_nat_dec_lt(v_i_4755_, v___x_4756_);
if (v___x_4757_ == 0)
{
uint8_t v___x_4758_; 
lean_dec(v_i_4755_);
lean_dec_ref(v_inst_4753_);
v___x_4758_ = 1;
return v___x_4758_;
}
else
{
lean_object* v___x_4759_; uint8_t v___x_4760_; 
v___x_4759_ = lean_array_fget_borrowed(v_as_4754_, v_i_4755_);
lean_inc(v_i_4755_);
lean_inc(v___x_4759_);
lean_inc_ref(v_inst_4753_);
v___x_4760_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4753_, v_as_4754_, v___x_4759_, v_i_4755_);
if (v___x_4760_ == 0)
{
lean_dec(v_i_4755_);
lean_dec_ref(v_inst_4753_);
return v___x_4760_;
}
else
{
lean_object* v___x_4761_; lean_object* v___x_4762_; 
v___x_4761_ = lean_unsigned_to_nat(1u);
v___x_4762_ = lean_nat_add(v_i_4755_, v___x_4761_);
lean_dec(v_i_4755_);
v_i_4755_ = v___x_4762_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg___boxed(lean_object* v_inst_4764_, lean_object* v_as_4765_, lean_object* v_i_4766_){
_start:
{
uint8_t v_res_4767_; lean_object* v_r_4768_; 
v_res_4767_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4764_, v_as_4765_, v_i_4766_);
lean_dec_ref(v_as_4765_);
v_r_4768_ = lean_box(v_res_4767_);
return v_r_4768_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux(lean_object* v_00_u03b1_4769_, lean_object* v_inst_4770_, lean_object* v_as_4771_, lean_object* v_i_4772_){
_start:
{
uint8_t v___x_4773_; 
v___x_4773_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4770_, v_as_4771_, v_i_4772_);
return v___x_4773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___boxed(lean_object* v_00_u03b1_4774_, lean_object* v_inst_4775_, lean_object* v_as_4776_, lean_object* v_i_4777_){
_start:
{
uint8_t v_res_4778_; lean_object* v_r_4779_; 
v_res_4778_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux(v_00_u03b1_4774_, v_inst_4775_, v_as_4776_, v_i_4777_);
lean_dec_ref(v_as_4776_);
v_r_4779_ = lean_box(v_res_4778_);
return v_r_4779_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___redArg(lean_object* v_inst_4780_, lean_object* v_as_4781_){
_start:
{
lean_object* v___x_4782_; uint8_t v___x_4783_; 
v___x_4782_ = lean_unsigned_to_nat(0u);
v___x_4783_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4780_, v_as_4781_, v___x_4782_);
return v___x_4783_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___redArg___boxed(lean_object* v_inst_4784_, lean_object* v_as_4785_){
_start:
{
uint8_t v_res_4786_; lean_object* v_r_4787_; 
v_res_4786_ = l_Array_allDiff___redArg(v_inst_4784_, v_as_4785_);
lean_dec_ref(v_as_4785_);
v_r_4787_ = lean_box(v_res_4786_);
return v_r_4787_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff(lean_object* v_00_u03b1_4788_, lean_object* v_inst_4789_, lean_object* v_as_4790_){
_start:
{
uint8_t v___x_4791_; 
v___x_4791_ = l_Array_allDiff___redArg(v_inst_4789_, v_as_4790_);
return v___x_4791_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___boxed(lean_object* v_00_u03b1_4792_, lean_object* v_inst_4793_, lean_object* v_as_4794_){
_start:
{
uint8_t v_res_4795_; lean_object* v_r_4796_; 
v_res_4795_ = l_Array_allDiff(v_00_u03b1_4792_, v_inst_4793_, v_as_4794_);
lean_dec_ref(v_as_4794_);
v_r_4796_ = lean_box(v_res_4795_);
return v_r_4796_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0(uint8_t v___x_4797_, lean_object* v_x1_4798_, lean_object* v_x2_4799_){
_start:
{
lean_object* v_fst_4800_; uint8_t v___x_4801_; 
v_fst_4800_ = lean_ctor_get(v_x1_4798_, 0);
v___x_4801_ = lean_unbox(v_fst_4800_);
if (v___x_4801_ == 0)
{
lean_object* v_snd_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4810_; 
lean_dec(v_x2_4799_);
v_snd_4802_ = lean_ctor_get(v_x1_4798_, 1);
v_isSharedCheck_4810_ = !lean_is_exclusive(v_x1_4798_);
if (v_isSharedCheck_4810_ == 0)
{
lean_object* v_unused_4811_; 
v_unused_4811_ = lean_ctor_get(v_x1_4798_, 0);
lean_dec(v_unused_4811_);
v___x_4804_ = v_x1_4798_;
v_isShared_4805_ = v_isSharedCheck_4810_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_snd_4802_);
lean_dec(v_x1_4798_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4810_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4806_; lean_object* v___x_4808_; 
v___x_4806_ = lean_box(v___x_4797_);
if (v_isShared_4805_ == 0)
{
lean_ctor_set(v___x_4804_, 0, v___x_4806_);
v___x_4808_ = v___x_4804_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___x_4806_);
lean_ctor_set(v_reuseFailAlloc_4809_, 1, v_snd_4802_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
else
{
lean_object* v_snd_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4822_; 
v_snd_4812_ = lean_ctor_get(v_x1_4798_, 1);
v_isSharedCheck_4822_ = !lean_is_exclusive(v_x1_4798_);
if (v_isSharedCheck_4822_ == 0)
{
lean_object* v_unused_4823_; 
v_unused_4823_ = lean_ctor_get(v_x1_4798_, 0);
lean_dec(v_unused_4823_);
v___x_4814_ = v_x1_4798_;
v_isShared_4815_ = v_isSharedCheck_4822_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_snd_4812_);
lean_dec(v_x1_4798_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4822_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
uint8_t v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4820_; 
v___x_4816_ = 0;
v___x_4817_ = lean_array_push(v_snd_4812_, v_x2_4799_);
v___x_4818_ = lean_box(v___x_4816_);
if (v_isShared_4815_ == 0)
{
lean_ctor_set(v___x_4814_, 1, v___x_4817_);
lean_ctor_set(v___x_4814_, 0, v___x_4818_);
v___x_4820_ = v___x_4814_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v___x_4818_);
lean_ctor_set(v_reuseFailAlloc_4821_, 1, v___x_4817_);
v___x_4820_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
return v___x_4820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0___boxed(lean_object* v___x_4824_, lean_object* v_x1_4825_, lean_object* v_x2_4826_){
_start:
{
uint8_t v___x_137__boxed_4827_; lean_object* v_res_4828_; 
v___x_137__boxed_4827_ = lean_unbox(v___x_4824_);
v_res_4828_ = l_Array_getEvenElems___redArg___lam__0(v___x_137__boxed_4827_, v_x1_4825_, v_x2_4826_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg(lean_object* v_as_4829_){
_start:
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; uint8_t v___x_4834_; 
v___x_4830_ = lean_unsigned_to_nat(0u);
v___x_4831_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_4832_ = lean_array_get_size(v_as_4829_);
v___x_4833_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4834_ = lean_nat_dec_lt(v___x_4830_, v___x_4832_);
if (v___x_4834_ == 0)
{
lean_dec_ref(v_as_4829_);
return v___x_4831_;
}
else
{
lean_object* v___x_4835_; lean_object* v___f_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; size_t v___x_4839_; size_t v___x_4840_; lean_object* v___x_4841_; lean_object* v_snd_4842_; 
v___x_4835_ = lean_box(v___x_4834_);
v___f_4836_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4836_, 0, v___x_4835_);
v___x_4837_ = lean_box(v___x_4834_);
v___x_4838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4838_, 0, v___x_4837_);
lean_ctor_set(v___x_4838_, 1, v___x_4831_);
v___x_4839_ = ((size_t)0ULL);
v___x_4840_ = lean_usize_of_nat(v___x_4832_);
v___x_4841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4833_, v___f_4836_, v_as_4829_, v___x_4839_, v___x_4840_, v___x_4838_);
v_snd_4842_ = lean_ctor_get(v___x_4841_, 1);
lean_inc(v_snd_4842_);
lean_dec(v___x_4841_);
return v_snd_4842_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems(lean_object* v_00_u03b1_4843_, lean_object* v_as_4844_){
_start:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; uint8_t v___x_4849_; 
v___x_4845_ = lean_unsigned_to_nat(0u);
v___x_4846_ = ((lean_object*)(l_Array_instEmptyCollection___redArg___closed__0));
v___x_4847_ = lean_array_get_size(v_as_4844_);
v___x_4848_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4849_ = lean_nat_dec_lt(v___x_4845_, v___x_4847_);
if (v___x_4849_ == 0)
{
lean_dec_ref(v_as_4844_);
return v___x_4846_;
}
else
{
lean_object* v___x_4850_; lean_object* v___f_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; size_t v___x_4854_; size_t v___x_4855_; lean_object* v___x_4856_; lean_object* v_snd_4857_; 
v___x_4850_ = lean_box(v___x_4849_);
v___f_4851_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4851_, 0, v___x_4850_);
v___x_4852_ = lean_box(v___x_4849_);
v___x_4853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4852_);
lean_ctor_set(v___x_4853_, 1, v___x_4846_);
v___x_4854_ = ((size_t)0ULL);
v___x_4855_ = lean_usize_of_nat(v___x_4847_);
v___x_4856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4848_, v___f_4851_, v_as_4844_, v___x_4854_, v___x_4855_, v___x_4853_);
v_snd_4857_ = lean_ctor_get(v___x_4856_, 1);
lean_inc(v_snd_4857_);
lean_dec(v___x_4856_);
return v_snd_4857_;
}
}
}
static lean_object* _init_l_Array_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4863_ = ((lean_object*)(l_term_x23_x5b___x2c_x5d___closed__4));
v___x_4864_ = lean_string_length(v___x_4863_);
return v___x_4864_;
}
}
static lean_object* _init_l_Array_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4865_ = lean_obj_once(&l_Array_repr___redArg___closed__2, &l_Array_repr___redArg___closed__2_once, _init_l_Array_repr___redArg___closed__2);
v___x_4866_ = lean_nat_to_int(v___x_4865_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___redArg(lean_object* v_inst_4874_, lean_object* v_xs_4875_){
_start:
{
lean_object* v___x_4876_; lean_object* v___x_4877_; uint8_t v___x_4878_; 
v___x_4876_ = lean_array_get_size(v_xs_4875_);
v___x_4877_ = lean_unsigned_to_nat(0u);
v___x_4878_ = lean_nat_dec_eq(v___x_4876_, v___x_4877_);
if (v___x_4878_ == 0)
{
lean_object* v_x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; 
v_x_4879_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_4879_, 0, lean_box(0));
lean_closure_set(v_x_4879_, 1, v_inst_4874_);
v___x_4880_ = lean_array_to_list(v_xs_4875_);
v___x_4881_ = ((lean_object*)(l_Array_repr___redArg___closed__1));
v___x_4882_ = l_Std_Format_joinSep___redArg(v_x_4879_, v___x_4880_, v___x_4881_);
v___x_4883_ = lean_obj_once(&l_Array_repr___redArg___closed__3, &l_Array_repr___redArg___closed__3_once, _init_l_Array_repr___redArg___closed__3);
v___x_4884_ = ((lean_object*)(l_Array_repr___redArg___closed__4));
v___x_4885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4884_);
lean_ctor_set(v___x_4885_, 1, v___x_4882_);
v___x_4886_ = ((lean_object*)(l_Array_repr___redArg___closed__5));
v___x_4887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4885_);
lean_ctor_set(v___x_4887_, 1, v___x_4886_);
v___x_4888_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4888_, 0, v___x_4883_);
lean_ctor_set(v___x_4888_, 1, v___x_4887_);
v___x_4889_ = l_Std_Format_fill(v___x_4888_);
return v___x_4889_;
}
else
{
lean_object* v___x_4890_; 
lean_dec_ref(v_xs_4875_);
lean_dec_ref(v_inst_4874_);
v___x_4890_ = ((lean_object*)(l_Array_repr___redArg___closed__7));
return v___x_4890_;
}
}
}
LEAN_EXPORT lean_object* l_Array_repr(lean_object* v_00_u03b1_4891_, lean_object* v_inst_4892_, lean_object* v_xs_4893_){
_start:
{
lean_object* v___x_4894_; 
v___x_4894_ = l_Array_repr___redArg(v_inst_4892_, v_xs_4893_);
return v___x_4894_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0(lean_object* v_inst_4895_, lean_object* v_xs_4896_, lean_object* v_x_4897_){
_start:
{
lean_object* v___x_4898_; 
v___x_4898_ = l_Array_repr___redArg(v_inst_4895_, v_xs_4896_);
return v___x_4898_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object* v_inst_4899_, lean_object* v_xs_4900_, lean_object* v_x_4901_){
_start:
{
lean_object* v_res_4902_; 
v_res_4902_ = l_Array_instRepr___redArg___lam__0(v_inst_4899_, v_xs_4900_, v_x_4901_);
lean_dec(v_x_4901_);
return v_res_4902_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg(lean_object* v_inst_4903_){
_start:
{
lean_object* v___f_4904_; 
v___f_4904_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4904_, 0, v_inst_4903_);
return v___f_4904_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr(lean_object* v_00_u03b1_4905_, lean_object* v_inst_4906_){
_start:
{
lean_object* v___f_4907_; 
v___f_4907_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4907_, 0, v_inst_4906_);
return v___f_4907_;
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
