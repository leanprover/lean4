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
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
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
uint8_t lean_usize_dec_lt(size_t, size_t);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_x_116_);
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
lean_dec_ref(v_x_126_);
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
lean_dec_ref(v_x_136_);
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
lean_dec_ref(v_x_145_);
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
lean_dec_ref(v_this_554_);
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
lean_dec_ref(v_this_575_);
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
lean_dec_ref(v_____do__lift_792_);
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
lean_dec_ref(v_____do__lift_792_);
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
lean_dec_ref(v_____do__lift_880_);
v___x_882_ = lean_apply_2(v_toPure_875_, lean_box(0), v_a_881_);
return v___x_882_;
}
else
{
lean_object* v_a_883_; lean_object* v___x_884_; 
lean_dec(v_toPure_875_);
v_a_883_ = lean_ctor_get(v_____do__lift_880_, 0);
lean_inc(v_a_883_);
lean_dec_ref(v_____do__lift_880_);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1444_, lean_object* v_bs_1445_, lean_object* v_inst_1446_, lean_object* v_as_1447_, lean_object* v_f_1448_, lean_object* v_n_1449_, lean_object* v_____do__lift_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Array_mapFinIdxM_map___redArg___lam__0(v_j_1444_, v_bs_1445_, v_inst_1446_, v_as_1447_, v_f_1448_, v_n_1449_, v_____do__lift_1450_);
lean_dec(v_n_1449_);
lean_dec(v_j_1444_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg(lean_object* v_inst_1452_, lean_object* v_as_1453_, lean_object* v_f_1454_, lean_object* v_i_1455_, lean_object* v_j_1456_, lean_object* v_bs_1457_){
_start:
{
lean_object* v_toApplicative_1458_; lean_object* v_toBind_1459_; lean_object* v_toPure_1460_; lean_object* v_zero_1461_; uint8_t v_isZero_1462_; 
v_toApplicative_1458_ = lean_ctor_get(v_inst_1452_, 0);
v_toBind_1459_ = lean_ctor_get(v_inst_1452_, 1);
lean_inc(v_toBind_1459_);
v_toPure_1460_ = lean_ctor_get(v_toApplicative_1458_, 1);
v_zero_1461_ = lean_unsigned_to_nat(0u);
v_isZero_1462_ = lean_nat_dec_eq(v_i_1455_, v_zero_1461_);
if (v_isZero_1462_ == 1)
{
lean_object* v___x_1463_; 
lean_inc(v_toPure_1460_);
lean_dec(v_toBind_1459_);
lean_dec(v_j_1456_);
lean_dec(v_f_1454_);
lean_dec_ref(v_as_1453_);
lean_dec_ref(v_inst_1452_);
v___x_1463_ = lean_apply_2(v_toPure_1460_, lean_box(0), v_bs_1457_);
return v___x_1463_;
}
else
{
lean_object* v_one_1464_; lean_object* v_n_1465_; lean_object* v___f_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_one_1464_ = lean_unsigned_to_nat(1u);
v_n_1465_ = lean_nat_sub(v_i_1455_, v_one_1464_);
lean_inc(v_f_1454_);
lean_inc_ref(v_as_1453_);
lean_inc(v_j_1456_);
v___f_1466_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1466_, 0, v_j_1456_);
lean_closure_set(v___f_1466_, 1, v_bs_1457_);
lean_closure_set(v___f_1466_, 2, v_inst_1452_);
lean_closure_set(v___f_1466_, 3, v_as_1453_);
lean_closure_set(v___f_1466_, 4, v_f_1454_);
lean_closure_set(v___f_1466_, 5, v_n_1465_);
v___x_1467_ = lean_array_fget(v_as_1453_, v_j_1456_);
lean_dec_ref(v_as_1453_);
v___x_1468_ = lean_apply_3(v_f_1454_, v_j_1456_, v___x_1467_, lean_box(0));
v___x_1469_ = lean_apply_4(v_toBind_1459_, lean_box(0), lean_box(0), v___x_1468_, v___f_1466_);
return v___x_1469_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1470_, lean_object* v_bs_1471_, lean_object* v_inst_1472_, lean_object* v_as_1473_, lean_object* v_f_1474_, lean_object* v_n_1475_, lean_object* v_____do__lift_1476_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = lean_nat_add(v_j_1470_, v___x_1477_);
v___x_1479_ = lean_array_push(v_bs_1471_, v_____do__lift_1476_);
v___x_1480_ = l_Array_mapFinIdxM_map___redArg(v_inst_1472_, v_as_1473_, v_f_1474_, v_n_1475_, v___x_1478_, v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1481_, lean_object* v_as_1482_, lean_object* v_f_1483_, lean_object* v_i_1484_, lean_object* v_j_1485_, lean_object* v_bs_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Array_mapFinIdxM_map___redArg(v_inst_1481_, v_as_1482_, v_f_1483_, v_i_1484_, v_j_1485_, v_bs_1486_);
lean_dec(v_i_1484_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map(lean_object* v_00_u03b1_1488_, lean_object* v_00_u03b2_1489_, lean_object* v_m_1490_, lean_object* v_inst_1491_, lean_object* v_as_1492_, lean_object* v_f_1493_, lean_object* v_i_1494_, lean_object* v_j_1495_, lean_object* v_inv_1496_, lean_object* v_bs_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Array_mapFinIdxM_map___redArg(v_inst_1491_, v_as_1492_, v_f_1493_, v_i_1494_, v_j_1495_, v_bs_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___boxed(lean_object* v_00_u03b1_1499_, lean_object* v_00_u03b2_1500_, lean_object* v_m_1501_, lean_object* v_inst_1502_, lean_object* v_as_1503_, lean_object* v_f_1504_, lean_object* v_i_1505_, lean_object* v_j_1506_, lean_object* v_inv_1507_, lean_object* v_bs_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Array_mapFinIdxM_map(v_00_u03b1_1499_, v_00_u03b2_1500_, v_m_1501_, v_inst_1502_, v_as_1503_, v_f_1504_, v_i_1505_, v_j_1506_, v_inv_1507_, v_bs_1508_);
lean_dec(v_i_1505_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM___redArg(lean_object* v_inst_1510_, lean_object* v_as_1511_, lean_object* v_f_1512_){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1513_ = lean_array_get_size(v_as_1511_);
v___x_1514_ = lean_unsigned_to_nat(0u);
v___x_1515_ = lean_mk_empty_array_with_capacity(v___x_1513_);
v___x_1516_ = l_Array_mapFinIdxM_map___redArg(v_inst_1510_, v_as_1511_, v_f_1512_, v___x_1513_, v___x_1514_, v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM(lean_object* v_00_u03b1_1517_, lean_object* v_00_u03b2_1518_, lean_object* v_m_1519_, lean_object* v_inst_1520_, lean_object* v_as_1521_, lean_object* v_f_1522_){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1523_ = lean_array_get_size(v_as_1521_);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = lean_mk_empty_array_with_capacity(v___x_1523_);
v___x_1526_ = l_Array_mapFinIdxM_map___redArg(v_inst_1520_, v_as_1521_, v_f_1522_, v___x_1523_, v___x_1524_, v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg___lam__0(lean_object* v_f_1527_, lean_object* v_i_1528_, lean_object* v_a_1529_, lean_object* v_x_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_apply_2(v_f_1527_, v_i_1528_, v_a_1529_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg(lean_object* v_inst_1532_, lean_object* v_f_1533_, lean_object* v_as_1534_){
_start:
{
lean_object* v___f_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___f_1535_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1535_, 0, v_f_1533_);
v___x_1536_ = lean_array_get_size(v_as_1534_);
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = lean_mk_empty_array_with_capacity(v___x_1536_);
v___x_1539_ = l_Array_mapFinIdxM_map___redArg(v_inst_1532_, v_as_1534_, v___f_1535_, v___x_1536_, v___x_1537_, v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM(lean_object* v_00_u03b1_1540_, lean_object* v_00_u03b2_1541_, lean_object* v_m_1542_, lean_object* v_inst_1543_, lean_object* v_f_1544_, lean_object* v_as_1545_){
_start:
{
lean_object* v___f_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___f_1546_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1546_, 0, v_f_1544_);
v___x_1547_ = lean_array_get_size(v_as_1545_);
v___x_1548_ = lean_unsigned_to_nat(0u);
v___x_1549_ = lean_mk_empty_array_with_capacity(v___x_1547_);
v___x_1550_ = l_Array_mapFinIdxM_map___redArg(v_inst_1543_, v_as_1545_, v___f_1546_, v___x_1547_, v___x_1548_, v___x_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed(lean_object* v_i_1551_, lean_object* v_inst_1552_, lean_object* v_f_1553_, lean_object* v_as_1554_, lean_object* v_x_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(v_i_1551_, v_inst_1552_, v_f_1553_, v_as_1554_, v_x_1555_);
lean_dec(v_i_1551_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(lean_object* v_inst_1557_, lean_object* v_f_1558_, lean_object* v_as_1559_, lean_object* v_i_1560_){
_start:
{
lean_object* v___x_1561_; uint8_t v___x_1562_; 
v___x_1561_ = lean_array_get_size(v_as_1559_);
v___x_1562_ = lean_nat_dec_lt(v_i_1560_, v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v_failure_1563_; lean_object* v___x_1564_; 
lean_dec(v_i_1560_);
lean_dec_ref(v_as_1559_);
lean_dec(v_f_1558_);
v_failure_1563_ = lean_ctor_get(v_inst_1557_, 1);
lean_inc(v_failure_1563_);
lean_dec_ref(v_inst_1557_);
v___x_1564_ = lean_apply_1(v_failure_1563_, lean_box(0));
return v___x_1564_;
}
else
{
lean_object* v_orElse_1565_; lean_object* v___f_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_orElse_1565_ = lean_ctor_get(v_inst_1557_, 2);
lean_inc(v_orElse_1565_);
lean_inc_ref(v_as_1559_);
lean_inc(v_f_1558_);
lean_inc(v_i_1560_);
v___f_1566_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1566_, 0, v_i_1560_);
lean_closure_set(v___f_1566_, 1, v_inst_1557_);
lean_closure_set(v___f_1566_, 2, v_f_1558_);
lean_closure_set(v___f_1566_, 3, v_as_1559_);
v___x_1567_ = lean_array_fget(v_as_1559_, v_i_1560_);
lean_dec(v_i_1560_);
lean_dec_ref(v_as_1559_);
v___x_1568_ = lean_apply_1(v_f_1558_, v___x_1567_);
v___x_1569_ = lean_apply_3(v_orElse_1565_, lean_box(0), v___x_1568_, v___f_1566_);
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(lean_object* v_i_1570_, lean_object* v_inst_1571_, lean_object* v_f_1572_, lean_object* v_as_1573_, lean_object* v_x_1574_){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1575_ = lean_unsigned_to_nat(1u);
v___x_1576_ = lean_nat_add(v_i_1570_, v___x_1575_);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1571_, v_f_1572_, v_as_1573_, v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_object* v_00_u03b2_1578_, lean_object* v_00_u03b1_1579_, lean_object* v_m_1580_, lean_object* v_inst_1581_, lean_object* v_f_1582_, lean_object* v_as_1583_, lean_object* v_i_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1581_, v_f_1582_, v_as_1583_, v_i_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM___redArg(lean_object* v_inst_1586_, lean_object* v_f_1587_, lean_object* v_as_1588_){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_unsigned_to_nat(0u);
v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1586_, v_f_1587_, v_as_1588_, v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM(lean_object* v_00_u03b2_1591_, lean_object* v_00_u03b1_1592_, lean_object* v_m_1593_, lean_object* v_inst_1594_, lean_object* v_f_1595_, lean_object* v_as_1596_){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = lean_unsigned_to_nat(0u);
v___x_1598_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1594_, v_f_1595_, v_as_1596_, v___x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__0(lean_object* v___x_1599_, lean_object* v_toPure_1600_, lean_object* v___x_1601_, lean_object* v_____do__lift_1602_){
_start:
{
if (lean_obj_tag(v_____do__lift_1602_) == 1)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_dec_ref(v___x_1601_);
v___x_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1603_, 0, v_____do__lift_1602_);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v___x_1599_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
v___x_1606_ = lean_apply_2(v_toPure_1600_, lean_box(0), v___x_1605_);
return v___x_1606_;
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_dec(v_____do__lift_1602_);
v___x_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1601_);
v___x_1608_ = lean_apply_2(v_toPure_1600_, lean_box(0), v___x_1607_);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1(lean_object* v_f_1609_, lean_object* v_toBind_1610_, lean_object* v___f_1611_, lean_object* v_a_1612_, lean_object* v_x_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = lean_apply_1(v_f_1609_, v_a_1612_);
v___x_1616_ = lean_apply_4(v_toBind_1610_, lean_box(0), lean_box(0), v___x_1615_, v___f_1611_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1___boxed(lean_object* v_f_1617_, lean_object* v_toBind_1618_, lean_object* v___f_1619_, lean_object* v_a_1620_, lean_object* v_x_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Array_findSomeM_x3f___redArg___lam__1(v_f_1617_, v_toBind_1618_, v___f_1619_, v_a_1620_, v_x_1621_, v___y_1622_);
lean_dec_ref(v___y_1622_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__2(lean_object* v_toPure_1624_, lean_object* v_____s_1625_){
_start:
{
lean_object* v_fst_1626_; 
v_fst_1626_ = lean_ctor_get(v_____s_1625_, 0);
lean_inc(v_fst_1626_);
lean_dec_ref(v_____s_1625_);
if (lean_obj_tag(v_fst_1626_) == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = lean_box(0);
v___x_1628_ = lean_apply_2(v_toPure_1624_, lean_box(0), v___x_1627_);
return v___x_1628_;
}
else
{
lean_object* v_val_1629_; lean_object* v___x_1630_; 
v_val_1629_ = lean_ctor_get(v_fst_1626_, 0);
lean_inc(v_val_1629_);
lean_dec_ref(v_fst_1626_);
v___x_1630_ = lean_apply_2(v_toPure_1624_, lean_box(0), v_val_1629_);
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg(lean_object* v_inst_1634_, lean_object* v_f_1635_, lean_object* v_as_1636_){
_start:
{
lean_object* v_toApplicative_1637_; lean_object* v_toBind_1638_; lean_object* v_toPure_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___f_1642_; lean_object* v___f_1643_; lean_object* v___f_1644_; size_t v_sz_1645_; size_t v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_toApplicative_1637_ = lean_ctor_get(v_inst_1634_, 0);
v_toBind_1638_ = lean_ctor_get(v_inst_1634_, 1);
lean_inc_n(v_toBind_1638_, 2);
v_toPure_1639_ = lean_ctor_get(v_toApplicative_1637_, 1);
v___x_1640_ = lean_box(0);
v___x_1641_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1639_, 2);
v___f_1642_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1642_, 0, v___x_1640_);
lean_closure_set(v___f_1642_, 1, v_toPure_1639_);
lean_closure_set(v___f_1642_, 2, v___x_1641_);
v___f_1643_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1643_, 0, v_f_1635_);
lean_closure_set(v___f_1643_, 1, v_toBind_1638_);
lean_closure_set(v___f_1643_, 2, v___f_1642_);
v___f_1644_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1644_, 0, v_toPure_1639_);
v_sz_1645_ = lean_array_size(v_as_1636_);
v___x_1646_ = ((size_t)0ULL);
v___x_1647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1634_, v_as_1636_, v___f_1643_, v_sz_1645_, v___x_1646_, v___x_1641_);
v___x_1648_ = lean_apply_4(v_toBind_1638_, lean_box(0), lean_box(0), v___x_1647_, v___f_1644_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f(lean_object* v_00_u03b1_1649_, lean_object* v_00_u03b2_1650_, lean_object* v_m_1651_, lean_object* v_inst_1652_, lean_object* v_f_1653_, lean_object* v_as_1654_){
_start:
{
lean_object* v_toApplicative_1655_; lean_object* v_toBind_1656_; lean_object* v_toPure_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___f_1660_; lean_object* v___f_1661_; lean_object* v___f_1662_; size_t v_sz_1663_; size_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_toApplicative_1655_ = lean_ctor_get(v_inst_1652_, 0);
v_toBind_1656_ = lean_ctor_get(v_inst_1652_, 1);
lean_inc_n(v_toBind_1656_, 2);
v_toPure_1657_ = lean_ctor_get(v_toApplicative_1655_, 1);
v___x_1658_ = lean_box(0);
v___x_1659_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1657_, 2);
v___f_1660_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1660_, 0, v___x_1658_);
lean_closure_set(v___f_1660_, 1, v_toPure_1657_);
lean_closure_set(v___f_1660_, 2, v___x_1659_);
v___f_1661_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1661_, 0, v_f_1653_);
lean_closure_set(v___f_1661_, 1, v_toBind_1656_);
lean_closure_set(v___f_1661_, 2, v___f_1660_);
v___f_1662_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1662_, 0, v_toPure_1657_);
v_sz_1663_ = lean_array_size(v_as_1654_);
v___x_1664_ = ((size_t)0ULL);
v___x_1665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1652_, v_as_1654_, v___f_1661_, v_sz_1663_, v___x_1664_, v___x_1659_);
v___x_1666_ = lean_apply_4(v_toBind_1656_, lean_box(0), lean_box(0), v___x_1665_, v___f_1662_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0(lean_object* v___x_1667_, lean_object* v_toPure_1668_, lean_object* v_a_1669_, lean_object* v___x_1670_, uint8_t v_____do__lift_1671_){
_start:
{
if (v_____do__lift_1671_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec(v_a_1669_);
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1667_);
v___x_1673_ = lean_apply_2(v_toPure_1668_, lean_box(0), v___x_1672_);
return v___x_1673_;
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec_ref(v___x_1667_);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_a_1669_);
v___x_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
v___x_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
lean_ctor_set(v___x_1676_, 1, v___x_1670_);
v___x_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
v___x_1678_ = lean_apply_2(v_toPure_1668_, lean_box(0), v___x_1677_);
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0___boxed(lean_object* v___x_1679_, lean_object* v_toPure_1680_, lean_object* v_a_1681_, lean_object* v___x_1682_, lean_object* v_____do__lift_1683_){
_start:
{
uint8_t v_____do__lift_214__boxed_1684_; lean_object* v_res_1685_; 
v_____do__lift_214__boxed_1684_ = lean_unbox(v_____do__lift_1683_);
v_res_1685_ = l_Array_findM_x3f___redArg___lam__0(v___x_1679_, v_toPure_1680_, v_a_1681_, v___x_1682_, v_____do__lift_214__boxed_1684_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1(lean_object* v___x_1686_, lean_object* v_toPure_1687_, lean_object* v___x_1688_, lean_object* v_p_1689_, lean_object* v_toBind_1690_, lean_object* v_a_1691_, lean_object* v_x_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___f_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_inc(v_a_1691_);
v___f_1694_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1694_, 0, v___x_1686_);
lean_closure_set(v___f_1694_, 1, v_toPure_1687_);
lean_closure_set(v___f_1694_, 2, v_a_1691_);
lean_closure_set(v___f_1694_, 3, v___x_1688_);
v___x_1695_ = lean_apply_1(v_p_1689_, v_a_1691_);
v___x_1696_ = lean_apply_4(v_toBind_1690_, lean_box(0), lean_box(0), v___x_1695_, v___f_1694_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_1697_, lean_object* v_toPure_1698_, lean_object* v___x_1699_, lean_object* v_p_1700_, lean_object* v_toBind_1701_, lean_object* v_a_1702_, lean_object* v_x_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Array_findM_x3f___redArg___lam__1(v___x_1697_, v_toPure_1698_, v___x_1699_, v_p_1700_, v_toBind_1701_, v_a_1702_, v_x_1703_, v___y_1704_);
lean_dec_ref(v___y_1704_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg(lean_object* v_inst_1706_, lean_object* v_p_1707_, lean_object* v_as_1708_){
_start:
{
lean_object* v_toApplicative_1709_; lean_object* v_toBind_1710_; lean_object* v_toPure_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___f_1714_; lean_object* v___f_1715_; size_t v_sz_1716_; size_t v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_toApplicative_1709_ = lean_ctor_get(v_inst_1706_, 0);
v_toBind_1710_ = lean_ctor_get(v_inst_1706_, 1);
lean_inc_n(v_toBind_1710_, 2);
v_toPure_1711_ = lean_ctor_get(v_toApplicative_1709_, 1);
v___x_1712_ = lean_box(0);
v___x_1713_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1711_, 2);
v___f_1714_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1714_, 0, v___x_1713_);
lean_closure_set(v___f_1714_, 1, v_toPure_1711_);
lean_closure_set(v___f_1714_, 2, v___x_1712_);
lean_closure_set(v___f_1714_, 3, v_p_1707_);
lean_closure_set(v___f_1714_, 4, v_toBind_1710_);
v___f_1715_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1715_, 0, v_toPure_1711_);
v_sz_1716_ = lean_array_size(v_as_1708_);
v___x_1717_ = ((size_t)0ULL);
v___x_1718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1706_, v_as_1708_, v___f_1714_, v_sz_1716_, v___x_1717_, v___x_1713_);
v___x_1719_ = lean_apply_4(v_toBind_1710_, lean_box(0), lean_box(0), v___x_1718_, v___f_1715_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f(lean_object* v_m_1720_, lean_object* v_00_u03b1_1721_, lean_object* v_inst_1722_, lean_object* v_p_1723_, lean_object* v_as_1724_){
_start:
{
lean_object* v_toApplicative_1725_; lean_object* v_toBind_1726_; lean_object* v_toPure_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___f_1730_; lean_object* v___f_1731_; size_t v_sz_1732_; size_t v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v_toApplicative_1725_ = lean_ctor_get(v_inst_1722_, 0);
v_toBind_1726_ = lean_ctor_get(v_inst_1722_, 1);
lean_inc_n(v_toBind_1726_, 2);
v_toPure_1727_ = lean_ctor_get(v_toApplicative_1725_, 1);
v___x_1728_ = lean_box(0);
v___x_1729_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1727_, 2);
v___f_1730_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1730_, 0, v___x_1729_);
lean_closure_set(v___f_1730_, 1, v_toPure_1727_);
lean_closure_set(v___f_1730_, 2, v___x_1728_);
lean_closure_set(v___f_1730_, 3, v_p_1723_);
lean_closure_set(v___f_1730_, 4, v_toBind_1726_);
v___f_1731_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1731_, 0, v_toPure_1727_);
v_sz_1732_ = lean_array_size(v_as_1724_);
v___x_1733_ = ((size_t)0ULL);
v___x_1734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1722_, v_as_1724_, v___f_1730_, v_sz_1732_, v___x_1733_, v___x_1729_);
v___x_1735_ = lean_apply_4(v_toBind_1726_, lean_box(0), lean_box(0), v___x_1734_, v___f_1731_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0(lean_object* v_snd_1736_, lean_object* v___x_1737_, lean_object* v_toPure_1738_, uint8_t v_____do__lift_1739_){
_start:
{
if (v_____do__lift_1739_ == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1740_ = lean_unsigned_to_nat(1u);
v___x_1741_ = lean_nat_add(v_snd_1736_, v___x_1740_);
lean_dec(v_snd_1736_);
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1737_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
v___x_1744_ = lean_apply_2(v_toPure_1738_, lean_box(0), v___x_1743_);
return v___x_1744_;
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec(v___x_1737_);
lean_inc(v_snd_1736_);
v___x_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_snd_1736_);
v___x_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
lean_ctor_set(v___x_1747_, 1, v_snd_1736_);
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
v___x_1749_ = lean_apply_2(v_toPure_1738_, lean_box(0), v___x_1748_);
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0___boxed(lean_object* v_snd_1750_, lean_object* v___x_1751_, lean_object* v_toPure_1752_, lean_object* v_____do__lift_1753_){
_start:
{
uint8_t v_____do__lift_249__boxed_1754_; lean_object* v_res_1755_; 
v_____do__lift_249__boxed_1754_ = lean_unbox(v_____do__lift_1753_);
v_res_1755_ = l_Array_findIdxM_x3f___redArg___lam__0(v_snd_1750_, v___x_1751_, v_toPure_1752_, v_____do__lift_249__boxed_1754_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__1(lean_object* v___x_1756_, lean_object* v_toPure_1757_, lean_object* v_p_1758_, lean_object* v_toBind_1759_, lean_object* v_a_1760_, lean_object* v_x_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_snd_1763_; lean_object* v___f_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_snd_1763_ = lean_ctor_get(v___y_1762_, 1);
lean_inc(v_snd_1763_);
lean_dec_ref(v___y_1762_);
v___f_1764_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1764_, 0, v_snd_1763_);
lean_closure_set(v___f_1764_, 1, v___x_1756_);
lean_closure_set(v___f_1764_, 2, v_toPure_1757_);
v___x_1765_ = lean_apply_1(v_p_1758_, v_a_1760_);
v___x_1766_ = lean_apply_4(v_toBind_1759_, lean_box(0), lean_box(0), v___x_1765_, v___f_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__2(lean_object* v_toPure_1767_, lean_object* v_____s_1768_){
_start:
{
lean_object* v_fst_1769_; 
v_fst_1769_ = lean_ctor_get(v_____s_1768_, 0);
lean_inc(v_fst_1769_);
lean_dec_ref(v_____s_1768_);
if (lean_obj_tag(v_fst_1769_) == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_box(0);
v___x_1771_ = lean_apply_2(v_toPure_1767_, lean_box(0), v___x_1770_);
return v___x_1771_;
}
else
{
lean_object* v_val_1772_; lean_object* v___x_1773_; 
v_val_1772_ = lean_ctor_get(v_fst_1769_, 0);
lean_inc(v_val_1772_);
lean_dec_ref(v_fst_1769_);
v___x_1773_ = lean_apply_2(v_toPure_1767_, lean_box(0), v_val_1772_);
return v___x_1773_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg(lean_object* v_inst_1777_, lean_object* v_p_1778_, lean_object* v_as_1779_){
_start:
{
lean_object* v_toApplicative_1780_; lean_object* v_toBind_1781_; lean_object* v_toPure_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___f_1785_; lean_object* v___f_1786_; size_t v_sz_1787_; size_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_toApplicative_1780_ = lean_ctor_get(v_inst_1777_, 0);
v_toBind_1781_ = lean_ctor_get(v_inst_1777_, 1);
lean_inc_n(v_toBind_1781_, 2);
v_toPure_1782_ = lean_ctor_get(v_toApplicative_1780_, 1);
v___x_1783_ = lean_box(0);
v___x_1784_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1782_, 2);
v___f_1785_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1785_, 0, v___x_1783_);
lean_closure_set(v___f_1785_, 1, v_toPure_1782_);
lean_closure_set(v___f_1785_, 2, v_p_1778_);
lean_closure_set(v___f_1785_, 3, v_toBind_1781_);
v___f_1786_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1786_, 0, v_toPure_1782_);
v_sz_1787_ = lean_array_size(v_as_1779_);
v___x_1788_ = ((size_t)0ULL);
v___x_1789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1777_, v_as_1779_, v___f_1785_, v_sz_1787_, v___x_1788_, v___x_1784_);
v___x_1790_ = lean_apply_4(v_toBind_1781_, lean_box(0), lean_box(0), v___x_1789_, v___f_1786_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f(lean_object* v_00_u03b1_1791_, lean_object* v_m_1792_, lean_object* v_inst_1793_, lean_object* v_p_1794_, lean_object* v_as_1795_){
_start:
{
lean_object* v_toApplicative_1796_; lean_object* v_toBind_1797_; lean_object* v_toPure_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___f_1801_; lean_object* v___f_1802_; size_t v_sz_1803_; size_t v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v_toApplicative_1796_ = lean_ctor_get(v_inst_1793_, 0);
v_toBind_1797_ = lean_ctor_get(v_inst_1793_, 1);
lean_inc_n(v_toBind_1797_, 2);
v_toPure_1798_ = lean_ctor_get(v_toApplicative_1796_, 1);
v___x_1799_ = lean_box(0);
v___x_1800_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1798_, 2);
v___f_1801_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1801_, 0, v___x_1799_);
lean_closure_set(v___f_1801_, 1, v_toPure_1798_);
lean_closure_set(v___f_1801_, 2, v_p_1794_);
lean_closure_set(v___f_1801_, 3, v_toBind_1797_);
v___f_1802_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1802_, 0, v_toPure_1798_);
v_sz_1803_ = lean_array_size(v_as_1795_);
v___x_1804_ = ((size_t)0ULL);
v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1793_, v_as_1795_, v___f_1801_, v_sz_1803_, v___x_1804_, v___x_1800_);
v___x_1806_ = lean_apply_4(v_toBind_1797_, lean_box(0), lean_box(0), v___x_1805_, v___f_1802_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed(lean_object* v_i_1807_, lean_object* v_inst_1808_, lean_object* v_p_1809_, lean_object* v_as_1810_, lean_object* v_stop_1811_, lean_object* v_toApplicative_1812_, lean_object* v___x_1813_, lean_object* v_____do__lift_1814_){
_start:
{
size_t v_i_boxed_1815_; size_t v_stop_boxed_1816_; uint8_t v___x_153__boxed_1817_; uint8_t v_____do__lift_154__boxed_1818_; lean_object* v_res_1819_; 
v_i_boxed_1815_ = lean_unbox_usize(v_i_1807_);
lean_dec(v_i_1807_);
v_stop_boxed_1816_ = lean_unbox_usize(v_stop_1811_);
lean_dec(v_stop_1811_);
v___x_153__boxed_1817_ = lean_unbox(v___x_1813_);
v_____do__lift_154__boxed_1818_ = lean_unbox(v_____do__lift_1814_);
v_res_1819_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(v_i_boxed_1815_, v_inst_1808_, v_p_1809_, v_as_1810_, v_stop_boxed_1816_, v_toApplicative_1812_, v___x_153__boxed_1817_, v_____do__lift_154__boxed_1818_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(lean_object* v_inst_1820_, lean_object* v_p_1821_, lean_object* v_as_1822_, size_t v_i_1823_, size_t v_stop_1824_){
_start:
{
uint8_t v___x_1825_; 
v___x_1825_ = lean_usize_dec_eq(v_i_1823_, v_stop_1824_);
if (v___x_1825_ == 0)
{
lean_object* v_toApplicative_1826_; lean_object* v_toBind_1827_; uint8_t v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___f_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v_toApplicative_1826_ = lean_ctor_get(v_inst_1820_, 0);
lean_inc_ref(v_toApplicative_1826_);
v_toBind_1827_ = lean_ctor_get(v_inst_1820_, 1);
lean_inc(v_toBind_1827_);
v___x_1828_ = 1;
v___x_1829_ = lean_box_usize(v_i_1823_);
v___x_1830_ = lean_box_usize(v_stop_1824_);
v___x_1831_ = lean_box(v___x_1828_);
lean_inc_ref(v_as_1822_);
lean_inc(v_p_1821_);
v___f_1832_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1832_, 0, v___x_1829_);
lean_closure_set(v___f_1832_, 1, v_inst_1820_);
lean_closure_set(v___f_1832_, 2, v_p_1821_);
lean_closure_set(v___f_1832_, 3, v_as_1822_);
lean_closure_set(v___f_1832_, 4, v___x_1830_);
lean_closure_set(v___f_1832_, 5, v_toApplicative_1826_);
lean_closure_set(v___f_1832_, 6, v___x_1831_);
v___x_1833_ = lean_array_uget(v_as_1822_, v_i_1823_);
lean_dec_ref(v_as_1822_);
v___x_1834_ = lean_apply_1(v_p_1821_, v___x_1833_);
v___x_1835_ = lean_apply_4(v_toBind_1827_, lean_box(0), lean_box(0), v___x_1834_, v___f_1832_);
return v___x_1835_;
}
else
{
lean_object* v_toApplicative_1836_; lean_object* v_toPure_1837_; uint8_t v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_dec_ref(v_as_1822_);
lean_dec(v_p_1821_);
v_toApplicative_1836_ = lean_ctor_get(v_inst_1820_, 0);
lean_inc_ref(v_toApplicative_1836_);
lean_dec_ref(v_inst_1820_);
v_toPure_1837_ = lean_ctor_get(v_toApplicative_1836_, 1);
lean_inc(v_toPure_1837_);
lean_dec_ref(v_toApplicative_1836_);
v___x_1838_ = 0;
v___x_1839_ = lean_box(v___x_1838_);
v___x_1840_ = lean_apply_2(v_toPure_1837_, lean_box(0), v___x_1839_);
return v___x_1840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(size_t v_i_1841_, lean_object* v_inst_1842_, lean_object* v_p_1843_, lean_object* v_as_1844_, size_t v_stop_1845_, lean_object* v_toApplicative_1846_, uint8_t v___x_1847_, uint8_t v_____do__lift_1848_){
_start:
{
if (v_____do__lift_1848_ == 0)
{
size_t v___x_1849_; size_t v___x_1850_; lean_object* v___x_1851_; 
lean_dec_ref(v_toApplicative_1846_);
v___x_1849_ = ((size_t)1ULL);
v___x_1850_ = lean_usize_add(v_i_1841_, v___x_1849_);
v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1842_, v_p_1843_, v_as_1844_, v___x_1850_, v_stop_1845_);
return v___x_1851_;
}
else
{
lean_object* v_toPure_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
lean_dec_ref(v_as_1844_);
lean_dec(v_p_1843_);
lean_dec_ref(v_inst_1842_);
v_toPure_1852_ = lean_ctor_get(v_toApplicative_1846_, 1);
lean_inc(v_toPure_1852_);
lean_dec_ref(v_toApplicative_1846_);
v___x_1853_ = lean_box(v___x_1847_);
v___x_1854_ = lean_apply_2(v_toPure_1852_, lean_box(0), v___x_1853_);
return v___x_1854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___boxed(lean_object* v_inst_1855_, lean_object* v_p_1856_, lean_object* v_as_1857_, lean_object* v_i_1858_, lean_object* v_stop_1859_){
_start:
{
size_t v_i_boxed_1860_; size_t v_stop_boxed_1861_; lean_object* v_res_1862_; 
v_i_boxed_1860_ = lean_unbox_usize(v_i_1858_);
lean_dec(v_i_1858_);
v_stop_boxed_1861_ = lean_unbox_usize(v_stop_1859_);
lean_dec(v_stop_1859_);
v_res_1862_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1855_, v_p_1856_, v_as_1857_, v_i_boxed_1860_, v_stop_boxed_1861_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object* v_00_u03b1_1863_, lean_object* v_m_1864_, lean_object* v_inst_1865_, lean_object* v_p_1866_, lean_object* v_as_1867_, size_t v_i_1868_, size_t v_stop_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1865_, v_p_1866_, v_as_1867_, v_i_1868_, v_stop_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___boxed(lean_object* v_00_u03b1_1871_, lean_object* v_m_1872_, lean_object* v_inst_1873_, lean_object* v_p_1874_, lean_object* v_as_1875_, lean_object* v_i_1876_, lean_object* v_stop_1877_){
_start:
{
size_t v_i_boxed_1878_; size_t v_stop_boxed_1879_; lean_object* v_res_1880_; 
v_i_boxed_1878_ = lean_unbox_usize(v_i_1876_);
lean_dec(v_i_1876_);
v_stop_boxed_1879_ = lean_unbox_usize(v_stop_1877_);
lean_dec(v_stop_1877_);
v_res_1880_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(v_00_u03b1_1871_, v_m_1872_, v_inst_1873_, v_p_1874_, v_as_1875_, v_i_boxed_1878_, v_stop_boxed_1879_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg(lean_object* v_inst_1881_, lean_object* v_p_1882_, lean_object* v_as_1883_, lean_object* v_start_1884_, lean_object* v_stop_1885_){
_start:
{
lean_object* v___y_1887_; uint8_t v___x_1896_; 
v___x_1896_ = lean_nat_dec_lt(v_start_1884_, v_stop_1885_);
if (v___x_1896_ == 0)
{
lean_object* v_toApplicative_1897_; lean_object* v_toPure_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
lean_dec(v_stop_1885_);
lean_dec_ref(v_as_1883_);
lean_dec(v_p_1882_);
v_toApplicative_1897_ = lean_ctor_get(v_inst_1881_, 0);
lean_inc_ref(v_toApplicative_1897_);
lean_dec_ref(v_inst_1881_);
v_toPure_1898_ = lean_ctor_get(v_toApplicative_1897_, 1);
lean_inc(v_toPure_1898_);
lean_dec_ref(v_toApplicative_1897_);
v___x_1899_ = lean_box(v___x_1896_);
v___x_1900_ = lean_apply_2(v_toPure_1898_, lean_box(0), v___x_1899_);
return v___x_1900_;
}
else
{
lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1901_ = lean_array_get_size(v_as_1883_);
v___x_1902_ = lean_nat_dec_le(v_stop_1885_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_dec(v_stop_1885_);
v___y_1887_ = v___x_1901_;
goto v___jp_1886_;
}
else
{
v___y_1887_ = v_stop_1885_;
goto v___jp_1886_;
}
}
v___jp_1886_:
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_nat_dec_lt(v_start_1884_, v___y_1887_);
if (v___x_1888_ == 0)
{
lean_object* v_toApplicative_1889_; lean_object* v_toPure_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
lean_dec(v___y_1887_);
lean_dec_ref(v_as_1883_);
lean_dec(v_p_1882_);
v_toApplicative_1889_ = lean_ctor_get(v_inst_1881_, 0);
lean_inc_ref(v_toApplicative_1889_);
lean_dec_ref(v_inst_1881_);
v_toPure_1890_ = lean_ctor_get(v_toApplicative_1889_, 1);
lean_inc(v_toPure_1890_);
lean_dec_ref(v_toApplicative_1889_);
v___x_1891_ = lean_box(v___x_1888_);
v___x_1892_ = lean_apply_2(v_toPure_1890_, lean_box(0), v___x_1891_);
return v___x_1892_;
}
else
{
size_t v___x_1893_; size_t v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = lean_usize_of_nat(v_start_1884_);
v___x_1894_ = lean_usize_of_nat(v___y_1887_);
lean_dec(v___y_1887_);
v___x_1895_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1881_, v_p_1882_, v_as_1883_, v___x_1893_, v___x_1894_);
return v___x_1895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg___boxed(lean_object* v_inst_1903_, lean_object* v_p_1904_, lean_object* v_as_1905_, lean_object* v_start_1906_, lean_object* v_stop_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Array_anyMUnsafe___redArg(v_inst_1903_, v_p_1904_, v_as_1905_, v_start_1906_, v_stop_1907_);
lean_dec(v_start_1906_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe(lean_object* v_00_u03b1_1909_, lean_object* v_m_1910_, lean_object* v_inst_1911_, lean_object* v_p_1912_, lean_object* v_as_1913_, lean_object* v_start_1914_, lean_object* v_stop_1915_){
_start:
{
lean_object* v___y_1917_; uint8_t v___x_1926_; 
v___x_1926_ = lean_nat_dec_lt(v_start_1914_, v_stop_1915_);
if (v___x_1926_ == 0)
{
lean_object* v_toApplicative_1927_; lean_object* v_toPure_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
lean_dec(v_stop_1915_);
lean_dec_ref(v_as_1913_);
lean_dec(v_p_1912_);
v_toApplicative_1927_ = lean_ctor_get(v_inst_1911_, 0);
lean_inc_ref(v_toApplicative_1927_);
lean_dec_ref(v_inst_1911_);
v_toPure_1928_ = lean_ctor_get(v_toApplicative_1927_, 1);
lean_inc(v_toPure_1928_);
lean_dec_ref(v_toApplicative_1927_);
v___x_1929_ = lean_box(v___x_1926_);
v___x_1930_ = lean_apply_2(v_toPure_1928_, lean_box(0), v___x_1929_);
return v___x_1930_;
}
else
{
lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1931_ = lean_array_get_size(v_as_1913_);
v___x_1932_ = lean_nat_dec_le(v_stop_1915_, v___x_1931_);
if (v___x_1932_ == 0)
{
lean_dec(v_stop_1915_);
v___y_1917_ = v___x_1931_;
goto v___jp_1916_;
}
else
{
v___y_1917_ = v_stop_1915_;
goto v___jp_1916_;
}
}
v___jp_1916_:
{
uint8_t v___x_1918_; 
v___x_1918_ = lean_nat_dec_lt(v_start_1914_, v___y_1917_);
if (v___x_1918_ == 0)
{
lean_object* v_toApplicative_1919_; lean_object* v_toPure_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
lean_dec(v___y_1917_);
lean_dec_ref(v_as_1913_);
lean_dec(v_p_1912_);
v_toApplicative_1919_ = lean_ctor_get(v_inst_1911_, 0);
lean_inc_ref(v_toApplicative_1919_);
lean_dec_ref(v_inst_1911_);
v_toPure_1920_ = lean_ctor_get(v_toApplicative_1919_, 1);
lean_inc(v_toPure_1920_);
lean_dec_ref(v_toApplicative_1919_);
v___x_1921_ = lean_box(v___x_1918_);
v___x_1922_ = lean_apply_2(v_toPure_1920_, lean_box(0), v___x_1921_);
return v___x_1922_;
}
else
{
size_t v___x_1923_; size_t v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = lean_usize_of_nat(v_start_1914_);
v___x_1924_ = lean_usize_of_nat(v___y_1917_);
lean_dec(v___y_1917_);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1911_, v_p_1912_, v_as_1913_, v___x_1923_, v___x_1924_);
return v___x_1925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___boxed(lean_object* v_00_u03b1_1933_, lean_object* v_m_1934_, lean_object* v_inst_1935_, lean_object* v_p_1936_, lean_object* v_as_1937_, lean_object* v_start_1938_, lean_object* v_stop_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Array_anyMUnsafe(v_00_u03b1_1933_, v_m_1934_, v_inst_1935_, v_p_1936_, v_as_1937_, v_start_1938_, v_stop_1939_);
lean_dec(v_start_1938_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0___boxed(lean_object* v_j_1941_, lean_object* v_inst_1942_, lean_object* v_p_1943_, lean_object* v_as_1944_, lean_object* v_stop_1945_, lean_object* v_toApplicative_1946_, lean_object* v_____do__lift_1947_){
_start:
{
uint8_t v_____do__lift_82__boxed_1948_; lean_object* v_res_1949_; 
v_____do__lift_82__boxed_1948_ = lean_unbox(v_____do__lift_1947_);
v_res_1949_ = l_Array_anyM_loop___redArg___lam__0(v_j_1941_, v_inst_1942_, v_p_1943_, v_as_1944_, v_stop_1945_, v_toApplicative_1946_, v_____do__lift_82__boxed_1948_);
lean_dec(v_j_1941_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg(lean_object* v_inst_1950_, lean_object* v_p_1951_, lean_object* v_as_1952_, lean_object* v_stop_1953_, lean_object* v_j_1954_){
_start:
{
uint8_t v___x_1955_; 
v___x_1955_ = lean_nat_dec_lt(v_j_1954_, v_stop_1953_);
if (v___x_1955_ == 0)
{
lean_object* v_toApplicative_1956_; lean_object* v_toPure_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_dec(v_j_1954_);
lean_dec(v_stop_1953_);
lean_dec_ref(v_as_1952_);
lean_dec(v_p_1951_);
v_toApplicative_1956_ = lean_ctor_get(v_inst_1950_, 0);
lean_inc_ref(v_toApplicative_1956_);
lean_dec_ref(v_inst_1950_);
v_toPure_1957_ = lean_ctor_get(v_toApplicative_1956_, 1);
lean_inc(v_toPure_1957_);
lean_dec_ref(v_toApplicative_1956_);
v___x_1958_ = lean_box(v___x_1955_);
v___x_1959_ = lean_apply_2(v_toPure_1957_, lean_box(0), v___x_1958_);
return v___x_1959_;
}
else
{
lean_object* v_toApplicative_1960_; lean_object* v_toBind_1961_; lean_object* v___f_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v_toApplicative_1960_ = lean_ctor_get(v_inst_1950_, 0);
lean_inc_ref(v_toApplicative_1960_);
v_toBind_1961_ = lean_ctor_get(v_inst_1950_, 1);
lean_inc(v_toBind_1961_);
lean_inc_ref(v_as_1952_);
lean_inc(v_p_1951_);
lean_inc(v_j_1954_);
v___f_1962_ = lean_alloc_closure((void*)(l_Array_anyM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1962_, 0, v_j_1954_);
lean_closure_set(v___f_1962_, 1, v_inst_1950_);
lean_closure_set(v___f_1962_, 2, v_p_1951_);
lean_closure_set(v___f_1962_, 3, v_as_1952_);
lean_closure_set(v___f_1962_, 4, v_stop_1953_);
lean_closure_set(v___f_1962_, 5, v_toApplicative_1960_);
v___x_1963_ = lean_array_fget(v_as_1952_, v_j_1954_);
lean_dec(v_j_1954_);
lean_dec_ref(v_as_1952_);
v___x_1964_ = lean_apply_1(v_p_1951_, v___x_1963_);
v___x_1965_ = lean_apply_4(v_toBind_1961_, lean_box(0), lean_box(0), v___x_1964_, v___f_1962_);
return v___x_1965_;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0(lean_object* v_j_1966_, lean_object* v_inst_1967_, lean_object* v_p_1968_, lean_object* v_as_1969_, lean_object* v_stop_1970_, lean_object* v_toApplicative_1971_, uint8_t v_____do__lift_1972_){
_start:
{
if (v_____do__lift_1972_ == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_dec_ref(v_toApplicative_1971_);
v___x_1973_ = lean_unsigned_to_nat(1u);
v___x_1974_ = lean_nat_add(v_j_1966_, v___x_1973_);
v___x_1975_ = l_Array_anyM_loop___redArg(v_inst_1967_, v_p_1968_, v_as_1969_, v_stop_1970_, v___x_1974_);
return v___x_1975_;
}
else
{
lean_object* v_toPure_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
lean_dec(v_stop_1970_);
lean_dec_ref(v_as_1969_);
lean_dec(v_p_1968_);
lean_dec_ref(v_inst_1967_);
v_toPure_1976_ = lean_ctor_get(v_toApplicative_1971_, 1);
lean_inc(v_toPure_1976_);
lean_dec_ref(v_toApplicative_1971_);
v___x_1977_ = lean_box(v_____do__lift_1972_);
v___x_1978_ = lean_apply_2(v_toPure_1976_, lean_box(0), v___x_1977_);
return v___x_1978_;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop(lean_object* v_00_u03b1_1979_, lean_object* v_m_1980_, lean_object* v_inst_1981_, lean_object* v_p_1982_, lean_object* v_as_1983_, lean_object* v_stop_1984_, lean_object* v_h_1985_, lean_object* v_j_1986_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l_Array_anyM_loop___redArg(v_inst_1981_, v_p_1982_, v_as_1983_, v_stop_1984_, v_j_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0(lean_object* v_toPure_1988_, uint8_t v_____do__lift_1989_){
_start:
{
if (v_____do__lift_1989_ == 0)
{
uint8_t v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = 1;
v___x_1991_ = lean_box(v___x_1990_);
v___x_1992_ = lean_apply_2(v_toPure_1988_, lean_box(0), v___x_1991_);
return v___x_1992_;
}
else
{
uint8_t v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = 0;
v___x_1994_ = lean_box(v___x_1993_);
v___x_1995_ = lean_apply_2(v_toPure_1988_, lean_box(0), v___x_1994_);
return v___x_1995_;
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0___boxed(lean_object* v_toPure_1996_, lean_object* v_____do__lift_1997_){
_start:
{
uint8_t v_____do__lift_123__boxed_1998_; lean_object* v_res_1999_; 
v_____do__lift_123__boxed_1998_ = lean_unbox(v_____do__lift_1997_);
v_res_1999_ = l_Array_allM___redArg___lam__0(v_toPure_1996_, v_____do__lift_123__boxed_1998_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1(lean_object* v_toPure_2000_, uint8_t v___x_2001_, uint8_t v_____do__lift_2002_){
_start:
{
if (v_____do__lift_2002_ == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_box(v___x_2001_);
v___x_2004_ = lean_apply_2(v_toPure_2000_, lean_box(0), v___x_2003_);
return v___x_2004_;
}
else
{
uint8_t v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = 0;
v___x_2006_ = lean_box(v___x_2005_);
v___x_2007_ = lean_apply_2(v_toPure_2000_, lean_box(0), v___x_2006_);
return v___x_2007_;
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1___boxed(lean_object* v_toPure_2008_, lean_object* v___x_2009_, lean_object* v_____do__lift_2010_){
_start:
{
uint8_t v___x_138__boxed_2011_; uint8_t v_____do__lift_139__boxed_2012_; lean_object* v_res_2013_; 
v___x_138__boxed_2011_ = lean_unbox(v___x_2009_);
v_____do__lift_139__boxed_2012_ = lean_unbox(v_____do__lift_2010_);
v_res_2013_ = l_Array_allM___redArg___lam__1(v_toPure_2008_, v___x_138__boxed_2011_, v_____do__lift_139__boxed_2012_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__2(lean_object* v_p_2014_, lean_object* v_toBind_2015_, lean_object* v___f_2016_, lean_object* v_v_2017_){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_apply_1(v_p_2014_, v_v_2017_);
v___x_2019_ = lean_apply_4(v_toBind_2015_, lean_box(0), lean_box(0), v___x_2018_, v___f_2016_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg(lean_object* v_inst_2020_, lean_object* v_p_2021_, lean_object* v_as_2022_, lean_object* v_start_2023_, lean_object* v_stop_2024_){
_start:
{
lean_object* v_toApplicative_2025_; lean_object* v_toBind_2026_; lean_object* v_toPure_2027_; lean_object* v___f_2028_; uint8_t v___x_2029_; 
v_toApplicative_2025_ = lean_ctor_get(v_inst_2020_, 0);
v_toBind_2026_ = lean_ctor_get(v_inst_2020_, 1);
lean_inc(v_toBind_2026_);
v_toPure_2027_ = lean_ctor_get(v_toApplicative_2025_, 1);
lean_inc(v_toPure_2027_);
v___f_2028_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2028_, 0, v_toPure_2027_);
v___x_2029_ = lean_nat_dec_lt(v_start_2023_, v_stop_2024_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_inc(v_toPure_2027_);
lean_dec(v_stop_2024_);
lean_dec_ref(v_as_2022_);
lean_dec(v_p_2021_);
lean_dec_ref(v_inst_2020_);
v___x_2030_ = lean_box(v___x_2029_);
v___x_2031_ = lean_apply_2(v_toPure_2027_, lean_box(0), v___x_2030_);
v___x_2032_ = lean_apply_4(v_toBind_2026_, lean_box(0), lean_box(0), v___x_2031_, v___f_2028_);
return v___x_2032_;
}
else
{
lean_object* v___x_2033_; lean_object* v___f_2034_; lean_object* v___f_2035_; lean_object* v___y_2037_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v___x_2033_ = lean_box(v___x_2029_);
lean_inc(v_toPure_2027_);
v___f_2034_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2034_, 0, v_toPure_2027_);
lean_closure_set(v___f_2034_, 1, v___x_2033_);
lean_inc(v_toBind_2026_);
v___f_2035_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2035_, 0, v_p_2021_);
lean_closure_set(v___f_2035_, 1, v_toBind_2026_);
lean_closure_set(v___f_2035_, 2, v___f_2034_);
v___x_2046_ = lean_array_get_size(v_as_2022_);
v___x_2047_ = lean_nat_dec_le(v_stop_2024_, v___x_2046_);
if (v___x_2047_ == 0)
{
lean_dec(v_stop_2024_);
v___y_2037_ = v___x_2046_;
goto v___jp_2036_;
}
else
{
v___y_2037_ = v_stop_2024_;
goto v___jp_2036_;
}
v___jp_2036_:
{
uint8_t v___x_2038_; 
v___x_2038_ = lean_nat_dec_lt(v_start_2023_, v___y_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
lean_inc(v_toPure_2027_);
lean_dec(v___y_2037_);
lean_dec_ref(v___f_2035_);
lean_dec_ref(v_as_2022_);
lean_dec_ref(v_inst_2020_);
v___x_2039_ = lean_box(v___x_2038_);
v___x_2040_ = lean_apply_2(v_toPure_2027_, lean_box(0), v___x_2039_);
v___x_2041_ = lean_apply_4(v_toBind_2026_, lean_box(0), lean_box(0), v___x_2040_, v___f_2028_);
return v___x_2041_;
}
else
{
size_t v___x_2042_; size_t v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2042_ = lean_usize_of_nat(v_start_2023_);
v___x_2043_ = lean_usize_of_nat(v___y_2037_);
lean_dec(v___y_2037_);
v___x_2044_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2020_, v___f_2035_, v_as_2022_, v___x_2042_, v___x_2043_);
v___x_2045_ = lean_apply_4(v_toBind_2026_, lean_box(0), lean_box(0), v___x_2044_, v___f_2028_);
return v___x_2045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___boxed(lean_object* v_inst_2048_, lean_object* v_p_2049_, lean_object* v_as_2050_, lean_object* v_start_2051_, lean_object* v_stop_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Array_allM___redArg(v_inst_2048_, v_p_2049_, v_as_2050_, v_start_2051_, v_stop_2052_);
lean_dec(v_start_2051_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Array_allM(lean_object* v_00_u03b1_2054_, lean_object* v_m_2055_, lean_object* v_inst_2056_, lean_object* v_p_2057_, lean_object* v_as_2058_, lean_object* v_start_2059_, lean_object* v_stop_2060_){
_start:
{
lean_object* v_toApplicative_2061_; lean_object* v_toBind_2062_; lean_object* v_toPure_2063_; lean_object* v___f_2064_; uint8_t v___x_2065_; 
v_toApplicative_2061_ = lean_ctor_get(v_inst_2056_, 0);
v_toBind_2062_ = lean_ctor_get(v_inst_2056_, 1);
lean_inc(v_toBind_2062_);
v_toPure_2063_ = lean_ctor_get(v_toApplicative_2061_, 1);
lean_inc(v_toPure_2063_);
v___f_2064_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2064_, 0, v_toPure_2063_);
v___x_2065_ = lean_nat_dec_lt(v_start_2059_, v_stop_2060_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
lean_inc(v_toPure_2063_);
lean_dec(v_stop_2060_);
lean_dec_ref(v_as_2058_);
lean_dec(v_p_2057_);
lean_dec_ref(v_inst_2056_);
v___x_2066_ = lean_box(v___x_2065_);
v___x_2067_ = lean_apply_2(v_toPure_2063_, lean_box(0), v___x_2066_);
v___x_2068_ = lean_apply_4(v_toBind_2062_, lean_box(0), lean_box(0), v___x_2067_, v___f_2064_);
return v___x_2068_;
}
else
{
lean_object* v___x_2069_; lean_object* v___f_2070_; lean_object* v___f_2071_; lean_object* v___y_2073_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2069_ = lean_box(v___x_2065_);
lean_inc(v_toPure_2063_);
v___f_2070_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2070_, 0, v_toPure_2063_);
lean_closure_set(v___f_2070_, 1, v___x_2069_);
lean_inc(v_toBind_2062_);
v___f_2071_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2071_, 0, v_p_2057_);
lean_closure_set(v___f_2071_, 1, v_toBind_2062_);
lean_closure_set(v___f_2071_, 2, v___f_2070_);
v___x_2082_ = lean_array_get_size(v_as_2058_);
v___x_2083_ = lean_nat_dec_le(v_stop_2060_, v___x_2082_);
if (v___x_2083_ == 0)
{
lean_dec(v_stop_2060_);
v___y_2073_ = v___x_2082_;
goto v___jp_2072_;
}
else
{
v___y_2073_ = v_stop_2060_;
goto v___jp_2072_;
}
v___jp_2072_:
{
uint8_t v___x_2074_; 
v___x_2074_ = lean_nat_dec_lt(v_start_2059_, v___y_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_inc(v_toPure_2063_);
lean_dec(v___y_2073_);
lean_dec_ref(v___f_2071_);
lean_dec_ref(v_as_2058_);
lean_dec_ref(v_inst_2056_);
v___x_2075_ = lean_box(v___x_2074_);
v___x_2076_ = lean_apply_2(v_toPure_2063_, lean_box(0), v___x_2075_);
v___x_2077_ = lean_apply_4(v_toBind_2062_, lean_box(0), lean_box(0), v___x_2076_, v___f_2064_);
return v___x_2077_;
}
else
{
size_t v___x_2078_; size_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2078_ = lean_usize_of_nat(v_start_2059_);
v___x_2079_ = lean_usize_of_nat(v___y_2073_);
lean_dec(v___y_2073_);
v___x_2080_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2056_, v___f_2071_, v_as_2058_, v___x_2078_, v___x_2079_);
v___x_2081_ = lean_apply_4(v_toBind_2062_, lean_box(0), lean_box(0), v___x_2080_, v___f_2064_);
return v___x_2081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___boxed(lean_object* v_00_u03b1_2084_, lean_object* v_m_2085_, lean_object* v_inst_2086_, lean_object* v_p_2087_, lean_object* v_as_2088_, lean_object* v_start_2089_, lean_object* v_stop_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Array_allM(v_00_u03b1_2084_, v_m_2085_, v_inst_2086_, v_p_2087_, v_as_2088_, v_start_2089_, v_stop_2090_);
lean_dec(v_start_2089_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed(lean_object* v_inst_2092_, lean_object* v_f_2093_, lean_object* v_as_2094_, lean_object* v_n_2095_, lean_object* v_toPure_2096_, lean_object* v_r_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(v_inst_2092_, v_f_2093_, v_as_2094_, v_n_2095_, v_toPure_2096_, v_r_2097_);
lean_dec(v_n_2095_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(lean_object* v_inst_2099_, lean_object* v_f_2100_, lean_object* v_as_2101_, lean_object* v_i_2102_){
_start:
{
lean_object* v_toApplicative_2103_; lean_object* v_toBind_2104_; lean_object* v_toPure_2105_; lean_object* v_zero_2106_; uint8_t v_isZero_2107_; 
v_toApplicative_2103_ = lean_ctor_get(v_inst_2099_, 0);
v_toBind_2104_ = lean_ctor_get(v_inst_2099_, 1);
lean_inc(v_toBind_2104_);
v_toPure_2105_ = lean_ctor_get(v_toApplicative_2103_, 1);
lean_inc(v_toPure_2105_);
v_zero_2106_ = lean_unsigned_to_nat(0u);
v_isZero_2107_ = lean_nat_dec_eq(v_i_2102_, v_zero_2106_);
if (v_isZero_2107_ == 1)
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
lean_dec(v_toBind_2104_);
lean_dec_ref(v_as_2101_);
lean_dec(v_f_2100_);
lean_dec_ref(v_inst_2099_);
v___x_2108_ = lean_box(0);
v___x_2109_ = lean_apply_2(v_toPure_2105_, lean_box(0), v___x_2108_);
return v___x_2109_;
}
else
{
lean_object* v_one_2110_; lean_object* v_n_2111_; lean_object* v___f_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v_one_2110_ = lean_unsigned_to_nat(1u);
v_n_2111_ = lean_nat_sub(v_i_2102_, v_one_2110_);
lean_inc(v_n_2111_);
lean_inc_ref(v_as_2101_);
lean_inc(v_f_2100_);
v___f_2112_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2112_, 0, v_inst_2099_);
lean_closure_set(v___f_2112_, 1, v_f_2100_);
lean_closure_set(v___f_2112_, 2, v_as_2101_);
lean_closure_set(v___f_2112_, 3, v_n_2111_);
lean_closure_set(v___f_2112_, 4, v_toPure_2105_);
v___x_2113_ = lean_array_fget(v_as_2101_, v_n_2111_);
lean_dec(v_n_2111_);
lean_dec_ref(v_as_2101_);
v___x_2114_ = lean_apply_1(v_f_2100_, v___x_2113_);
v___x_2115_ = lean_apply_4(v_toBind_2104_, lean_box(0), lean_box(0), v___x_2114_, v___f_2112_);
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(lean_object* v_inst_2116_, lean_object* v_f_2117_, lean_object* v_as_2118_, lean_object* v_n_2119_, lean_object* v_toPure_2120_, lean_object* v_r_2121_){
_start:
{
if (lean_obj_tag(v_r_2121_) == 0)
{
lean_object* v___x_2122_; 
lean_dec(v_toPure_2120_);
v___x_2122_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2116_, v_f_2117_, v_as_2118_, v_n_2119_);
return v___x_2122_;
}
else
{
lean_object* v___x_2123_; 
lean_dec_ref(v_as_2118_);
lean_dec(v_f_2117_);
lean_dec_ref(v_inst_2116_);
v___x_2123_ = lean_apply_2(v_toPure_2120_, lean_box(0), v_r_2121_);
return v___x_2123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___boxed(lean_object* v_inst_2124_, lean_object* v_f_2125_, lean_object* v_as_2126_, lean_object* v_i_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2124_, v_f_2125_, v_as_2126_, v_i_2127_);
lean_dec(v_i_2127_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_object* v_00_u03b1_2129_, lean_object* v_00_u03b2_2130_, lean_object* v_m_2131_, lean_object* v_inst_2132_, lean_object* v_f_2133_, lean_object* v_as_2134_, lean_object* v_i_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2132_, v_f_2133_, v_as_2134_, v_i_2135_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___boxed(lean_object* v_00_u03b1_2138_, lean_object* v_00_u03b2_2139_, lean_object* v_m_2140_, lean_object* v_inst_2141_, lean_object* v_f_2142_, lean_object* v_as_2143_, lean_object* v_i_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(v_00_u03b1_2138_, v_00_u03b2_2139_, v_m_2140_, v_inst_2141_, v_f_2142_, v_as_2143_, v_i_2144_, v_a_2145_);
lean_dec(v_i_2144_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f___redArg(lean_object* v_inst_2147_, lean_object* v_f_2148_, lean_object* v_as_2149_){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = lean_array_get_size(v_as_2149_);
v___x_2151_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2147_, v_f_2148_, v_as_2149_, v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f(lean_object* v_00_u03b1_2152_, lean_object* v_00_u03b2_2153_, lean_object* v_m_2154_, lean_object* v_inst_2155_, lean_object* v_f_2156_, lean_object* v_as_2157_){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = lean_array_get_size(v_as_2157_);
v___x_2159_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2155_, v_f_2156_, v_as_2157_, v___x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2160_, lean_object* v_a_2161_, uint8_t v_____do__lift_2162_){
_start:
{
if (v_____do__lift_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
lean_dec(v_a_2161_);
v___x_2163_ = lean_box(0);
v___x_2164_ = lean_apply_2(v_toPure_2160_, lean_box(0), v___x_2163_);
return v___x_2164_;
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v_a_2161_);
v___x_2166_ = lean_apply_2(v_toPure_2160_, lean_box(0), v___x_2165_);
return v___x_2166_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2167_, lean_object* v_a_2168_, lean_object* v_____do__lift_2169_){
_start:
{
uint8_t v_____do__lift_74__boxed_2170_; lean_object* v_res_2171_; 
v_____do__lift_74__boxed_2170_ = lean_unbox(v_____do__lift_2169_);
v_res_2171_ = l_Array_findRevM_x3f___redArg___lam__0(v_toPure_2167_, v_a_2168_, v_____do__lift_74__boxed_2170_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2172_, lean_object* v_p_2173_, lean_object* v_toBind_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v___f_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_inc(v_a_2175_);
v___f_2176_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2176_, 0, v_toPure_2172_);
lean_closure_set(v___f_2176_, 1, v_a_2175_);
v___x_2177_ = lean_apply_1(v_p_2173_, v_a_2175_);
v___x_2178_ = lean_apply_4(v_toBind_2174_, lean_box(0), lean_box(0), v___x_2177_, v___f_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg(lean_object* v_inst_2179_, lean_object* v_p_2180_, lean_object* v_as_2181_){
_start:
{
lean_object* v_toApplicative_2182_; lean_object* v_toBind_2183_; lean_object* v_toPure_2184_; lean_object* v___f_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v_toApplicative_2182_ = lean_ctor_get(v_inst_2179_, 0);
v_toBind_2183_ = lean_ctor_get(v_inst_2179_, 1);
v_toPure_2184_ = lean_ctor_get(v_toApplicative_2182_, 1);
lean_inc(v_toBind_2183_);
lean_inc(v_toPure_2184_);
v___f_2185_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2185_, 0, v_toPure_2184_);
lean_closure_set(v___f_2185_, 1, v_p_2180_);
lean_closure_set(v___f_2185_, 2, v_toBind_2183_);
v___x_2186_ = lean_array_get_size(v_as_2181_);
v___x_2187_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2179_, v___f_2185_, v_as_2181_, v___x_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f(lean_object* v_00_u03b1_2188_, lean_object* v_m_2189_, lean_object* v_inst_2190_, lean_object* v_p_2191_, lean_object* v_as_2192_){
_start:
{
lean_object* v_toApplicative_2193_; lean_object* v_toBind_2194_; lean_object* v_toPure_2195_; lean_object* v___f_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v_toApplicative_2193_ = lean_ctor_get(v_inst_2190_, 0);
v_toBind_2194_ = lean_ctor_get(v_inst_2190_, 1);
v_toPure_2195_ = lean_ctor_get(v_toApplicative_2193_, 1);
lean_inc(v_toBind_2194_);
lean_inc(v_toPure_2195_);
v___f_2196_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2196_, 0, v_toPure_2195_);
lean_closure_set(v___f_2196_, 1, v_p_2191_);
lean_closure_set(v___f_2196_, 2, v_toBind_2194_);
v___x_2197_ = lean_array_get_size(v_as_2192_);
v___x_2198_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2190_, v___f_2196_, v_as_2192_, v___x_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___lam__0(lean_object* v_f_2199_, lean_object* v_x_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_apply_1(v_f_2199_, v___y_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg(lean_object* v_inst_2203_, lean_object* v_f_2204_, lean_object* v_as_2205_, lean_object* v_start_2206_, lean_object* v_stop_2207_){
_start:
{
lean_object* v___x_2208_; uint8_t v___x_2209_; 
v___x_2208_ = lean_box(0);
v___x_2209_ = lean_nat_dec_lt(v_start_2206_, v_stop_2207_);
if (v___x_2209_ == 0)
{
lean_object* v_toApplicative_2210_; lean_object* v_toPure_2211_; lean_object* v___x_2212_; 
lean_dec_ref(v_as_2205_);
lean_dec(v_f_2204_);
v_toApplicative_2210_ = lean_ctor_get(v_inst_2203_, 0);
lean_inc_ref(v_toApplicative_2210_);
lean_dec_ref(v_inst_2203_);
v_toPure_2211_ = lean_ctor_get(v_toApplicative_2210_, 1);
lean_inc(v_toPure_2211_);
lean_dec_ref(v_toApplicative_2210_);
v___x_2212_ = lean_apply_2(v_toPure_2211_, lean_box(0), v___x_2208_);
return v___x_2212_;
}
else
{
lean_object* v___f_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; 
v___f_2213_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2213_, 0, v_f_2204_);
v___x_2214_ = lean_array_get_size(v_as_2205_);
v___x_2215_ = lean_nat_dec_le(v_stop_2207_, v___x_2214_);
if (v___x_2215_ == 0)
{
uint8_t v___x_2216_; 
v___x_2216_ = lean_nat_dec_lt(v_start_2206_, v___x_2214_);
if (v___x_2216_ == 0)
{
lean_object* v_toApplicative_2217_; lean_object* v_toPure_2218_; lean_object* v___x_2219_; 
lean_dec_ref(v___f_2213_);
lean_dec_ref(v_as_2205_);
v_toApplicative_2217_ = lean_ctor_get(v_inst_2203_, 0);
lean_inc_ref(v_toApplicative_2217_);
lean_dec_ref(v_inst_2203_);
v_toPure_2218_ = lean_ctor_get(v_toApplicative_2217_, 1);
lean_inc(v_toPure_2218_);
lean_dec_ref(v_toApplicative_2217_);
v___x_2219_ = lean_apply_2(v_toPure_2218_, lean_box(0), v___x_2208_);
return v___x_2219_;
}
else
{
size_t v___x_2220_; size_t v___x_2221_; lean_object* v___x_2222_; 
v___x_2220_ = lean_usize_of_nat(v_start_2206_);
v___x_2221_ = lean_usize_of_nat(v___x_2214_);
v___x_2222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2203_, v___f_2213_, v_as_2205_, v___x_2220_, v___x_2221_, v___x_2208_);
return v___x_2222_;
}
}
else
{
size_t v___x_2223_; size_t v___x_2224_; lean_object* v___x_2225_; 
v___x_2223_ = lean_usize_of_nat(v_start_2206_);
v___x_2224_ = lean_usize_of_nat(v_stop_2207_);
v___x_2225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2203_, v___f_2213_, v_as_2205_, v___x_2223_, v___x_2224_, v___x_2208_);
return v___x_2225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___boxed(lean_object* v_inst_2226_, lean_object* v_f_2227_, lean_object* v_as_2228_, lean_object* v_start_2229_, lean_object* v_stop_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Array_forM___redArg(v_inst_2226_, v_f_2227_, v_as_2228_, v_start_2229_, v_stop_2230_);
lean_dec(v_stop_2230_);
lean_dec(v_start_2229_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Array_forM(lean_object* v_00_u03b1_2232_, lean_object* v_m_2233_, lean_object* v_inst_2234_, lean_object* v_f_2235_, lean_object* v_as_2236_, lean_object* v_start_2237_, lean_object* v_stop_2238_){
_start:
{
lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = lean_box(0);
v___x_2240_ = lean_nat_dec_lt(v_start_2237_, v_stop_2238_);
if (v___x_2240_ == 0)
{
lean_object* v_toApplicative_2241_; lean_object* v_toPure_2242_; lean_object* v___x_2243_; 
lean_dec_ref(v_as_2236_);
lean_dec(v_f_2235_);
v_toApplicative_2241_ = lean_ctor_get(v_inst_2234_, 0);
lean_inc_ref(v_toApplicative_2241_);
lean_dec_ref(v_inst_2234_);
v_toPure_2242_ = lean_ctor_get(v_toApplicative_2241_, 1);
lean_inc(v_toPure_2242_);
lean_dec_ref(v_toApplicative_2241_);
v___x_2243_ = lean_apply_2(v_toPure_2242_, lean_box(0), v___x_2239_);
return v___x_2243_;
}
else
{
lean_object* v___f_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v___f_2244_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2244_, 0, v_f_2235_);
v___x_2245_ = lean_array_get_size(v_as_2236_);
v___x_2246_ = lean_nat_dec_le(v_stop_2238_, v___x_2245_);
if (v___x_2246_ == 0)
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_nat_dec_lt(v_start_2237_, v___x_2245_);
if (v___x_2247_ == 0)
{
lean_object* v_toApplicative_2248_; lean_object* v_toPure_2249_; lean_object* v___x_2250_; 
lean_dec_ref(v___f_2244_);
lean_dec_ref(v_as_2236_);
v_toApplicative_2248_ = lean_ctor_get(v_inst_2234_, 0);
lean_inc_ref(v_toApplicative_2248_);
lean_dec_ref(v_inst_2234_);
v_toPure_2249_ = lean_ctor_get(v_toApplicative_2248_, 1);
lean_inc(v_toPure_2249_);
lean_dec_ref(v_toApplicative_2248_);
v___x_2250_ = lean_apply_2(v_toPure_2249_, lean_box(0), v___x_2239_);
return v___x_2250_;
}
else
{
size_t v___x_2251_; size_t v___x_2252_; lean_object* v___x_2253_; 
v___x_2251_ = lean_usize_of_nat(v_start_2237_);
v___x_2252_ = lean_usize_of_nat(v___x_2245_);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2234_, v___f_2244_, v_as_2236_, v___x_2251_, v___x_2252_, v___x_2239_);
return v___x_2253_;
}
}
else
{
size_t v___x_2254_; size_t v___x_2255_; lean_object* v___x_2256_; 
v___x_2254_ = lean_usize_of_nat(v_start_2237_);
v___x_2255_ = lean_usize_of_nat(v_stop_2238_);
v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2234_, v___f_2244_, v_as_2236_, v___x_2254_, v___x_2255_, v___x_2239_);
return v___x_2256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___boxed(lean_object* v_00_u03b1_2257_, lean_object* v_m_2258_, lean_object* v_inst_2259_, lean_object* v_f_2260_, lean_object* v_as_2261_, lean_object* v_start_2262_, lean_object* v_stop_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Array_forM(v_00_u03b1_2257_, v_m_2258_, v_inst_2259_, v_f_2260_, v_as_2261_, v_start_2262_, v_stop_2263_);
lean_dec(v_stop_2263_);
lean_dec(v_start_2262_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg___lam__1(lean_object* v_inst_2265_, lean_object* v_xs_2266_, lean_object* v_f_2267_){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2268_ = lean_unsigned_to_nat(0u);
v___x_2269_ = lean_array_get_size(v_xs_2266_);
v___x_2270_ = lean_box(0);
v___x_2271_ = lean_nat_dec_lt(v___x_2268_, v___x_2269_);
if (v___x_2271_ == 0)
{
lean_object* v_toApplicative_2272_; lean_object* v_toPure_2273_; lean_object* v___x_2274_; 
lean_dec(v_f_2267_);
lean_dec_ref(v_xs_2266_);
v_toApplicative_2272_ = lean_ctor_get(v_inst_2265_, 0);
lean_inc_ref(v_toApplicative_2272_);
lean_dec_ref(v_inst_2265_);
v_toPure_2273_ = lean_ctor_get(v_toApplicative_2272_, 1);
lean_inc(v_toPure_2273_);
lean_dec_ref(v_toApplicative_2272_);
v___x_2274_ = lean_apply_2(v_toPure_2273_, lean_box(0), v___x_2270_);
return v___x_2274_;
}
else
{
lean_object* v___f_2275_; uint8_t v___x_2276_; 
v___f_2275_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2275_, 0, v_f_2267_);
v___x_2276_ = lean_nat_dec_le(v___x_2269_, v___x_2269_);
if (v___x_2276_ == 0)
{
if (v___x_2271_ == 0)
{
lean_object* v_toApplicative_2277_; lean_object* v_toPure_2278_; lean_object* v___x_2279_; 
lean_dec_ref(v___f_2275_);
lean_dec_ref(v_xs_2266_);
v_toApplicative_2277_ = lean_ctor_get(v_inst_2265_, 0);
lean_inc_ref(v_toApplicative_2277_);
lean_dec_ref(v_inst_2265_);
v_toPure_2278_ = lean_ctor_get(v_toApplicative_2277_, 1);
lean_inc(v_toPure_2278_);
lean_dec_ref(v_toApplicative_2277_);
v___x_2279_ = lean_apply_2(v_toPure_2278_, lean_box(0), v___x_2270_);
return v___x_2279_;
}
else
{
size_t v___x_2280_; size_t v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = ((size_t)0ULL);
v___x_2281_ = lean_usize_of_nat(v___x_2269_);
v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2265_, v___f_2275_, v_xs_2266_, v___x_2280_, v___x_2281_, v___x_2270_);
return v___x_2282_;
}
}
else
{
size_t v___x_2283_; size_t v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = ((size_t)0ULL);
v___x_2284_ = lean_usize_of_nat(v___x_2269_);
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2265_, v___f_2275_, v_xs_2266_, v___x_2283_, v___x_2284_, v___x_2270_);
return v___x_2285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg(lean_object* v_inst_2286_){
_start:
{
lean_object* v___f_2287_; 
v___f_2287_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2287_, 0, v_inst_2286_);
return v___f_2287_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad(lean_object* v_00_u03b1_2288_, lean_object* v_m_2289_, lean_object* v_inst_2290_){
_start:
{
lean_object* v___f_2291_; 
v___f_2291_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2291_, 0, v_inst_2290_);
return v___f_2291_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___lam__0(lean_object* v_f_2292_, lean_object* v_a_2293_, lean_object* v_x_2294_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = lean_apply_1(v_f_2292_, v_a_2293_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg(lean_object* v_inst_2296_, lean_object* v_f_2297_, lean_object* v_as_2298_, lean_object* v_start_2299_, lean_object* v_stop_2300_){
_start:
{
lean_object* v___f_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___f_2301_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2301_, 0, v_f_2297_);
v___x_2302_ = lean_box(0);
v___x_2303_ = lean_array_get_size(v_as_2298_);
v___x_2304_ = lean_nat_dec_le(v_start_2299_, v___x_2303_);
if (v___x_2304_ == 0)
{
uint8_t v___x_2305_; 
v___x_2305_ = lean_nat_dec_lt(v_stop_2300_, v___x_2303_);
if (v___x_2305_ == 0)
{
lean_object* v_toApplicative_2306_; lean_object* v_toPure_2307_; lean_object* v___x_2308_; 
lean_dec_ref(v___f_2301_);
lean_dec_ref(v_as_2298_);
v_toApplicative_2306_ = lean_ctor_get(v_inst_2296_, 0);
lean_inc_ref(v_toApplicative_2306_);
lean_dec_ref(v_inst_2296_);
v_toPure_2307_ = lean_ctor_get(v_toApplicative_2306_, 1);
lean_inc(v_toPure_2307_);
lean_dec_ref(v_toApplicative_2306_);
v___x_2308_ = lean_apply_2(v_toPure_2307_, lean_box(0), v___x_2302_);
return v___x_2308_;
}
else
{
size_t v___x_2309_; size_t v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = lean_usize_of_nat(v___x_2303_);
v___x_2310_ = lean_usize_of_nat(v_stop_2300_);
v___x_2311_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2296_, v___f_2301_, v_as_2298_, v___x_2309_, v___x_2310_, v___x_2302_);
return v___x_2311_;
}
}
else
{
uint8_t v___x_2312_; 
v___x_2312_ = lean_nat_dec_lt(v_stop_2300_, v_start_2299_);
if (v___x_2312_ == 0)
{
lean_object* v_toApplicative_2313_; lean_object* v_toPure_2314_; lean_object* v___x_2315_; 
lean_dec_ref(v___f_2301_);
lean_dec_ref(v_as_2298_);
v_toApplicative_2313_ = lean_ctor_get(v_inst_2296_, 0);
lean_inc_ref(v_toApplicative_2313_);
lean_dec_ref(v_inst_2296_);
v_toPure_2314_ = lean_ctor_get(v_toApplicative_2313_, 1);
lean_inc(v_toPure_2314_);
lean_dec_ref(v_toApplicative_2313_);
v___x_2315_ = lean_apply_2(v_toPure_2314_, lean_box(0), v___x_2302_);
return v___x_2315_;
}
else
{
size_t v___x_2316_; size_t v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = lean_usize_of_nat(v_start_2299_);
v___x_2317_ = lean_usize_of_nat(v_stop_2300_);
v___x_2318_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2296_, v___f_2301_, v_as_2298_, v___x_2316_, v___x_2317_, v___x_2302_);
return v___x_2318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___boxed(lean_object* v_inst_2319_, lean_object* v_f_2320_, lean_object* v_as_2321_, lean_object* v_start_2322_, lean_object* v_stop_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Array_forRevM___redArg(v_inst_2319_, v_f_2320_, v_as_2321_, v_start_2322_, v_stop_2323_);
lean_dec(v_stop_2323_);
lean_dec(v_start_2322_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM(lean_object* v_00_u03b1_2325_, lean_object* v_m_2326_, lean_object* v_inst_2327_, lean_object* v_f_2328_, lean_object* v_as_2329_, lean_object* v_start_2330_, lean_object* v_stop_2331_){
_start:
{
lean_object* v___f_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___f_2332_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2332_, 0, v_f_2328_);
v___x_2333_ = lean_box(0);
v___x_2334_ = lean_array_get_size(v_as_2329_);
v___x_2335_ = lean_nat_dec_le(v_start_2330_, v___x_2334_);
if (v___x_2335_ == 0)
{
uint8_t v___x_2336_; 
v___x_2336_ = lean_nat_dec_lt(v_stop_2331_, v___x_2334_);
if (v___x_2336_ == 0)
{
lean_object* v_toApplicative_2337_; lean_object* v_toPure_2338_; lean_object* v___x_2339_; 
lean_dec_ref(v___f_2332_);
lean_dec_ref(v_as_2329_);
v_toApplicative_2337_ = lean_ctor_get(v_inst_2327_, 0);
lean_inc_ref(v_toApplicative_2337_);
lean_dec_ref(v_inst_2327_);
v_toPure_2338_ = lean_ctor_get(v_toApplicative_2337_, 1);
lean_inc(v_toPure_2338_);
lean_dec_ref(v_toApplicative_2337_);
v___x_2339_ = lean_apply_2(v_toPure_2338_, lean_box(0), v___x_2333_);
return v___x_2339_;
}
else
{
size_t v___x_2340_; size_t v___x_2341_; lean_object* v___x_2342_; 
v___x_2340_ = lean_usize_of_nat(v___x_2334_);
v___x_2341_ = lean_usize_of_nat(v_stop_2331_);
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2327_, v___f_2332_, v_as_2329_, v___x_2340_, v___x_2341_, v___x_2333_);
return v___x_2342_;
}
}
else
{
uint8_t v___x_2343_; 
v___x_2343_ = lean_nat_dec_lt(v_stop_2331_, v_start_2330_);
if (v___x_2343_ == 0)
{
lean_object* v_toApplicative_2344_; lean_object* v_toPure_2345_; lean_object* v___x_2346_; 
lean_dec_ref(v___f_2332_);
lean_dec_ref(v_as_2329_);
v_toApplicative_2344_ = lean_ctor_get(v_inst_2327_, 0);
lean_inc_ref(v_toApplicative_2344_);
lean_dec_ref(v_inst_2327_);
v_toPure_2345_ = lean_ctor_get(v_toApplicative_2344_, 1);
lean_inc(v_toPure_2345_);
lean_dec_ref(v_toApplicative_2344_);
v___x_2346_ = lean_apply_2(v_toPure_2345_, lean_box(0), v___x_2333_);
return v___x_2346_;
}
else
{
size_t v___x_2347_; size_t v___x_2348_; lean_object* v___x_2349_; 
v___x_2347_ = lean_usize_of_nat(v_start_2330_);
v___x_2348_ = lean_usize_of_nat(v_stop_2331_);
v___x_2349_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2327_, v___f_2332_, v_as_2329_, v___x_2347_, v___x_2348_, v___x_2333_);
return v___x_2349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___boxed(lean_object* v_00_u03b1_2350_, lean_object* v_m_2351_, lean_object* v_inst_2352_, lean_object* v_f_2353_, lean_object* v_as_2354_, lean_object* v_start_2355_, lean_object* v_stop_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Array_forRevM(v_00_u03b1_2350_, v_m_2351_, v_inst_2352_, v_f_2353_, v_as_2354_, v_start_2355_, v_stop_2356_);
lean_dec(v_stop_2356_);
lean_dec(v_start_2355_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___lam__0(lean_object* v_f_2358_, lean_object* v_x1_2359_, lean_object* v_x2_2360_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = lean_apply_2(v_f_2358_, v_x1_2359_, v_x2_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg(lean_object* v_f_2381_, lean_object* v_init_2382_, lean_object* v_as_2383_, lean_object* v_start_2384_, lean_object* v_stop_2385_){
_start:
{
lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2386_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2387_ = lean_nat_dec_lt(v_start_2384_, v_stop_2385_);
if (v___x_2387_ == 0)
{
lean_dec_ref(v_as_2383_);
lean_dec(v_f_2381_);
return v_init_2382_;
}
else
{
lean_object* v___f_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___f_2388_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2388_, 0, v_f_2381_);
v___x_2389_ = lean_array_get_size(v_as_2383_);
v___x_2390_ = lean_nat_dec_le(v_stop_2385_, v___x_2389_);
if (v___x_2390_ == 0)
{
uint8_t v___x_2391_; 
v___x_2391_ = lean_nat_dec_lt(v_start_2384_, v___x_2389_);
if (v___x_2391_ == 0)
{
lean_dec_ref(v___f_2388_);
lean_dec_ref(v_as_2383_);
return v_init_2382_;
}
else
{
size_t v___x_2392_; size_t v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = lean_usize_of_nat(v_start_2384_);
v___x_2393_ = lean_usize_of_nat(v___x_2389_);
v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2386_, v___f_2388_, v_as_2383_, v___x_2392_, v___x_2393_, v_init_2382_);
return v___x_2394_;
}
}
else
{
size_t v___x_2395_; size_t v___x_2396_; lean_object* v___x_2397_; 
v___x_2395_ = lean_usize_of_nat(v_start_2384_);
v___x_2396_ = lean_usize_of_nat(v_stop_2385_);
v___x_2397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2386_, v___f_2388_, v_as_2383_, v___x_2395_, v___x_2396_, v_init_2382_);
return v___x_2397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___boxed(lean_object* v_f_2398_, lean_object* v_init_2399_, lean_object* v_as_2400_, lean_object* v_start_2401_, lean_object* v_stop_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Array_foldl___redArg(v_f_2398_, v_init_2399_, v_as_2400_, v_start_2401_, v_stop_2402_);
lean_dec(v_stop_2402_);
lean_dec(v_start_2401_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl(lean_object* v_00_u03b1_2404_, lean_object* v_00_u03b2_2405_, lean_object* v_f_2406_, lean_object* v_init_2407_, lean_object* v_as_2408_, lean_object* v_start_2409_, lean_object* v_stop_2410_){
_start:
{
lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2411_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2412_ = lean_nat_dec_lt(v_start_2409_, v_stop_2410_);
if (v___x_2412_ == 0)
{
lean_dec_ref(v_as_2408_);
lean_dec(v_f_2406_);
return v_init_2407_;
}
else
{
lean_object* v___f_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___f_2413_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2413_, 0, v_f_2406_);
v___x_2414_ = lean_array_get_size(v_as_2408_);
v___x_2415_ = lean_nat_dec_le(v_stop_2410_, v___x_2414_);
if (v___x_2415_ == 0)
{
uint8_t v___x_2416_; 
v___x_2416_ = lean_nat_dec_lt(v_start_2409_, v___x_2414_);
if (v___x_2416_ == 0)
{
lean_dec_ref(v___f_2413_);
lean_dec_ref(v_as_2408_);
return v_init_2407_;
}
else
{
size_t v___x_2417_; size_t v___x_2418_; lean_object* v___x_2419_; 
v___x_2417_ = lean_usize_of_nat(v_start_2409_);
v___x_2418_ = lean_usize_of_nat(v___x_2414_);
v___x_2419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2411_, v___f_2413_, v_as_2408_, v___x_2417_, v___x_2418_, v_init_2407_);
return v___x_2419_;
}
}
else
{
size_t v___x_2420_; size_t v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = lean_usize_of_nat(v_start_2409_);
v___x_2421_ = lean_usize_of_nat(v_stop_2410_);
v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2411_, v___f_2413_, v_as_2408_, v___x_2420_, v___x_2421_, v_init_2407_);
return v___x_2422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___boxed(lean_object* v_00_u03b1_2423_, lean_object* v_00_u03b2_2424_, lean_object* v_f_2425_, lean_object* v_init_2426_, lean_object* v_as_2427_, lean_object* v_start_2428_, lean_object* v_stop_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Array_foldl(v_00_u03b1_2423_, v_00_u03b2_2424_, v_f_2425_, v_init_2426_, v_as_2427_, v_start_2428_, v_stop_2429_);
lean_dec(v_stop_2429_);
lean_dec(v_start_2428_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg(lean_object* v_f_2431_, lean_object* v_init_2432_, lean_object* v_as_2433_, lean_object* v_start_2434_, lean_object* v_stop_2435_){
_start:
{
lean_object* v___f_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
v___f_2436_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2436_, 0, v_f_2431_);
v___x_2437_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2438_ = lean_array_get_size(v_as_2433_);
v___x_2439_ = lean_nat_dec_le(v_start_2434_, v___x_2438_);
if (v___x_2439_ == 0)
{
uint8_t v___x_2440_; 
v___x_2440_ = lean_nat_dec_lt(v_stop_2435_, v___x_2438_);
if (v___x_2440_ == 0)
{
lean_dec_ref(v___f_2436_);
lean_dec_ref(v_as_2433_);
return v_init_2432_;
}
else
{
size_t v___x_2441_; size_t v___x_2442_; lean_object* v___x_2443_; 
v___x_2441_ = lean_usize_of_nat(v___x_2438_);
v___x_2442_ = lean_usize_of_nat(v_stop_2435_);
v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2437_, v___f_2436_, v_as_2433_, v___x_2441_, v___x_2442_, v_init_2432_);
return v___x_2443_;
}
}
else
{
uint8_t v___x_2444_; 
v___x_2444_ = lean_nat_dec_lt(v_stop_2435_, v_start_2434_);
if (v___x_2444_ == 0)
{
lean_dec_ref(v___f_2436_);
lean_dec_ref(v_as_2433_);
return v_init_2432_;
}
else
{
size_t v___x_2445_; size_t v___x_2446_; lean_object* v___x_2447_; 
v___x_2445_ = lean_usize_of_nat(v_start_2434_);
v___x_2446_ = lean_usize_of_nat(v_stop_2435_);
v___x_2447_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2437_, v___f_2436_, v_as_2433_, v___x_2445_, v___x_2446_, v_init_2432_);
return v___x_2447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg___boxed(lean_object* v_f_2448_, lean_object* v_init_2449_, lean_object* v_as_2450_, lean_object* v_start_2451_, lean_object* v_stop_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Array_foldr___redArg(v_f_2448_, v_init_2449_, v_as_2450_, v_start_2451_, v_stop_2452_);
lean_dec(v_stop_2452_);
lean_dec(v_start_2451_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr(lean_object* v_00_u03b1_2454_, lean_object* v_00_u03b2_2455_, lean_object* v_f_2456_, lean_object* v_init_2457_, lean_object* v_as_2458_, lean_object* v_start_2459_, lean_object* v_stop_2460_){
_start:
{
lean_object* v___f_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___f_2461_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2461_, 0, v_f_2456_);
v___x_2462_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2463_ = lean_array_get_size(v_as_2458_);
v___x_2464_ = lean_nat_dec_le(v_start_2459_, v___x_2463_);
if (v___x_2464_ == 0)
{
uint8_t v___x_2465_; 
v___x_2465_ = lean_nat_dec_lt(v_stop_2460_, v___x_2463_);
if (v___x_2465_ == 0)
{
lean_dec_ref(v___f_2461_);
lean_dec_ref(v_as_2458_);
return v_init_2457_;
}
else
{
size_t v___x_2466_; size_t v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = lean_usize_of_nat(v___x_2463_);
v___x_2467_ = lean_usize_of_nat(v_stop_2460_);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2462_, v___f_2461_, v_as_2458_, v___x_2466_, v___x_2467_, v_init_2457_);
return v___x_2468_;
}
}
else
{
uint8_t v___x_2469_; 
v___x_2469_ = lean_nat_dec_lt(v_stop_2460_, v_start_2459_);
if (v___x_2469_ == 0)
{
lean_dec_ref(v___f_2461_);
lean_dec_ref(v_as_2458_);
return v_init_2457_;
}
else
{
size_t v___x_2470_; size_t v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = lean_usize_of_nat(v_start_2459_);
v___x_2471_ = lean_usize_of_nat(v_stop_2460_);
v___x_2472_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2462_, v___f_2461_, v_as_2458_, v___x_2470_, v___x_2471_, v_init_2457_);
return v___x_2472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___boxed(lean_object* v_00_u03b1_2473_, lean_object* v_00_u03b2_2474_, lean_object* v_f_2475_, lean_object* v_init_2476_, lean_object* v_as_2477_, lean_object* v_start_2478_, lean_object* v_stop_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Array_foldr(v_00_u03b1_2473_, v_00_u03b2_2474_, v_f_2475_, v_init_2476_, v_as_2477_, v_start_2478_, v_stop_2479_);
lean_dec(v_stop_2479_);
lean_dec(v_start_2478_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg___lam__0(lean_object* v_inst_2481_, lean_object* v_x1_2482_, lean_object* v_x2_2483_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_apply_2(v_inst_2481_, v_x1_2482_, v_x2_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg(lean_object* v_inst_2485_, lean_object* v_inst_2486_, lean_object* v_as_2487_){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; 
v___x_2488_ = lean_array_get_size(v_as_2487_);
v___x_2489_ = lean_unsigned_to_nat(0u);
v___x_2490_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2491_ = lean_nat_dec_lt(v___x_2489_, v___x_2488_);
if (v___x_2491_ == 0)
{
lean_dec_ref(v_as_2487_);
lean_dec(v_inst_2485_);
return v_inst_2486_;
}
else
{
lean_object* v___f_2492_; size_t v___x_2493_; size_t v___x_2494_; lean_object* v___x_2495_; 
v___f_2492_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2492_, 0, v_inst_2485_);
v___x_2493_ = lean_usize_of_nat(v___x_2488_);
v___x_2494_ = ((size_t)0ULL);
v___x_2495_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2490_, v___f_2492_, v_as_2487_, v___x_2493_, v___x_2494_, v_inst_2486_);
return v___x_2495_;
}
}
}
LEAN_EXPORT lean_object* l_Array_sum(lean_object* v_00_u03b1_2496_, lean_object* v_inst_2497_, lean_object* v_inst_2498_, lean_object* v_as_2499_){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v___x_2500_ = lean_array_get_size(v_as_2499_);
v___x_2501_ = lean_unsigned_to_nat(0u);
v___x_2502_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2503_ = lean_nat_dec_lt(v___x_2501_, v___x_2500_);
if (v___x_2503_ == 0)
{
lean_dec_ref(v_as_2499_);
lean_dec(v_inst_2497_);
return v_inst_2498_;
}
else
{
lean_object* v___f_2504_; size_t v___x_2505_; size_t v___x_2506_; lean_object* v___x_2507_; 
v___f_2504_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2504_, 0, v_inst_2497_);
v___x_2505_ = lean_usize_of_nat(v___x_2500_);
v___x_2506_ = ((size_t)0ULL);
v___x_2507_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2502_, v___f_2504_, v_as_2499_, v___x_2505_, v___x_2506_, v_inst_2498_);
return v___x_2507_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0(lean_object* v_p_2508_, lean_object* v_x1_2509_, lean_object* v_x2_2510_){
_start:
{
lean_object* v___x_2511_; uint8_t v___x_2512_; 
v___x_2511_ = lean_apply_1(v_p_2508_, v_x1_2509_);
v___x_2512_ = lean_unbox(v___x_2511_);
if (v___x_2512_ == 0)
{
lean_inc(v_x2_2510_);
return v_x2_2510_;
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = lean_unsigned_to_nat(1u);
v___x_2514_ = lean_nat_add(v_x2_2510_, v___x_2513_);
return v___x_2514_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0___boxed(lean_object* v_p_2515_, lean_object* v_x1_2516_, lean_object* v_x2_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Array_countP___redArg___lam__0(v_p_2515_, v_x1_2516_, v_x2_2517_);
lean_dec(v_x2_2517_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg(lean_object* v_p_2519_, lean_object* v_as_2520_){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2521_ = lean_unsigned_to_nat(0u);
v___x_2522_ = lean_array_get_size(v_as_2520_);
v___x_2523_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2524_ = lean_nat_dec_lt(v___x_2521_, v___x_2522_);
if (v___x_2524_ == 0)
{
lean_dec_ref(v_as_2520_);
lean_dec_ref(v_p_2519_);
return v___x_2521_;
}
else
{
lean_object* v___f_2525_; size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___f_2525_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2525_, 0, v_p_2519_);
v___x_2526_ = lean_usize_of_nat(v___x_2522_);
v___x_2527_ = ((size_t)0ULL);
v___x_2528_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2523_, v___f_2525_, v_as_2520_, v___x_2526_, v___x_2527_, v___x_2521_);
return v___x_2528_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP(lean_object* v_00_u03b1_2529_, lean_object* v_p_2530_, lean_object* v_as_2531_){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2532_ = lean_unsigned_to_nat(0u);
v___x_2533_ = lean_array_get_size(v_as_2531_);
v___x_2534_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2535_ = lean_nat_dec_lt(v___x_2532_, v___x_2533_);
if (v___x_2535_ == 0)
{
lean_dec_ref(v_as_2531_);
lean_dec_ref(v_p_2530_);
return v___x_2532_;
}
else
{
lean_object* v___f_2536_; size_t v___x_2537_; size_t v___x_2538_; lean_object* v___x_2539_; 
v___f_2536_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2536_, 0, v_p_2530_);
v___x_2537_ = lean_usize_of_nat(v___x_2533_);
v___x_2538_ = ((size_t)0ULL);
v___x_2539_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2534_, v___f_2536_, v_as_2531_, v___x_2537_, v___x_2538_, v___x_2532_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0(lean_object* v_inst_2540_, lean_object* v_a_2541_, lean_object* v_x1_2542_, lean_object* v_x2_2543_){
_start:
{
lean_object* v___x_2544_; uint8_t v___x_2545_; 
v___x_2544_ = lean_apply_2(v_inst_2540_, v_x1_2542_, v_a_2541_);
v___x_2545_ = lean_unbox(v___x_2544_);
if (v___x_2545_ == 0)
{
lean_inc(v_x2_2543_);
return v_x2_2543_;
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = lean_unsigned_to_nat(1u);
v___x_2547_ = lean_nat_add(v_x2_2543_, v___x_2546_);
return v___x_2547_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0___boxed(lean_object* v_inst_2548_, lean_object* v_a_2549_, lean_object* v_x1_2550_, lean_object* v_x2_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Array_count___redArg___lam__0(v_inst_2548_, v_a_2549_, v_x1_2550_, v_x2_2551_);
lean_dec(v_x2_2551_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg(lean_object* v_inst_2553_, lean_object* v_a_2554_, lean_object* v_as_2555_){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2556_ = lean_unsigned_to_nat(0u);
v___x_2557_ = lean_array_get_size(v_as_2555_);
v___x_2558_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2559_ = lean_nat_dec_lt(v___x_2556_, v___x_2557_);
if (v___x_2559_ == 0)
{
lean_dec_ref(v_as_2555_);
lean_dec(v_a_2554_);
lean_dec_ref(v_inst_2553_);
return v___x_2556_;
}
else
{
lean_object* v___f_2560_; size_t v___x_2561_; size_t v___x_2562_; lean_object* v___x_2563_; 
v___f_2560_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2560_, 0, v_inst_2553_);
lean_closure_set(v___f_2560_, 1, v_a_2554_);
v___x_2561_ = lean_usize_of_nat(v___x_2557_);
v___x_2562_ = ((size_t)0ULL);
v___x_2563_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2558_, v___f_2560_, v_as_2555_, v___x_2561_, v___x_2562_, v___x_2556_);
return v___x_2563_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count(lean_object* v_00_u03b1_2564_, lean_object* v_inst_2565_, lean_object* v_a_2566_, lean_object* v_as_2567_){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2568_ = lean_unsigned_to_nat(0u);
v___x_2569_ = lean_array_get_size(v_as_2567_);
v___x_2570_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2571_ = lean_nat_dec_lt(v___x_2568_, v___x_2569_);
if (v___x_2571_ == 0)
{
lean_dec_ref(v_as_2567_);
lean_dec(v_a_2566_);
lean_dec_ref(v_inst_2565_);
return v___x_2568_;
}
else
{
lean_object* v___f_2572_; size_t v___x_2573_; size_t v___x_2574_; lean_object* v___x_2575_; 
v___f_2572_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2572_, 0, v_inst_2565_);
lean_closure_set(v___f_2572_, 1, v_a_2566_);
v___x_2573_ = lean_usize_of_nat(v___x_2569_);
v___x_2574_ = ((size_t)0ULL);
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2570_, v___f_2572_, v_as_2567_, v___x_2573_, v___x_2574_, v___x_2568_);
return v___x_2575_;
}
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg___lam__0(lean_object* v_f_2576_, lean_object* v_x_2577_){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = lean_apply_1(v_f_2576_, v_x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg(lean_object* v_f_2579_, lean_object* v_as_2580_){
_start:
{
lean_object* v___f_2581_; lean_object* v___x_2582_; size_t v_sz_2583_; size_t v___x_2584_; lean_object* v___x_2585_; 
v___f_2581_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2581_, 0, v_f_2579_);
v___x_2582_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2583_ = lean_array_size(v_as_2580_);
v___x_2584_ = ((size_t)0ULL);
v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2582_, v___f_2581_, v_sz_2583_, v___x_2584_, v_as_2580_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Array_map(lean_object* v_00_u03b1_2586_, lean_object* v_00_u03b2_2587_, lean_object* v_f_2588_, lean_object* v_as_2589_){
_start:
{
lean_object* v___f_2590_; lean_object* v___x_2591_; size_t v_sz_2592_; size_t v___x_2593_; lean_object* v___x_2594_; 
v___f_2590_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2590_, 0, v_f_2588_);
v___x_2591_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2592_ = lean_array_size(v_as_2589_);
v___x_2593_ = ((size_t)0ULL);
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2591_, v___f_2590_, v_sz_2592_, v___x_2593_, v_as_2589_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0(lean_object* v___y_2595_, lean_object* v_x_2596_){
_start:
{
lean_inc(v___y_2595_);
return v___y_2595_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0___boxed(lean_object* v___y_2597_, lean_object* v_x_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Array_instFunctor___lam__0(v___y_2597_, v_x_2598_);
lean_dec(v_x_2598_);
lean_dec(v___y_2597_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__1(lean_object* v_00_u03b1_2600_, lean_object* v_00_u03b2_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v___f_2604_; lean_object* v___x_2605_; size_t v_sz_2606_; size_t v___x_2607_; lean_object* v___x_2608_; 
v___f_2604_ = lean_alloc_closure((void*)(l_Array_instFunctor___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2604_, 0, v___y_2602_);
v___x_2605_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2606_ = lean_array_size(v___y_2603_);
v___x_2607_ = ((size_t)0ULL);
v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2605_, v___f_2604_, v_sz_2606_, v___x_2607_, v___y_2603_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg___lam__0(lean_object* v_f_2615_, lean_object* v_x1_2616_, lean_object* v_x2_2617_, lean_object* v_x3_2618_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = lean_apply_3(v_f_2615_, v_x1_2616_, v_x2_2617_, lean_box(0));
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg(lean_object* v_as_2620_, lean_object* v_f_2621_){
_start:
{
lean_object* v___f_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___f_2622_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2622_, 0, v_f_2621_);
v___x_2623_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2624_ = lean_array_get_size(v_as_2620_);
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = lean_mk_empty_array_with_capacity(v___x_2624_);
v___x_2627_ = l_Array_mapFinIdxM_map___redArg(v___x_2623_, v_as_2620_, v___f_2622_, v___x_2624_, v___x_2625_, v___x_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx(lean_object* v_00_u03b1_2628_, lean_object* v_00_u03b2_2629_, lean_object* v_as_2630_, lean_object* v_f_2631_){
_start:
{
lean_object* v___f_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___f_2632_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2632_, 0, v_f_2631_);
v___x_2633_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2634_ = lean_array_get_size(v_as_2630_);
v___x_2635_ = lean_unsigned_to_nat(0u);
v___x_2636_ = lean_mk_empty_array_with_capacity(v___x_2634_);
v___x_2637_ = l_Array_mapFinIdxM_map___redArg(v___x_2633_, v_as_2630_, v___f_2632_, v___x_2634_, v___x_2635_, v___x_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx___redArg(lean_object* v_f_2638_, lean_object* v_as_2639_){
_start:
{
lean_object* v___f_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___f_2640_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2640_, 0, v_f_2638_);
v___x_2641_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2642_ = lean_array_get_size(v_as_2639_);
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = lean_mk_empty_array_with_capacity(v___x_2642_);
v___x_2645_ = l_Array_mapFinIdxM_map___redArg(v___x_2641_, v_as_2639_, v___f_2640_, v___x_2642_, v___x_2643_, v___x_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx(lean_object* v_00_u03b1_2646_, lean_object* v_00_u03b2_2647_, lean_object* v_f_2648_, lean_object* v_as_2649_){
_start:
{
lean_object* v___f_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___f_2650_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2650_, 0, v_f_2648_);
v___x_2651_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2652_ = lean_array_get_size(v_as_2649_);
v___x_2653_ = lean_unsigned_to_nat(0u);
v___x_2654_ = lean_mk_empty_array_with_capacity(v___x_2652_);
v___x_2655_ = l_Array_mapFinIdxM_map___redArg(v___x_2651_, v_as_2649_, v___f_2650_, v___x_2652_, v___x_2653_, v___x_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(lean_object* v_start_2656_, lean_object* v_as_2657_, lean_object* v_i_2658_, lean_object* v_j_2659_, lean_object* v_bs_2660_){
_start:
{
lean_object* v_zero_2661_; uint8_t v_isZero_2662_; 
v_zero_2661_ = lean_unsigned_to_nat(0u);
v_isZero_2662_ = lean_nat_dec_eq(v_i_2658_, v_zero_2661_);
if (v_isZero_2662_ == 1)
{
lean_dec(v_j_2659_);
lean_dec(v_i_2658_);
return v_bs_2660_;
}
else
{
lean_object* v_one_2663_; lean_object* v_n_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v_one_2663_ = lean_unsigned_to_nat(1u);
v_n_2664_ = lean_nat_sub(v_i_2658_, v_one_2663_);
lean_dec(v_i_2658_);
v___x_2665_ = lean_array_fget_borrowed(v_as_2657_, v_j_2659_);
v___x_2666_ = lean_nat_add(v_start_2656_, v_j_2659_);
lean_inc(v___x_2665_);
v___x_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2665_);
lean_ctor_set(v___x_2667_, 1, v___x_2666_);
v___x_2668_ = lean_nat_add(v_j_2659_, v_one_2663_);
lean_dec(v_j_2659_);
v___x_2669_ = lean_array_push(v_bs_2660_, v___x_2667_);
v_i_2658_ = v_n_2664_;
v_j_2659_ = v___x_2668_;
v_bs_2660_ = v___x_2669_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg___boxed(lean_object* v_start_2671_, lean_object* v_as_2672_, lean_object* v_i_2673_, lean_object* v_j_2674_, lean_object* v_bs_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(v_start_2671_, v_as_2672_, v_i_2673_, v_j_2674_, v_bs_2675_);
lean_dec_ref(v_as_2672_);
lean_dec(v_start_2671_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg(lean_object* v_xs_2677_, lean_object* v_start_2678_){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2679_ = lean_array_get_size(v_xs_2677_);
v___x_2680_ = lean_unsigned_to_nat(0u);
v___x_2681_ = lean_mk_empty_array_with_capacity(v___x_2679_);
v___x_2682_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(v_start_2678_, v_xs_2677_, v___x_2679_, v___x_2680_, v___x_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg___boxed(lean_object* v_xs_2683_, lean_object* v_start_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Array_zipIdx___redArg(v_xs_2683_, v_start_2684_);
lean_dec(v_start_2684_);
lean_dec_ref(v_xs_2683_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx(lean_object* v_00_u03b1_2686_, lean_object* v_xs_2687_, lean_object* v_start_2688_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Array_zipIdx___redArg(v_xs_2687_, v_start_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___boxed(lean_object* v_00_u03b1_2690_, lean_object* v_xs_2691_, lean_object* v_start_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Array_zipIdx(v_00_u03b1_2690_, v_xs_2691_, v_start_2692_);
lean_dec(v_start_2692_);
lean_dec_ref(v_xs_2691_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0(lean_object* v_00_u03b1_2694_, lean_object* v_start_2695_, lean_object* v_as_2696_, lean_object* v_i_2697_, lean_object* v_j_2698_, lean_object* v_inv_2699_, lean_object* v_bs_2700_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(v_start_2695_, v_as_2696_, v_i_2697_, v_j_2698_, v_bs_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___boxed(lean_object* v_00_u03b1_2702_, lean_object* v_start_2703_, lean_object* v_as_2704_, lean_object* v_i_2705_, lean_object* v_j_2706_, lean_object* v_inv_2707_, lean_object* v_bs_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0(v_00_u03b1_2702_, v_start_2703_, v_as_2704_, v_i_2705_, v_j_2706_, v_inv_2707_, v_bs_2708_);
lean_dec_ref(v_as_2704_);
lean_dec(v_start_2703_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0(lean_object* v_p_2710_, lean_object* v___x_2711_, lean_object* v___x_2712_, lean_object* v_a_2713_, lean_object* v_x_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2716_; uint8_t v___x_2717_; 
lean_inc(v_a_2713_);
v___x_2716_ = lean_apply_1(v_p_2710_, v_a_2713_);
v___x_2717_ = lean_unbox(v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; 
lean_dec(v_a_2713_);
v___x_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2711_);
return v___x_2718_;
}
else
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
lean_dec_ref(v___x_2711_);
v___x_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2719_, 0, v_a_2713_);
v___x_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
lean_ctor_set(v___x_2721_, 1, v___x_2712_);
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0___boxed(lean_object* v_p_2723_, lean_object* v___x_2724_, lean_object* v___x_2725_, lean_object* v_a_2726_, lean_object* v_x_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Array_find_x3f___redArg___lam__0(v_p_2723_, v___x_2724_, v___x_2725_, v_a_2726_, v_x_2727_, v___y_2728_);
lean_dec_ref(v___y_2728_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg(lean_object* v_p_2730_, lean_object* v_as_2731_){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___f_2736_; size_t v_sz_2737_; size_t v___x_2738_; lean_object* v___x_2739_; lean_object* v_fst_2740_; 
v___x_2732_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2733_ = lean_box(0);
v___x_2734_ = lean_box(0);
v___x_2735_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2736_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2736_, 0, v_p_2730_);
lean_closure_set(v___f_2736_, 1, v___x_2735_);
lean_closure_set(v___f_2736_, 2, v___x_2734_);
v_sz_2737_ = lean_array_size(v_as_2731_);
v___x_2738_ = ((size_t)0ULL);
v___x_2739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2732_, v_as_2731_, v___f_2736_, v_sz_2737_, v___x_2738_, v___x_2735_);
v_fst_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_fst_2740_);
lean_dec(v___x_2739_);
if (lean_obj_tag(v_fst_2740_) == 0)
{
return v___x_2733_;
}
else
{
lean_object* v_val_2741_; 
v_val_2741_ = lean_ctor_get(v_fst_2740_, 0);
lean_inc(v_val_2741_);
lean_dec_ref(v_fst_2740_);
return v_val_2741_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f(lean_object* v_00_u03b1_2742_, lean_object* v_p_2743_, lean_object* v_as_2744_){
_start:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___f_2749_; size_t v_sz_2750_; size_t v___x_2751_; lean_object* v___x_2752_; lean_object* v_fst_2753_; 
v___x_2745_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2746_ = lean_box(0);
v___x_2747_ = lean_box(0);
v___x_2748_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2749_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2749_, 0, v_p_2743_);
lean_closure_set(v___f_2749_, 1, v___x_2748_);
lean_closure_set(v___f_2749_, 2, v___x_2747_);
v_sz_2750_ = lean_array_size(v_as_2744_);
v___x_2751_ = ((size_t)0ULL);
v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2745_, v_as_2744_, v___f_2749_, v_sz_2750_, v___x_2751_, v___x_2748_);
v_fst_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_fst_2753_);
lean_dec(v___x_2752_);
if (lean_obj_tag(v_fst_2753_) == 0)
{
return v___x_2746_;
}
else
{
lean_object* v_val_2754_; 
v_val_2754_ = lean_ctor_get(v_fst_2753_, 0);
lean_inc(v_val_2754_);
lean_dec_ref(v_fst_2753_);
return v_val_2754_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0(lean_object* v_f_2755_, lean_object* v___x_2756_, lean_object* v___x_2757_, lean_object* v_a_2758_, lean_object* v_x_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_apply_1(v_f_2755_, v_a_2758_);
if (lean_obj_tag(v___x_2761_) == 1)
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_dec_ref(v___x_2757_);
v___x_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
v___x_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
lean_ctor_set(v___x_2763_, 1, v___x_2756_);
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
return v___x_2764_;
}
else
{
lean_object* v___x_2765_; 
lean_dec(v___x_2761_);
v___x_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2757_);
return v___x_2765_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2766_, lean_object* v___x_2767_, lean_object* v___x_2768_, lean_object* v_a_2769_, lean_object* v_x_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Array_findSome_x3f___redArg___lam__0(v_f_2766_, v___x_2767_, v___x_2768_, v_a_2769_, v_x_2770_, v___y_2771_);
lean_dec_ref(v___y_2771_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg(lean_object* v_f_2773_, lean_object* v_as_2774_){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___f_2779_; size_t v_sz_2780_; size_t v___x_2781_; lean_object* v___x_2782_; lean_object* v_fst_2783_; 
v___x_2775_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2776_ = lean_box(0);
v___x_2777_ = lean_box(0);
v___x_2778_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2779_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2779_, 0, v_f_2773_);
lean_closure_set(v___f_2779_, 1, v___x_2777_);
lean_closure_set(v___f_2779_, 2, v___x_2778_);
v_sz_2780_ = lean_array_size(v_as_2774_);
v___x_2781_ = ((size_t)0ULL);
v___x_2782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2775_, v_as_2774_, v___f_2779_, v_sz_2780_, v___x_2781_, v___x_2778_);
v_fst_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_fst_2783_);
lean_dec(v___x_2782_);
if (lean_obj_tag(v_fst_2783_) == 0)
{
return v___x_2776_;
}
else
{
lean_object* v_val_2784_; 
v_val_2784_ = lean_ctor_get(v_fst_2783_, 0);
lean_inc(v_val_2784_);
lean_dec_ref(v_fst_2783_);
return v_val_2784_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f(lean_object* v_00_u03b1_2785_, lean_object* v_00_u03b2_2786_, lean_object* v_f_2787_, lean_object* v_as_2788_){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___f_2793_; size_t v_sz_2794_; size_t v___x_2795_; lean_object* v___x_2796_; lean_object* v_fst_2797_; 
v___x_2789_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2790_ = lean_box(0);
v___x_2791_ = lean_box(0);
v___x_2792_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2793_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2793_, 0, v_f_2787_);
lean_closure_set(v___f_2793_, 1, v___x_2791_);
lean_closure_set(v___f_2793_, 2, v___x_2792_);
v_sz_2794_ = lean_array_size(v_as_2788_);
v___x_2795_ = ((size_t)0ULL);
v___x_2796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2789_, v_as_2788_, v___f_2793_, v_sz_2794_, v___x_2795_, v___x_2792_);
v_fst_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_fst_2797_);
lean_dec(v___x_2796_);
if (lean_obj_tag(v_fst_2797_) == 0)
{
return v___x_2790_;
}
else
{
lean_object* v_val_2798_; 
v_val_2798_ = lean_ctor_get(v_fst_2797_, 0);
lean_inc(v_val_2798_);
lean_dec_ref(v_fst_2797_);
return v_val_2798_;
}
}
}
static lean_object* _init_l_Array_findSome_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2801_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__1));
v___x_2802_ = lean_unsigned_to_nat(14u);
v___x_2803_ = lean_unsigned_to_nat(1220u);
v___x_2804_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__0));
v___x_2805_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_2806_ = l_mkPanicMessageWithDecl(v___x_2805_, v___x_2804_, v___x_2803_, v___x_2802_, v___x_2801_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg(lean_object* v_inst_2807_, lean_object* v_f_2808_, lean_object* v_xs_2809_){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___f_2816_; size_t v_sz_2817_; size_t v___x_2818_; lean_object* v___x_2819_; lean_object* v_fst_2820_; 
v___x_2813_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2814_ = lean_box(0);
v___x_2815_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2816_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2816_, 0, v_f_2808_);
lean_closure_set(v___f_2816_, 1, v___x_2814_);
lean_closure_set(v___f_2816_, 2, v___x_2815_);
v_sz_2817_ = lean_array_size(v_xs_2809_);
v___x_2818_ = ((size_t)0ULL);
v___x_2819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2813_, v_xs_2809_, v___f_2816_, v_sz_2817_, v___x_2818_, v___x_2815_);
v_fst_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_fst_2820_);
lean_dec(v___x_2819_);
if (lean_obj_tag(v_fst_2820_) == 0)
{
goto v___jp_2810_;
}
else
{
lean_object* v_val_2821_; 
v_val_2821_ = lean_ctor_get(v_fst_2820_, 0);
lean_inc(v_val_2821_);
lean_dec_ref(v_fst_2820_);
if (lean_obj_tag(v_val_2821_) == 0)
{
goto v___jp_2810_;
}
else
{
lean_object* v_val_2822_; 
v_val_2822_ = lean_ctor_get(v_val_2821_, 0);
lean_inc(v_val_2822_);
lean_dec_ref(v_val_2821_);
return v_val_2822_;
}
}
v___jp_2810_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2812_ = l_panic___redArg(v_inst_2807_, v___x_2811_);
return v___x_2812_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg___boxed(lean_object* v_inst_2823_, lean_object* v_f_2824_, lean_object* v_xs_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_Array_findSome_x21___redArg(v_inst_2823_, v_f_2824_, v_xs_2825_);
lean_dec(v_inst_2823_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21(lean_object* v_00_u03b1_2827_, lean_object* v_00_u03b2_2828_, lean_object* v_inst_2829_, lean_object* v_f_2830_, lean_object* v_xs_2831_){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___f_2838_; size_t v_sz_2839_; size_t v___x_2840_; lean_object* v___x_2841_; lean_object* v_fst_2842_; 
v___x_2835_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2836_ = lean_box(0);
v___x_2837_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2838_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2838_, 0, v_f_2830_);
lean_closure_set(v___f_2838_, 1, v___x_2836_);
lean_closure_set(v___f_2838_, 2, v___x_2837_);
v_sz_2839_ = lean_array_size(v_xs_2831_);
v___x_2840_ = ((size_t)0ULL);
v___x_2841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2835_, v_xs_2831_, v___f_2838_, v_sz_2839_, v___x_2840_, v___x_2837_);
v_fst_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_fst_2842_);
lean_dec(v___x_2841_);
if (lean_obj_tag(v_fst_2842_) == 0)
{
goto v___jp_2832_;
}
else
{
lean_object* v_val_2843_; 
v_val_2843_ = lean_ctor_get(v_fst_2842_, 0);
lean_inc(v_val_2843_);
lean_dec_ref(v_fst_2842_);
if (lean_obj_tag(v_val_2843_) == 0)
{
goto v___jp_2832_;
}
else
{
lean_object* v_val_2844_; 
v_val_2844_ = lean_ctor_get(v_val_2843_, 0);
lean_inc(v_val_2844_);
lean_dec_ref(v_val_2843_);
return v_val_2844_;
}
}
v___jp_2832_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2834_ = l_panic___redArg(v_inst_2829_, v___x_2833_);
return v___x_2834_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___boxed(lean_object* v_00_u03b1_2845_, lean_object* v_00_u03b2_2846_, lean_object* v_inst_2847_, lean_object* v_f_2848_, lean_object* v_xs_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Array_findSome_x21(v_00_u03b1_2845_, v_00_u03b2_2846_, v_inst_2847_, v_f_2848_, v_xs_2849_);
lean_dec(v_inst_2847_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2851_, lean_object* v_x_2852_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = lean_apply_1(v_f_2851_, v_x_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg(lean_object* v_f_2854_, lean_object* v_as_2855_){
_start:
{
lean_object* v___f_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___f_2856_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2856_, 0, v_f_2854_);
v___x_2857_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2858_ = lean_array_get_size(v_as_2855_);
v___x_2859_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2857_, v___f_2856_, v_as_2855_, v___x_2858_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f(lean_object* v_00_u03b1_2860_, lean_object* v_00_u03b2_2861_, lean_object* v_f_2862_, lean_object* v_as_2863_){
_start:
{
lean_object* v___f_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___f_2864_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2864_, 0, v_f_2862_);
v___x_2865_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2866_ = lean_array_get_size(v_as_2863_);
v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2865_, v___f_2864_, v_as_2863_, v___x_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg___lam__0(lean_object* v_p_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v___x_2870_; uint8_t v___x_2871_; 
lean_inc(v_a_2869_);
v___x_2870_ = lean_apply_1(v_p_2868_, v_a_2869_);
v___x_2871_ = lean_unbox(v___x_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; 
lean_dec(v_a_2869_);
v___x_2872_ = lean_box(0);
return v___x_2872_;
}
else
{
lean_object* v___x_2873_; 
v___x_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2873_, 0, v_a_2869_);
return v___x_2873_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg(lean_object* v_p_2874_, lean_object* v_as_2875_){
_start:
{
lean_object* v___f_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___f_2876_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2876_, 0, v_p_2874_);
v___x_2877_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2878_ = lean_array_get_size(v_as_2875_);
v___x_2879_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2877_, v___f_2876_, v_as_2875_, v___x_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f(lean_object* v_00_u03b1_2880_, lean_object* v_p_2881_, lean_object* v_as_2882_){
_start:
{
lean_object* v___f_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___f_2883_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2883_, 0, v_p_2881_);
v___x_2884_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2885_ = lean_array_get_size(v_as_2882_);
v___x_2886_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2884_, v___f_2883_, v_as_2882_, v___x_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object* v_p_2887_, lean_object* v_as_2888_, lean_object* v_j_2889_){
_start:
{
lean_object* v___x_2890_; uint8_t v___x_2891_; 
v___x_2890_ = lean_array_get_size(v_as_2888_);
v___x_2891_ = lean_nat_dec_lt(v_j_2889_, v___x_2890_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; 
lean_dec(v_j_2889_);
lean_dec_ref(v_p_2887_);
v___x_2892_ = lean_box(0);
return v___x_2892_;
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; 
v___x_2893_ = lean_array_fget_borrowed(v_as_2888_, v_j_2889_);
lean_inc_ref(v_p_2887_);
lean_inc(v___x_2893_);
v___x_2894_ = lean_apply_1(v_p_2887_, v___x_2893_);
v___x_2895_ = lean_unbox(v___x_2894_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_unsigned_to_nat(1u);
v___x_2897_ = lean_nat_add(v_j_2889_, v___x_2896_);
lean_dec(v_j_2889_);
v_j_2889_ = v___x_2897_;
goto _start;
}
else
{
lean_object* v___x_2899_; 
lean_dec_ref(v_p_2887_);
v___x_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2899_, 0, v_j_2889_);
return v___x_2899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg___boxed(lean_object* v_p_2900_, lean_object* v_as_2901_, lean_object* v_j_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Array_findIdx_x3f_loop___redArg(v_p_2900_, v_as_2901_, v_j_2902_);
lean_dec_ref(v_as_2901_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop(lean_object* v_00_u03b1_2904_, lean_object* v_p_2905_, lean_object* v_as_2906_, lean_object* v_j_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Array_findIdx_x3f_loop___redArg(v_p_2905_, v_as_2906_, v_j_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___boxed(lean_object* v_00_u03b1_2909_, lean_object* v_p_2910_, lean_object* v_as_2911_, lean_object* v_j_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Array_findIdx_x3f_loop(v_00_u03b1_2909_, v_p_2910_, v_as_2911_, v_j_2912_);
lean_dec_ref(v_as_2911_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg(lean_object* v_p_2914_, lean_object* v_as_2915_){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_unsigned_to_nat(0u);
v___x_2917_ = l_Array_findIdx_x3f_loop___redArg(v_p_2914_, v_as_2915_, v___x_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg___boxed(lean_object* v_p_2918_, lean_object* v_as_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Array_findIdx_x3f___redArg(v_p_2918_, v_as_2919_);
lean_dec_ref(v_as_2919_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f(lean_object* v_00_u03b1_2921_, lean_object* v_p_2922_, lean_object* v_as_2923_){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = lean_unsigned_to_nat(0u);
v___x_2925_ = l_Array_findIdx_x3f_loop___redArg(v_p_2922_, v_as_2923_, v___x_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___boxed(lean_object* v_00_u03b1_2926_, lean_object* v_p_2927_, lean_object* v_as_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Array_findIdx_x3f(v_00_u03b1_2926_, v_p_2927_, v_as_2928_);
lean_dec_ref(v_as_2928_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(lean_object* v_p_2930_, lean_object* v_as_2931_, lean_object* v_j_2932_){
_start:
{
lean_object* v___x_2933_; uint8_t v___x_2934_; 
v___x_2933_ = lean_array_get_size(v_as_2931_);
v___x_2934_ = lean_nat_dec_lt(v_j_2932_, v___x_2933_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; 
lean_dec(v_j_2932_);
lean_dec_ref(v_p_2930_);
v___x_2935_ = lean_box(0);
return v___x_2935_;
}
else
{
lean_object* v___x_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v___x_2936_ = lean_array_fget_borrowed(v_as_2931_, v_j_2932_);
lean_inc_ref(v_p_2930_);
lean_inc(v___x_2936_);
v___x_2937_ = lean_apply_1(v_p_2930_, v___x_2936_);
v___x_2938_ = lean_unbox(v___x_2937_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = lean_unsigned_to_nat(1u);
v___x_2940_ = lean_nat_add(v_j_2932_, v___x_2939_);
lean_dec(v_j_2932_);
v_j_2932_ = v___x_2940_;
goto _start;
}
else
{
lean_object* v___x_2942_; 
lean_dec_ref(v_p_2930_);
v___x_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_j_2932_);
return v___x_2942_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg___boxed(lean_object* v_p_2943_, lean_object* v_as_2944_, lean_object* v_j_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2943_, v_as_2944_, v_j_2945_);
lean_dec_ref(v_as_2944_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object* v_00_u03b1_2947_, lean_object* v_p_2948_, lean_object* v_as_2949_, lean_object* v_j_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2948_, v_as_2949_, v_j_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___boxed(lean_object* v_00_u03b1_2952_, lean_object* v_p_2953_, lean_object* v_as_2954_, lean_object* v_j_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(v_00_u03b1_2952_, v_p_2953_, v_as_2954_, v_j_2955_);
lean_dec_ref(v_as_2954_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg(lean_object* v_p_2957_, lean_object* v_as_2958_){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = lean_unsigned_to_nat(0u);
v___x_2960_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2957_, v_as_2958_, v___x_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg___boxed(lean_object* v_p_2961_, lean_object* v_as_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Array_findFinIdx_x3f___redArg(v_p_2961_, v_as_2962_);
lean_dec_ref(v_as_2962_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f(lean_object* v_00_u03b1_2964_, lean_object* v_p_2965_, lean_object* v_as_2966_){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = lean_unsigned_to_nat(0u);
v___x_2968_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2965_, v_as_2966_, v___x_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_2969_, lean_object* v_p_2970_, lean_object* v_as_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Array_findFinIdx_x3f(v_00_u03b1_2969_, v_p_2970_, v_as_2971_);
lean_dec_ref(v_as_2971_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg(lean_object* v_p_2973_, lean_object* v_as_2974_){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = lean_unsigned_to_nat(0u);
v___x_2976_ = l_Array_findIdx_x3f_loop___redArg(v_p_2973_, v_as_2974_, v___x_2975_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_array_get_size(v_as_2974_);
return v___x_2977_;
}
else
{
lean_object* v_val_2978_; 
v_val_2978_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_val_2978_);
lean_dec_ref(v___x_2976_);
return v_val_2978_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg___boxed(lean_object* v_p_2979_, lean_object* v_as_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Array_findIdx___redArg(v_p_2979_, v_as_2980_);
lean_dec_ref(v_as_2980_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx(lean_object* v_00_u03b1_2982_, lean_object* v_p_2983_, lean_object* v_as_2984_){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = lean_unsigned_to_nat(0u);
v___x_2986_ = l_Array_findIdx_x3f_loop___redArg(v_p_2983_, v_as_2984_, v___x_2985_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_array_get_size(v_as_2984_);
return v___x_2987_;
}
else
{
lean_object* v_val_2988_; 
v_val_2988_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_val_2988_);
lean_dec_ref(v___x_2986_);
return v_val_2988_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___boxed(lean_object* v_00_u03b1_2989_, lean_object* v_p_2990_, lean_object* v_as_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Array_findIdx(v_00_u03b1_2989_, v_p_2990_, v_as_2991_);
lean_dec_ref(v_as_2991_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg(lean_object* v_inst_2993_, lean_object* v_xs_2994_, lean_object* v_v_2995_, lean_object* v_i_2996_){
_start:
{
lean_object* v___x_2997_; uint8_t v___x_2998_; 
v___x_2997_ = lean_array_get_size(v_xs_2994_);
v___x_2998_ = lean_nat_dec_lt(v_i_2996_, v___x_2997_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; 
lean_dec(v_i_2996_);
lean_dec(v_v_2995_);
lean_dec_ref(v_inst_2993_);
v___x_2999_ = lean_box(0);
return v___x_2999_;
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3001_; uint8_t v___x_3002_; 
v___x_3000_ = lean_array_fget_borrowed(v_xs_2994_, v_i_2996_);
lean_inc_ref(v_inst_2993_);
lean_inc(v_v_2995_);
lean_inc(v___x_3000_);
v___x_3001_ = lean_apply_2(v_inst_2993_, v___x_3000_, v_v_2995_);
v___x_3002_ = lean_unbox(v___x_3001_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = lean_unsigned_to_nat(1u);
v___x_3004_ = lean_nat_add(v_i_2996_, v___x_3003_);
lean_dec(v_i_2996_);
v_i_2996_ = v___x_3004_;
goto _start;
}
else
{
lean_object* v___x_3006_; 
lean_dec(v_v_2995_);
lean_dec_ref(v_inst_2993_);
v___x_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3006_, 0, v_i_2996_);
return v___x_3006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg___boxed(lean_object* v_inst_3007_, lean_object* v_xs_3008_, lean_object* v_v_3009_, lean_object* v_i_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Array_idxOfAux___redArg(v_inst_3007_, v_xs_3008_, v_v_3009_, v_i_3010_);
lean_dec_ref(v_xs_3008_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux(lean_object* v_00_u03b1_3012_, lean_object* v_inst_3013_, lean_object* v_xs_3014_, lean_object* v_v_3015_, lean_object* v_i_3016_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Array_idxOfAux___redArg(v_inst_3013_, v_xs_3014_, v_v_3015_, v_i_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___boxed(lean_object* v_00_u03b1_3018_, lean_object* v_inst_3019_, lean_object* v_xs_3020_, lean_object* v_v_3021_, lean_object* v_i_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Array_idxOfAux(v_00_u03b1_3018_, v_inst_3019_, v_xs_3020_, v_v_3021_, v_i_3022_);
lean_dec_ref(v_xs_3020_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg(lean_object* v_inst_3024_, lean_object* v_xs_3025_, lean_object* v_v_3026_){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = lean_unsigned_to_nat(0u);
v___x_3028_ = l_Array_idxOfAux___redArg(v_inst_3024_, v_xs_3025_, v_v_3026_, v___x_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_3029_, lean_object* v_xs_3030_, lean_object* v_v_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Array_finIdxOf_x3f___redArg(v_inst_3029_, v_xs_3030_, v_v_3031_);
lean_dec_ref(v_xs_3030_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f(lean_object* v_00_u03b1_3033_, lean_object* v_inst_3034_, lean_object* v_xs_3035_, lean_object* v_v_3036_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Array_finIdxOf_x3f___redArg(v_inst_3034_, v_xs_3035_, v_v_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_3038_, lean_object* v_inst_3039_, lean_object* v_xs_3040_, lean_object* v_v_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Array_finIdxOf_x3f(v_00_u03b1_3038_, v_inst_3039_, v_xs_3040_, v_v_3041_);
lean_dec_ref(v_xs_3040_);
return v_res_3042_;
}
}
LEAN_EXPORT uint8_t l_Array_idxOf___redArg___lam__0(lean_object* v_inst_3043_, lean_object* v_a_3044_, lean_object* v_x_3045_){
_start:
{
lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3046_ = lean_apply_2(v_inst_3043_, v_x_3045_, v_a_3044_);
v___x_3047_ = lean_unbox(v___x_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___lam__0___boxed(lean_object* v_inst_3048_, lean_object* v_a_3049_, lean_object* v_x_3050_){
_start:
{
uint8_t v_res_3051_; lean_object* v_r_3052_; 
v_res_3051_ = l_Array_idxOf___redArg___lam__0(v_inst_3048_, v_a_3049_, v_x_3050_);
v_r_3052_ = lean_box(v_res_3051_);
return v_r_3052_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg(lean_object* v_inst_3053_, lean_object* v_a_3054_, lean_object* v_as_3055_){
_start:
{
lean_object* v___f_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___f_3056_ = lean_alloc_closure((void*)(l_Array_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3056_, 0, v_inst_3053_);
lean_closure_set(v___f_3056_, 1, v_a_3054_);
v___x_3057_ = lean_unsigned_to_nat(0u);
v___x_3058_ = l_Array_findIdx_x3f_loop___redArg(v___f_3056_, v_as_3055_, v___x_3057_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_array_get_size(v_as_3055_);
return v___x_3059_;
}
else
{
lean_object* v_val_3060_; 
v_val_3060_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_val_3060_);
lean_dec_ref(v___x_3058_);
return v_val_3060_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___boxed(lean_object* v_inst_3061_, lean_object* v_a_3062_, lean_object* v_as_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Array_idxOf___redArg(v_inst_3061_, v_a_3062_, v_as_3063_);
lean_dec_ref(v_as_3063_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf(lean_object* v_00_u03b1_3065_, lean_object* v_inst_3066_, lean_object* v_a_3067_, lean_object* v_as_3068_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Array_idxOf___redArg(v_inst_3066_, v_a_3067_, v_as_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___boxed(lean_object* v_00_u03b1_3070_, lean_object* v_inst_3071_, lean_object* v_a_3072_, lean_object* v_as_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Array_idxOf(v_00_u03b1_3070_, v_inst_3071_, v_a_3072_, v_as_3073_);
lean_dec_ref(v_as_3073_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg(lean_object* v_inst_3075_, lean_object* v_xs_3076_, lean_object* v_v_3077_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l_Array_finIdxOf_x3f___redArg(v_inst_3075_, v_xs_3076_, v_v_3077_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v___x_3079_; 
v___x_3079_ = lean_box(0);
return v___x_3079_;
}
else
{
lean_object* v_val_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
v_val_3080_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3078_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_val_3080_);
lean_dec(v___x_3078_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_val_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg___boxed(lean_object* v_inst_3088_, lean_object* v_xs_3089_, lean_object* v_v_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Array_idxOf_x3f___redArg(v_inst_3088_, v_xs_3089_, v_v_3090_);
lean_dec_ref(v_xs_3089_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f(lean_object* v_00_u03b1_3092_, lean_object* v_inst_3093_, lean_object* v_xs_3094_, lean_object* v_v_3095_){
_start:
{
lean_object* v___x_3096_; 
v___x_3096_ = l_Array_idxOf_x3f___redArg(v_inst_3093_, v_xs_3094_, v_v_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___boxed(lean_object* v_00_u03b1_3097_, lean_object* v_inst_3098_, lean_object* v_xs_3099_, lean_object* v_v_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Array_idxOf_x3f(v_00_u03b1_3097_, v_inst_3098_, v_xs_3099_, v_v_3100_);
lean_dec_ref(v_xs_3099_);
return v_res_3101_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg___lam__0(lean_object* v_p_3102_, lean_object* v_x_3103_){
_start:
{
lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3104_ = lean_apply_1(v_p_3102_, v_x_3103_);
v___x_3105_ = lean_unbox(v___x_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___lam__0___boxed(lean_object* v_p_3106_, lean_object* v_x_3107_){
_start:
{
uint8_t v_res_3108_; lean_object* v_r_3109_; 
v_res_3108_ = l_Array_any___redArg___lam__0(v_p_3106_, v_x_3107_);
v_r_3109_ = lean_box(v_res_3108_);
return v_r_3109_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg(lean_object* v_as_3110_, lean_object* v_p_3111_, lean_object* v_start_3112_, lean_object* v_stop_3113_){
_start:
{
lean_object* v___x_3114_; uint8_t v___x_3115_; 
v___x_3114_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3115_ = lean_nat_dec_lt(v_start_3112_, v_stop_3113_);
if (v___x_3115_ == 0)
{
lean_dec(v_stop_3113_);
lean_dec_ref(v_p_3111_);
lean_dec_ref(v_as_3110_);
return v___x_3115_;
}
else
{
lean_object* v___f_3116_; lean_object* v___y_3118_; lean_object* v___x_3124_; uint8_t v___x_3125_; 
v___f_3116_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3116_, 0, v_p_3111_);
v___x_3124_ = lean_array_get_size(v_as_3110_);
v___x_3125_ = lean_nat_dec_le(v_stop_3113_, v___x_3124_);
if (v___x_3125_ == 0)
{
lean_dec(v_stop_3113_);
v___y_3118_ = v___x_3124_;
goto v___jp_3117_;
}
else
{
v___y_3118_ = v_stop_3113_;
goto v___jp_3117_;
}
v___jp_3117_:
{
uint8_t v___x_3119_; 
v___x_3119_ = lean_nat_dec_lt(v_start_3112_, v___y_3118_);
if (v___x_3119_ == 0)
{
lean_dec(v___y_3118_);
lean_dec_ref(v___f_3116_);
lean_dec_ref(v_as_3110_);
return v___x_3119_;
}
else
{
size_t v___x_3120_; size_t v___x_3121_; lean_object* v___x_3122_; uint8_t v___x_3123_; 
v___x_3120_ = lean_usize_of_nat(v_start_3112_);
v___x_3121_ = lean_usize_of_nat(v___y_3118_);
lean_dec(v___y_3118_);
v___x_3122_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3114_, v___f_3116_, v_as_3110_, v___x_3120_, v___x_3121_);
v___x_3123_ = lean_unbox(v___x_3122_);
lean_dec(v___x_3122_);
return v___x_3123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___boxed(lean_object* v_as_3126_, lean_object* v_p_3127_, lean_object* v_start_3128_, lean_object* v_stop_3129_){
_start:
{
uint8_t v_res_3130_; lean_object* v_r_3131_; 
v_res_3130_ = l_Array_any___redArg(v_as_3126_, v_p_3127_, v_start_3128_, v_stop_3129_);
lean_dec(v_start_3128_);
v_r_3131_ = lean_box(v_res_3130_);
return v_r_3131_;
}
}
LEAN_EXPORT uint8_t l_Array_any(lean_object* v_00_u03b1_3132_, lean_object* v_as_3133_, lean_object* v_p_3134_, lean_object* v_start_3135_, lean_object* v_stop_3136_){
_start:
{
lean_object* v___x_3137_; uint8_t v___x_3138_; 
v___x_3137_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3138_ = lean_nat_dec_lt(v_start_3135_, v_stop_3136_);
if (v___x_3138_ == 0)
{
lean_dec(v_stop_3136_);
lean_dec_ref(v_p_3134_);
lean_dec_ref(v_as_3133_);
return v___x_3138_;
}
else
{
lean_object* v___f_3139_; lean_object* v___y_3141_; lean_object* v___x_3147_; uint8_t v___x_3148_; 
v___f_3139_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3139_, 0, v_p_3134_);
v___x_3147_ = lean_array_get_size(v_as_3133_);
v___x_3148_ = lean_nat_dec_le(v_stop_3136_, v___x_3147_);
if (v___x_3148_ == 0)
{
lean_dec(v_stop_3136_);
v___y_3141_ = v___x_3147_;
goto v___jp_3140_;
}
else
{
v___y_3141_ = v_stop_3136_;
goto v___jp_3140_;
}
v___jp_3140_:
{
uint8_t v___x_3142_; 
v___x_3142_ = lean_nat_dec_lt(v_start_3135_, v___y_3141_);
if (v___x_3142_ == 0)
{
lean_dec(v___y_3141_);
lean_dec_ref(v___f_3139_);
lean_dec_ref(v_as_3133_);
return v___x_3142_;
}
else
{
size_t v___x_3143_; size_t v___x_3144_; lean_object* v___x_3145_; uint8_t v___x_3146_; 
v___x_3143_ = lean_usize_of_nat(v_start_3135_);
v___x_3144_ = lean_usize_of_nat(v___y_3141_);
lean_dec(v___y_3141_);
v___x_3145_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3137_, v___f_3139_, v_as_3133_, v___x_3143_, v___x_3144_);
v___x_3146_ = lean_unbox(v___x_3145_);
lean_dec(v___x_3145_);
return v___x_3146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___boxed(lean_object* v_00_u03b1_3149_, lean_object* v_as_3150_, lean_object* v_p_3151_, lean_object* v_start_3152_, lean_object* v_stop_3153_){
_start:
{
uint8_t v_res_3154_; lean_object* v_r_3155_; 
v_res_3154_ = l_Array_any(v_00_u03b1_3149_, v_as_3150_, v_p_3151_, v_start_3152_, v_stop_3153_);
lean_dec(v_start_3152_);
v_r_3155_ = lean_box(v_res_3154_);
return v_r_3155_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg___lam__0(lean_object* v_p_3156_, uint8_t v___x_3157_, lean_object* v_v_3158_){
_start:
{
lean_object* v___x_3159_; uint8_t v___x_3160_; 
v___x_3159_ = lean_apply_1(v_p_3156_, v_v_3158_);
v___x_3160_ = lean_unbox(v___x_3159_);
if (v___x_3160_ == 0)
{
return v___x_3157_;
}
else
{
uint8_t v___x_3161_; 
v___x_3161_ = 0;
return v___x_3161_;
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___lam__0___boxed(lean_object* v_p_3162_, lean_object* v___x_3163_, lean_object* v_v_3164_){
_start:
{
uint8_t v___x_339__boxed_3165_; uint8_t v_res_3166_; lean_object* v_r_3167_; 
v___x_339__boxed_3165_ = lean_unbox(v___x_3163_);
v_res_3166_ = l_Array_all___redArg___lam__0(v_p_3162_, v___x_339__boxed_3165_, v_v_3164_);
v_r_3167_ = lean_box(v_res_3166_);
return v_r_3167_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg(lean_object* v_as_3168_, lean_object* v_p_3169_, lean_object* v_start_3170_, lean_object* v_stop_3171_){
_start:
{
lean_object* v___x_3172_; uint8_t v___x_3173_; 
v___x_3172_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3173_ = lean_nat_dec_lt(v_start_3170_, v_stop_3171_);
if (v___x_3173_ == 0)
{
uint8_t v___x_3174_; 
lean_dec(v_stop_3171_);
lean_dec_ref(v_p_3169_);
lean_dec_ref(v_as_3168_);
v___x_3174_ = 1;
return v___x_3174_;
}
else
{
lean_object* v___x_3175_; lean_object* v___f_3176_; lean_object* v___y_3178_; lean_object* v___x_3185_; uint8_t v___x_3186_; 
v___x_3175_ = lean_box(v___x_3173_);
v___f_3176_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3176_, 0, v_p_3169_);
lean_closure_set(v___f_3176_, 1, v___x_3175_);
v___x_3185_ = lean_array_get_size(v_as_3168_);
v___x_3186_ = lean_nat_dec_le(v_stop_3171_, v___x_3185_);
if (v___x_3186_ == 0)
{
lean_dec(v_stop_3171_);
v___y_3178_ = v___x_3185_;
goto v___jp_3177_;
}
else
{
v___y_3178_ = v_stop_3171_;
goto v___jp_3177_;
}
v___jp_3177_:
{
uint8_t v___x_3179_; 
v___x_3179_ = lean_nat_dec_lt(v_start_3170_, v___y_3178_);
if (v___x_3179_ == 0)
{
lean_dec(v___y_3178_);
lean_dec_ref(v___f_3176_);
lean_dec_ref(v_as_3168_);
return v___x_3173_;
}
else
{
size_t v___x_3180_; size_t v___x_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; 
v___x_3180_ = lean_usize_of_nat(v_start_3170_);
v___x_3181_ = lean_usize_of_nat(v___y_3178_);
lean_dec(v___y_3178_);
v___x_3182_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3172_, v___f_3176_, v_as_3168_, v___x_3180_, v___x_3181_);
v___x_3183_ = lean_unbox(v___x_3182_);
lean_dec(v___x_3182_);
if (v___x_3183_ == 0)
{
return v___x_3179_;
}
else
{
uint8_t v___x_3184_; 
v___x_3184_ = 0;
return v___x_3184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___boxed(lean_object* v_as_3187_, lean_object* v_p_3188_, lean_object* v_start_3189_, lean_object* v_stop_3190_){
_start:
{
uint8_t v_res_3191_; lean_object* v_r_3192_; 
v_res_3191_ = l_Array_all___redArg(v_as_3187_, v_p_3188_, v_start_3189_, v_stop_3190_);
lean_dec(v_start_3189_);
v_r_3192_ = lean_box(v_res_3191_);
return v_r_3192_;
}
}
LEAN_EXPORT uint8_t l_Array_all(lean_object* v_00_u03b1_3193_, lean_object* v_as_3194_, lean_object* v_p_3195_, lean_object* v_start_3196_, lean_object* v_stop_3197_){
_start:
{
lean_object* v___x_3198_; uint8_t v___x_3199_; 
v___x_3198_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3199_ = lean_nat_dec_lt(v_start_3196_, v_stop_3197_);
if (v___x_3199_ == 0)
{
uint8_t v___x_3200_; 
lean_dec(v_stop_3197_);
lean_dec_ref(v_p_3195_);
lean_dec_ref(v_as_3194_);
v___x_3200_ = 1;
return v___x_3200_;
}
else
{
lean_object* v___x_3201_; lean_object* v___f_3202_; lean_object* v___y_3204_; lean_object* v___x_3211_; uint8_t v___x_3212_; 
v___x_3201_ = lean_box(v___x_3199_);
v___f_3202_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3202_, 0, v_p_3195_);
lean_closure_set(v___f_3202_, 1, v___x_3201_);
v___x_3211_ = lean_array_get_size(v_as_3194_);
v___x_3212_ = lean_nat_dec_le(v_stop_3197_, v___x_3211_);
if (v___x_3212_ == 0)
{
lean_dec(v_stop_3197_);
v___y_3204_ = v___x_3211_;
goto v___jp_3203_;
}
else
{
v___y_3204_ = v_stop_3197_;
goto v___jp_3203_;
}
v___jp_3203_:
{
uint8_t v___x_3205_; 
v___x_3205_ = lean_nat_dec_lt(v_start_3196_, v___y_3204_);
if (v___x_3205_ == 0)
{
lean_dec(v___y_3204_);
lean_dec_ref(v___f_3202_);
lean_dec_ref(v_as_3194_);
return v___x_3199_;
}
else
{
size_t v___x_3206_; size_t v___x_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v___x_3206_ = lean_usize_of_nat(v_start_3196_);
v___x_3207_ = lean_usize_of_nat(v___y_3204_);
lean_dec(v___y_3204_);
v___x_3208_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3198_, v___f_3202_, v_as_3194_, v___x_3206_, v___x_3207_);
v___x_3209_ = lean_unbox(v___x_3208_);
lean_dec(v___x_3208_);
if (v___x_3209_ == 0)
{
return v___x_3205_;
}
else
{
uint8_t v___x_3210_; 
v___x_3210_ = 0;
return v___x_3210_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___boxed(lean_object* v_00_u03b1_3213_, lean_object* v_as_3214_, lean_object* v_p_3215_, lean_object* v_start_3216_, lean_object* v_stop_3217_){
_start:
{
uint8_t v_res_3218_; lean_object* v_r_3219_; 
v_res_3218_ = l_Array_all(v_00_u03b1_3213_, v_as_3214_, v_p_3215_, v_start_3216_, v_stop_3217_);
lean_dec(v_start_3216_);
v_r_3219_ = lean_box(v_res_3218_);
return v_r_3219_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg___lam__0(lean_object* v_inst_3220_, lean_object* v_a_3221_, lean_object* v_x_3222_){
_start:
{
lean_object* v___x_3223_; uint8_t v___x_3224_; 
v___x_3223_ = lean_apply_2(v_inst_3220_, v_a_3221_, v_x_3222_);
v___x_3224_ = lean_unbox(v___x_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___lam__0___boxed(lean_object* v_inst_3225_, lean_object* v_a_3226_, lean_object* v_x_3227_){
_start:
{
uint8_t v_res_3228_; lean_object* v_r_3229_; 
v_res_3228_ = l_Array_contains___redArg___lam__0(v_inst_3225_, v_a_3226_, v_x_3227_);
v_r_3229_ = lean_box(v_res_3228_);
return v_r_3229_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg(lean_object* v_inst_3230_, lean_object* v_as_3231_, lean_object* v_a_3232_){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3233_ = lean_unsigned_to_nat(0u);
v___x_3234_ = lean_array_get_size(v_as_3231_);
v___x_3235_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3236_ = lean_nat_dec_lt(v___x_3233_, v___x_3234_);
if (v___x_3236_ == 0)
{
lean_dec(v_a_3232_);
lean_dec_ref(v_as_3231_);
lean_dec_ref(v_inst_3230_);
return v___x_3236_;
}
else
{
if (v___x_3236_ == 0)
{
lean_dec(v_a_3232_);
lean_dec_ref(v_as_3231_);
lean_dec_ref(v_inst_3230_);
return v___x_3236_;
}
else
{
lean_object* v___f_3237_; size_t v___x_3238_; size_t v___x_3239_; lean_object* v___x_3240_; uint8_t v___x_3241_; 
v___f_3237_ = lean_alloc_closure((void*)(l_Array_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3237_, 0, v_inst_3230_);
lean_closure_set(v___f_3237_, 1, v_a_3232_);
v___x_3238_ = ((size_t)0ULL);
v___x_3239_ = lean_usize_of_nat(v___x_3234_);
v___x_3240_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3235_, v___f_3237_, v_as_3231_, v___x_3238_, v___x_3239_);
v___x_3241_ = lean_unbox(v___x_3240_);
lean_dec(v___x_3240_);
return v___x_3241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___boxed(lean_object* v_inst_3242_, lean_object* v_as_3243_, lean_object* v_a_3244_){
_start:
{
uint8_t v_res_3245_; lean_object* v_r_3246_; 
v_res_3245_ = l_Array_contains___redArg(v_inst_3242_, v_as_3243_, v_a_3244_);
v_r_3246_ = lean_box(v_res_3245_);
return v_r_3246_;
}
}
LEAN_EXPORT uint8_t l_Array_contains(lean_object* v_00_u03b1_3247_, lean_object* v_inst_3248_, lean_object* v_as_3249_, lean_object* v_a_3250_){
_start:
{
uint8_t v___x_3251_; 
v___x_3251_ = l_Array_contains___redArg(v_inst_3248_, v_as_3249_, v_a_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___boxed(lean_object* v_00_u03b1_3252_, lean_object* v_inst_3253_, lean_object* v_as_3254_, lean_object* v_a_3255_){
_start:
{
uint8_t v_res_3256_; lean_object* v_r_3257_; 
v_res_3256_ = l_Array_contains(v_00_u03b1_3252_, v_inst_3253_, v_as_3254_, v_a_3255_);
v_r_3257_ = lean_box(v_res_3256_);
return v_r_3257_;
}
}
LEAN_EXPORT uint8_t l_Array_elem___redArg(lean_object* v_inst_3258_, lean_object* v_a_3259_, lean_object* v_as_3260_){
_start:
{
uint8_t v___x_3261_; 
v___x_3261_ = l_Array_contains___redArg(v_inst_3258_, v_as_3260_, v_a_3259_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___redArg___boxed(lean_object* v_inst_3262_, lean_object* v_a_3263_, lean_object* v_as_3264_){
_start:
{
uint8_t v_res_3265_; lean_object* v_r_3266_; 
v_res_3265_ = l_Array_elem___redArg(v_inst_3262_, v_a_3263_, v_as_3264_);
v_r_3266_ = lean_box(v_res_3265_);
return v_r_3266_;
}
}
LEAN_EXPORT uint8_t l_Array_elem(lean_object* v_00_u03b1_3267_, lean_object* v_inst_3268_, lean_object* v_a_3269_, lean_object* v_as_3270_){
_start:
{
uint8_t v___x_3271_; 
v___x_3271_ = l_Array_contains___redArg(v_inst_3268_, v_as_3270_, v_a_3269_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___boxed(lean_object* v_00_u03b1_3272_, lean_object* v_inst_3273_, lean_object* v_a_3274_, lean_object* v_as_3275_){
_start:
{
uint8_t v_res_3276_; lean_object* v_r_3277_; 
v_res_3276_ = l_Array_elem(v_00_u03b1_3272_, v_inst_3273_, v_a_3274_, v_as_3275_);
v_r_3277_ = lean_box(v_res_3276_);
return v_r_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(lean_object* v_as_3278_, size_t v_i_3279_, size_t v_stop_3280_, lean_object* v_b_3281_){
_start:
{
uint8_t v___x_3282_; 
v___x_3282_ = lean_usize_dec_eq(v_i_3279_, v_stop_3280_);
if (v___x_3282_ == 0)
{
size_t v___x_3283_; size_t v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3283_ = ((size_t)1ULL);
v___x_3284_ = lean_usize_sub(v_i_3279_, v___x_3283_);
v___x_3285_ = lean_array_uget_borrowed(v_as_3278_, v___x_3284_);
lean_inc(v___x_3285_);
v___x_3286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
lean_ctor_set(v___x_3286_, 1, v_b_3281_);
v_i_3279_ = v___x_3284_;
v_b_3281_ = v___x_3286_;
goto _start;
}
else
{
return v_b_3281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg___boxed(lean_object* v_as_3288_, lean_object* v_i_3289_, lean_object* v_stop_3290_, lean_object* v_b_3291_){
_start:
{
size_t v_i_boxed_3292_; size_t v_stop_boxed_3293_; lean_object* v_res_3294_; 
v_i_boxed_3292_ = lean_unbox_usize(v_i_3289_);
lean_dec(v_i_3289_);
v_stop_boxed_3293_ = lean_unbox_usize(v_stop_3290_);
lean_dec(v_stop_3290_);
v_res_3294_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3288_, v_i_boxed_3292_, v_stop_boxed_3293_, v_b_3291_);
lean_dec_ref(v_as_3288_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg(lean_object* v_as_3295_){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; uint8_t v___x_3299_; 
v___x_3296_ = lean_box(0);
v___x_3297_ = lean_array_get_size(v_as_3295_);
v___x_3298_ = lean_unsigned_to_nat(0u);
v___x_3299_ = lean_nat_dec_lt(v___x_3298_, v___x_3297_);
if (v___x_3299_ == 0)
{
return v___x_3296_;
}
else
{
size_t v___x_3300_; size_t v___x_3301_; lean_object* v___x_3302_; 
v___x_3300_ = lean_usize_of_nat(v___x_3297_);
v___x_3301_ = ((size_t)0ULL);
v___x_3302_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3295_, v___x_3300_, v___x_3301_, v___x_3296_);
return v___x_3302_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg___boxed(lean_object* v_as_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Array_toListImpl___redArg(v_as_3303_);
lean_dec_ref(v_as_3303_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* lean_array_to_list_impl(lean_object* v_00_u03b1_3305_, lean_object* v_as_3306_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Array_toListImpl___redArg(v_as_3306_);
lean_dec_ref(v_as_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(lean_object* v_00_u03b1_3308_, lean_object* v_as_3309_, size_t v_i_3310_, size_t v_stop_3311_, lean_object* v_b_3312_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3309_, v_i_3310_, v_stop_3311_, v_b_3312_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___boxed(lean_object* v_00_u03b1_3314_, lean_object* v_as_3315_, lean_object* v_i_3316_, lean_object* v_stop_3317_, lean_object* v_b_3318_){
_start:
{
size_t v_i_boxed_3319_; size_t v_stop_boxed_3320_; lean_object* v_res_3321_; 
v_i_boxed_3319_ = lean_unbox_usize(v_i_3316_);
lean_dec(v_i_3316_);
v_stop_boxed_3320_ = lean_unbox_usize(v_stop_3317_);
lean_dec(v_stop_3317_);
v_res_3321_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(v_00_u03b1_3314_, v_as_3315_, v_i_boxed_3319_, v_stop_boxed_3320_, v_b_3318_);
lean_dec_ref(v_as_3315_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg___lam__0(lean_object* v_x1_3322_, lean_object* v_x2_3323_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3324_, 0, v_x1_3322_);
lean_ctor_set(v___x_3324_, 1, v_x2_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg(lean_object* v_as_3326_, lean_object* v_l_3327_){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; 
v___x_3328_ = lean_array_get_size(v_as_3326_);
v___x_3329_ = lean_unsigned_to_nat(0u);
v___x_3330_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3331_ = lean_nat_dec_lt(v___x_3329_, v___x_3328_);
if (v___x_3331_ == 0)
{
lean_dec_ref(v_as_3326_);
return v_l_3327_;
}
else
{
lean_object* v___f_3332_; size_t v___x_3333_; size_t v___x_3334_; lean_object* v___x_3335_; 
v___f_3332_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3333_ = lean_usize_of_nat(v___x_3328_);
v___x_3334_ = ((size_t)0ULL);
v___x_3335_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3330_, v___f_3332_, v_as_3326_, v___x_3333_, v___x_3334_, v_l_3327_);
return v___x_3335_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend(lean_object* v_00_u03b1_3336_, lean_object* v_as_3337_, lean_object* v_l_3338_){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; uint8_t v___x_3342_; 
v___x_3339_ = lean_array_get_size(v_as_3337_);
v___x_3340_ = lean_unsigned_to_nat(0u);
v___x_3341_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3342_ = lean_nat_dec_lt(v___x_3340_, v___x_3339_);
if (v___x_3342_ == 0)
{
lean_dec_ref(v_as_3337_);
return v_l_3338_;
}
else
{
lean_object* v___f_3343_; size_t v___x_3344_; size_t v___x_3345_; lean_object* v___x_3346_; 
v___f_3343_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3344_ = lean_usize_of_nat(v___x_3339_);
v___x_3345_ = ((size_t)0ULL);
v___x_3346_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3341_, v___f_3343_, v_as_3337_, v___x_3344_, v___x_3345_, v_l_3338_);
return v___x_3346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(lean_object* v_as_3347_, size_t v_i_3348_, size_t v_stop_3349_, lean_object* v_b_3350_){
_start:
{
uint8_t v___x_3351_; 
v___x_3351_ = lean_usize_dec_eq(v_i_3348_, v_stop_3349_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; size_t v___x_3354_; size_t v___x_3355_; 
v___x_3352_ = lean_array_uget_borrowed(v_as_3347_, v_i_3348_);
lean_inc(v___x_3352_);
v___x_3353_ = lean_array_push(v_b_3350_, v___x_3352_);
v___x_3354_ = ((size_t)1ULL);
v___x_3355_ = lean_usize_add(v_i_3348_, v___x_3354_);
v_i_3348_ = v___x_3355_;
v_b_3350_ = v___x_3353_;
goto _start;
}
else
{
return v_b_3350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg___boxed(lean_object* v_as_3357_, lean_object* v_i_3358_, lean_object* v_stop_3359_, lean_object* v_b_3360_){
_start:
{
size_t v_i_boxed_3361_; size_t v_stop_boxed_3362_; lean_object* v_res_3363_; 
v_i_boxed_3361_ = lean_unbox_usize(v_i_3358_);
lean_dec(v_i_3358_);
v_stop_boxed_3362_ = lean_unbox_usize(v_stop_3359_);
lean_dec(v_stop_3359_);
v_res_3363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3357_, v_i_boxed_3361_, v_stop_boxed_3362_, v_b_3360_);
lean_dec_ref(v_as_3357_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg(lean_object* v_as_3364_, lean_object* v_bs_3365_){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; uint8_t v___x_3368_; 
v___x_3366_ = lean_unsigned_to_nat(0u);
v___x_3367_ = lean_array_get_size(v_bs_3365_);
v___x_3368_ = lean_nat_dec_lt(v___x_3366_, v___x_3367_);
if (v___x_3368_ == 0)
{
return v_as_3364_;
}
else
{
uint8_t v___x_3369_; 
v___x_3369_ = lean_nat_dec_le(v___x_3367_, v___x_3367_);
if (v___x_3369_ == 0)
{
if (v___x_3368_ == 0)
{
return v_as_3364_;
}
else
{
size_t v___x_3370_; size_t v___x_3371_; lean_object* v___x_3372_; 
v___x_3370_ = ((size_t)0ULL);
v___x_3371_ = lean_usize_of_nat(v___x_3367_);
v___x_3372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3365_, v___x_3370_, v___x_3371_, v_as_3364_);
return v___x_3372_;
}
}
else
{
size_t v___x_3373_; size_t v___x_3374_; lean_object* v___x_3375_; 
v___x_3373_ = ((size_t)0ULL);
v___x_3374_ = lean_usize_of_nat(v___x_3367_);
v___x_3375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3365_, v___x_3373_, v___x_3374_, v_as_3364_);
return v___x_3375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg___boxed(lean_object* v_as_3376_, lean_object* v_bs_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_Array_append___redArg(v_as_3376_, v_bs_3377_);
lean_dec_ref(v_bs_3377_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Array_append(lean_object* v_00_u03b1_3379_, lean_object* v_as_3380_, lean_object* v_bs_3381_){
_start:
{
lean_object* v___x_3382_; 
v___x_3382_ = l_Array_append___redArg(v_as_3380_, v_bs_3381_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Array_append___boxed(lean_object* v_00_u03b1_3383_, lean_object* v_as_3384_, lean_object* v_bs_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Array_append(v_00_u03b1_3383_, v_as_3384_, v_bs_3385_);
lean_dec_ref(v_bs_3385_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(lean_object* v_00_u03b1_3387_, lean_object* v_as_3388_, size_t v_i_3389_, size_t v_stop_3390_, lean_object* v_b_3391_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3388_, v_i_3389_, v_stop_3390_, v_b_3391_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___boxed(lean_object* v_00_u03b1_3393_, lean_object* v_as_3394_, lean_object* v_i_3395_, lean_object* v_stop_3396_, lean_object* v_b_3397_){
_start:
{
size_t v_i_boxed_3398_; size_t v_stop_boxed_3399_; lean_object* v_res_3400_; 
v_i_boxed_3398_ = lean_unbox_usize(v_i_3395_);
lean_dec(v_i_3395_);
v_stop_boxed_3399_ = lean_unbox_usize(v_stop_3396_);
lean_dec(v_stop_3396_);
v_res_3400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(v_00_u03b1_3393_, v_as_3394_, v_i_boxed_3398_, v_stop_boxed_3399_, v_b_3397_);
lean_dec_ref(v_as_3394_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend(lean_object* v_00_u03b1_3402_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = ((lean_object*)(l_Array_instAppend___closed__0));
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object* v_x_3404_, lean_object* v_x_3405_){
_start:
{
if (lean_obj_tag(v_x_3405_) == 0)
{
return v_x_3404_;
}
else
{
lean_object* v_head_3406_; lean_object* v_tail_3407_; lean_object* v___x_3408_; 
v_head_3406_ = lean_ctor_get(v_x_3405_, 0);
lean_inc(v_head_3406_);
v_tail_3407_ = lean_ctor_get(v_x_3405_, 1);
lean_inc(v_tail_3407_);
lean_dec_ref(v_x_3405_);
v___x_3408_ = lean_array_push(v_x_3404_, v_head_3406_);
v_x_3404_ = v___x_3408_;
v_x_3405_ = v_tail_3407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_appendList___redArg(lean_object* v_as_3410_, lean_object* v_bs_3411_){
_start:
{
lean_object* v___x_3412_; 
v___x_3412_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3410_, v_bs_3411_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Array_appendList(lean_object* v_00_u03b1_3413_, lean_object* v_as_3414_, lean_object* v_bs_3415_){
_start:
{
lean_object* v___x_3416_; 
v___x_3416_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3414_, v_bs_3415_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0(lean_object* v_00_u03b1_3417_, lean_object* v_x_3418_, lean_object* v_x_3419_){
_start:
{
lean_object* v___x_3420_; 
v___x_3420_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_3418_, v_x_3419_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList(lean_object* v_00_u03b1_3422_){
_start:
{
lean_object* v___x_3423_; 
v___x_3423_ = ((lean_object*)(l_Array_instHAppendList___closed__0));
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0(lean_object* v_bs_3424_, lean_object* v_toPure_3425_, lean_object* v_____do__lift_3426_){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = l_Array_append___redArg(v_bs_3424_, v_____do__lift_3426_);
v___x_3428_ = lean_apply_2(v_toPure_3425_, lean_box(0), v___x_3427_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0___boxed(lean_object* v_bs_3429_, lean_object* v_toPure_3430_, lean_object* v_____do__lift_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Array_flatMapM___redArg___lam__0(v_bs_3429_, v_toPure_3430_, v_____do__lift_3431_);
lean_dec_ref(v_____do__lift_3431_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__1(lean_object* v_toPure_3433_, lean_object* v_f_3434_, lean_object* v_toBind_3435_, lean_object* v_bs_3436_, lean_object* v_a_3437_){
_start:
{
lean_object* v___f_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___f_3438_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3438_, 0, v_bs_3436_);
lean_closure_set(v___f_3438_, 1, v_toPure_3433_);
v___x_3439_ = lean_apply_1(v_f_3434_, v_a_3437_);
v___x_3440_ = lean_apply_4(v_toBind_3435_, lean_box(0), lean_box(0), v___x_3439_, v___f_3438_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg(lean_object* v_inst_3441_, lean_object* v_f_3442_, lean_object* v_as_3443_){
_start:
{
lean_object* v_toApplicative_3444_; lean_object* v_toBind_3445_; lean_object* v_toPure_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; uint8_t v___x_3450_; 
v_toApplicative_3444_ = lean_ctor_get(v_inst_3441_, 0);
v_toBind_3445_ = lean_ctor_get(v_inst_3441_, 1);
v_toPure_3446_ = lean_ctor_get(v_toApplicative_3444_, 1);
v___x_3447_ = lean_unsigned_to_nat(0u);
v___x_3448_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3449_ = lean_array_get_size(v_as_3443_);
v___x_3450_ = lean_nat_dec_lt(v___x_3447_, v___x_3449_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; 
lean_inc(v_toPure_3446_);
lean_dec_ref(v_as_3443_);
lean_dec(v_f_3442_);
lean_dec_ref(v_inst_3441_);
v___x_3451_ = lean_apply_2(v_toPure_3446_, lean_box(0), v___x_3448_);
return v___x_3451_;
}
else
{
lean_object* v___f_3452_; uint8_t v___x_3453_; 
lean_inc(v_toBind_3445_);
lean_inc(v_toPure_3446_);
v___f_3452_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3452_, 0, v_toPure_3446_);
lean_closure_set(v___f_3452_, 1, v_f_3442_);
lean_closure_set(v___f_3452_, 2, v_toBind_3445_);
v___x_3453_ = lean_nat_dec_le(v___x_3449_, v___x_3449_);
if (v___x_3453_ == 0)
{
if (v___x_3450_ == 0)
{
lean_object* v___x_3454_; 
lean_inc(v_toPure_3446_);
lean_dec_ref(v___f_3452_);
lean_dec_ref(v_as_3443_);
lean_dec_ref(v_inst_3441_);
v___x_3454_ = lean_apply_2(v_toPure_3446_, lean_box(0), v___x_3448_);
return v___x_3454_;
}
else
{
size_t v___x_3455_; size_t v___x_3456_; lean_object* v___x_3457_; 
v___x_3455_ = ((size_t)0ULL);
v___x_3456_ = lean_usize_of_nat(v___x_3449_);
v___x_3457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3441_, v___f_3452_, v_as_3443_, v___x_3455_, v___x_3456_, v___x_3448_);
return v___x_3457_;
}
}
else
{
size_t v___x_3458_; size_t v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = ((size_t)0ULL);
v___x_3459_ = lean_usize_of_nat(v___x_3449_);
v___x_3460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3441_, v___f_3452_, v_as_3443_, v___x_3458_, v___x_3459_, v___x_3448_);
return v___x_3460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM(lean_object* v_00_u03b1_3461_, lean_object* v_m_3462_, lean_object* v_00_u03b2_3463_, lean_object* v_inst_3464_, lean_object* v_f_3465_, lean_object* v_as_3466_){
_start:
{
lean_object* v_toApplicative_3467_; lean_object* v_toBind_3468_; lean_object* v_toPure_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; uint8_t v___x_3473_; 
v_toApplicative_3467_ = lean_ctor_get(v_inst_3464_, 0);
v_toBind_3468_ = lean_ctor_get(v_inst_3464_, 1);
v_toPure_3469_ = lean_ctor_get(v_toApplicative_3467_, 1);
v___x_3470_ = lean_unsigned_to_nat(0u);
v___x_3471_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3472_ = lean_array_get_size(v_as_3466_);
v___x_3473_ = lean_nat_dec_lt(v___x_3470_, v___x_3472_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3474_; 
lean_inc(v_toPure_3469_);
lean_dec_ref(v_as_3466_);
lean_dec(v_f_3465_);
lean_dec_ref(v_inst_3464_);
v___x_3474_ = lean_apply_2(v_toPure_3469_, lean_box(0), v___x_3471_);
return v___x_3474_;
}
else
{
lean_object* v___f_3475_; uint8_t v___x_3476_; 
lean_inc(v_toBind_3468_);
lean_inc(v_toPure_3469_);
v___f_3475_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3475_, 0, v_toPure_3469_);
lean_closure_set(v___f_3475_, 1, v_f_3465_);
lean_closure_set(v___f_3475_, 2, v_toBind_3468_);
v___x_3476_ = lean_nat_dec_le(v___x_3472_, v___x_3472_);
if (v___x_3476_ == 0)
{
if (v___x_3473_ == 0)
{
lean_object* v___x_3477_; 
lean_inc(v_toPure_3469_);
lean_dec_ref(v___f_3475_);
lean_dec_ref(v_as_3466_);
lean_dec_ref(v_inst_3464_);
v___x_3477_ = lean_apply_2(v_toPure_3469_, lean_box(0), v___x_3471_);
return v___x_3477_;
}
else
{
size_t v___x_3478_; size_t v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = ((size_t)0ULL);
v___x_3479_ = lean_usize_of_nat(v___x_3472_);
v___x_3480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3464_, v___f_3475_, v_as_3466_, v___x_3478_, v___x_3479_, v___x_3471_);
return v___x_3480_;
}
}
else
{
size_t v___x_3481_; size_t v___x_3482_; lean_object* v___x_3483_; 
v___x_3481_ = ((size_t)0ULL);
v___x_3482_ = lean_usize_of_nat(v___x_3472_);
v___x_3483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3464_, v___f_3475_, v_as_3466_, v___x_3481_, v___x_3482_, v___x_3471_);
return v___x_3483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg___lam__0(lean_object* v_f_3484_, lean_object* v_x1_3485_, lean_object* v_x2_3486_){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = lean_apply_1(v_f_3484_, v_x2_3486_);
v___x_3488_ = l_Array_append___redArg(v_x1_3485_, v___x_3487_);
lean_dec_ref(v___x_3487_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg(lean_object* v_f_3489_, lean_object* v_as_3490_){
_start:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; uint8_t v___x_3495_; 
v___x_3491_ = lean_unsigned_to_nat(0u);
v___x_3492_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3493_ = lean_array_get_size(v_as_3490_);
v___x_3494_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3495_ = lean_nat_dec_lt(v___x_3491_, v___x_3493_);
if (v___x_3495_ == 0)
{
lean_dec_ref(v_as_3490_);
lean_dec_ref(v_f_3489_);
return v___x_3492_;
}
else
{
lean_object* v___f_3496_; uint8_t v___x_3497_; 
v___f_3496_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3496_, 0, v_f_3489_);
v___x_3497_ = lean_nat_dec_le(v___x_3493_, v___x_3493_);
if (v___x_3497_ == 0)
{
if (v___x_3495_ == 0)
{
lean_dec_ref(v___f_3496_);
lean_dec_ref(v_as_3490_);
return v___x_3492_;
}
else
{
size_t v___x_3498_; size_t v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = ((size_t)0ULL);
v___x_3499_ = lean_usize_of_nat(v___x_3493_);
v___x_3500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3494_, v___f_3496_, v_as_3490_, v___x_3498_, v___x_3499_, v___x_3492_);
return v___x_3500_;
}
}
else
{
size_t v___x_3501_; size_t v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = ((size_t)0ULL);
v___x_3502_ = lean_usize_of_nat(v___x_3493_);
v___x_3503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3494_, v___f_3496_, v_as_3490_, v___x_3501_, v___x_3502_, v___x_3492_);
return v___x_3503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap(lean_object* v_00_u03b1_3504_, lean_object* v_00_u03b2_3505_, lean_object* v_f_3506_, lean_object* v_as_3507_){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_3508_ = lean_unsigned_to_nat(0u);
v___x_3509_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3510_ = lean_array_get_size(v_as_3507_);
v___x_3511_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3512_ = lean_nat_dec_lt(v___x_3508_, v___x_3510_);
if (v___x_3512_ == 0)
{
lean_dec_ref(v_as_3507_);
lean_dec_ref(v_f_3506_);
return v___x_3509_;
}
else
{
lean_object* v___f_3513_; uint8_t v___x_3514_; 
v___f_3513_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3513_, 0, v_f_3506_);
v___x_3514_ = lean_nat_dec_le(v___x_3510_, v___x_3510_);
if (v___x_3514_ == 0)
{
if (v___x_3512_ == 0)
{
lean_dec_ref(v___f_3513_);
lean_dec_ref(v_as_3507_);
return v___x_3509_;
}
else
{
size_t v___x_3515_; size_t v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = ((size_t)0ULL);
v___x_3516_ = lean_usize_of_nat(v___x_3510_);
v___x_3517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3511_, v___f_3513_, v_as_3507_, v___x_3515_, v___x_3516_, v___x_3509_);
return v___x_3517_;
}
}
else
{
size_t v___x_3518_; size_t v___x_3519_; lean_object* v___x_3520_; 
v___x_3518_ = ((size_t)0ULL);
v___x_3519_ = lean_usize_of_nat(v___x_3510_);
v___x_3520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3511_, v___f_3513_, v_as_3507_, v___x_3518_, v___x_3519_, v___x_3509_);
return v___x_3520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten___redArg(lean_object* v_xss_3522_){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; 
v___x_3523_ = lean_unsigned_to_nat(0u);
v___x_3524_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3525_ = lean_array_get_size(v_xss_3522_);
v___x_3526_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3527_ = lean_nat_dec_lt(v___x_3523_, v___x_3525_);
if (v___x_3527_ == 0)
{
lean_dec_ref(v_xss_3522_);
return v___x_3524_;
}
else
{
lean_object* v___f_3528_; uint8_t v___x_3529_; 
v___f_3528_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3529_ = lean_nat_dec_le(v___x_3525_, v___x_3525_);
if (v___x_3529_ == 0)
{
if (v___x_3527_ == 0)
{
lean_dec_ref(v_xss_3522_);
return v___x_3524_;
}
else
{
size_t v___x_3530_; size_t v___x_3531_; lean_object* v___x_3532_; 
v___x_3530_ = ((size_t)0ULL);
v___x_3531_ = lean_usize_of_nat(v___x_3525_);
v___x_3532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3526_, v___f_3528_, v_xss_3522_, v___x_3530_, v___x_3531_, v___x_3524_);
return v___x_3532_;
}
}
else
{
size_t v___x_3533_; size_t v___x_3534_; lean_object* v___x_3535_; 
v___x_3533_ = ((size_t)0ULL);
v___x_3534_ = lean_usize_of_nat(v___x_3525_);
v___x_3535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3526_, v___f_3528_, v_xss_3522_, v___x_3533_, v___x_3534_, v___x_3524_);
return v___x_3535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten(lean_object* v_00_u03b1_3536_, lean_object* v_xss_3537_){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v___x_3538_ = lean_unsigned_to_nat(0u);
v___x_3539_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3540_ = lean_array_get_size(v_xss_3537_);
v___x_3541_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3542_ = lean_nat_dec_lt(v___x_3538_, v___x_3540_);
if (v___x_3542_ == 0)
{
lean_dec_ref(v_xss_3537_);
return v___x_3539_;
}
else
{
lean_object* v___f_3543_; uint8_t v___x_3544_; 
v___f_3543_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3544_ = lean_nat_dec_le(v___x_3540_, v___x_3540_);
if (v___x_3544_ == 0)
{
if (v___x_3542_ == 0)
{
lean_dec_ref(v_xss_3537_);
return v___x_3539_;
}
else
{
size_t v___x_3545_; size_t v___x_3546_; lean_object* v___x_3547_; 
v___x_3545_ = ((size_t)0ULL);
v___x_3546_ = lean_usize_of_nat(v___x_3540_);
v___x_3547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3541_, v___f_3543_, v_xss_3537_, v___x_3545_, v___x_3546_, v___x_3539_);
return v___x_3547_;
}
}
else
{
size_t v___x_3548_; size_t v___x_3549_; lean_object* v___x_3550_; 
v___x_3548_ = ((size_t)0ULL);
v___x_3549_ = lean_usize_of_nat(v___x_3540_);
v___x_3550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3541_, v___f_3543_, v_xss_3537_, v___x_3548_, v___x_3549_, v___x_3539_);
return v___x_3550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop___redArg(lean_object* v_as_3551_, lean_object* v_i_3552_, lean_object* v_j_3553_){
_start:
{
uint8_t v___x_3554_; 
v___x_3554_ = lean_nat_dec_lt(v_i_3552_, v_j_3553_);
if (v___x_3554_ == 0)
{
lean_dec(v_j_3553_);
lean_dec(v_i_3552_);
return v_as_3551_;
}
else
{
lean_object* v_as_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v_as_3555_ = lean_array_fswap(v_as_3551_, v_i_3552_, v_j_3553_);
v___x_3556_ = lean_unsigned_to_nat(1u);
v___x_3557_ = lean_nat_add(v_i_3552_, v___x_3556_);
lean_dec(v_i_3552_);
v___x_3558_ = lean_nat_sub(v_j_3553_, v___x_3556_);
lean_dec(v_j_3553_);
v_as_3551_ = v_as_3555_;
v_i_3552_ = v___x_3557_;
v_j_3553_ = v___x_3558_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop(lean_object* v_00_u03b1_3560_, lean_object* v_as_3561_, lean_object* v_i_3562_, lean_object* v_j_3563_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Array_reverse_loop___redArg(v_as_3561_, v_i_3562_, v_j_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Array_reverse___redArg(lean_object* v_as_3565_){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; uint8_t v___x_3568_; 
v___x_3566_ = lean_array_get_size(v_as_3565_);
v___x_3567_ = lean_unsigned_to_nat(1u);
v___x_3568_ = lean_nat_dec_le(v___x_3566_, v___x_3567_);
if (v___x_3568_ == 0)
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3569_ = lean_unsigned_to_nat(0u);
v___x_3570_ = lean_nat_sub(v___x_3566_, v___x_3567_);
v___x_3571_ = l_Array_reverse_loop___redArg(v_as_3565_, v___x_3569_, v___x_3570_);
return v___x_3571_;
}
else
{
return v_as_3565_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse(lean_object* v_00_u03b1_3572_, lean_object* v_as_3573_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l_Array_reverse___redArg(v_as_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___lam__0(lean_object* v_p_3575_, lean_object* v_x1_3576_, lean_object* v_x2_3577_){
_start:
{
lean_object* v___x_3578_; uint8_t v___x_3579_; 
lean_inc(v_x2_3577_);
v___x_3578_ = lean_apply_1(v_p_3575_, v_x2_3577_);
v___x_3579_ = lean_unbox(v___x_3578_);
if (v___x_3579_ == 0)
{
lean_dec(v_x2_3577_);
return v_x1_3576_;
}
else
{
lean_object* v___x_3580_; 
v___x_3580_ = lean_array_push(v_x1_3576_, v_x2_3577_);
return v___x_3580_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg(lean_object* v_p_3583_, lean_object* v_as_3584_, lean_object* v_start_3585_, lean_object* v_stop_3586_){
_start:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; uint8_t v___x_3589_; 
v___x_3587_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3588_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3589_ = lean_nat_dec_lt(v_start_3585_, v_stop_3586_);
if (v___x_3589_ == 0)
{
lean_dec_ref(v_as_3584_);
lean_dec_ref(v_p_3583_);
return v___x_3587_;
}
else
{
lean_object* v___f_3590_; lean_object* v___x_3591_; uint8_t v___x_3592_; 
v___f_3590_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3590_, 0, v_p_3583_);
v___x_3591_ = lean_array_get_size(v_as_3584_);
v___x_3592_ = lean_nat_dec_le(v_stop_3586_, v___x_3591_);
if (v___x_3592_ == 0)
{
uint8_t v___x_3593_; 
v___x_3593_ = lean_nat_dec_lt(v_start_3585_, v___x_3591_);
if (v___x_3593_ == 0)
{
lean_dec_ref(v___f_3590_);
lean_dec_ref(v_as_3584_);
return v___x_3587_;
}
else
{
size_t v___x_3594_; size_t v___x_3595_; lean_object* v___x_3596_; 
v___x_3594_ = lean_usize_of_nat(v_start_3585_);
v___x_3595_ = lean_usize_of_nat(v___x_3591_);
v___x_3596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3588_, v___f_3590_, v_as_3584_, v___x_3594_, v___x_3595_, v___x_3587_);
return v___x_3596_;
}
}
else
{
size_t v___x_3597_; size_t v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = lean_usize_of_nat(v_start_3585_);
v___x_3598_ = lean_usize_of_nat(v_stop_3586_);
v___x_3599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3588_, v___f_3590_, v_as_3584_, v___x_3597_, v___x_3598_, v___x_3587_);
return v___x_3599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___boxed(lean_object* v_p_3600_, lean_object* v_as_3601_, lean_object* v_start_3602_, lean_object* v_stop_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Array_filter___redArg(v_p_3600_, v_as_3601_, v_start_3602_, v_stop_3603_);
lean_dec(v_stop_3603_);
lean_dec(v_start_3602_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Array_filter(lean_object* v_00_u03b1_3605_, lean_object* v_p_3606_, lean_object* v_as_3607_, lean_object* v_start_3608_, lean_object* v_stop_3609_){
_start:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v___x_3610_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3611_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3612_ = lean_nat_dec_lt(v_start_3608_, v_stop_3609_);
if (v___x_3612_ == 0)
{
lean_dec_ref(v_as_3607_);
lean_dec_ref(v_p_3606_);
return v___x_3610_;
}
else
{
lean_object* v___f_3613_; lean_object* v___x_3614_; uint8_t v___x_3615_; 
v___f_3613_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3613_, 0, v_p_3606_);
v___x_3614_ = lean_array_get_size(v_as_3607_);
v___x_3615_ = lean_nat_dec_le(v_stop_3609_, v___x_3614_);
if (v___x_3615_ == 0)
{
uint8_t v___x_3616_; 
v___x_3616_ = lean_nat_dec_lt(v_start_3608_, v___x_3614_);
if (v___x_3616_ == 0)
{
lean_dec_ref(v___f_3613_);
lean_dec_ref(v_as_3607_);
return v___x_3610_;
}
else
{
size_t v___x_3617_; size_t v___x_3618_; lean_object* v___x_3619_; 
v___x_3617_ = lean_usize_of_nat(v_start_3608_);
v___x_3618_ = lean_usize_of_nat(v___x_3614_);
v___x_3619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3611_, v___f_3613_, v_as_3607_, v___x_3617_, v___x_3618_, v___x_3610_);
return v___x_3619_;
}
}
else
{
size_t v___x_3620_; size_t v___x_3621_; lean_object* v___x_3622_; 
v___x_3620_ = lean_usize_of_nat(v_start_3608_);
v___x_3621_ = lean_usize_of_nat(v_stop_3609_);
v___x_3622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3611_, v___f_3613_, v_as_3607_, v___x_3620_, v___x_3621_, v___x_3610_);
return v___x_3622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___boxed(lean_object* v_00_u03b1_3623_, lean_object* v_p_3624_, lean_object* v_as_3625_, lean_object* v_start_3626_, lean_object* v_stop_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Array_filter(v_00_u03b1_3623_, v_p_3624_, v_as_3625_, v_start_3626_, v_stop_3627_);
lean_dec(v_stop_3627_);
lean_dec(v_start_3626_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0(lean_object* v_toApplicative_3629_, lean_object* v_acc_3630_, lean_object* v_a_3631_, uint8_t v_____do__lift_3632_){
_start:
{
if (v_____do__lift_3632_ == 0)
{
lean_object* v_toPure_3633_; lean_object* v___x_3634_; 
lean_dec(v_a_3631_);
v_toPure_3633_ = lean_ctor_get(v_toApplicative_3629_, 1);
lean_inc(v_toPure_3633_);
lean_dec_ref(v_toApplicative_3629_);
v___x_3634_ = lean_apply_2(v_toPure_3633_, lean_box(0), v_acc_3630_);
return v___x_3634_;
}
else
{
lean_object* v_toPure_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v_toPure_3635_ = lean_ctor_get(v_toApplicative_3629_, 1);
lean_inc(v_toPure_3635_);
lean_dec_ref(v_toApplicative_3629_);
v___x_3636_ = lean_array_push(v_acc_3630_, v_a_3631_);
v___x_3637_ = lean_apply_2(v_toPure_3635_, lean_box(0), v___x_3636_);
return v___x_3637_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0___boxed(lean_object* v_toApplicative_3638_, lean_object* v_acc_3639_, lean_object* v_a_3640_, lean_object* v_____do__lift_3641_){
_start:
{
uint8_t v_____do__lift_119__boxed_3642_; lean_object* v_res_3643_; 
v_____do__lift_119__boxed_3642_ = lean_unbox(v_____do__lift_3641_);
v_res_3643_ = l_Array_filterM___redArg___lam__0(v_toApplicative_3638_, v_acc_3639_, v_a_3640_, v_____do__lift_119__boxed_3642_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__1(lean_object* v_toApplicative_3644_, lean_object* v_p_3645_, lean_object* v_toBind_3646_, lean_object* v_acc_3647_, lean_object* v_a_3648_){
_start:
{
lean_object* v___f_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_inc(v_a_3648_);
v___f_3649_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3649_, 0, v_toApplicative_3644_);
lean_closure_set(v___f_3649_, 1, v_acc_3647_);
lean_closure_set(v___f_3649_, 2, v_a_3648_);
v___x_3650_ = lean_apply_1(v_p_3645_, v_a_3648_);
v___x_3651_ = lean_apply_4(v_toBind_3646_, lean_box(0), lean_box(0), v___x_3650_, v___f_3649_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg(lean_object* v_inst_3652_, lean_object* v_p_3653_, lean_object* v_as_3654_, lean_object* v_start_3655_, lean_object* v_stop_3656_){
_start:
{
lean_object* v_toApplicative_3657_; lean_object* v_toBind_3658_; lean_object* v___x_3659_; uint8_t v___x_3660_; 
v_toApplicative_3657_ = lean_ctor_get(v_inst_3652_, 0);
v_toBind_3658_ = lean_ctor_get(v_inst_3652_, 1);
v___x_3659_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3660_ = lean_nat_dec_lt(v_start_3655_, v_stop_3656_);
if (v___x_3660_ == 0)
{
lean_object* v_toPure_3661_; lean_object* v___x_3662_; 
lean_inc_ref(v_toApplicative_3657_);
lean_dec_ref(v_as_3654_);
lean_dec(v_p_3653_);
lean_dec_ref(v_inst_3652_);
v_toPure_3661_ = lean_ctor_get(v_toApplicative_3657_, 1);
lean_inc(v_toPure_3661_);
lean_dec_ref(v_toApplicative_3657_);
v___x_3662_ = lean_apply_2(v_toPure_3661_, lean_box(0), v___x_3659_);
return v___x_3662_;
}
else
{
lean_object* v___f_3663_; lean_object* v___x_3664_; uint8_t v___x_3665_; 
lean_inc(v_toBind_3658_);
lean_inc_ref(v_toApplicative_3657_);
v___f_3663_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3663_, 0, v_toApplicative_3657_);
lean_closure_set(v___f_3663_, 1, v_p_3653_);
lean_closure_set(v___f_3663_, 2, v_toBind_3658_);
v___x_3664_ = lean_array_get_size(v_as_3654_);
v___x_3665_ = lean_nat_dec_le(v_stop_3656_, v___x_3664_);
if (v___x_3665_ == 0)
{
uint8_t v___x_3666_; 
v___x_3666_ = lean_nat_dec_lt(v_start_3655_, v___x_3664_);
if (v___x_3666_ == 0)
{
lean_object* v_toPure_3667_; lean_object* v___x_3668_; 
lean_inc_ref(v_toApplicative_3657_);
lean_dec_ref(v___f_3663_);
lean_dec_ref(v_as_3654_);
lean_dec_ref(v_inst_3652_);
v_toPure_3667_ = lean_ctor_get(v_toApplicative_3657_, 1);
lean_inc(v_toPure_3667_);
lean_dec_ref(v_toApplicative_3657_);
v___x_3668_ = lean_apply_2(v_toPure_3667_, lean_box(0), v___x_3659_);
return v___x_3668_;
}
else
{
size_t v___x_3669_; size_t v___x_3670_; lean_object* v___x_3671_; 
v___x_3669_ = lean_usize_of_nat(v_start_3655_);
v___x_3670_ = lean_usize_of_nat(v___x_3664_);
v___x_3671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3652_, v___f_3663_, v_as_3654_, v___x_3669_, v___x_3670_, v___x_3659_);
return v___x_3671_;
}
}
else
{
size_t v___x_3672_; size_t v___x_3673_; lean_object* v___x_3674_; 
v___x_3672_ = lean_usize_of_nat(v_start_3655_);
v___x_3673_ = lean_usize_of_nat(v_stop_3656_);
v___x_3674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3652_, v___f_3663_, v_as_3654_, v___x_3672_, v___x_3673_, v___x_3659_);
return v___x_3674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___boxed(lean_object* v_inst_3675_, lean_object* v_p_3676_, lean_object* v_as_3677_, lean_object* v_start_3678_, lean_object* v_stop_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Array_filterM___redArg(v_inst_3675_, v_p_3676_, v_as_3677_, v_start_3678_, v_stop_3679_);
lean_dec(v_stop_3679_);
lean_dec(v_start_3678_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM(lean_object* v_m_3681_, lean_object* v_00_u03b1_3682_, lean_object* v_inst_3683_, lean_object* v_p_3684_, lean_object* v_as_3685_, lean_object* v_start_3686_, lean_object* v_stop_3687_){
_start:
{
lean_object* v_toApplicative_3688_; lean_object* v_toBind_3689_; lean_object* v___x_3690_; uint8_t v___x_3691_; 
v_toApplicative_3688_ = lean_ctor_get(v_inst_3683_, 0);
v_toBind_3689_ = lean_ctor_get(v_inst_3683_, 1);
v___x_3690_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3691_ = lean_nat_dec_lt(v_start_3686_, v_stop_3687_);
if (v___x_3691_ == 0)
{
lean_object* v_toPure_3692_; lean_object* v___x_3693_; 
lean_inc_ref(v_toApplicative_3688_);
lean_dec_ref(v_as_3685_);
lean_dec(v_p_3684_);
lean_dec_ref(v_inst_3683_);
v_toPure_3692_ = lean_ctor_get(v_toApplicative_3688_, 1);
lean_inc(v_toPure_3692_);
lean_dec_ref(v_toApplicative_3688_);
v___x_3693_ = lean_apply_2(v_toPure_3692_, lean_box(0), v___x_3690_);
return v___x_3693_;
}
else
{
lean_object* v___f_3694_; lean_object* v___x_3695_; uint8_t v___x_3696_; 
lean_inc(v_toBind_3689_);
lean_inc_ref(v_toApplicative_3688_);
v___f_3694_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3694_, 0, v_toApplicative_3688_);
lean_closure_set(v___f_3694_, 1, v_p_3684_);
lean_closure_set(v___f_3694_, 2, v_toBind_3689_);
v___x_3695_ = lean_array_get_size(v_as_3685_);
v___x_3696_ = lean_nat_dec_le(v_stop_3687_, v___x_3695_);
if (v___x_3696_ == 0)
{
uint8_t v___x_3697_; 
v___x_3697_ = lean_nat_dec_lt(v_start_3686_, v___x_3695_);
if (v___x_3697_ == 0)
{
lean_object* v_toPure_3698_; lean_object* v___x_3699_; 
lean_inc_ref(v_toApplicative_3688_);
lean_dec_ref(v___f_3694_);
lean_dec_ref(v_as_3685_);
lean_dec_ref(v_inst_3683_);
v_toPure_3698_ = lean_ctor_get(v_toApplicative_3688_, 1);
lean_inc(v_toPure_3698_);
lean_dec_ref(v_toApplicative_3688_);
v___x_3699_ = lean_apply_2(v_toPure_3698_, lean_box(0), v___x_3690_);
return v___x_3699_;
}
else
{
size_t v___x_3700_; size_t v___x_3701_; lean_object* v___x_3702_; 
v___x_3700_ = lean_usize_of_nat(v_start_3686_);
v___x_3701_ = lean_usize_of_nat(v___x_3695_);
v___x_3702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3683_, v___f_3694_, v_as_3685_, v___x_3700_, v___x_3701_, v___x_3690_);
return v___x_3702_;
}
}
else
{
size_t v___x_3703_; size_t v___x_3704_; lean_object* v___x_3705_; 
v___x_3703_ = lean_usize_of_nat(v_start_3686_);
v___x_3704_ = lean_usize_of_nat(v_stop_3687_);
v___x_3705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3683_, v___f_3694_, v_as_3685_, v___x_3703_, v___x_3704_, v___x_3690_);
return v___x_3705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___boxed(lean_object* v_m_3706_, lean_object* v_00_u03b1_3707_, lean_object* v_inst_3708_, lean_object* v_p_3709_, lean_object* v_as_3710_, lean_object* v_start_3711_, lean_object* v_stop_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Array_filterM(v_m_3706_, v_00_u03b1_3707_, v_inst_3708_, v_p_3709_, v_as_3710_, v_start_3711_, v_stop_3712_);
lean_dec(v_stop_3712_);
lean_dec(v_start_3711_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__0(lean_object* v_toPure_3714_, lean_object* v_acc_3715_, lean_object* v_a_3716_, uint8_t v_____do__lift_3717_){
_start:
{
if (v_____do__lift_3717_ == 0)
{
lean_object* v___x_3718_; 
lean_dec(v_a_3716_);
v___x_3718_ = lean_apply_2(v_toPure_3714_, lean_box(0), v_acc_3715_);
return v___x_3718_;
}
else
{
lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = lean_array_push(v_acc_3715_, v_a_3716_);
v___x_3720_ = lean_apply_2(v_toPure_3714_, lean_box(0), v___x_3719_);
return v___x_3720_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__0___boxed(lean_object* v_toPure_3721_, lean_object* v_acc_3722_, lean_object* v_a_3723_, lean_object* v_____do__lift_3724_){
_start:
{
uint8_t v_____do__lift_129__boxed_3725_; lean_object* v_res_3726_; 
v_____do__lift_129__boxed_3725_ = lean_unbox(v_____do__lift_3724_);
v_res_3726_ = l_Array_filterRevM___redArg___lam__0(v_toPure_3721_, v_acc_3722_, v_a_3723_, v_____do__lift_129__boxed_3725_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__1(lean_object* v_toPure_3727_, lean_object* v_p_3728_, lean_object* v_toBind_3729_, lean_object* v_a_3730_, lean_object* v_acc_3731_){
_start:
{
lean_object* v___f_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
lean_inc(v_a_3730_);
v___f_3732_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3732_, 0, v_toPure_3727_);
lean_closure_set(v___f_3732_, 1, v_acc_3731_);
lean_closure_set(v___f_3732_, 2, v_a_3730_);
v___x_3733_ = lean_apply_1(v_p_3728_, v_a_3730_);
v___x_3734_ = lean_apply_4(v_toBind_3729_, lean_box(0), lean_box(0), v___x_3733_, v___f_3732_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg(lean_object* v_inst_3736_, lean_object* v_p_3737_, lean_object* v_as_3738_, lean_object* v_start_3739_, lean_object* v_stop_3740_){
_start:
{
lean_object* v_toApplicative_3741_; lean_object* v_toFunctor_3742_; lean_object* v_toBind_3743_; lean_object* v_toPure_3744_; lean_object* v_map_3745_; lean_object* v___f_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; uint8_t v___x_3750_; 
v_toApplicative_3741_ = lean_ctor_get(v_inst_3736_, 0);
v_toFunctor_3742_ = lean_ctor_get(v_toApplicative_3741_, 0);
v_toBind_3743_ = lean_ctor_get(v_inst_3736_, 1);
v_toPure_3744_ = lean_ctor_get(v_toApplicative_3741_, 1);
v_map_3745_ = lean_ctor_get(v_toFunctor_3742_, 0);
lean_inc(v_map_3745_);
lean_inc(v_toBind_3743_);
lean_inc(v_toPure_3744_);
v___f_3746_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3746_, 0, v_toPure_3744_);
lean_closure_set(v___f_3746_, 1, v_p_3737_);
lean_closure_set(v___f_3746_, 2, v_toBind_3743_);
v___x_3747_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3748_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3749_ = lean_array_get_size(v_as_3738_);
v___x_3750_ = lean_nat_dec_le(v_start_3739_, v___x_3749_);
if (v___x_3750_ == 0)
{
uint8_t v___x_3751_; 
v___x_3751_ = lean_nat_dec_lt(v_stop_3740_, v___x_3749_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
lean_inc(v_toPure_3744_);
lean_dec_ref(v___f_3746_);
lean_dec_ref(v_as_3738_);
lean_dec_ref(v_inst_3736_);
v___x_3752_ = lean_apply_2(v_toPure_3744_, lean_box(0), v___x_3748_);
v___x_3753_ = lean_apply_4(v_map_3745_, lean_box(0), lean_box(0), v___x_3747_, v___x_3752_);
return v___x_3753_;
}
else
{
size_t v___x_3754_; size_t v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3754_ = lean_usize_of_nat(v___x_3749_);
v___x_3755_ = lean_usize_of_nat(v_stop_3740_);
v___x_3756_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3736_, v___f_3746_, v_as_3738_, v___x_3754_, v___x_3755_, v___x_3748_);
v___x_3757_ = lean_apply_4(v_map_3745_, lean_box(0), lean_box(0), v___x_3747_, v___x_3756_);
return v___x_3757_;
}
}
else
{
uint8_t v___x_3758_; 
v___x_3758_ = lean_nat_dec_lt(v_stop_3740_, v_start_3739_);
if (v___x_3758_ == 0)
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
lean_inc(v_toPure_3744_);
lean_dec_ref(v___f_3746_);
lean_dec_ref(v_as_3738_);
lean_dec_ref(v_inst_3736_);
v___x_3759_ = lean_apply_2(v_toPure_3744_, lean_box(0), v___x_3748_);
v___x_3760_ = lean_apply_4(v_map_3745_, lean_box(0), lean_box(0), v___x_3747_, v___x_3759_);
return v___x_3760_;
}
else
{
size_t v___x_3761_; size_t v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3761_ = lean_usize_of_nat(v_start_3739_);
v___x_3762_ = lean_usize_of_nat(v_stop_3740_);
v___x_3763_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3736_, v___f_3746_, v_as_3738_, v___x_3761_, v___x_3762_, v___x_3748_);
v___x_3764_ = lean_apply_4(v_map_3745_, lean_box(0), lean_box(0), v___x_3747_, v___x_3763_);
return v___x_3764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___boxed(lean_object* v_inst_3765_, lean_object* v_p_3766_, lean_object* v_as_3767_, lean_object* v_start_3768_, lean_object* v_stop_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l_Array_filterRevM___redArg(v_inst_3765_, v_p_3766_, v_as_3767_, v_start_3768_, v_stop_3769_);
lean_dec(v_stop_3769_);
lean_dec(v_start_3768_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM(lean_object* v_m_3771_, lean_object* v_00_u03b1_3772_, lean_object* v_inst_3773_, lean_object* v_p_3774_, lean_object* v_as_3775_, lean_object* v_start_3776_, lean_object* v_stop_3777_){
_start:
{
lean_object* v_toApplicative_3778_; lean_object* v_toFunctor_3779_; lean_object* v_toBind_3780_; lean_object* v_toPure_3781_; lean_object* v_map_3782_; lean_object* v___f_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; uint8_t v___x_3787_; 
v_toApplicative_3778_ = lean_ctor_get(v_inst_3773_, 0);
v_toFunctor_3779_ = lean_ctor_get(v_toApplicative_3778_, 0);
v_toBind_3780_ = lean_ctor_get(v_inst_3773_, 1);
v_toPure_3781_ = lean_ctor_get(v_toApplicative_3778_, 1);
v_map_3782_ = lean_ctor_get(v_toFunctor_3779_, 0);
lean_inc(v_map_3782_);
lean_inc(v_toBind_3780_);
lean_inc(v_toPure_3781_);
v___f_3783_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3783_, 0, v_toPure_3781_);
lean_closure_set(v___f_3783_, 1, v_p_3774_);
lean_closure_set(v___f_3783_, 2, v_toBind_3780_);
v___x_3784_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3785_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3786_ = lean_array_get_size(v_as_3775_);
v___x_3787_ = lean_nat_dec_le(v_start_3776_, v___x_3786_);
if (v___x_3787_ == 0)
{
uint8_t v___x_3788_; 
v___x_3788_ = lean_nat_dec_lt(v_stop_3777_, v___x_3786_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
lean_inc(v_toPure_3781_);
lean_dec_ref(v___f_3783_);
lean_dec_ref(v_as_3775_);
lean_dec_ref(v_inst_3773_);
v___x_3789_ = lean_apply_2(v_toPure_3781_, lean_box(0), v___x_3785_);
v___x_3790_ = lean_apply_4(v_map_3782_, lean_box(0), lean_box(0), v___x_3784_, v___x_3789_);
return v___x_3790_;
}
else
{
size_t v___x_3791_; size_t v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3791_ = lean_usize_of_nat(v___x_3786_);
v___x_3792_ = lean_usize_of_nat(v_stop_3777_);
v___x_3793_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3773_, v___f_3783_, v_as_3775_, v___x_3791_, v___x_3792_, v___x_3785_);
v___x_3794_ = lean_apply_4(v_map_3782_, lean_box(0), lean_box(0), v___x_3784_, v___x_3793_);
return v___x_3794_;
}
}
else
{
uint8_t v___x_3795_; 
v___x_3795_ = lean_nat_dec_lt(v_stop_3777_, v_start_3776_);
if (v___x_3795_ == 0)
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
lean_inc(v_toPure_3781_);
lean_dec_ref(v___f_3783_);
lean_dec_ref(v_as_3775_);
lean_dec_ref(v_inst_3773_);
v___x_3796_ = lean_apply_2(v_toPure_3781_, lean_box(0), v___x_3785_);
v___x_3797_ = lean_apply_4(v_map_3782_, lean_box(0), lean_box(0), v___x_3784_, v___x_3796_);
return v___x_3797_;
}
else
{
size_t v___x_3798_; size_t v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3798_ = lean_usize_of_nat(v_start_3776_);
v___x_3799_ = lean_usize_of_nat(v_stop_3777_);
v___x_3800_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3773_, v___f_3783_, v_as_3775_, v___x_3798_, v___x_3799_, v___x_3785_);
v___x_3801_ = lean_apply_4(v_map_3782_, lean_box(0), lean_box(0), v___x_3784_, v___x_3800_);
return v___x_3801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___boxed(lean_object* v_m_3802_, lean_object* v_00_u03b1_3803_, lean_object* v_inst_3804_, lean_object* v_p_3805_, lean_object* v_as_3806_, lean_object* v_start_3807_, lean_object* v_stop_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_Array_filterRevM(v_m_3802_, v_00_u03b1_3803_, v_inst_3804_, v_p_3805_, v_as_3806_, v_start_3807_, v_stop_3808_);
lean_dec(v_stop_3808_);
lean_dec(v_start_3807_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__0(lean_object* v_toPure_3810_, lean_object* v_bs_3811_, lean_object* v_____do__lift_3812_){
_start:
{
if (lean_obj_tag(v_____do__lift_3812_) == 0)
{
lean_object* v___x_3813_; 
v___x_3813_ = lean_apply_2(v_toPure_3810_, lean_box(0), v_bs_3811_);
return v___x_3813_;
}
else
{
lean_object* v_val_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v_val_3814_ = lean_ctor_get(v_____do__lift_3812_, 0);
lean_inc(v_val_3814_);
lean_dec_ref(v_____do__lift_3812_);
v___x_3815_ = lean_array_push(v_bs_3811_, v_val_3814_);
v___x_3816_ = lean_apply_2(v_toPure_3810_, lean_box(0), v___x_3815_);
return v___x_3816_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__1(lean_object* v_toPure_3817_, lean_object* v_f_3818_, lean_object* v_toBind_3819_, lean_object* v_bs_3820_, lean_object* v_a_3821_){
_start:
{
lean_object* v___f_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___f_3822_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3822_, 0, v_toPure_3817_);
lean_closure_set(v___f_3822_, 1, v_bs_3820_);
v___x_3823_ = lean_apply_1(v_f_3818_, v_a_3821_);
v___x_3824_ = lean_apply_4(v_toBind_3819_, lean_box(0), lean_box(0), v___x_3823_, v___f_3822_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg(lean_object* v_inst_3825_, lean_object* v_f_3826_, lean_object* v_as_3827_, lean_object* v_start_3828_, lean_object* v_stop_3829_){
_start:
{
lean_object* v_toApplicative_3830_; lean_object* v_toBind_3831_; lean_object* v_toPure_3832_; lean_object* v___x_3833_; uint8_t v___x_3834_; 
v_toApplicative_3830_ = lean_ctor_get(v_inst_3825_, 0);
v_toBind_3831_ = lean_ctor_get(v_inst_3825_, 1);
v_toPure_3832_ = lean_ctor_get(v_toApplicative_3830_, 1);
v___x_3833_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3834_ = lean_nat_dec_lt(v_start_3828_, v_stop_3829_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3835_; 
lean_inc(v_toPure_3832_);
lean_dec_ref(v_as_3827_);
lean_dec(v_f_3826_);
lean_dec_ref(v_inst_3825_);
v___x_3835_ = lean_apply_2(v_toPure_3832_, lean_box(0), v___x_3833_);
return v___x_3835_;
}
else
{
lean_object* v___f_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
lean_inc(v_toBind_3831_);
lean_inc(v_toPure_3832_);
v___f_3836_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3836_, 0, v_toPure_3832_);
lean_closure_set(v___f_3836_, 1, v_f_3826_);
lean_closure_set(v___f_3836_, 2, v_toBind_3831_);
v___x_3837_ = lean_array_get_size(v_as_3827_);
v___x_3838_ = lean_nat_dec_le(v_stop_3829_, v___x_3837_);
if (v___x_3838_ == 0)
{
uint8_t v___x_3839_; 
v___x_3839_ = lean_nat_dec_lt(v_start_3828_, v___x_3837_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; 
lean_inc(v_toPure_3832_);
lean_dec_ref(v___f_3836_);
lean_dec_ref(v_as_3827_);
lean_dec_ref(v_inst_3825_);
v___x_3840_ = lean_apply_2(v_toPure_3832_, lean_box(0), v___x_3833_);
return v___x_3840_;
}
else
{
size_t v___x_3841_; size_t v___x_3842_; lean_object* v___x_3843_; 
v___x_3841_ = lean_usize_of_nat(v_start_3828_);
v___x_3842_ = lean_usize_of_nat(v___x_3837_);
v___x_3843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3825_, v___f_3836_, v_as_3827_, v___x_3841_, v___x_3842_, v___x_3833_);
return v___x_3843_;
}
}
else
{
size_t v___x_3844_; size_t v___x_3845_; lean_object* v___x_3846_; 
v___x_3844_ = lean_usize_of_nat(v_start_3828_);
v___x_3845_ = lean_usize_of_nat(v_stop_3829_);
v___x_3846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3825_, v___f_3836_, v_as_3827_, v___x_3844_, v___x_3845_, v___x_3833_);
return v___x_3846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___boxed(lean_object* v_inst_3847_, lean_object* v_f_3848_, lean_object* v_as_3849_, lean_object* v_start_3850_, lean_object* v_stop_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_Array_filterMapM___redArg(v_inst_3847_, v_f_3848_, v_as_3849_, v_start_3850_, v_stop_3851_);
lean_dec(v_stop_3851_);
lean_dec(v_start_3850_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM(lean_object* v_00_u03b1_3853_, lean_object* v_m_3854_, lean_object* v_00_u03b2_3855_, lean_object* v_inst_3856_, lean_object* v_f_3857_, lean_object* v_as_3858_, lean_object* v_start_3859_, lean_object* v_stop_3860_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = l_Array_filterMapM___redArg(v_inst_3856_, v_f_3857_, v_as_3858_, v_start_3859_, v_stop_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___boxed(lean_object* v_00_u03b1_3862_, lean_object* v_m_3863_, lean_object* v_00_u03b2_3864_, lean_object* v_inst_3865_, lean_object* v_f_3866_, lean_object* v_as_3867_, lean_object* v_start_3868_, lean_object* v_stop_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_Array_filterMapM(v_00_u03b1_3862_, v_m_3863_, v_00_u03b2_3864_, v_inst_3865_, v_f_3866_, v_as_3867_, v_start_3868_, v_stop_3869_);
lean_dec(v_stop_3869_);
lean_dec(v_start_3868_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg(lean_object* v_f_3871_, lean_object* v_as_3872_, lean_object* v_start_3873_, lean_object* v_stop_3874_){
_start:
{
lean_object* v___f_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___f_3875_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3875_, 0, v_f_3871_);
v___x_3876_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3877_ = l_Array_filterMapM___redArg(v___x_3876_, v___f_3875_, v_as_3872_, v_start_3873_, v_stop_3874_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg___boxed(lean_object* v_f_3878_, lean_object* v_as_3879_, lean_object* v_start_3880_, lean_object* v_stop_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l_Array_filterMap___redArg(v_f_3878_, v_as_3879_, v_start_3880_, v_stop_3881_);
lean_dec(v_stop_3881_);
lean_dec(v_start_3880_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap(lean_object* v_00_u03b1_3883_, lean_object* v_00_u03b2_3884_, lean_object* v_f_3885_, lean_object* v_as_3886_, lean_object* v_start_3887_, lean_object* v_stop_3888_){
_start:
{
lean_object* v___f_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___f_3889_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3889_, 0, v_f_3885_);
v___x_3890_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3891_ = l_Array_filterMapM___redArg(v___x_3890_, v___f_3889_, v_as_3886_, v_start_3887_, v_stop_3888_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___boxed(lean_object* v_00_u03b1_3892_, lean_object* v_00_u03b2_3893_, lean_object* v_f_3894_, lean_object* v_as_3895_, lean_object* v_start_3896_, lean_object* v_stop_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Array_filterMap(v_00_u03b1_3892_, v_00_u03b2_3893_, v_f_3894_, v_as_3895_, v_start_3896_, v_stop_3897_);
lean_dec(v_stop_3897_);
lean_dec(v_start_3896_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg___lam__0(lean_object* v_lt_3899_, lean_object* v_x1_3900_, lean_object* v_x2_3901_){
_start:
{
lean_object* v___x_3902_; uint8_t v___x_3903_; 
lean_inc(v_x2_3901_);
lean_inc(v_x1_3900_);
v___x_3902_ = lean_apply_2(v_lt_3899_, v_x1_3900_, v_x2_3901_);
v___x_3903_ = lean_unbox(v___x_3902_);
if (v___x_3903_ == 0)
{
lean_dec(v_x2_3901_);
return v_x1_3900_;
}
else
{
lean_dec(v_x1_3900_);
return v_x2_3901_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg(lean_object* v_as_3904_, lean_object* v_lt_3905_){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; uint8_t v___x_3908_; 
v___x_3906_ = lean_unsigned_to_nat(0u);
v___x_3907_ = lean_array_get_size(v_as_3904_);
v___x_3908_ = lean_nat_dec_lt(v___x_3906_, v___x_3907_);
if (v___x_3908_ == 0)
{
lean_object* v___x_3909_; 
lean_dec_ref(v_lt_3905_);
lean_dec_ref(v_as_3904_);
v___x_3909_ = lean_box(0);
return v___x_3909_;
}
else
{
lean_object* v_a0_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; uint8_t v___x_3913_; 
v_a0_3910_ = lean_array_fget(v_as_3904_, v___x_3906_);
v___x_3911_ = lean_unsigned_to_nat(1u);
v___x_3912_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3913_ = lean_nat_dec_lt(v___x_3911_, v___x_3907_);
if (v___x_3913_ == 0)
{
lean_object* v___x_3914_; 
lean_dec_ref(v_lt_3905_);
lean_dec_ref(v_as_3904_);
v___x_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3914_, 0, v_a0_3910_);
return v___x_3914_;
}
else
{
lean_object* v___f_3915_; uint8_t v___x_3916_; 
v___f_3915_ = lean_alloc_closure((void*)(l_Array_getMax_x3f___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3915_, 0, v_lt_3905_);
v___x_3916_ = lean_nat_dec_le(v___x_3907_, v___x_3907_);
if (v___x_3916_ == 0)
{
if (v___x_3913_ == 0)
{
lean_object* v___x_3917_; 
lean_dec_ref(v___f_3915_);
lean_dec_ref(v_as_3904_);
v___x_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3917_, 0, v_a0_3910_);
return v___x_3917_;
}
else
{
size_t v___x_3918_; size_t v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3918_ = ((size_t)1ULL);
v___x_3919_ = lean_usize_of_nat(v___x_3907_);
v___x_3920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3912_, v___f_3915_, v_as_3904_, v___x_3918_, v___x_3919_, v_a0_3910_);
v___x_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
return v___x_3921_;
}
}
else
{
size_t v___x_3922_; size_t v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3922_ = ((size_t)1ULL);
v___x_3923_ = lean_usize_of_nat(v___x_3907_);
v___x_3924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3912_, v___f_3915_, v_as_3904_, v___x_3922_, v___x_3923_, v_a0_3910_);
v___x_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
return v___x_3925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f(lean_object* v_00_u03b1_3926_, lean_object* v_as_3927_, lean_object* v_lt_3928_){
_start:
{
lean_object* v___x_3929_; 
v___x_3929_ = l_Array_getMax_x3f___redArg(v_as_3927_, v_lt_3928_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg___lam__0(lean_object* v_p_3930_, lean_object* v_a_3931_, lean_object* v_x_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v_fst_3934_; lean_object* v_snd_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3951_; 
v_fst_3934_ = lean_ctor_get(v___y_3933_, 0);
v_snd_3935_ = lean_ctor_get(v___y_3933_, 1);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___y_3933_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3937_ = v___y_3933_;
v_isShared_3938_ = v_isSharedCheck_3951_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_snd_3935_);
lean_inc(v_fst_3934_);
lean_dec(v___y_3933_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3951_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3939_; uint8_t v___x_3940_; 
lean_inc(v_a_3931_);
v___x_3939_ = lean_apply_1(v_p_3930_, v_a_3931_);
v___x_3940_ = lean_unbox(v___x_3939_);
if (v___x_3940_ == 0)
{
lean_object* v___x_3941_; lean_object* v___x_3943_; 
v___x_3941_ = lean_array_push(v_snd_3935_, v_a_3931_);
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 1, v___x_3941_);
v___x_3943_ = v___x_3937_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_fst_3934_);
lean_ctor_set(v_reuseFailAlloc_3945_, 1, v___x_3941_);
v___x_3943_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
lean_object* v___x_3944_; 
v___x_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
return v___x_3944_;
}
}
else
{
lean_object* v___x_3946_; lean_object* v___x_3948_; 
v___x_3946_ = lean_array_push(v_fst_3934_, v_a_3931_);
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 0, v___x_3946_);
v___x_3948_ = v___x_3937_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3946_);
lean_ctor_set(v_reuseFailAlloc_3950_, 1, v_snd_3935_);
v___x_3948_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
lean_object* v___x_3949_; 
v___x_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
return v___x_3949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg(lean_object* v_p_3954_, lean_object* v_as_3955_){
_start:
{
lean_object* v___f_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; size_t v_sz_3959_; size_t v___x_3960_; lean_object* v___x_3961_; lean_object* v_fst_3962_; lean_object* v_snd_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
v___f_3956_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3956_, 0, v_p_3954_);
v___x_3957_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3958_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_3959_ = lean_array_size(v_as_3955_);
v___x_3960_ = ((size_t)0ULL);
v___x_3961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_3957_, v_as_3955_, v___f_3956_, v_sz_3959_, v___x_3960_, v___x_3958_);
v_fst_3962_ = lean_ctor_get(v___x_3961_, 0);
v_snd_3963_ = lean_ctor_get(v___x_3961_, 1);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3961_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_snd_3963_);
lean_inc(v_fst_3962_);
lean_dec(v___x_3961_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_fst_3962_);
lean_ctor_set(v_reuseFailAlloc_3969_, 1, v_snd_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition(lean_object* v_00_u03b1_3971_, lean_object* v_p_3972_, lean_object* v_as_3973_){
_start:
{
lean_object* v___f_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; size_t v_sz_3977_; size_t v___x_3978_; lean_object* v___x_3979_; lean_object* v_fst_3980_; lean_object* v_snd_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
v___f_3974_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3974_, 0, v_p_3972_);
v___x_3975_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3976_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_3977_ = lean_array_size(v_as_3973_);
v___x_3978_ = ((size_t)0ULL);
v___x_3979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_3975_, v_as_3973_, v___f_3974_, v_sz_3977_, v___x_3978_, v___x_3976_);
v_fst_3980_ = lean_ctor_get(v___x_3979_, 0);
v_snd_3981_ = lean_ctor_get(v___x_3979_, 1);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3979_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_snd_3981_);
lean_inc(v_fst_3980_);
lean_dec(v___x_3979_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_fst_3980_);
lean_ctor_set(v_reuseFailAlloc_3987_, 1, v_snd_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile___redArg(lean_object* v_p_3989_, lean_object* v_as_3990_){
_start:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; uint8_t v___x_3993_; 
v___x_3991_ = lean_unsigned_to_nat(0u);
v___x_3992_ = lean_array_get_size(v_as_3990_);
v___x_3993_ = lean_nat_dec_lt(v___x_3991_, v___x_3992_);
if (v___x_3993_ == 0)
{
lean_dec_ref(v_p_3989_);
return v_as_3990_;
}
else
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; uint8_t v___x_3998_; 
v___x_3994_ = lean_unsigned_to_nat(1u);
v___x_3995_ = lean_nat_sub(v___x_3992_, v___x_3994_);
v___x_3996_ = lean_array_fget_borrowed(v_as_3990_, v___x_3995_);
lean_dec(v___x_3995_);
lean_inc_ref(v_p_3989_);
lean_inc(v___x_3996_);
v___x_3997_ = lean_apply_1(v_p_3989_, v___x_3996_);
v___x_3998_ = lean_unbox(v___x_3997_);
if (v___x_3998_ == 0)
{
lean_dec_ref(v_p_3989_);
return v_as_3990_;
}
else
{
lean_object* v___x_3999_; 
v___x_3999_ = lean_array_pop(v_as_3990_);
v_as_3990_ = v___x_3999_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile(lean_object* v_00_u03b1_4001_, lean_object* v_p_4002_, lean_object* v_as_4003_){
_start:
{
lean_object* v___x_4004_; 
v___x_4004_ = l_Array_popWhile___redArg(v_p_4002_, v_as_4003_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(lean_object* v_p_4005_, lean_object* v_as_4006_, lean_object* v_i_4007_, lean_object* v_acc_4008_){
_start:
{
lean_object* v___x_4009_; uint8_t v___x_4010_; 
v___x_4009_ = lean_array_get_size(v_as_4006_);
v___x_4010_ = lean_nat_dec_lt(v_i_4007_, v___x_4009_);
if (v___x_4010_ == 0)
{
lean_dec(v_i_4007_);
lean_dec_ref(v_p_4005_);
return v_acc_4008_;
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4012_; uint8_t v___x_4013_; 
v_a_4011_ = lean_array_fget_borrowed(v_as_4006_, v_i_4007_);
lean_inc_ref(v_p_4005_);
lean_inc(v_a_4011_);
v___x_4012_ = lean_apply_1(v_p_4005_, v_a_4011_);
v___x_4013_ = lean_unbox(v___x_4012_);
if (v___x_4013_ == 0)
{
lean_dec(v_i_4007_);
lean_dec_ref(v_p_4005_);
return v_acc_4008_;
}
else
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4014_ = lean_unsigned_to_nat(1u);
v___x_4015_ = lean_nat_add(v_i_4007_, v___x_4014_);
lean_dec(v_i_4007_);
lean_inc(v_a_4011_);
v___x_4016_ = lean_array_push(v_acc_4008_, v_a_4011_);
v_i_4007_ = v___x_4015_;
v_acc_4008_ = v___x_4016_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg___boxed(lean_object* v_p_4018_, lean_object* v_as_4019_, lean_object* v_i_4020_, lean_object* v_acc_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4018_, v_as_4019_, v_i_4020_, v_acc_4021_);
lean_dec_ref(v_as_4019_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(lean_object* v_00_u03b1_4023_, lean_object* v_p_4024_, lean_object* v_as_4025_, lean_object* v_i_4026_, lean_object* v_acc_4027_){
_start:
{
lean_object* v___x_4028_; 
v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4024_, v_as_4025_, v_i_4026_, v_acc_4027_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___boxed(lean_object* v_00_u03b1_4029_, lean_object* v_p_4030_, lean_object* v_as_4031_, lean_object* v_i_4032_, lean_object* v_acc_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(v_00_u03b1_4029_, v_p_4030_, v_as_4031_, v_i_4032_, v_acc_4033_);
lean_dec_ref(v_as_4031_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg(lean_object* v_p_4035_, lean_object* v_as_4036_){
_start:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4037_ = lean_unsigned_to_nat(0u);
v___x_4038_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4039_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4035_, v_as_4036_, v___x_4037_, v___x_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg___boxed(lean_object* v_p_4040_, lean_object* v_as_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l_Array_takeWhile___redArg(v_p_4040_, v_as_4041_);
lean_dec_ref(v_as_4041_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile(lean_object* v_00_u03b1_4043_, lean_object* v_p_4044_, lean_object* v_as_4045_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Array_takeWhile___redArg(v_p_4044_, v_as_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___boxed(lean_object* v_00_u03b1_4047_, lean_object* v_p_4048_, lean_object* v_as_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Array_takeWhile(v_00_u03b1_4047_, v_p_4048_, v_as_4049_);
lean_dec_ref(v_as_4049_);
return v_res_4050_;
}
}
static lean_object* _init_l_Array_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx___redArg(lean_object* v_xs_4052_, lean_object* v_i_4053_){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; 
v___x_4054_ = lean_unsigned_to_nat(1u);
v___x_4055_ = lean_nat_add(v_i_4053_, v___x_4054_);
v___x_4056_ = lean_array_get_size(v_xs_4052_);
v___x_4057_ = lean_nat_dec_lt(v___x_4055_, v___x_4056_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4058_; 
lean_dec(v___x_4055_);
lean_dec(v_i_4053_);
v___x_4058_ = lean_array_pop(v_xs_4052_);
return v___x_4058_;
}
else
{
lean_object* v_xs_x27_4059_; 
v_xs_x27_4059_ = lean_array_fswap(v_xs_4052_, v___x_4055_, v_i_4053_);
lean_dec(v_i_4053_);
v_xs_4052_ = v_xs_x27_4059_;
v_i_4053_ = v___x_4055_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx(lean_object* v_00_u03b1_4061_, lean_object* v_xs_4062_, lean_object* v_i_4063_, lean_object* v_h_4064_){
_start:
{
lean_object* v___x_4065_; 
v___x_4065_ = l_Array_eraseIdx___redArg(v_xs_4062_, v_i_4063_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds___redArg(lean_object* v_xs_4066_, lean_object* v_i_4067_){
_start:
{
lean_object* v___x_4068_; uint8_t v___x_4069_; 
v___x_4068_ = lean_array_get_size(v_xs_4066_);
v___x_4069_ = lean_nat_dec_lt(v_i_4067_, v___x_4068_);
if (v___x_4069_ == 0)
{
lean_dec(v_i_4067_);
return v_xs_4066_;
}
else
{
lean_object* v___x_4070_; 
v___x_4070_ = l_Array_eraseIdx___redArg(v_xs_4066_, v_i_4067_);
return v___x_4070_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds(lean_object* v_00_u03b1_4071_, lean_object* v_xs_4072_, lean_object* v_i_4073_){
_start:
{
lean_object* v___x_4074_; 
v___x_4074_ = l_Array_eraseIdxIfInBounds___redArg(v_xs_4072_, v_i_4073_);
return v___x_4074_;
}
}
static lean_object* _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Array_instInhabited(lean_box(0));
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(lean_object* v_msg_4076_){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = lean_obj_once(&l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0, &l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0_once, _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0);
v___x_4078_ = lean_panic_fn_borrowed(v___x_4077_, v_msg_4076_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0(lean_object* v_00_u03b1_4079_, lean_object* v_msg_4080_){
_start:
{
lean_object* v___x_4081_; 
v___x_4081_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v_msg_4080_);
return v___x_4081_;
}
}
static lean_object* _init_l_Array_eraseIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4084_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4085_ = lean_unsigned_to_nat(47u);
v___x_4086_ = lean_unsigned_to_nat(1808u);
v___x_4087_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__0));
v___x_4088_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4089_ = l_mkPanicMessageWithDecl(v___x_4088_, v___x_4087_, v___x_4086_, v___x_4085_, v___x_4084_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21___redArg(lean_object* v_xs_4090_, lean_object* v_i_4091_){
_start:
{
lean_object* v___x_4092_; uint8_t v___x_4093_; 
v___x_4092_ = lean_array_get_size(v_xs_4090_);
v___x_4093_ = lean_nat_dec_lt(v_i_4091_, v___x_4092_);
if (v___x_4093_ == 0)
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
lean_dec(v_i_4091_);
lean_dec_ref(v_xs_4090_);
v___x_4094_ = lean_obj_once(&l_Array_eraseIdx_x21___redArg___closed__2, &l_Array_eraseIdx_x21___redArg___closed__2_once, _init_l_Array_eraseIdx_x21___redArg___closed__2);
v___x_4095_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4094_);
return v___x_4095_;
}
else
{
lean_object* v___x_4096_; 
v___x_4096_ = l_Array_eraseIdx___redArg(v_xs_4090_, v_i_4091_);
return v___x_4096_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21(lean_object* v_00_u03b1_4097_, lean_object* v_xs_4098_, lean_object* v_i_4099_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Array_eraseIdx_x21___redArg(v_xs_4098_, v_i_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Array_erase___redArg(lean_object* v_inst_4101_, lean_object* v_as_4102_, lean_object* v_a_4103_){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = l_Array_finIdxOf_x3f___redArg(v_inst_4101_, v_as_4102_, v_a_4103_);
if (lean_obj_tag(v___x_4104_) == 0)
{
return v_as_4102_;
}
else
{
lean_object* v_val_4105_; lean_object* v___x_4106_; 
v_val_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc(v_val_4105_);
lean_dec_ref(v___x_4104_);
v___x_4106_ = l_Array_eraseIdx___redArg(v_as_4102_, v_val_4105_);
return v___x_4106_;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase(lean_object* v_00_u03b1_4107_, lean_object* v_inst_4108_, lean_object* v_as_4109_, lean_object* v_a_4110_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Array_erase___redArg(v_inst_4108_, v_as_4109_, v_a_4110_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseP___redArg(lean_object* v_as_4112_, lean_object* v_p_4113_){
_start:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4114_ = lean_unsigned_to_nat(0u);
v___x_4115_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_4113_, v_as_4112_, v___x_4114_);
if (lean_obj_tag(v___x_4115_) == 0)
{
return v_as_4112_;
}
else
{
lean_object* v_val_4116_; lean_object* v___x_4117_; 
v_val_4116_ = lean_ctor_get(v___x_4115_, 0);
lean_inc(v_val_4116_);
lean_dec_ref(v___x_4115_);
v___x_4117_ = l_Array_eraseIdx___redArg(v_as_4112_, v_val_4116_);
return v___x_4117_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseP(lean_object* v_00_u03b1_4118_, lean_object* v_as_4119_, lean_object* v_p_4120_){
_start:
{
lean_object* v___x_4121_; 
v___x_4121_ = l_Array_eraseP___redArg(v_as_4119_, v_p_4120_);
return v___x_4121_;
}
}
static lean_object* _init_l_Array_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_4122_; 
v___x_4122_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(lean_object* v_i_4123_, lean_object* v_as_4124_, lean_object* v_j_4125_){
_start:
{
uint8_t v___x_4126_; 
v___x_4126_ = lean_nat_dec_lt(v_i_4123_, v_j_4125_);
if (v___x_4126_ == 0)
{
lean_dec(v_j_4125_);
return v_as_4124_;
}
else
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v_as_4129_; 
v___x_4127_ = lean_unsigned_to_nat(1u);
v___x_4128_ = lean_nat_sub(v_j_4125_, v___x_4127_);
v_as_4129_ = lean_array_fswap(v_as_4124_, v___x_4128_, v_j_4125_);
lean_dec(v_j_4125_);
v_as_4124_ = v_as_4129_;
v_j_4125_ = v___x_4128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg___boxed(lean_object* v_i_4131_, lean_object* v_as_4132_, lean_object* v_j_4133_){
_start:
{
lean_object* v_res_4134_; 
v_res_4134_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4131_, v_as_4132_, v_j_4133_);
lean_dec(v_i_4131_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object* v_00_u03b1_4135_, lean_object* v_i_4136_, lean_object* v_as_4137_, lean_object* v_j_4138_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4136_, v_as_4137_, v_j_4138_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___boxed(lean_object* v_00_u03b1_4140_, lean_object* v_i_4141_, lean_object* v_as_4142_, lean_object* v_j_4143_){
_start:
{
lean_object* v_res_4144_; 
v_res_4144_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(v_00_u03b1_4140_, v_i_4141_, v_as_4142_, v_j_4143_);
lean_dec(v_i_4141_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg(lean_object* v_as_4145_, lean_object* v_i_4146_, lean_object* v_a_4147_){
_start:
{
lean_object* v_j_4148_; lean_object* v_as_4149_; lean_object* v___x_4150_; 
v_j_4148_ = lean_array_get_size(v_as_4145_);
v_as_4149_ = lean_array_push(v_as_4145_, v_a_4147_);
v___x_4150_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4146_, v_as_4149_, v_j_4148_);
return v___x_4150_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg___boxed(lean_object* v_as_4151_, lean_object* v_i_4152_, lean_object* v_a_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_Array_insertIdx___redArg(v_as_4151_, v_i_4152_, v_a_4153_);
lean_dec(v_i_4152_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx(lean_object* v_00_u03b1_4155_, lean_object* v_as_4156_, lean_object* v_i_4157_, lean_object* v_a_4158_, lean_object* v_x_4159_){
_start:
{
lean_object* v_j_4160_; lean_object* v_as_4161_; lean_object* v___x_4162_; 
v_j_4160_ = lean_array_get_size(v_as_4156_);
v_as_4161_ = lean_array_push(v_as_4156_, v_a_4158_);
v___x_4162_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4157_, v_as_4161_, v_j_4160_);
return v___x_4162_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___boxed(lean_object* v_00_u03b1_4163_, lean_object* v_as_4164_, lean_object* v_i_4165_, lean_object* v_a_4166_, lean_object* v_x_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Array_insertIdx(v_00_u03b1_4163_, v_as_4164_, v_i_4165_, v_a_4166_, v_x_4167_);
lean_dec(v_i_4165_);
return v_res_4168_;
}
}
static lean_object* _init_l_Array_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4170_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4171_ = lean_unsigned_to_nat(7u);
v___x_4172_ = lean_unsigned_to_nat(1890u);
v___x_4173_ = ((lean_object*)(l_Array_insertIdx_x21___redArg___closed__0));
v___x_4174_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4175_ = l_mkPanicMessageWithDecl(v___x_4174_, v___x_4173_, v___x_4172_, v___x_4171_, v___x_4170_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg(lean_object* v_as_4176_, lean_object* v_i_4177_, lean_object* v_a_4178_){
_start:
{
lean_object* v___x_4179_; uint8_t v___x_4180_; 
v___x_4179_ = lean_array_get_size(v_as_4176_);
v___x_4180_ = lean_nat_dec_le(v_i_4177_, v___x_4179_);
if (v___x_4180_ == 0)
{
lean_object* v___x_4181_; lean_object* v___x_4182_; 
lean_dec(v_a_4178_);
lean_dec_ref(v_as_4176_);
v___x_4181_ = lean_obj_once(&l_Array_insertIdx_x21___redArg___closed__1, &l_Array_insertIdx_x21___redArg___closed__1_once, _init_l_Array_insertIdx_x21___redArg___closed__1);
v___x_4182_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4181_);
return v___x_4182_;
}
else
{
lean_object* v_as_4183_; lean_object* v___x_4184_; 
v_as_4183_ = lean_array_push(v_as_4176_, v_a_4178_);
v___x_4184_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4177_, v_as_4183_, v___x_4179_);
return v___x_4184_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg___boxed(lean_object* v_as_4185_, lean_object* v_i_4186_, lean_object* v_a_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_Array_insertIdx_x21___redArg(v_as_4185_, v_i_4186_, v_a_4187_);
lean_dec(v_i_4186_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21(lean_object* v_00_u03b1_4189_, lean_object* v_as_4190_, lean_object* v_i_4191_, lean_object* v_a_4192_){
_start:
{
lean_object* v___x_4193_; 
v___x_4193_ = l_Array_insertIdx_x21___redArg(v_as_4190_, v_i_4191_, v_a_4192_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___boxed(lean_object* v_00_u03b1_4194_, lean_object* v_as_4195_, lean_object* v_i_4196_, lean_object* v_a_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l_Array_insertIdx_x21(v_00_u03b1_4194_, v_as_4195_, v_i_4196_, v_a_4197_);
lean_dec(v_i_4196_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg(lean_object* v_as_4199_, lean_object* v_i_4200_, lean_object* v_a_4201_){
_start:
{
lean_object* v___x_4202_; uint8_t v___x_4203_; 
v___x_4202_ = lean_array_get_size(v_as_4199_);
v___x_4203_ = lean_nat_dec_le(v_i_4200_, v___x_4202_);
if (v___x_4203_ == 0)
{
lean_dec(v_a_4201_);
return v_as_4199_;
}
else
{
lean_object* v_as_4204_; lean_object* v___x_4205_; 
v_as_4204_ = lean_array_push(v_as_4199_, v_a_4201_);
v___x_4205_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4200_, v_as_4204_, v___x_4202_);
return v___x_4205_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg___boxed(lean_object* v_as_4206_, lean_object* v_i_4207_, lean_object* v_a_4208_){
_start:
{
lean_object* v_res_4209_; 
v_res_4209_ = l_Array_insertIdxIfInBounds___redArg(v_as_4206_, v_i_4207_, v_a_4208_);
lean_dec(v_i_4207_);
return v_res_4209_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds(lean_object* v_00_u03b1_4210_, lean_object* v_as_4211_, lean_object* v_i_4212_, lean_object* v_a_4213_){
_start:
{
lean_object* v___x_4214_; 
v___x_4214_ = l_Array_insertIdxIfInBounds___redArg(v_as_4211_, v_i_4212_, v_a_4213_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___boxed(lean_object* v_00_u03b1_4215_, lean_object* v_as_4216_, lean_object* v_i_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_Array_insertIdxIfInBounds(v_00_u03b1_4215_, v_as_4216_, v_i_4217_, v_a_4218_);
lean_dec(v_i_4217_);
return v_res_4219_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux___redArg(lean_object* v_inst_4220_, lean_object* v_as_4221_, lean_object* v_bs_4222_, lean_object* v_i_4223_){
_start:
{
lean_object* v___x_4224_; uint8_t v___x_4225_; 
v___x_4224_ = lean_array_get_size(v_as_4221_);
v___x_4225_ = lean_nat_dec_lt(v_i_4223_, v___x_4224_);
if (v___x_4225_ == 0)
{
uint8_t v___x_4226_; 
lean_dec(v_i_4223_);
lean_dec_ref(v_inst_4220_);
v___x_4226_ = 1;
return v___x_4226_;
}
else
{
lean_object* v_a_4227_; lean_object* v_b_4228_; lean_object* v___x_4229_; uint8_t v___x_4230_; 
v_a_4227_ = lean_array_fget_borrowed(v_as_4221_, v_i_4223_);
v_b_4228_ = lean_array_fget_borrowed(v_bs_4222_, v_i_4223_);
lean_inc_ref(v_inst_4220_);
lean_inc(v_b_4228_);
lean_inc(v_a_4227_);
v___x_4229_ = lean_apply_2(v_inst_4220_, v_a_4227_, v_b_4228_);
v___x_4230_ = lean_unbox(v___x_4229_);
if (v___x_4230_ == 0)
{
uint8_t v___x_4231_; 
lean_dec(v_i_4223_);
lean_dec_ref(v_inst_4220_);
v___x_4231_ = lean_unbox(v___x_4229_);
return v___x_4231_;
}
else
{
lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4232_ = lean_unsigned_to_nat(1u);
v___x_4233_ = lean_nat_add(v_i_4223_, v___x_4232_);
lean_dec(v_i_4223_);
v_i_4223_ = v___x_4233_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___redArg___boxed(lean_object* v_inst_4235_, lean_object* v_as_4236_, lean_object* v_bs_4237_, lean_object* v_i_4238_){
_start:
{
uint8_t v_res_4239_; lean_object* v_r_4240_; 
v_res_4239_ = l_Array_isPrefixOfAux___redArg(v_inst_4235_, v_as_4236_, v_bs_4237_, v_i_4238_);
lean_dec_ref(v_bs_4237_);
lean_dec_ref(v_as_4236_);
v_r_4240_ = lean_box(v_res_4239_);
return v_r_4240_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux(lean_object* v_00_u03b1_4241_, lean_object* v_inst_4242_, lean_object* v_as_4243_, lean_object* v_bs_4244_, lean_object* v_hle_4245_, lean_object* v_i_4246_){
_start:
{
uint8_t v___x_4247_; 
v___x_4247_ = l_Array_isPrefixOfAux___redArg(v_inst_4242_, v_as_4243_, v_bs_4244_, v_i_4246_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___boxed(lean_object* v_00_u03b1_4248_, lean_object* v_inst_4249_, lean_object* v_as_4250_, lean_object* v_bs_4251_, lean_object* v_hle_4252_, lean_object* v_i_4253_){
_start:
{
uint8_t v_res_4254_; lean_object* v_r_4255_; 
v_res_4254_ = l_Array_isPrefixOfAux(v_00_u03b1_4248_, v_inst_4249_, v_as_4250_, v_bs_4251_, v_hle_4252_, v_i_4253_);
lean_dec_ref(v_bs_4251_);
lean_dec_ref(v_as_4250_);
v_r_4255_ = lean_box(v_res_4254_);
return v_r_4255_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf___redArg(lean_object* v_inst_4256_, lean_object* v_as_4257_, lean_object* v_bs_4258_){
_start:
{
lean_object* v___x_4259_; lean_object* v___x_4260_; uint8_t v___x_4261_; 
v___x_4259_ = lean_array_get_size(v_as_4257_);
v___x_4260_ = lean_array_get_size(v_bs_4258_);
v___x_4261_ = lean_nat_dec_le(v___x_4259_, v___x_4260_);
if (v___x_4261_ == 0)
{
lean_dec_ref(v_inst_4256_);
return v___x_4261_;
}
else
{
lean_object* v___x_4262_; uint8_t v___x_4263_; 
v___x_4262_ = lean_unsigned_to_nat(0u);
v___x_4263_ = l_Array_isPrefixOfAux___redArg(v_inst_4256_, v_as_4257_, v_bs_4258_, v___x_4262_);
return v___x_4263_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___redArg___boxed(lean_object* v_inst_4264_, lean_object* v_as_4265_, lean_object* v_bs_4266_){
_start:
{
uint8_t v_res_4267_; lean_object* v_r_4268_; 
v_res_4267_ = l_Array_isPrefixOf___redArg(v_inst_4264_, v_as_4265_, v_bs_4266_);
lean_dec_ref(v_bs_4266_);
lean_dec_ref(v_as_4265_);
v_r_4268_ = lean_box(v_res_4267_);
return v_r_4268_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf(lean_object* v_00_u03b1_4269_, lean_object* v_inst_4270_, lean_object* v_as_4271_, lean_object* v_bs_4272_){
_start:
{
uint8_t v___x_4273_; 
v___x_4273_ = l_Array_isPrefixOf___redArg(v_inst_4270_, v_as_4271_, v_bs_4272_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___boxed(lean_object* v_00_u03b1_4274_, lean_object* v_inst_4275_, lean_object* v_as_4276_, lean_object* v_bs_4277_){
_start:
{
uint8_t v_res_4278_; lean_object* v_r_4279_; 
v_res_4278_ = l_Array_isPrefixOf(v_00_u03b1_4274_, v_inst_4275_, v_as_4276_, v_bs_4277_);
lean_dec_ref(v_bs_4277_);
lean_dec_ref(v_as_4276_);
v_r_4279_ = lean_box(v_res_4278_);
return v_r_4279_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0___boxed(lean_object* v_i_4280_, lean_object* v_cs_4281_, lean_object* v_inst_4282_, lean_object* v_as_4283_, lean_object* v_bs_4284_, lean_object* v_f_4285_, lean_object* v_____do__lift_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l_Array_zipWithMAux___redArg___lam__0(v_i_4280_, v_cs_4281_, v_inst_4282_, v_as_4283_, v_bs_4284_, v_f_4285_, v_____do__lift_4286_);
lean_dec(v_i_4280_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg(lean_object* v_inst_4288_, lean_object* v_as_4289_, lean_object* v_bs_4290_, lean_object* v_f_4291_, lean_object* v_i_4292_, lean_object* v_cs_4293_){
_start:
{
lean_object* v___x_4294_; uint8_t v___x_4295_; 
v___x_4294_ = lean_array_get_size(v_as_4289_);
v___x_4295_ = lean_nat_dec_lt(v_i_4292_, v___x_4294_);
if (v___x_4295_ == 0)
{
lean_object* v_toApplicative_4296_; lean_object* v_toPure_4297_; lean_object* v___x_4298_; 
lean_dec(v_i_4292_);
lean_dec(v_f_4291_);
lean_dec_ref(v_bs_4290_);
lean_dec_ref(v_as_4289_);
v_toApplicative_4296_ = lean_ctor_get(v_inst_4288_, 0);
lean_inc_ref(v_toApplicative_4296_);
lean_dec_ref(v_inst_4288_);
v_toPure_4297_ = lean_ctor_get(v_toApplicative_4296_, 1);
lean_inc(v_toPure_4297_);
lean_dec_ref(v_toApplicative_4296_);
v___x_4298_ = lean_apply_2(v_toPure_4297_, lean_box(0), v_cs_4293_);
return v___x_4298_;
}
else
{
lean_object* v___x_4299_; uint8_t v___x_4300_; 
v___x_4299_ = lean_array_get_size(v_bs_4290_);
v___x_4300_ = lean_nat_dec_lt(v_i_4292_, v___x_4299_);
if (v___x_4300_ == 0)
{
lean_object* v_toApplicative_4301_; lean_object* v_toPure_4302_; lean_object* v___x_4303_; 
lean_dec(v_i_4292_);
lean_dec(v_f_4291_);
lean_dec_ref(v_bs_4290_);
lean_dec_ref(v_as_4289_);
v_toApplicative_4301_ = lean_ctor_get(v_inst_4288_, 0);
lean_inc_ref(v_toApplicative_4301_);
lean_dec_ref(v_inst_4288_);
v_toPure_4302_ = lean_ctor_get(v_toApplicative_4301_, 1);
lean_inc(v_toPure_4302_);
lean_dec_ref(v_toApplicative_4301_);
v___x_4303_ = lean_apply_2(v_toPure_4302_, lean_box(0), v_cs_4293_);
return v___x_4303_;
}
else
{
lean_object* v_toBind_4304_; lean_object* v___f_4305_; lean_object* v_a_4306_; lean_object* v_b_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v_toBind_4304_ = lean_ctor_get(v_inst_4288_, 1);
lean_inc(v_toBind_4304_);
lean_inc(v_f_4291_);
lean_inc_ref(v_bs_4290_);
lean_inc_ref(v_as_4289_);
lean_inc(v_i_4292_);
v___f_4305_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4305_, 0, v_i_4292_);
lean_closure_set(v___f_4305_, 1, v_cs_4293_);
lean_closure_set(v___f_4305_, 2, v_inst_4288_);
lean_closure_set(v___f_4305_, 3, v_as_4289_);
lean_closure_set(v___f_4305_, 4, v_bs_4290_);
lean_closure_set(v___f_4305_, 5, v_f_4291_);
v_a_4306_ = lean_array_fget(v_as_4289_, v_i_4292_);
lean_dec_ref(v_as_4289_);
v_b_4307_ = lean_array_fget(v_bs_4290_, v_i_4292_);
lean_dec(v_i_4292_);
lean_dec_ref(v_bs_4290_);
v___x_4308_ = lean_apply_2(v_f_4291_, v_a_4306_, v_b_4307_);
v___x_4309_ = lean_apply_4(v_toBind_4304_, lean_box(0), lean_box(0), v___x_4308_, v___f_4305_);
return v___x_4309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0(lean_object* v_i_4310_, lean_object* v_cs_4311_, lean_object* v_inst_4312_, lean_object* v_as_4313_, lean_object* v_bs_4314_, lean_object* v_f_4315_, lean_object* v_____do__lift_4316_){
_start:
{
lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4317_ = lean_unsigned_to_nat(1u);
v___x_4318_ = lean_nat_add(v_i_4310_, v___x_4317_);
v___x_4319_ = lean_array_push(v_cs_4311_, v_____do__lift_4316_);
v___x_4320_ = l_Array_zipWithMAux___redArg(v_inst_4312_, v_as_4313_, v_bs_4314_, v_f_4315_, v___x_4318_, v___x_4319_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux(lean_object* v_00_u03b1_4321_, lean_object* v_00_u03b2_4322_, lean_object* v_00_u03b3_4323_, lean_object* v_m_4324_, lean_object* v_inst_4325_, lean_object* v_as_4326_, lean_object* v_bs_4327_, lean_object* v_f_4328_, lean_object* v_i_4329_, lean_object* v_cs_4330_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_Array_zipWithMAux___redArg(v_inst_4325_, v_as_4326_, v_bs_4327_, v_f_4328_, v_i_4329_, v_cs_4330_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith___redArg(lean_object* v_f_4332_, lean_object* v_as_4333_, lean_object* v_bs_4334_){
_start:
{
lean_object* v___f_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___f_4335_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4335_, 0, v_f_4332_);
v___x_4336_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4337_ = lean_unsigned_to_nat(0u);
v___x_4338_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4339_ = l_Array_zipWithMAux___redArg(v___x_4336_, v_as_4333_, v_bs_4334_, v___f_4335_, v___x_4337_, v___x_4338_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith(lean_object* v_00_u03b1_4340_, lean_object* v_00_u03b2_4341_, lean_object* v_00_u03b3_4342_, lean_object* v_f_4343_, lean_object* v_as_4344_, lean_object* v_bs_4345_){
_start:
{
lean_object* v___f_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___f_4346_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4346_, 0, v_f_4343_);
v___x_4347_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4348_ = lean_unsigned_to_nat(0u);
v___x_4349_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4350_ = l_Array_zipWithMAux___redArg(v___x_4347_, v_as_4344_, v_bs_4345_, v___f_4346_, v___x_4348_, v___x_4349_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(lean_object* v_as_4351_, lean_object* v_bs_4352_, lean_object* v_i_4353_, lean_object* v_cs_4354_){
_start:
{
lean_object* v___x_4355_; uint8_t v___x_4356_; 
v___x_4355_ = lean_array_get_size(v_as_4351_);
v___x_4356_ = lean_nat_dec_lt(v_i_4353_, v___x_4355_);
if (v___x_4356_ == 0)
{
lean_dec(v_i_4353_);
return v_cs_4354_;
}
else
{
lean_object* v___x_4357_; uint8_t v___x_4358_; 
v___x_4357_ = lean_array_get_size(v_bs_4352_);
v___x_4358_ = lean_nat_dec_lt(v_i_4353_, v___x_4357_);
if (v___x_4358_ == 0)
{
lean_dec(v_i_4353_);
return v_cs_4354_;
}
else
{
lean_object* v_a_4359_; lean_object* v_b_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v_a_4359_ = lean_array_fget_borrowed(v_as_4351_, v_i_4353_);
v_b_4360_ = lean_array_fget_borrowed(v_bs_4352_, v_i_4353_);
lean_inc(v_b_4360_);
lean_inc(v_a_4359_);
v___x_4361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4361_, 0, v_a_4359_);
lean_ctor_set(v___x_4361_, 1, v_b_4360_);
v___x_4362_ = lean_unsigned_to_nat(1u);
v___x_4363_ = lean_nat_add(v_i_4353_, v___x_4362_);
lean_dec(v_i_4353_);
v___x_4364_ = lean_array_push(v_cs_4354_, v___x_4361_);
v_i_4353_ = v___x_4363_;
v_cs_4354_ = v___x_4364_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg___boxed(lean_object* v_as_4366_, lean_object* v_bs_4367_, lean_object* v_i_4368_, lean_object* v_cs_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4366_, v_bs_4367_, v_i_4368_, v_cs_4369_);
lean_dec_ref(v_bs_4367_);
lean_dec_ref(v_as_4366_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg(lean_object* v_as_4373_, lean_object* v_bs_4374_){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4375_ = lean_unsigned_to_nat(0u);
v___x_4376_ = ((lean_object*)(l_Array_zip___redArg___closed__0));
v___x_4377_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4373_, v_bs_4374_, v___x_4375_, v___x_4376_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg___boxed(lean_object* v_as_4378_, lean_object* v_bs_4379_){
_start:
{
lean_object* v_res_4380_; 
v_res_4380_ = l_Array_zip___redArg(v_as_4378_, v_bs_4379_);
lean_dec_ref(v_bs_4379_);
lean_dec_ref(v_as_4378_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l_Array_zip(lean_object* v_00_u03b1_4381_, lean_object* v_00_u03b2_4382_, lean_object* v_as_4383_, lean_object* v_bs_4384_){
_start:
{
lean_object* v___x_4385_; 
v___x_4385_ = l_Array_zip___redArg(v_as_4383_, v_bs_4384_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___boxed(lean_object* v_00_u03b1_4386_, lean_object* v_00_u03b2_4387_, lean_object* v_as_4388_, lean_object* v_bs_4389_){
_start:
{
lean_object* v_res_4390_; 
v_res_4390_ = l_Array_zip(v_00_u03b1_4386_, v_00_u03b2_4387_, v_as_4388_, v_bs_4389_);
lean_dec_ref(v_bs_4389_);
lean_dec_ref(v_as_4388_);
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0(lean_object* v_00_u03b1_4391_, lean_object* v_00_u03b2_4392_, lean_object* v_as_4393_, lean_object* v_bs_4394_, lean_object* v_i_4395_, lean_object* v_cs_4396_){
_start:
{
lean_object* v___x_4397_; 
v___x_4397_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4393_, v_bs_4394_, v_i_4395_, v_cs_4396_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___boxed(lean_object* v_00_u03b1_4398_, lean_object* v_00_u03b2_4399_, lean_object* v_as_4400_, lean_object* v_bs_4401_, lean_object* v_i_4402_, lean_object* v_cs_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Array_zipWithMAux___at___00Array_zip_spec__0(v_00_u03b1_4398_, v_00_u03b2_4399_, v_as_4400_, v_bs_4401_, v_i_4402_, v_cs_4403_);
lean_dec_ref(v_bs_4401_);
lean_dec_ref(v_as_4400_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(lean_object* v_f_4405_, lean_object* v_as_4406_, lean_object* v_bs_4407_, lean_object* v_i_4408_, lean_object* v_cs_4409_){
_start:
{
lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4419_; lean_object* v___y_4426_; lean_object* v___x_4433_; lean_object* v___x_4434_; uint8_t v___x_4435_; 
v___x_4433_ = lean_array_get_size(v_as_4406_);
v___x_4434_ = lean_array_get_size(v_bs_4407_);
v___x_4435_ = lean_nat_dec_le(v___x_4433_, v___x_4434_);
if (v___x_4435_ == 0)
{
v___y_4426_ = v___x_4433_;
goto v___jp_4425_;
}
else
{
v___y_4426_ = v___x_4434_;
goto v___jp_4425_;
}
v___jp_4410_:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4413_ = lean_unsigned_to_nat(1u);
v___x_4414_ = lean_nat_add(v_i_4408_, v___x_4413_);
lean_dec(v_i_4408_);
lean_inc(v_f_4405_);
v___x_4415_ = lean_apply_2(v_f_4405_, v___y_4411_, v___y_4412_);
v___x_4416_ = lean_array_push(v_cs_4409_, v___x_4415_);
v_i_4408_ = v___x_4414_;
v_cs_4409_ = v___x_4416_;
goto _start;
}
v___jp_4418_:
{
lean_object* v___x_4420_; uint8_t v___x_4421_; 
v___x_4420_ = lean_array_get_size(v_bs_4407_);
v___x_4421_ = lean_nat_dec_lt(v_i_4408_, v___x_4420_);
if (v___x_4421_ == 0)
{
lean_object* v___x_4422_; 
v___x_4422_ = lean_box(0);
v___y_4411_ = v___y_4419_;
v___y_4412_ = v___x_4422_;
goto v___jp_4410_;
}
else
{
lean_object* v___x_4423_; lean_object* v___x_4424_; 
v___x_4423_ = lean_array_fget_borrowed(v_bs_4407_, v_i_4408_);
lean_inc(v___x_4423_);
v___x_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4424_, 0, v___x_4423_);
v___y_4411_ = v___y_4419_;
v___y_4412_ = v___x_4424_;
goto v___jp_4410_;
}
}
v___jp_4425_:
{
uint8_t v___x_4427_; 
v___x_4427_ = lean_nat_dec_lt(v_i_4408_, v___y_4426_);
lean_dec(v___y_4426_);
if (v___x_4427_ == 0)
{
lean_dec(v_i_4408_);
lean_dec(v_f_4405_);
return v_cs_4409_;
}
else
{
lean_object* v___x_4428_; uint8_t v___x_4429_; 
v___x_4428_ = lean_array_get_size(v_as_4406_);
v___x_4429_ = lean_nat_dec_lt(v_i_4408_, v___x_4428_);
if (v___x_4429_ == 0)
{
lean_object* v___x_4430_; 
v___x_4430_ = lean_box(0);
v___y_4419_ = v___x_4430_;
goto v___jp_4418_;
}
else
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4431_ = lean_array_fget_borrowed(v_as_4406_, v_i_4408_);
lean_inc(v___x_4431_);
v___x_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4431_);
v___y_4419_ = v___x_4432_;
goto v___jp_4418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg___boxed(lean_object* v_f_4436_, lean_object* v_as_4437_, lean_object* v_bs_4438_, lean_object* v_i_4439_, lean_object* v_cs_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4436_, v_as_4437_, v_bs_4438_, v_i_4439_, v_cs_4440_);
lean_dec_ref(v_bs_4438_);
lean_dec_ref(v_as_4437_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(lean_object* v_00_u03b1_4442_, lean_object* v_00_u03b2_4443_, lean_object* v_00_u03b3_4444_, lean_object* v_f_4445_, lean_object* v_as_4446_, lean_object* v_bs_4447_, lean_object* v_i_4448_, lean_object* v_cs_4449_){
_start:
{
lean_object* v___x_4450_; 
v___x_4450_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4445_, v_as_4446_, v_bs_4447_, v_i_4448_, v_cs_4449_);
return v___x_4450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___boxed(lean_object* v_00_u03b1_4451_, lean_object* v_00_u03b2_4452_, lean_object* v_00_u03b3_4453_, lean_object* v_f_4454_, lean_object* v_as_4455_, lean_object* v_bs_4456_, lean_object* v_i_4457_, lean_object* v_cs_4458_){
_start:
{
lean_object* v_res_4459_; 
v_res_4459_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(v_00_u03b1_4451_, v_00_u03b2_4452_, v_00_u03b3_4453_, v_f_4454_, v_as_4455_, v_bs_4456_, v_i_4457_, v_cs_4458_);
lean_dec_ref(v_bs_4456_);
lean_dec_ref(v_as_4455_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg(lean_object* v_f_4460_, lean_object* v_as_4461_, lean_object* v_bs_4462_){
_start:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___x_4463_ = lean_unsigned_to_nat(0u);
v___x_4464_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4465_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4460_, v_as_4461_, v_bs_4462_, v___x_4463_, v___x_4464_);
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg___boxed(lean_object* v_f_4466_, lean_object* v_as_4467_, lean_object* v_bs_4468_){
_start:
{
lean_object* v_res_4469_; 
v_res_4469_ = l_Array_zipWithAll___redArg(v_f_4466_, v_as_4467_, v_bs_4468_);
lean_dec_ref(v_bs_4468_);
lean_dec_ref(v_as_4467_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll(lean_object* v_00_u03b1_4470_, lean_object* v_00_u03b2_4471_, lean_object* v_00_u03b3_4472_, lean_object* v_f_4473_, lean_object* v_as_4474_, lean_object* v_bs_4475_){
_start:
{
lean_object* v___x_4476_; 
v___x_4476_ = l_Array_zipWithAll___redArg(v_f_4473_, v_as_4474_, v_bs_4475_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___boxed(lean_object* v_00_u03b1_4477_, lean_object* v_00_u03b2_4478_, lean_object* v_00_u03b3_4479_, lean_object* v_f_4480_, lean_object* v_as_4481_, lean_object* v_bs_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_Array_zipWithAll(v_00_u03b1_4477_, v_00_u03b2_4478_, v_00_u03b3_4479_, v_f_4480_, v_as_4481_, v_bs_4482_);
lean_dec_ref(v_bs_4482_);
lean_dec_ref(v_as_4481_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM___redArg(lean_object* v_inst_4484_, lean_object* v_f_4485_, lean_object* v_as_4486_, lean_object* v_bs_4487_){
_start:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4488_ = lean_unsigned_to_nat(0u);
v___x_4489_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4490_ = l_Array_zipWithMAux___redArg(v_inst_4484_, v_as_4486_, v_bs_4487_, v_f_4485_, v___x_4488_, v___x_4489_);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM(lean_object* v_00_u03b1_4491_, lean_object* v_00_u03b2_4492_, lean_object* v_00_u03b3_4493_, lean_object* v_m_4494_, lean_object* v_inst_4495_, lean_object* v_f_4496_, lean_object* v_as_4497_, lean_object* v_bs_4498_){
_start:
{
lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4499_ = lean_unsigned_to_nat(0u);
v___x_4500_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4501_ = l_Array_zipWithMAux___redArg(v_inst_4495_, v_as_4497_, v_bs_4498_, v_f_4496_, v___x_4499_, v___x_4500_);
return v___x_4501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(lean_object* v_as_4502_, size_t v_i_4503_, size_t v_stop_4504_, lean_object* v_b_4505_){
_start:
{
uint8_t v___x_4506_; 
v___x_4506_ = lean_usize_dec_eq(v_i_4503_, v_stop_4504_);
if (v___x_4506_ == 0)
{
lean_object* v_fst_4507_; lean_object* v_snd_4508_; lean_object* v___x_4509_; lean_object* v_fst_4510_; lean_object* v_snd_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4523_; 
v_fst_4507_ = lean_ctor_get(v_b_4505_, 0);
lean_inc(v_fst_4507_);
v_snd_4508_ = lean_ctor_get(v_b_4505_, 1);
lean_inc(v_snd_4508_);
lean_dec_ref(v_b_4505_);
v___x_4509_ = lean_array_uget(v_as_4502_, v_i_4503_);
v_fst_4510_ = lean_ctor_get(v___x_4509_, 0);
v_snd_4511_ = lean_ctor_get(v___x_4509_, 1);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4509_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4513_ = v___x_4509_;
v_isShared_4514_ = v_isSharedCheck_4523_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_snd_4511_);
lean_inc(v_fst_4510_);
lean_dec(v___x_4509_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4523_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4518_; 
v___x_4515_ = lean_array_push(v_fst_4507_, v_fst_4510_);
v___x_4516_ = lean_array_push(v_snd_4508_, v_snd_4511_);
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 1, v___x_4516_);
lean_ctor_set(v___x_4513_, 0, v___x_4515_);
v___x_4518_ = v___x_4513_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4515_);
lean_ctor_set(v_reuseFailAlloc_4522_, 1, v___x_4516_);
v___x_4518_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
size_t v___x_4519_; size_t v___x_4520_; 
v___x_4519_ = ((size_t)1ULL);
v___x_4520_ = lean_usize_add(v_i_4503_, v___x_4519_);
v_i_4503_ = v___x_4520_;
v_b_4505_ = v___x_4518_;
goto _start;
}
}
}
else
{
return v_b_4505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg___boxed(lean_object* v_as_4524_, lean_object* v_i_4525_, lean_object* v_stop_4526_, lean_object* v_b_4527_){
_start:
{
size_t v_i_boxed_4528_; size_t v_stop_boxed_4529_; lean_object* v_res_4530_; 
v_i_boxed_4528_ = lean_unbox_usize(v_i_4525_);
lean_dec(v_i_4525_);
v_stop_boxed_4529_ = lean_unbox_usize(v_stop_4526_);
lean_dec(v_stop_4526_);
v_res_4530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4524_, v_i_boxed_4528_, v_stop_boxed_4529_, v_b_4527_);
lean_dec_ref(v_as_4524_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg(lean_object* v_as_4531_){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; uint8_t v___x_4535_; 
v___x_4532_ = lean_unsigned_to_nat(0u);
v___x_4533_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v___x_4534_ = lean_array_get_size(v_as_4531_);
v___x_4535_ = lean_nat_dec_lt(v___x_4532_, v___x_4534_);
if (v___x_4535_ == 0)
{
return v___x_4533_;
}
else
{
uint8_t v___x_4536_; 
v___x_4536_ = lean_nat_dec_le(v___x_4534_, v___x_4534_);
if (v___x_4536_ == 0)
{
if (v___x_4535_ == 0)
{
return v___x_4533_;
}
else
{
size_t v___x_4537_; size_t v___x_4538_; lean_object* v___x_4539_; 
v___x_4537_ = ((size_t)0ULL);
v___x_4538_ = lean_usize_of_nat(v___x_4534_);
v___x_4539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4531_, v___x_4537_, v___x_4538_, v___x_4533_);
return v___x_4539_;
}
}
else
{
size_t v___x_4540_; size_t v___x_4541_; lean_object* v___x_4542_; 
v___x_4540_ = ((size_t)0ULL);
v___x_4541_ = lean_usize_of_nat(v___x_4534_);
v___x_4542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4531_, v___x_4540_, v___x_4541_, v___x_4533_);
return v___x_4542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg___boxed(lean_object* v_as_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Array_unzip___redArg(v_as_4543_);
lean_dec_ref(v_as_4543_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip(lean_object* v_00_u03b1_4545_, lean_object* v_00_u03b2_4546_, lean_object* v_as_4547_){
_start:
{
lean_object* v___x_4548_; 
v___x_4548_ = l_Array_unzip___redArg(v_as_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___boxed(lean_object* v_00_u03b1_4549_, lean_object* v_00_u03b2_4550_, lean_object* v_as_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_Array_unzip(v_00_u03b1_4549_, v_00_u03b2_4550_, v_as_4551_);
lean_dec_ref(v_as_4551_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(lean_object* v_00_u03b1_4553_, lean_object* v_00_u03b2_4554_, lean_object* v_as_4555_, size_t v_i_4556_, size_t v_stop_4557_, lean_object* v_b_4558_){
_start:
{
lean_object* v___x_4559_; 
v___x_4559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4555_, v_i_4556_, v_stop_4557_, v_b_4558_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___boxed(lean_object* v_00_u03b1_4560_, lean_object* v_00_u03b2_4561_, lean_object* v_as_4562_, lean_object* v_i_4563_, lean_object* v_stop_4564_, lean_object* v_b_4565_){
_start:
{
size_t v_i_boxed_4566_; size_t v_stop_boxed_4567_; lean_object* v_res_4568_; 
v_i_boxed_4566_ = lean_unbox_usize(v_i_4563_);
lean_dec(v_i_4563_);
v_stop_boxed_4567_ = lean_unbox_usize(v_stop_4564_);
lean_dec(v_stop_4564_);
v_res_4568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(v_00_u03b1_4560_, v_00_u03b2_4561_, v_as_4562_, v_i_boxed_4566_, v_stop_boxed_4567_, v_b_4565_);
lean_dec_ref(v_as_4562_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l_Array_replace___redArg(lean_object* v_inst_4569_, lean_object* v_xs_4570_, lean_object* v_a_4571_, lean_object* v_b_4572_){
_start:
{
lean_object* v___x_4573_; 
v___x_4573_ = l_Array_finIdxOf_x3f___redArg(v_inst_4569_, v_xs_4570_, v_a_4571_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_dec(v_b_4572_);
return v_xs_4570_;
}
else
{
lean_object* v_val_4574_; lean_object* v___x_4575_; 
v_val_4574_ = lean_ctor_get(v___x_4573_, 0);
lean_inc(v_val_4574_);
lean_dec_ref(v___x_4573_);
v___x_4575_ = lean_array_fset(v_xs_4570_, v_val_4574_, v_b_4572_);
lean_dec(v_val_4574_);
return v___x_4575_;
}
}
}
LEAN_EXPORT lean_object* l_Array_replace(lean_object* v_00_u03b1_4576_, lean_object* v_inst_4577_, lean_object* v_xs_4578_, lean_object* v_a_4579_, lean_object* v_b_4580_){
_start:
{
lean_object* v___x_4581_; 
v___x_4581_ = l_Array_replace___redArg(v_inst_4577_, v_xs_4578_, v_a_4579_, v_b_4580_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l_Array_instLT(lean_object* v_00_u03b1_4582_, lean_object* v_inst_4583_){
_start:
{
lean_object* v___x_4584_; 
v___x_4584_ = lean_box(0);
return v___x_4584_;
}
}
LEAN_EXPORT lean_object* l_Array_instLE(lean_object* v_00_u03b1_4585_, lean_object* v_inst_4586_){
_start:
{
lean_object* v___x_4587_; 
v___x_4587_ = lean_box(0);
return v___x_4587_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg(lean_object* v_n_4588_, lean_object* v_a_4589_, lean_object* v_xs_4590_){
_start:
{
lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4591_ = lean_array_get_size(v_xs_4590_);
v___x_4592_ = lean_nat_sub(v_n_4588_, v___x_4591_);
v___x_4593_ = lean_mk_array(v___x_4592_, v_a_4589_);
v___x_4594_ = l_Array_append___redArg(v___x_4593_, v_xs_4590_);
return v___x_4594_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg___boxed(lean_object* v_n_4595_, lean_object* v_a_4596_, lean_object* v_xs_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l_Array_leftpad___redArg(v_n_4595_, v_a_4596_, v_xs_4597_);
lean_dec_ref(v_xs_4597_);
lean_dec(v_n_4595_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad(lean_object* v_00_u03b1_4599_, lean_object* v_n_4600_, lean_object* v_a_4601_, lean_object* v_xs_4602_){
_start:
{
lean_object* v___x_4603_; 
v___x_4603_ = l_Array_leftpad___redArg(v_n_4600_, v_a_4601_, v_xs_4602_);
return v___x_4603_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___boxed(lean_object* v_00_u03b1_4604_, lean_object* v_n_4605_, lean_object* v_a_4606_, lean_object* v_xs_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l_Array_leftpad(v_00_u03b1_4604_, v_n_4605_, v_a_4606_, v_xs_4607_);
lean_dec_ref(v_xs_4607_);
lean_dec(v_n_4605_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg(lean_object* v_n_4609_, lean_object* v_a_4610_, lean_object* v_xs_4611_){
_start:
{
lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4612_ = lean_array_get_size(v_xs_4611_);
v___x_4613_ = lean_nat_sub(v_n_4609_, v___x_4612_);
v___x_4614_ = lean_mk_array(v___x_4613_, v_a_4610_);
v___x_4615_ = l_Array_append___redArg(v_xs_4611_, v___x_4614_);
lean_dec_ref(v___x_4614_);
return v___x_4615_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg___boxed(lean_object* v_n_4616_, lean_object* v_a_4617_, lean_object* v_xs_4618_){
_start:
{
lean_object* v_res_4619_; 
v_res_4619_ = l_Array_rightpad___redArg(v_n_4616_, v_a_4617_, v_xs_4618_);
lean_dec(v_n_4616_);
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad(lean_object* v_00_u03b1_4620_, lean_object* v_n_4621_, lean_object* v_a_4622_, lean_object* v_xs_4623_){
_start:
{
lean_object* v___x_4624_; 
v___x_4624_ = l_Array_rightpad___redArg(v_n_4621_, v_a_4622_, v_xs_4623_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___boxed(lean_object* v_00_u03b1_4625_, lean_object* v_n_4626_, lean_object* v_a_4627_, lean_object* v_xs_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l_Array_rightpad(v_00_u03b1_4625_, v_n_4626_, v_a_4627_, v_xs_4628_);
lean_dec(v_n_4626_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0(lean_object* v_x_4630_){
_start:
{
lean_inc(v_x_4630_);
return v_x_4630_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0___boxed(lean_object* v_x_4631_){
_start:
{
lean_object* v_res_4632_; 
v_res_4632_ = l_Array_reduceOption___redArg___lam__0(v_x_4631_);
lean_dec(v_x_4631_);
return v_res_4632_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg(lean_object* v_as_4634_){
_start:
{
lean_object* v___f_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___f_4635_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4636_ = lean_unsigned_to_nat(0u);
v___x_4637_ = lean_array_get_size(v_as_4634_);
v___x_4638_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4639_ = l_Array_filterMapM___redArg(v___x_4638_, v___f_4635_, v_as_4634_, v___x_4636_, v___x_4637_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption(lean_object* v_00_u03b1_4640_, lean_object* v_as_4641_){
_start:
{
lean_object* v___f_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___f_4642_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4643_ = lean_unsigned_to_nat(0u);
v___x_4644_ = lean_array_get_size(v_as_4641_);
v___x_4645_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4646_ = l_Array_filterMapM___redArg(v___x_4645_, v___f_4642_, v_as_4641_, v___x_4643_, v___x_4644_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg___lam__0(lean_object* v_inst_4647_, lean_object* v_x1_4648_, lean_object* v_x2_4649_){
_start:
{
lean_object* v_fst_4650_; lean_object* v_snd_4651_; lean_object* v___x_4652_; uint8_t v___x_4653_; 
v_fst_4650_ = lean_ctor_get(v_x1_4648_, 0);
v_snd_4651_ = lean_ctor_get(v_x1_4648_, 1);
lean_inc(v_fst_4650_);
lean_inc(v_x2_4649_);
v___x_4652_ = lean_apply_2(v_inst_4647_, v_x2_4649_, v_fst_4650_);
v___x_4653_ = lean_unbox(v___x_4652_);
if (v___x_4653_ == 0)
{
lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4661_; 
lean_inc(v_snd_4651_);
lean_inc(v_fst_4650_);
v_isSharedCheck_4661_ = !lean_is_exclusive(v_x1_4648_);
if (v_isSharedCheck_4661_ == 0)
{
lean_object* v_unused_4662_; lean_object* v_unused_4663_; 
v_unused_4662_ = lean_ctor_get(v_x1_4648_, 1);
lean_dec(v_unused_4662_);
v_unused_4663_ = lean_ctor_get(v_x1_4648_, 0);
lean_dec(v_unused_4663_);
v___x_4655_ = v_x1_4648_;
v_isShared_4656_ = v_isSharedCheck_4661_;
goto v_resetjp_4654_;
}
else
{
lean_dec(v_x1_4648_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4661_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4657_; lean_object* v___x_4659_; 
v___x_4657_ = lean_array_push(v_snd_4651_, v_fst_4650_);
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 1, v___x_4657_);
lean_ctor_set(v___x_4655_, 0, v_x2_4649_);
v___x_4659_ = v___x_4655_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_x2_4649_);
lean_ctor_set(v_reuseFailAlloc_4660_, 1, v___x_4657_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
else
{
lean_dec(v_x2_4649_);
return v_x1_4648_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg(lean_object* v_inst_4664_, lean_object* v_as_4665_){
_start:
{
lean_object* v___y_4667_; lean_object* v___x_4671_; lean_object* v___x_4672_; uint8_t v___x_4673_; 
v___x_4671_ = lean_unsigned_to_nat(0u);
v___x_4672_ = lean_array_get_size(v_as_4665_);
v___x_4673_ = lean_nat_dec_lt(v___x_4671_, v___x_4672_);
if (v___x_4673_ == 0)
{
lean_object* v___x_4674_; 
lean_dec_ref(v_as_4665_);
lean_dec_ref(v_inst_4664_);
v___x_4674_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
return v___x_4674_;
}
else
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4675_ = lean_array_fget_borrowed(v_as_4665_, v___x_4671_);
v___x_4676_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4677_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
if (v___x_4673_ == 0)
{
lean_object* v___x_4678_; 
lean_inc(v___x_4675_);
lean_dec_ref(v_as_4665_);
lean_dec_ref(v_inst_4664_);
v___x_4678_ = lean_array_push(v___x_4676_, v___x_4675_);
return v___x_4678_;
}
else
{
lean_object* v___f_4679_; lean_object* v___x_4680_; uint8_t v___x_4681_; 
v___f_4679_ = lean_alloc_closure((void*)(l_Array_eraseReps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4679_, 0, v_inst_4664_);
lean_inc(v___x_4675_);
v___x_4680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4680_, 0, v___x_4675_);
lean_ctor_set(v___x_4680_, 1, v___x_4676_);
v___x_4681_ = lean_nat_dec_le(v___x_4672_, v___x_4672_);
if (v___x_4681_ == 0)
{
if (v___x_4673_ == 0)
{
lean_object* v___x_4682_; 
lean_inc(v___x_4675_);
lean_dec_ref(v___x_4680_);
lean_dec_ref(v___f_4679_);
lean_dec_ref(v_as_4665_);
v___x_4682_ = lean_array_push(v___x_4676_, v___x_4675_);
return v___x_4682_;
}
else
{
size_t v___x_4683_; size_t v___x_4684_; lean_object* v___x_4685_; 
v___x_4683_ = ((size_t)0ULL);
v___x_4684_ = lean_usize_of_nat(v___x_4672_);
v___x_4685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4677_, v___f_4679_, v_as_4665_, v___x_4683_, v___x_4684_, v___x_4680_);
v___y_4667_ = v___x_4685_;
goto v___jp_4666_;
}
}
else
{
size_t v___x_4686_; size_t v___x_4687_; lean_object* v___x_4688_; 
v___x_4686_ = ((size_t)0ULL);
v___x_4687_ = lean_usize_of_nat(v___x_4672_);
v___x_4688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4677_, v___f_4679_, v_as_4665_, v___x_4686_, v___x_4687_, v___x_4680_);
v___y_4667_ = v___x_4688_;
goto v___jp_4666_;
}
}
}
v___jp_4666_:
{
lean_object* v_fst_4668_; lean_object* v_snd_4669_; lean_object* v___x_4670_; 
v_fst_4668_ = lean_ctor_get(v___y_4667_, 0);
lean_inc(v_fst_4668_);
v_snd_4669_ = lean_ctor_get(v___y_4667_, 1);
lean_inc(v_snd_4669_);
lean_dec_ref(v___y_4667_);
v___x_4670_ = lean_array_push(v_snd_4669_, v_fst_4668_);
return v___x_4670_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps(lean_object* v_00_u03b1_4689_, lean_object* v_inst_4690_, lean_object* v_as_4691_){
_start:
{
lean_object* v___x_4692_; 
v___x_4692_ = l_Array_eraseReps___redArg(v_inst_4690_, v_as_4691_);
return v___x_4692_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(lean_object* v_inst_4693_, lean_object* v_as_4694_, lean_object* v_a_4695_, lean_object* v_x_4696_){
_start:
{
lean_object* v_zero_4697_; uint8_t v_isZero_4698_; 
v_zero_4697_ = lean_unsigned_to_nat(0u);
v_isZero_4698_ = lean_nat_dec_eq(v_x_4696_, v_zero_4697_);
if (v_isZero_4698_ == 1)
{
lean_dec(v_x_4696_);
lean_dec(v_a_4695_);
lean_dec_ref(v_inst_4693_);
return v_isZero_4698_;
}
else
{
lean_object* v_one_4699_; lean_object* v_n_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; uint8_t v___x_4703_; 
v_one_4699_ = lean_unsigned_to_nat(1u);
v_n_4700_ = lean_nat_sub(v_x_4696_, v_one_4699_);
lean_dec(v_x_4696_);
v___x_4701_ = lean_array_fget_borrowed(v_as_4694_, v_n_4700_);
lean_inc_ref(v_inst_4693_);
lean_inc(v___x_4701_);
lean_inc(v_a_4695_);
v___x_4702_ = lean_apply_2(v_inst_4693_, v_a_4695_, v___x_4701_);
v___x_4703_ = lean_unbox(v___x_4702_);
if (v___x_4703_ == 0)
{
v_x_4696_ = v_n_4700_;
goto _start;
}
else
{
lean_dec(v_n_4700_);
lean_dec(v_a_4695_);
lean_dec_ref(v_inst_4693_);
return v_isZero_4698_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg___boxed(lean_object* v_inst_4705_, lean_object* v_as_4706_, lean_object* v_a_4707_, lean_object* v_x_4708_){
_start:
{
uint8_t v_res_4709_; lean_object* v_r_4710_; 
v_res_4709_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4705_, v_as_4706_, v_a_4707_, v_x_4708_);
lean_dec_ref(v_as_4706_);
v_r_4710_ = lean_box(v_res_4709_);
return v_r_4710_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(lean_object* v_00_u03b1_4711_, lean_object* v_inst_4712_, lean_object* v_as_4713_, lean_object* v_a_4714_, lean_object* v_x_4715_, lean_object* v_x_4716_){
_start:
{
uint8_t v___x_4717_; 
v___x_4717_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4712_, v_as_4713_, v_a_4714_, v_x_4715_);
return v___x_4717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___boxed(lean_object* v_00_u03b1_4718_, lean_object* v_inst_4719_, lean_object* v_as_4720_, lean_object* v_a_4721_, lean_object* v_x_4722_, lean_object* v_x_4723_){
_start:
{
uint8_t v_res_4724_; lean_object* v_r_4725_; 
v_res_4724_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(v_00_u03b1_4718_, v_inst_4719_, v_as_4720_, v_a_4721_, v_x_4722_, v_x_4723_);
lean_dec_ref(v_as_4720_);
v_r_4725_ = lean_box(v_res_4724_);
return v_r_4725_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(lean_object* v_inst_4726_, lean_object* v_as_4727_, lean_object* v_i_4728_){
_start:
{
lean_object* v___x_4729_; uint8_t v___x_4730_; 
v___x_4729_ = lean_array_get_size(v_as_4727_);
v___x_4730_ = lean_nat_dec_lt(v_i_4728_, v___x_4729_);
if (v___x_4730_ == 0)
{
uint8_t v___x_4731_; 
lean_dec(v_i_4728_);
lean_dec_ref(v_inst_4726_);
v___x_4731_ = 1;
return v___x_4731_;
}
else
{
lean_object* v___x_4732_; uint8_t v___x_4733_; 
v___x_4732_ = lean_array_fget_borrowed(v_as_4727_, v_i_4728_);
lean_inc(v_i_4728_);
lean_inc(v___x_4732_);
lean_inc_ref(v_inst_4726_);
v___x_4733_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4726_, v_as_4727_, v___x_4732_, v_i_4728_);
if (v___x_4733_ == 0)
{
lean_dec(v_i_4728_);
lean_dec_ref(v_inst_4726_);
return v___x_4733_;
}
else
{
lean_object* v___x_4734_; lean_object* v___x_4735_; 
v___x_4734_ = lean_unsigned_to_nat(1u);
v___x_4735_ = lean_nat_add(v_i_4728_, v___x_4734_);
lean_dec(v_i_4728_);
v_i_4728_ = v___x_4735_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg___boxed(lean_object* v_inst_4737_, lean_object* v_as_4738_, lean_object* v_i_4739_){
_start:
{
uint8_t v_res_4740_; lean_object* v_r_4741_; 
v_res_4740_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4737_, v_as_4738_, v_i_4739_);
lean_dec_ref(v_as_4738_);
v_r_4741_ = lean_box(v_res_4740_);
return v_r_4741_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux(lean_object* v_00_u03b1_4742_, lean_object* v_inst_4743_, lean_object* v_as_4744_, lean_object* v_i_4745_){
_start:
{
uint8_t v___x_4746_; 
v___x_4746_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4743_, v_as_4744_, v_i_4745_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___boxed(lean_object* v_00_u03b1_4747_, lean_object* v_inst_4748_, lean_object* v_as_4749_, lean_object* v_i_4750_){
_start:
{
uint8_t v_res_4751_; lean_object* v_r_4752_; 
v_res_4751_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux(v_00_u03b1_4747_, v_inst_4748_, v_as_4749_, v_i_4750_);
lean_dec_ref(v_as_4749_);
v_r_4752_ = lean_box(v_res_4751_);
return v_r_4752_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___redArg(lean_object* v_inst_4753_, lean_object* v_as_4754_){
_start:
{
lean_object* v___x_4755_; uint8_t v___x_4756_; 
v___x_4755_ = lean_unsigned_to_nat(0u);
v___x_4756_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4753_, v_as_4754_, v___x_4755_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___redArg___boxed(lean_object* v_inst_4757_, lean_object* v_as_4758_){
_start:
{
uint8_t v_res_4759_; lean_object* v_r_4760_; 
v_res_4759_ = l_Array_allDiff___redArg(v_inst_4757_, v_as_4758_);
lean_dec_ref(v_as_4758_);
v_r_4760_ = lean_box(v_res_4759_);
return v_r_4760_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff(lean_object* v_00_u03b1_4761_, lean_object* v_inst_4762_, lean_object* v_as_4763_){
_start:
{
uint8_t v___x_4764_; 
v___x_4764_ = l_Array_allDiff___redArg(v_inst_4762_, v_as_4763_);
return v___x_4764_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___boxed(lean_object* v_00_u03b1_4765_, lean_object* v_inst_4766_, lean_object* v_as_4767_){
_start:
{
uint8_t v_res_4768_; lean_object* v_r_4769_; 
v_res_4768_ = l_Array_allDiff(v_00_u03b1_4765_, v_inst_4766_, v_as_4767_);
lean_dec_ref(v_as_4767_);
v_r_4769_ = lean_box(v_res_4768_);
return v_r_4769_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0(uint8_t v___x_4770_, lean_object* v_x1_4771_, lean_object* v_x2_4772_){
_start:
{
lean_object* v_fst_4773_; uint8_t v___x_4774_; 
v_fst_4773_ = lean_ctor_get(v_x1_4771_, 0);
v___x_4774_ = lean_unbox(v_fst_4773_);
if (v___x_4774_ == 0)
{
lean_object* v_snd_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4783_; 
lean_dec(v_x2_4772_);
v_snd_4775_ = lean_ctor_get(v_x1_4771_, 1);
v_isSharedCheck_4783_ = !lean_is_exclusive(v_x1_4771_);
if (v_isSharedCheck_4783_ == 0)
{
lean_object* v_unused_4784_; 
v_unused_4784_ = lean_ctor_get(v_x1_4771_, 0);
lean_dec(v_unused_4784_);
v___x_4777_ = v_x1_4771_;
v_isShared_4778_ = v_isSharedCheck_4783_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_snd_4775_);
lean_dec(v_x1_4771_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4783_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4779_; lean_object* v___x_4781_; 
v___x_4779_ = lean_box(v___x_4770_);
if (v_isShared_4778_ == 0)
{
lean_ctor_set(v___x_4777_, 0, v___x_4779_);
v___x_4781_ = v___x_4777_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v___x_4779_);
lean_ctor_set(v_reuseFailAlloc_4782_, 1, v_snd_4775_);
v___x_4781_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
return v___x_4781_;
}
}
}
else
{
lean_object* v_snd_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4795_; 
v_snd_4785_ = lean_ctor_get(v_x1_4771_, 1);
v_isSharedCheck_4795_ = !lean_is_exclusive(v_x1_4771_);
if (v_isSharedCheck_4795_ == 0)
{
lean_object* v_unused_4796_; 
v_unused_4796_ = lean_ctor_get(v_x1_4771_, 0);
lean_dec(v_unused_4796_);
v___x_4787_ = v_x1_4771_;
v_isShared_4788_ = v_isSharedCheck_4795_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_snd_4785_);
lean_dec(v_x1_4771_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4795_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
uint8_t v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4793_; 
v___x_4789_ = 0;
v___x_4790_ = lean_array_push(v_snd_4785_, v_x2_4772_);
v___x_4791_ = lean_box(v___x_4789_);
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 1, v___x_4790_);
lean_ctor_set(v___x_4787_, 0, v___x_4791_);
v___x_4793_ = v___x_4787_;
goto v_reusejp_4792_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4791_);
lean_ctor_set(v_reuseFailAlloc_4794_, 1, v___x_4790_);
v___x_4793_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4792_;
}
v_reusejp_4792_:
{
return v___x_4793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0___boxed(lean_object* v___x_4797_, lean_object* v_x1_4798_, lean_object* v_x2_4799_){
_start:
{
uint8_t v___x_172__boxed_4800_; lean_object* v_res_4801_; 
v___x_172__boxed_4800_ = lean_unbox(v___x_4797_);
v_res_4801_ = l_Array_getEvenElems___redArg___lam__0(v___x_172__boxed_4800_, v_x1_4798_, v_x2_4799_);
return v_res_4801_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg(lean_object* v_as_4802_){
_start:
{
lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; uint8_t v___x_4807_; 
v___x_4803_ = lean_unsigned_to_nat(0u);
v___x_4804_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_4805_ = lean_array_get_size(v_as_4802_);
v___x_4806_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4807_ = lean_nat_dec_lt(v___x_4803_, v___x_4805_);
if (v___x_4807_ == 0)
{
lean_dec_ref(v_as_4802_);
return v___x_4804_;
}
else
{
lean_object* v___x_4808_; lean_object* v___f_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; uint8_t v___x_4812_; 
v___x_4808_ = lean_box(v___x_4807_);
v___f_4809_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4809_, 0, v___x_4808_);
v___x_4810_ = lean_box(v___x_4807_);
v___x_4811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4811_, 0, v___x_4810_);
lean_ctor_set(v___x_4811_, 1, v___x_4804_);
v___x_4812_ = lean_nat_dec_le(v___x_4805_, v___x_4805_);
if (v___x_4812_ == 0)
{
if (v___x_4807_ == 0)
{
lean_dec_ref(v___x_4811_);
lean_dec_ref(v___f_4809_);
lean_dec_ref(v_as_4802_);
return v___x_4804_;
}
else
{
size_t v___x_4813_; size_t v___x_4814_; lean_object* v___x_4815_; lean_object* v_snd_4816_; 
v___x_4813_ = ((size_t)0ULL);
v___x_4814_ = lean_usize_of_nat(v___x_4805_);
v___x_4815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4806_, v___f_4809_, v_as_4802_, v___x_4813_, v___x_4814_, v___x_4811_);
v_snd_4816_ = lean_ctor_get(v___x_4815_, 1);
lean_inc(v_snd_4816_);
lean_dec(v___x_4815_);
return v_snd_4816_;
}
}
else
{
size_t v___x_4817_; size_t v___x_4818_; lean_object* v___x_4819_; lean_object* v_snd_4820_; 
v___x_4817_ = ((size_t)0ULL);
v___x_4818_ = lean_usize_of_nat(v___x_4805_);
v___x_4819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4806_, v___f_4809_, v_as_4802_, v___x_4817_, v___x_4818_, v___x_4811_);
v_snd_4820_ = lean_ctor_get(v___x_4819_, 1);
lean_inc(v_snd_4820_);
lean_dec(v___x_4819_);
return v_snd_4820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems(lean_object* v_00_u03b1_4821_, lean_object* v_as_4822_){
_start:
{
lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; uint8_t v___x_4827_; 
v___x_4823_ = lean_unsigned_to_nat(0u);
v___x_4824_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_4825_ = lean_array_get_size(v_as_4822_);
v___x_4826_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4827_ = lean_nat_dec_lt(v___x_4823_, v___x_4825_);
if (v___x_4827_ == 0)
{
lean_dec_ref(v_as_4822_);
return v___x_4824_;
}
else
{
lean_object* v___x_4828_; lean_object* v___f_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; uint8_t v___x_4832_; 
v___x_4828_ = lean_box(v___x_4827_);
v___f_4829_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4829_, 0, v___x_4828_);
v___x_4830_ = lean_box(v___x_4827_);
v___x_4831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4830_);
lean_ctor_set(v___x_4831_, 1, v___x_4824_);
v___x_4832_ = lean_nat_dec_le(v___x_4825_, v___x_4825_);
if (v___x_4832_ == 0)
{
if (v___x_4827_ == 0)
{
lean_dec_ref(v___x_4831_);
lean_dec_ref(v___f_4829_);
lean_dec_ref(v_as_4822_);
return v___x_4824_;
}
else
{
size_t v___x_4833_; size_t v___x_4834_; lean_object* v___x_4835_; lean_object* v_snd_4836_; 
v___x_4833_ = ((size_t)0ULL);
v___x_4834_ = lean_usize_of_nat(v___x_4825_);
v___x_4835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4826_, v___f_4829_, v_as_4822_, v___x_4833_, v___x_4834_, v___x_4831_);
v_snd_4836_ = lean_ctor_get(v___x_4835_, 1);
lean_inc(v_snd_4836_);
lean_dec(v___x_4835_);
return v_snd_4836_;
}
}
else
{
size_t v___x_4837_; size_t v___x_4838_; lean_object* v___x_4839_; lean_object* v_snd_4840_; 
v___x_4837_ = ((size_t)0ULL);
v___x_4838_ = lean_usize_of_nat(v___x_4825_);
v___x_4839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4826_, v___f_4829_, v_as_4822_, v___x_4837_, v___x_4838_, v___x_4831_);
v_snd_4840_ = lean_ctor_get(v___x_4839_, 1);
lean_inc(v_snd_4840_);
lean_dec(v___x_4839_);
return v_snd_4840_;
}
}
}
}
static lean_object* _init_l_Array_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4846_ = ((lean_object*)(l_term_x23_x5b___x2c_x5d___closed__4));
v___x_4847_ = lean_string_length(v___x_4846_);
return v___x_4847_;
}
}
static lean_object* _init_l_Array_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4848_ = lean_obj_once(&l_Array_repr___redArg___closed__2, &l_Array_repr___redArg___closed__2_once, _init_l_Array_repr___redArg___closed__2);
v___x_4849_ = lean_nat_to_int(v___x_4848_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___redArg(lean_object* v_inst_4857_, lean_object* v_xs_4858_){
_start:
{
lean_object* v___x_4859_; lean_object* v___x_4860_; uint8_t v___x_4861_; 
v___x_4859_ = lean_array_get_size(v_xs_4858_);
v___x_4860_ = lean_unsigned_to_nat(0u);
v___x_4861_ = lean_nat_dec_eq(v___x_4859_, v___x_4860_);
if (v___x_4861_ == 0)
{
lean_object* v_x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; 
v_x_4862_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_4862_, 0, lean_box(0));
lean_closure_set(v_x_4862_, 1, v_inst_4857_);
v___x_4863_ = lean_array_to_list(v_xs_4858_);
v___x_4864_ = ((lean_object*)(l_Array_repr___redArg___closed__1));
v___x_4865_ = l_Std_Format_joinSep___redArg(v_x_4862_, v___x_4863_, v___x_4864_);
v___x_4866_ = lean_obj_once(&l_Array_repr___redArg___closed__3, &l_Array_repr___redArg___closed__3_once, _init_l_Array_repr___redArg___closed__3);
v___x_4867_ = ((lean_object*)(l_Array_repr___redArg___closed__4));
v___x_4868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4868_, 0, v___x_4867_);
lean_ctor_set(v___x_4868_, 1, v___x_4865_);
v___x_4869_ = ((lean_object*)(l_Array_repr___redArg___closed__5));
v___x_4870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4868_);
lean_ctor_set(v___x_4870_, 1, v___x_4869_);
v___x_4871_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4871_, 0, v___x_4866_);
lean_ctor_set(v___x_4871_, 1, v___x_4870_);
v___x_4872_ = l_Std_Format_fill(v___x_4871_);
return v___x_4872_;
}
else
{
lean_object* v___x_4873_; 
lean_dec_ref(v_xs_4858_);
lean_dec_ref(v_inst_4857_);
v___x_4873_ = ((lean_object*)(l_Array_repr___redArg___closed__7));
return v___x_4873_;
}
}
}
LEAN_EXPORT lean_object* l_Array_repr(lean_object* v_00_u03b1_4874_, lean_object* v_inst_4875_, lean_object* v_xs_4876_){
_start:
{
lean_object* v___x_4877_; 
v___x_4877_ = l_Array_repr___redArg(v_inst_4875_, v_xs_4876_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0(lean_object* v_inst_4878_, lean_object* v_xs_4879_, lean_object* v_x_4880_){
_start:
{
lean_object* v___x_4881_; 
v___x_4881_ = l_Array_repr___redArg(v_inst_4878_, v_xs_4879_);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object* v_inst_4882_, lean_object* v_xs_4883_, lean_object* v_x_4884_){
_start:
{
lean_object* v_res_4885_; 
v_res_4885_ = l_Array_instRepr___redArg___lam__0(v_inst_4882_, v_xs_4883_, v_x_4884_);
lean_dec(v_x_4884_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg(lean_object* v_inst_4886_){
_start:
{
lean_object* v___f_4887_; 
v___f_4887_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4887_, 0, v_inst_4886_);
return v___f_4887_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr(lean_object* v_00_u03b1_4888_, lean_object* v_inst_4889_){
_start:
{
lean_object* v___f_4890_; 
v___f_4890_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4890_, 0, v_inst_4889_);
return v___f_4890_;
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
