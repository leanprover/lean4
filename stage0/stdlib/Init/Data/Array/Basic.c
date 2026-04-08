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
LEAN_EXPORT lean_object* l_Array_prod___redArg(lean_object* v_inst_2508_, lean_object* v_inst_2509_, lean_object* v_as_2510_){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2511_ = lean_array_get_size(v_as_2510_);
v___x_2512_ = lean_unsigned_to_nat(0u);
v___x_2513_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2514_ = lean_nat_dec_lt(v___x_2512_, v___x_2511_);
if (v___x_2514_ == 0)
{
lean_dec_ref(v_as_2510_);
lean_dec(v_inst_2508_);
return v_inst_2509_;
}
else
{
lean_object* v___f_2515_; size_t v___x_2516_; size_t v___x_2517_; lean_object* v___x_2518_; 
v___f_2515_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2515_, 0, v_inst_2508_);
v___x_2516_ = lean_usize_of_nat(v___x_2511_);
v___x_2517_ = ((size_t)0ULL);
v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2513_, v___f_2515_, v_as_2510_, v___x_2516_, v___x_2517_, v_inst_2509_);
return v___x_2518_;
}
}
}
LEAN_EXPORT lean_object* l_Array_prod(lean_object* v_00_u03b1_2519_, lean_object* v_inst_2520_, lean_object* v_inst_2521_, lean_object* v_as_2522_){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v___x_2523_ = lean_array_get_size(v_as_2522_);
v___x_2524_ = lean_unsigned_to_nat(0u);
v___x_2525_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2526_ = lean_nat_dec_lt(v___x_2524_, v___x_2523_);
if (v___x_2526_ == 0)
{
lean_dec_ref(v_as_2522_);
lean_dec(v_inst_2520_);
return v_inst_2521_;
}
else
{
lean_object* v___f_2527_; size_t v___x_2528_; size_t v___x_2529_; lean_object* v___x_2530_; 
v___f_2527_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2527_, 0, v_inst_2520_);
v___x_2528_ = lean_usize_of_nat(v___x_2523_);
v___x_2529_ = ((size_t)0ULL);
v___x_2530_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2525_, v___f_2527_, v_as_2522_, v___x_2528_, v___x_2529_, v_inst_2521_);
return v___x_2530_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0(lean_object* v_p_2531_, lean_object* v_x1_2532_, lean_object* v_x2_2533_){
_start:
{
lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2534_ = lean_apply_1(v_p_2531_, v_x1_2532_);
v___x_2535_ = lean_unbox(v___x_2534_);
if (v___x_2535_ == 0)
{
lean_inc(v_x2_2533_);
return v_x2_2533_;
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_unsigned_to_nat(1u);
v___x_2537_ = lean_nat_add(v_x2_2533_, v___x_2536_);
return v___x_2537_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0___boxed(lean_object* v_p_2538_, lean_object* v_x1_2539_, lean_object* v_x2_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Array_countP___redArg___lam__0(v_p_2538_, v_x1_2539_, v_x2_2540_);
lean_dec(v_x2_2540_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg(lean_object* v_p_2542_, lean_object* v_as_2543_){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2544_ = lean_unsigned_to_nat(0u);
v___x_2545_ = lean_array_get_size(v_as_2543_);
v___x_2546_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2547_ = lean_nat_dec_lt(v___x_2544_, v___x_2545_);
if (v___x_2547_ == 0)
{
lean_dec_ref(v_as_2543_);
lean_dec_ref(v_p_2542_);
return v___x_2544_;
}
else
{
lean_object* v___f_2548_; size_t v___x_2549_; size_t v___x_2550_; lean_object* v___x_2551_; 
v___f_2548_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2548_, 0, v_p_2542_);
v___x_2549_ = lean_usize_of_nat(v___x_2545_);
v___x_2550_ = ((size_t)0ULL);
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2546_, v___f_2548_, v_as_2543_, v___x_2549_, v___x_2550_, v___x_2544_);
return v___x_2551_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP(lean_object* v_00_u03b1_2552_, lean_object* v_p_2553_, lean_object* v_as_2554_){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; 
v___x_2555_ = lean_unsigned_to_nat(0u);
v___x_2556_ = lean_array_get_size(v_as_2554_);
v___x_2557_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2558_ = lean_nat_dec_lt(v___x_2555_, v___x_2556_);
if (v___x_2558_ == 0)
{
lean_dec_ref(v_as_2554_);
lean_dec_ref(v_p_2553_);
return v___x_2555_;
}
else
{
lean_object* v___f_2559_; size_t v___x_2560_; size_t v___x_2561_; lean_object* v___x_2562_; 
v___f_2559_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2559_, 0, v_p_2553_);
v___x_2560_ = lean_usize_of_nat(v___x_2556_);
v___x_2561_ = ((size_t)0ULL);
v___x_2562_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2557_, v___f_2559_, v_as_2554_, v___x_2560_, v___x_2561_, v___x_2555_);
return v___x_2562_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0(lean_object* v_inst_2563_, lean_object* v_a_2564_, lean_object* v_x1_2565_, lean_object* v_x2_2566_){
_start:
{
lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2567_ = lean_apply_2(v_inst_2563_, v_x1_2565_, v_a_2564_);
v___x_2568_ = lean_unbox(v___x_2567_);
if (v___x_2568_ == 0)
{
lean_inc(v_x2_2566_);
return v_x2_2566_;
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = lean_unsigned_to_nat(1u);
v___x_2570_ = lean_nat_add(v_x2_2566_, v___x_2569_);
return v___x_2570_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0___boxed(lean_object* v_inst_2571_, lean_object* v_a_2572_, lean_object* v_x1_2573_, lean_object* v_x2_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Array_count___redArg___lam__0(v_inst_2571_, v_a_2572_, v_x1_2573_, v_x2_2574_);
lean_dec(v_x2_2574_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg(lean_object* v_inst_2576_, lean_object* v_a_2577_, lean_object* v_as_2578_){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v___x_2579_ = lean_unsigned_to_nat(0u);
v___x_2580_ = lean_array_get_size(v_as_2578_);
v___x_2581_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2582_ = lean_nat_dec_lt(v___x_2579_, v___x_2580_);
if (v___x_2582_ == 0)
{
lean_dec_ref(v_as_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_inst_2576_);
return v___x_2579_;
}
else
{
lean_object* v___f_2583_; size_t v___x_2584_; size_t v___x_2585_; lean_object* v___x_2586_; 
v___f_2583_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2583_, 0, v_inst_2576_);
lean_closure_set(v___f_2583_, 1, v_a_2577_);
v___x_2584_ = lean_usize_of_nat(v___x_2580_);
v___x_2585_ = ((size_t)0ULL);
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2581_, v___f_2583_, v_as_2578_, v___x_2584_, v___x_2585_, v___x_2579_);
return v___x_2586_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count(lean_object* v_00_u03b1_2587_, lean_object* v_inst_2588_, lean_object* v_a_2589_, lean_object* v_as_2590_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; 
v___x_2591_ = lean_unsigned_to_nat(0u);
v___x_2592_ = lean_array_get_size(v_as_2590_);
v___x_2593_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2594_ = lean_nat_dec_lt(v___x_2591_, v___x_2592_);
if (v___x_2594_ == 0)
{
lean_dec_ref(v_as_2590_);
lean_dec(v_a_2589_);
lean_dec_ref(v_inst_2588_);
return v___x_2591_;
}
else
{
lean_object* v___f_2595_; size_t v___x_2596_; size_t v___x_2597_; lean_object* v___x_2598_; 
v___f_2595_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2595_, 0, v_inst_2588_);
lean_closure_set(v___f_2595_, 1, v_a_2589_);
v___x_2596_ = lean_usize_of_nat(v___x_2592_);
v___x_2597_ = ((size_t)0ULL);
v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2593_, v___f_2595_, v_as_2590_, v___x_2596_, v___x_2597_, v___x_2591_);
return v___x_2598_;
}
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg___lam__0(lean_object* v_f_2599_, lean_object* v_x_2600_){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_apply_1(v_f_2599_, v_x_2600_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg(lean_object* v_f_2602_, lean_object* v_as_2603_){
_start:
{
lean_object* v___f_2604_; lean_object* v___x_2605_; size_t v_sz_2606_; size_t v___x_2607_; lean_object* v___x_2608_; 
v___f_2604_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2604_, 0, v_f_2602_);
v___x_2605_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2606_ = lean_array_size(v_as_2603_);
v___x_2607_ = ((size_t)0ULL);
v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2605_, v___f_2604_, v_sz_2606_, v___x_2607_, v_as_2603_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Array_map(lean_object* v_00_u03b1_2609_, lean_object* v_00_u03b2_2610_, lean_object* v_f_2611_, lean_object* v_as_2612_){
_start:
{
lean_object* v___f_2613_; lean_object* v___x_2614_; size_t v_sz_2615_; size_t v___x_2616_; lean_object* v___x_2617_; 
v___f_2613_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2613_, 0, v_f_2611_);
v___x_2614_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2615_ = lean_array_size(v_as_2612_);
v___x_2616_ = ((size_t)0ULL);
v___x_2617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2614_, v___f_2613_, v_sz_2615_, v___x_2616_, v_as_2612_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0(lean_object* v___y_2618_, lean_object* v_x_2619_){
_start:
{
lean_inc(v___y_2618_);
return v___y_2618_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0___boxed(lean_object* v___y_2620_, lean_object* v_x_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Array_instFunctor___lam__0(v___y_2620_, v_x_2621_);
lean_dec(v_x_2621_);
lean_dec(v___y_2620_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__1(lean_object* v_00_u03b1_2623_, lean_object* v_00_u03b2_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v___f_2627_; lean_object* v___x_2628_; size_t v_sz_2629_; size_t v___x_2630_; lean_object* v___x_2631_; 
v___f_2627_ = lean_alloc_closure((void*)(l_Array_instFunctor___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2627_, 0, v___y_2625_);
v___x_2628_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2629_ = lean_array_size(v___y_2626_);
v___x_2630_ = ((size_t)0ULL);
v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2628_, v___f_2627_, v_sz_2629_, v___x_2630_, v___y_2626_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg___lam__0(lean_object* v_f_2638_, lean_object* v_x1_2639_, lean_object* v_x2_2640_, lean_object* v_x3_2641_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = lean_apply_3(v_f_2638_, v_x1_2639_, v_x2_2640_, lean_box(0));
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg(lean_object* v_as_2643_, lean_object* v_f_2644_){
_start:
{
lean_object* v___f_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___f_2645_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2645_, 0, v_f_2644_);
v___x_2646_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2647_ = lean_array_get_size(v_as_2643_);
v___x_2648_ = lean_unsigned_to_nat(0u);
v___x_2649_ = lean_mk_empty_array_with_capacity(v___x_2647_);
v___x_2650_ = l_Array_mapFinIdxM_map___redArg(v___x_2646_, v_as_2643_, v___f_2645_, v___x_2647_, v___x_2648_, v___x_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx(lean_object* v_00_u03b1_2651_, lean_object* v_00_u03b2_2652_, lean_object* v_as_2653_, lean_object* v_f_2654_){
_start:
{
lean_object* v___f_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___f_2655_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2655_, 0, v_f_2654_);
v___x_2656_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2657_ = lean_array_get_size(v_as_2653_);
v___x_2658_ = lean_unsigned_to_nat(0u);
v___x_2659_ = lean_mk_empty_array_with_capacity(v___x_2657_);
v___x_2660_ = l_Array_mapFinIdxM_map___redArg(v___x_2656_, v_as_2653_, v___f_2655_, v___x_2657_, v___x_2658_, v___x_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx___redArg(lean_object* v_f_2661_, lean_object* v_as_2662_){
_start:
{
lean_object* v___f_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___f_2663_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2663_, 0, v_f_2661_);
v___x_2664_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2665_ = lean_array_get_size(v_as_2662_);
v___x_2666_ = lean_unsigned_to_nat(0u);
v___x_2667_ = lean_mk_empty_array_with_capacity(v___x_2665_);
v___x_2668_ = l_Array_mapFinIdxM_map___redArg(v___x_2664_, v_as_2662_, v___f_2663_, v___x_2665_, v___x_2666_, v___x_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx(lean_object* v_00_u03b1_2669_, lean_object* v_00_u03b2_2670_, lean_object* v_f_2671_, lean_object* v_as_2672_){
_start:
{
lean_object* v___f_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___f_2673_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2673_, 0, v_f_2671_);
v___x_2674_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2675_ = lean_array_get_size(v_as_2672_);
v___x_2676_ = lean_unsigned_to_nat(0u);
v___x_2677_ = lean_mk_empty_array_with_capacity(v___x_2675_);
v___x_2678_ = l_Array_mapFinIdxM_map___redArg(v___x_2674_, v_as_2672_, v___f_2673_, v___x_2675_, v___x_2676_, v___x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(lean_object* v_start_2679_, lean_object* v_as_2680_, lean_object* v_i_2681_, lean_object* v_j_2682_, lean_object* v_bs_2683_){
_start:
{
lean_object* v_zero_2684_; uint8_t v_isZero_2685_; 
v_zero_2684_ = lean_unsigned_to_nat(0u);
v_isZero_2685_ = lean_nat_dec_eq(v_i_2681_, v_zero_2684_);
if (v_isZero_2685_ == 1)
{
lean_dec(v_j_2682_);
lean_dec(v_i_2681_);
return v_bs_2683_;
}
else
{
lean_object* v_one_2686_; lean_object* v_n_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_one_2686_ = lean_unsigned_to_nat(1u);
v_n_2687_ = lean_nat_sub(v_i_2681_, v_one_2686_);
lean_dec(v_i_2681_);
v___x_2688_ = lean_array_fget_borrowed(v_as_2680_, v_j_2682_);
v___x_2689_ = lean_nat_add(v_start_2679_, v_j_2682_);
lean_inc(v___x_2688_);
v___x_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2688_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
v___x_2691_ = lean_nat_add(v_j_2682_, v_one_2686_);
lean_dec(v_j_2682_);
v___x_2692_ = lean_array_push(v_bs_2683_, v___x_2690_);
v_i_2681_ = v_n_2687_;
v_j_2682_ = v___x_2691_;
v_bs_2683_ = v___x_2692_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg___boxed(lean_object* v_start_2694_, lean_object* v_as_2695_, lean_object* v_i_2696_, lean_object* v_j_2697_, lean_object* v_bs_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(v_start_2694_, v_as_2695_, v_i_2696_, v_j_2697_, v_bs_2698_);
lean_dec_ref(v_as_2695_);
lean_dec(v_start_2694_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg(lean_object* v_xs_2700_, lean_object* v_start_2701_){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2702_ = lean_array_get_size(v_xs_2700_);
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = lean_mk_empty_array_with_capacity(v___x_2702_);
v___x_2705_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(v_start_2701_, v_xs_2700_, v___x_2702_, v___x_2703_, v___x_2704_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg___boxed(lean_object* v_xs_2706_, lean_object* v_start_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Array_zipIdx___redArg(v_xs_2706_, v_start_2707_);
lean_dec(v_start_2707_);
lean_dec_ref(v_xs_2706_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx(lean_object* v_00_u03b1_2709_, lean_object* v_xs_2710_, lean_object* v_start_2711_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Array_zipIdx___redArg(v_xs_2710_, v_start_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___boxed(lean_object* v_00_u03b1_2713_, lean_object* v_xs_2714_, lean_object* v_start_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Array_zipIdx(v_00_u03b1_2713_, v_xs_2714_, v_start_2715_);
lean_dec(v_start_2715_);
lean_dec_ref(v_xs_2714_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0(lean_object* v_00_u03b1_2717_, lean_object* v_start_2718_, lean_object* v_as_2719_, lean_object* v_i_2720_, lean_object* v_j_2721_, lean_object* v_inv_2722_, lean_object* v_bs_2723_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(v_start_2718_, v_as_2719_, v_i_2720_, v_j_2721_, v_bs_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___boxed(lean_object* v_00_u03b1_2725_, lean_object* v_start_2726_, lean_object* v_as_2727_, lean_object* v_i_2728_, lean_object* v_j_2729_, lean_object* v_inv_2730_, lean_object* v_bs_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0(v_00_u03b1_2725_, v_start_2726_, v_as_2727_, v_i_2728_, v_j_2729_, v_inv_2730_, v_bs_2731_);
lean_dec_ref(v_as_2727_);
lean_dec(v_start_2726_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0(lean_object* v_p_2733_, lean_object* v___x_2734_, lean_object* v___x_2735_, lean_object* v_a_2736_, lean_object* v_x_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
lean_inc(v_a_2736_);
v___x_2739_ = lean_apply_1(v_p_2733_, v_a_2736_);
v___x_2740_ = lean_unbox(v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; 
lean_dec(v_a_2736_);
v___x_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2734_);
return v___x_2741_;
}
else
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_dec_ref(v___x_2734_);
v___x_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2742_, 0, v_a_2736_);
v___x_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2742_);
v___x_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
lean_ctor_set(v___x_2744_, 1, v___x_2735_);
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0___boxed(lean_object* v_p_2746_, lean_object* v___x_2747_, lean_object* v___x_2748_, lean_object* v_a_2749_, lean_object* v_x_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Array_find_x3f___redArg___lam__0(v_p_2746_, v___x_2747_, v___x_2748_, v_a_2749_, v_x_2750_, v___y_2751_);
lean_dec_ref(v___y_2751_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg(lean_object* v_p_2753_, lean_object* v_as_2754_){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___f_2759_; size_t v_sz_2760_; size_t v___x_2761_; lean_object* v___x_2762_; lean_object* v_fst_2763_; 
v___x_2755_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2756_ = lean_box(0);
v___x_2757_ = lean_box(0);
v___x_2758_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2759_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2759_, 0, v_p_2753_);
lean_closure_set(v___f_2759_, 1, v___x_2758_);
lean_closure_set(v___f_2759_, 2, v___x_2757_);
v_sz_2760_ = lean_array_size(v_as_2754_);
v___x_2761_ = ((size_t)0ULL);
v___x_2762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2755_, v_as_2754_, v___f_2759_, v_sz_2760_, v___x_2761_, v___x_2758_);
v_fst_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_fst_2763_);
lean_dec(v___x_2762_);
if (lean_obj_tag(v_fst_2763_) == 0)
{
return v___x_2756_;
}
else
{
lean_object* v_val_2764_; 
v_val_2764_ = lean_ctor_get(v_fst_2763_, 0);
lean_inc(v_val_2764_);
lean_dec_ref(v_fst_2763_);
return v_val_2764_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f(lean_object* v_00_u03b1_2765_, lean_object* v_p_2766_, lean_object* v_as_2767_){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___f_2772_; size_t v_sz_2773_; size_t v___x_2774_; lean_object* v___x_2775_; lean_object* v_fst_2776_; 
v___x_2768_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2769_ = lean_box(0);
v___x_2770_ = lean_box(0);
v___x_2771_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2772_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2772_, 0, v_p_2766_);
lean_closure_set(v___f_2772_, 1, v___x_2771_);
lean_closure_set(v___f_2772_, 2, v___x_2770_);
v_sz_2773_ = lean_array_size(v_as_2767_);
v___x_2774_ = ((size_t)0ULL);
v___x_2775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2768_, v_as_2767_, v___f_2772_, v_sz_2773_, v___x_2774_, v___x_2771_);
v_fst_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_fst_2776_);
lean_dec(v___x_2775_);
if (lean_obj_tag(v_fst_2776_) == 0)
{
return v___x_2769_;
}
else
{
lean_object* v_val_2777_; 
v_val_2777_ = lean_ctor_get(v_fst_2776_, 0);
lean_inc(v_val_2777_);
lean_dec_ref(v_fst_2776_);
return v_val_2777_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0(lean_object* v_f_2778_, lean_object* v___x_2779_, lean_object* v___x_2780_, lean_object* v_a_2781_, lean_object* v_x_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_apply_1(v_f_2778_, v_a_2781_);
if (lean_obj_tag(v___x_2784_) == 1)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
lean_dec_ref(v___x_2780_);
v___x_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
v___x_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v___x_2779_);
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
return v___x_2787_;
}
else
{
lean_object* v___x_2788_; 
lean_dec(v___x_2784_);
v___x_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2780_);
return v___x_2788_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2789_, lean_object* v___x_2790_, lean_object* v___x_2791_, lean_object* v_a_2792_, lean_object* v_x_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Array_findSome_x3f___redArg___lam__0(v_f_2789_, v___x_2790_, v___x_2791_, v_a_2792_, v_x_2793_, v___y_2794_);
lean_dec_ref(v___y_2794_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg(lean_object* v_f_2796_, lean_object* v_as_2797_){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___f_2802_; size_t v_sz_2803_; size_t v___x_2804_; lean_object* v___x_2805_; lean_object* v_fst_2806_; 
v___x_2798_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2799_ = lean_box(0);
v___x_2800_ = lean_box(0);
v___x_2801_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2802_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2802_, 0, v_f_2796_);
lean_closure_set(v___f_2802_, 1, v___x_2800_);
lean_closure_set(v___f_2802_, 2, v___x_2801_);
v_sz_2803_ = lean_array_size(v_as_2797_);
v___x_2804_ = ((size_t)0ULL);
v___x_2805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2798_, v_as_2797_, v___f_2802_, v_sz_2803_, v___x_2804_, v___x_2801_);
v_fst_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_fst_2806_);
lean_dec(v___x_2805_);
if (lean_obj_tag(v_fst_2806_) == 0)
{
return v___x_2799_;
}
else
{
lean_object* v_val_2807_; 
v_val_2807_ = lean_ctor_get(v_fst_2806_, 0);
lean_inc(v_val_2807_);
lean_dec_ref(v_fst_2806_);
return v_val_2807_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f(lean_object* v_00_u03b1_2808_, lean_object* v_00_u03b2_2809_, lean_object* v_f_2810_, lean_object* v_as_2811_){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___f_2816_; size_t v_sz_2817_; size_t v___x_2818_; lean_object* v___x_2819_; lean_object* v_fst_2820_; 
v___x_2812_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2813_ = lean_box(0);
v___x_2814_ = lean_box(0);
v___x_2815_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2816_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2816_, 0, v_f_2810_);
lean_closure_set(v___f_2816_, 1, v___x_2814_);
lean_closure_set(v___f_2816_, 2, v___x_2815_);
v_sz_2817_ = lean_array_size(v_as_2811_);
v___x_2818_ = ((size_t)0ULL);
v___x_2819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2812_, v_as_2811_, v___f_2816_, v_sz_2817_, v___x_2818_, v___x_2815_);
v_fst_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_fst_2820_);
lean_dec(v___x_2819_);
if (lean_obj_tag(v_fst_2820_) == 0)
{
return v___x_2813_;
}
else
{
lean_object* v_val_2821_; 
v_val_2821_ = lean_ctor_get(v_fst_2820_, 0);
lean_inc(v_val_2821_);
lean_dec_ref(v_fst_2820_);
return v_val_2821_;
}
}
}
static lean_object* _init_l_Array_findSome_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2824_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__1));
v___x_2825_ = lean_unsigned_to_nat(14u);
v___x_2826_ = lean_unsigned_to_nat(1231u);
v___x_2827_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__0));
v___x_2828_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_2829_ = l_mkPanicMessageWithDecl(v___x_2828_, v___x_2827_, v___x_2826_, v___x_2825_, v___x_2824_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg(lean_object* v_inst_2830_, lean_object* v_f_2831_, lean_object* v_xs_2832_){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___f_2839_; size_t v_sz_2840_; size_t v___x_2841_; lean_object* v___x_2842_; lean_object* v_fst_2843_; 
v___x_2836_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2837_ = lean_box(0);
v___x_2838_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2839_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2839_, 0, v_f_2831_);
lean_closure_set(v___f_2839_, 1, v___x_2837_);
lean_closure_set(v___f_2839_, 2, v___x_2838_);
v_sz_2840_ = lean_array_size(v_xs_2832_);
v___x_2841_ = ((size_t)0ULL);
v___x_2842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2836_, v_xs_2832_, v___f_2839_, v_sz_2840_, v___x_2841_, v___x_2838_);
v_fst_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_fst_2843_);
lean_dec(v___x_2842_);
if (lean_obj_tag(v_fst_2843_) == 0)
{
goto v___jp_2833_;
}
else
{
lean_object* v_val_2844_; 
v_val_2844_ = lean_ctor_get(v_fst_2843_, 0);
lean_inc(v_val_2844_);
lean_dec_ref(v_fst_2843_);
if (lean_obj_tag(v_val_2844_) == 0)
{
goto v___jp_2833_;
}
else
{
lean_object* v_val_2845_; 
v_val_2845_ = lean_ctor_get(v_val_2844_, 0);
lean_inc(v_val_2845_);
lean_dec_ref(v_val_2844_);
return v_val_2845_;
}
}
v___jp_2833_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2835_ = l_panic___redArg(v_inst_2830_, v___x_2834_);
return v___x_2835_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg___boxed(lean_object* v_inst_2846_, lean_object* v_f_2847_, lean_object* v_xs_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Array_findSome_x21___redArg(v_inst_2846_, v_f_2847_, v_xs_2848_);
lean_dec(v_inst_2846_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21(lean_object* v_00_u03b1_2850_, lean_object* v_00_u03b2_2851_, lean_object* v_inst_2852_, lean_object* v_f_2853_, lean_object* v_xs_2854_){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___f_2861_; size_t v_sz_2862_; size_t v___x_2863_; lean_object* v___x_2864_; lean_object* v_fst_2865_; 
v___x_2858_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2859_ = lean_box(0);
v___x_2860_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2861_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2861_, 0, v_f_2853_);
lean_closure_set(v___f_2861_, 1, v___x_2859_);
lean_closure_set(v___f_2861_, 2, v___x_2860_);
v_sz_2862_ = lean_array_size(v_xs_2854_);
v___x_2863_ = ((size_t)0ULL);
v___x_2864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2858_, v_xs_2854_, v___f_2861_, v_sz_2862_, v___x_2863_, v___x_2860_);
v_fst_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_fst_2865_);
lean_dec(v___x_2864_);
if (lean_obj_tag(v_fst_2865_) == 0)
{
goto v___jp_2855_;
}
else
{
lean_object* v_val_2866_; 
v_val_2866_ = lean_ctor_get(v_fst_2865_, 0);
lean_inc(v_val_2866_);
lean_dec_ref(v_fst_2865_);
if (lean_obj_tag(v_val_2866_) == 0)
{
goto v___jp_2855_;
}
else
{
lean_object* v_val_2867_; 
v_val_2867_ = lean_ctor_get(v_val_2866_, 0);
lean_inc(v_val_2867_);
lean_dec_ref(v_val_2866_);
return v_val_2867_;
}
}
v___jp_2855_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2857_ = l_panic___redArg(v_inst_2852_, v___x_2856_);
return v___x_2857_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___boxed(lean_object* v_00_u03b1_2868_, lean_object* v_00_u03b2_2869_, lean_object* v_inst_2870_, lean_object* v_f_2871_, lean_object* v_xs_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Array_findSome_x21(v_00_u03b1_2868_, v_00_u03b2_2869_, v_inst_2870_, v_f_2871_, v_xs_2872_);
lean_dec(v_inst_2870_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2874_, lean_object* v_x_2875_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = lean_apply_1(v_f_2874_, v_x_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg(lean_object* v_f_2877_, lean_object* v_as_2878_){
_start:
{
lean_object* v___f_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___f_2879_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2879_, 0, v_f_2877_);
v___x_2880_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2881_ = lean_array_get_size(v_as_2878_);
v___x_2882_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2880_, v___f_2879_, v_as_2878_, v___x_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f(lean_object* v_00_u03b1_2883_, lean_object* v_00_u03b2_2884_, lean_object* v_f_2885_, lean_object* v_as_2886_){
_start:
{
lean_object* v___f_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___f_2887_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2887_, 0, v_f_2885_);
v___x_2888_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2889_ = lean_array_get_size(v_as_2886_);
v___x_2890_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2888_, v___f_2887_, v_as_2886_, v___x_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg___lam__0(lean_object* v_p_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v___x_2893_; uint8_t v___x_2894_; 
lean_inc(v_a_2892_);
v___x_2893_ = lean_apply_1(v_p_2891_, v_a_2892_);
v___x_2894_ = lean_unbox(v___x_2893_);
if (v___x_2894_ == 0)
{
lean_object* v___x_2895_; 
lean_dec(v_a_2892_);
v___x_2895_ = lean_box(0);
return v___x_2895_;
}
else
{
lean_object* v___x_2896_; 
v___x_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2896_, 0, v_a_2892_);
return v___x_2896_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg(lean_object* v_p_2897_, lean_object* v_as_2898_){
_start:
{
lean_object* v___f_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___f_2899_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2899_, 0, v_p_2897_);
v___x_2900_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2901_ = lean_array_get_size(v_as_2898_);
v___x_2902_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2900_, v___f_2899_, v_as_2898_, v___x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f(lean_object* v_00_u03b1_2903_, lean_object* v_p_2904_, lean_object* v_as_2905_){
_start:
{
lean_object* v___f_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___f_2906_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2906_, 0, v_p_2904_);
v___x_2907_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2908_ = lean_array_get_size(v_as_2905_);
v___x_2909_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2907_, v___f_2906_, v_as_2905_, v___x_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object* v_p_2910_, lean_object* v_as_2911_, lean_object* v_j_2912_){
_start:
{
lean_object* v___x_2913_; uint8_t v___x_2914_; 
v___x_2913_ = lean_array_get_size(v_as_2911_);
v___x_2914_ = lean_nat_dec_lt(v_j_2912_, v___x_2913_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; 
lean_dec(v_j_2912_);
lean_dec_ref(v_p_2910_);
v___x_2915_ = lean_box(0);
return v___x_2915_;
}
else
{
lean_object* v___x_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; 
v___x_2916_ = lean_array_fget_borrowed(v_as_2911_, v_j_2912_);
lean_inc_ref(v_p_2910_);
lean_inc(v___x_2916_);
v___x_2917_ = lean_apply_1(v_p_2910_, v___x_2916_);
v___x_2918_ = lean_unbox(v___x_2917_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = lean_unsigned_to_nat(1u);
v___x_2920_ = lean_nat_add(v_j_2912_, v___x_2919_);
lean_dec(v_j_2912_);
v_j_2912_ = v___x_2920_;
goto _start;
}
else
{
lean_object* v___x_2922_; 
lean_dec_ref(v_p_2910_);
v___x_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2922_, 0, v_j_2912_);
return v___x_2922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg___boxed(lean_object* v_p_2923_, lean_object* v_as_2924_, lean_object* v_j_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_Array_findIdx_x3f_loop___redArg(v_p_2923_, v_as_2924_, v_j_2925_);
lean_dec_ref(v_as_2924_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop(lean_object* v_00_u03b1_2927_, lean_object* v_p_2928_, lean_object* v_as_2929_, lean_object* v_j_2930_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Array_findIdx_x3f_loop___redArg(v_p_2928_, v_as_2929_, v_j_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___boxed(lean_object* v_00_u03b1_2932_, lean_object* v_p_2933_, lean_object* v_as_2934_, lean_object* v_j_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Array_findIdx_x3f_loop(v_00_u03b1_2932_, v_p_2933_, v_as_2934_, v_j_2935_);
lean_dec_ref(v_as_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg(lean_object* v_p_2937_, lean_object* v_as_2938_){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = lean_unsigned_to_nat(0u);
v___x_2940_ = l_Array_findIdx_x3f_loop___redArg(v_p_2937_, v_as_2938_, v___x_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg___boxed(lean_object* v_p_2941_, lean_object* v_as_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Array_findIdx_x3f___redArg(v_p_2941_, v_as_2942_);
lean_dec_ref(v_as_2942_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f(lean_object* v_00_u03b1_2944_, lean_object* v_p_2945_, lean_object* v_as_2946_){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = lean_unsigned_to_nat(0u);
v___x_2948_ = l_Array_findIdx_x3f_loop___redArg(v_p_2945_, v_as_2946_, v___x_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___boxed(lean_object* v_00_u03b1_2949_, lean_object* v_p_2950_, lean_object* v_as_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Array_findIdx_x3f(v_00_u03b1_2949_, v_p_2950_, v_as_2951_);
lean_dec_ref(v_as_2951_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(lean_object* v_p_2953_, lean_object* v_as_2954_, lean_object* v_j_2955_){
_start:
{
lean_object* v___x_2956_; uint8_t v___x_2957_; 
v___x_2956_ = lean_array_get_size(v_as_2954_);
v___x_2957_ = lean_nat_dec_lt(v_j_2955_, v___x_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; 
lean_dec(v_j_2955_);
lean_dec_ref(v_p_2953_);
v___x_2958_ = lean_box(0);
return v___x_2958_;
}
else
{
lean_object* v___x_2959_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v___x_2959_ = lean_array_fget_borrowed(v_as_2954_, v_j_2955_);
lean_inc_ref(v_p_2953_);
lean_inc(v___x_2959_);
v___x_2960_ = lean_apply_1(v_p_2953_, v___x_2959_);
v___x_2961_ = lean_unbox(v___x_2960_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = lean_unsigned_to_nat(1u);
v___x_2963_ = lean_nat_add(v_j_2955_, v___x_2962_);
lean_dec(v_j_2955_);
v_j_2955_ = v___x_2963_;
goto _start;
}
else
{
lean_object* v___x_2965_; 
lean_dec_ref(v_p_2953_);
v___x_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2965_, 0, v_j_2955_);
return v___x_2965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg___boxed(lean_object* v_p_2966_, lean_object* v_as_2967_, lean_object* v_j_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2966_, v_as_2967_, v_j_2968_);
lean_dec_ref(v_as_2967_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object* v_00_u03b1_2970_, lean_object* v_p_2971_, lean_object* v_as_2972_, lean_object* v_j_2973_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2971_, v_as_2972_, v_j_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___boxed(lean_object* v_00_u03b1_2975_, lean_object* v_p_2976_, lean_object* v_as_2977_, lean_object* v_j_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(v_00_u03b1_2975_, v_p_2976_, v_as_2977_, v_j_2978_);
lean_dec_ref(v_as_2977_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg(lean_object* v_p_2980_, lean_object* v_as_2981_){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = lean_unsigned_to_nat(0u);
v___x_2983_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2980_, v_as_2981_, v___x_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg___boxed(lean_object* v_p_2984_, lean_object* v_as_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_Array_findFinIdx_x3f___redArg(v_p_2984_, v_as_2985_);
lean_dec_ref(v_as_2985_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f(lean_object* v_00_u03b1_2987_, lean_object* v_p_2988_, lean_object* v_as_2989_){
_start:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = lean_unsigned_to_nat(0u);
v___x_2991_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2988_, v_as_2989_, v___x_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_2992_, lean_object* v_p_2993_, lean_object* v_as_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Array_findFinIdx_x3f(v_00_u03b1_2992_, v_p_2993_, v_as_2994_);
lean_dec_ref(v_as_2994_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg(lean_object* v_p_2996_, lean_object* v_as_2997_){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = lean_unsigned_to_nat(0u);
v___x_2999_ = l_Array_findIdx_x3f_loop___redArg(v_p_2996_, v_as_2997_, v___x_2998_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_array_get_size(v_as_2997_);
return v___x_3000_;
}
else
{
lean_object* v_val_3001_; 
v_val_3001_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_val_3001_);
lean_dec_ref(v___x_2999_);
return v_val_3001_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg___boxed(lean_object* v_p_3002_, lean_object* v_as_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Array_findIdx___redArg(v_p_3002_, v_as_3003_);
lean_dec_ref(v_as_3003_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx(lean_object* v_00_u03b1_3005_, lean_object* v_p_3006_, lean_object* v_as_3007_){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = lean_unsigned_to_nat(0u);
v___x_3009_ = l_Array_findIdx_x3f_loop___redArg(v_p_3006_, v_as_3007_, v___x_3008_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v___x_3010_; 
v___x_3010_ = lean_array_get_size(v_as_3007_);
return v___x_3010_;
}
else
{
lean_object* v_val_3011_; 
v_val_3011_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_val_3011_);
lean_dec_ref(v___x_3009_);
return v_val_3011_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___boxed(lean_object* v_00_u03b1_3012_, lean_object* v_p_3013_, lean_object* v_as_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l_Array_findIdx(v_00_u03b1_3012_, v_p_3013_, v_as_3014_);
lean_dec_ref(v_as_3014_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg(lean_object* v_inst_3016_, lean_object* v_xs_3017_, lean_object* v_v_3018_, lean_object* v_i_3019_){
_start:
{
lean_object* v___x_3020_; uint8_t v___x_3021_; 
v___x_3020_ = lean_array_get_size(v_xs_3017_);
v___x_3021_ = lean_nat_dec_lt(v_i_3019_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; 
lean_dec(v_i_3019_);
lean_dec(v_v_3018_);
lean_dec_ref(v_inst_3016_);
v___x_3022_ = lean_box(0);
return v___x_3022_;
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; 
v___x_3023_ = lean_array_fget_borrowed(v_xs_3017_, v_i_3019_);
lean_inc_ref(v_inst_3016_);
lean_inc(v_v_3018_);
lean_inc(v___x_3023_);
v___x_3024_ = lean_apply_2(v_inst_3016_, v___x_3023_, v_v_3018_);
v___x_3025_ = lean_unbox(v___x_3024_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = lean_unsigned_to_nat(1u);
v___x_3027_ = lean_nat_add(v_i_3019_, v___x_3026_);
lean_dec(v_i_3019_);
v_i_3019_ = v___x_3027_;
goto _start;
}
else
{
lean_object* v___x_3029_; 
lean_dec(v_v_3018_);
lean_dec_ref(v_inst_3016_);
v___x_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3029_, 0, v_i_3019_);
return v___x_3029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg___boxed(lean_object* v_inst_3030_, lean_object* v_xs_3031_, lean_object* v_v_3032_, lean_object* v_i_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Array_idxOfAux___redArg(v_inst_3030_, v_xs_3031_, v_v_3032_, v_i_3033_);
lean_dec_ref(v_xs_3031_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux(lean_object* v_00_u03b1_3035_, lean_object* v_inst_3036_, lean_object* v_xs_3037_, lean_object* v_v_3038_, lean_object* v_i_3039_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Array_idxOfAux___redArg(v_inst_3036_, v_xs_3037_, v_v_3038_, v_i_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___boxed(lean_object* v_00_u03b1_3041_, lean_object* v_inst_3042_, lean_object* v_xs_3043_, lean_object* v_v_3044_, lean_object* v_i_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Array_idxOfAux(v_00_u03b1_3041_, v_inst_3042_, v_xs_3043_, v_v_3044_, v_i_3045_);
lean_dec_ref(v_xs_3043_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg(lean_object* v_inst_3047_, lean_object* v_xs_3048_, lean_object* v_v_3049_){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_unsigned_to_nat(0u);
v___x_3051_ = l_Array_idxOfAux___redArg(v_inst_3047_, v_xs_3048_, v_v_3049_, v___x_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_3052_, lean_object* v_xs_3053_, lean_object* v_v_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Array_finIdxOf_x3f___redArg(v_inst_3052_, v_xs_3053_, v_v_3054_);
lean_dec_ref(v_xs_3053_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f(lean_object* v_00_u03b1_3056_, lean_object* v_inst_3057_, lean_object* v_xs_3058_, lean_object* v_v_3059_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Array_finIdxOf_x3f___redArg(v_inst_3057_, v_xs_3058_, v_v_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_3061_, lean_object* v_inst_3062_, lean_object* v_xs_3063_, lean_object* v_v_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Array_finIdxOf_x3f(v_00_u03b1_3061_, v_inst_3062_, v_xs_3063_, v_v_3064_);
lean_dec_ref(v_xs_3063_);
return v_res_3065_;
}
}
LEAN_EXPORT uint8_t l_Array_idxOf___redArg___lam__0(lean_object* v_inst_3066_, lean_object* v_a_3067_, lean_object* v_x_3068_){
_start:
{
lean_object* v___x_3069_; uint8_t v___x_3070_; 
v___x_3069_ = lean_apply_2(v_inst_3066_, v_x_3068_, v_a_3067_);
v___x_3070_ = lean_unbox(v___x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___lam__0___boxed(lean_object* v_inst_3071_, lean_object* v_a_3072_, lean_object* v_x_3073_){
_start:
{
uint8_t v_res_3074_; lean_object* v_r_3075_; 
v_res_3074_ = l_Array_idxOf___redArg___lam__0(v_inst_3071_, v_a_3072_, v_x_3073_);
v_r_3075_ = lean_box(v_res_3074_);
return v_r_3075_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg(lean_object* v_inst_3076_, lean_object* v_a_3077_, lean_object* v_as_3078_){
_start:
{
lean_object* v___f_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___f_3079_ = lean_alloc_closure((void*)(l_Array_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3079_, 0, v_inst_3076_);
lean_closure_set(v___f_3079_, 1, v_a_3077_);
v___x_3080_ = lean_unsigned_to_nat(0u);
v___x_3081_ = l_Array_findIdx_x3f_loop___redArg(v___f_3079_, v_as_3078_, v___x_3080_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v___x_3082_; 
v___x_3082_ = lean_array_get_size(v_as_3078_);
return v___x_3082_;
}
else
{
lean_object* v_val_3083_; 
v_val_3083_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_val_3083_);
lean_dec_ref(v___x_3081_);
return v_val_3083_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___boxed(lean_object* v_inst_3084_, lean_object* v_a_3085_, lean_object* v_as_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l_Array_idxOf___redArg(v_inst_3084_, v_a_3085_, v_as_3086_);
lean_dec_ref(v_as_3086_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf(lean_object* v_00_u03b1_3088_, lean_object* v_inst_3089_, lean_object* v_a_3090_, lean_object* v_as_3091_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = l_Array_idxOf___redArg(v_inst_3089_, v_a_3090_, v_as_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___boxed(lean_object* v_00_u03b1_3093_, lean_object* v_inst_3094_, lean_object* v_a_3095_, lean_object* v_as_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Array_idxOf(v_00_u03b1_3093_, v_inst_3094_, v_a_3095_, v_as_3096_);
lean_dec_ref(v_as_3096_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg(lean_object* v_inst_3098_, lean_object* v_xs_3099_, lean_object* v_v_3100_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Array_finIdxOf_x3f___redArg(v_inst_3098_, v_xs_3099_, v_v_3100_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v___x_3102_; 
v___x_3102_ = lean_box(0);
return v___x_3102_;
}
else
{
lean_object* v_val_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
v_val_3103_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3101_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_val_3103_);
lean_dec(v___x_3101_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_val_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg___boxed(lean_object* v_inst_3111_, lean_object* v_xs_3112_, lean_object* v_v_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Array_idxOf_x3f___redArg(v_inst_3111_, v_xs_3112_, v_v_3113_);
lean_dec_ref(v_xs_3112_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f(lean_object* v_00_u03b1_3115_, lean_object* v_inst_3116_, lean_object* v_xs_3117_, lean_object* v_v_3118_){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = l_Array_idxOf_x3f___redArg(v_inst_3116_, v_xs_3117_, v_v_3118_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___boxed(lean_object* v_00_u03b1_3120_, lean_object* v_inst_3121_, lean_object* v_xs_3122_, lean_object* v_v_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Array_idxOf_x3f(v_00_u03b1_3120_, v_inst_3121_, v_xs_3122_, v_v_3123_);
lean_dec_ref(v_xs_3122_);
return v_res_3124_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg___lam__0(lean_object* v_p_3125_, lean_object* v_x_3126_){
_start:
{
lean_object* v___x_3127_; uint8_t v___x_3128_; 
v___x_3127_ = lean_apply_1(v_p_3125_, v_x_3126_);
v___x_3128_ = lean_unbox(v___x_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___lam__0___boxed(lean_object* v_p_3129_, lean_object* v_x_3130_){
_start:
{
uint8_t v_res_3131_; lean_object* v_r_3132_; 
v_res_3131_ = l_Array_any___redArg___lam__0(v_p_3129_, v_x_3130_);
v_r_3132_ = lean_box(v_res_3131_);
return v_r_3132_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg(lean_object* v_as_3133_, lean_object* v_p_3134_, lean_object* v_start_3135_, lean_object* v_stop_3136_){
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
LEAN_EXPORT lean_object* l_Array_any___redArg___boxed(lean_object* v_as_3149_, lean_object* v_p_3150_, lean_object* v_start_3151_, lean_object* v_stop_3152_){
_start:
{
uint8_t v_res_3153_; lean_object* v_r_3154_; 
v_res_3153_ = l_Array_any___redArg(v_as_3149_, v_p_3150_, v_start_3151_, v_stop_3152_);
lean_dec(v_start_3151_);
v_r_3154_ = lean_box(v_res_3153_);
return v_r_3154_;
}
}
LEAN_EXPORT uint8_t l_Array_any(lean_object* v_00_u03b1_3155_, lean_object* v_as_3156_, lean_object* v_p_3157_, lean_object* v_start_3158_, lean_object* v_stop_3159_){
_start:
{
lean_object* v___x_3160_; uint8_t v___x_3161_; 
v___x_3160_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3161_ = lean_nat_dec_lt(v_start_3158_, v_stop_3159_);
if (v___x_3161_ == 0)
{
lean_dec(v_stop_3159_);
lean_dec_ref(v_p_3157_);
lean_dec_ref(v_as_3156_);
return v___x_3161_;
}
else
{
lean_object* v___f_3162_; lean_object* v___y_3164_; lean_object* v___x_3170_; uint8_t v___x_3171_; 
v___f_3162_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3162_, 0, v_p_3157_);
v___x_3170_ = lean_array_get_size(v_as_3156_);
v___x_3171_ = lean_nat_dec_le(v_stop_3159_, v___x_3170_);
if (v___x_3171_ == 0)
{
lean_dec(v_stop_3159_);
v___y_3164_ = v___x_3170_;
goto v___jp_3163_;
}
else
{
v___y_3164_ = v_stop_3159_;
goto v___jp_3163_;
}
v___jp_3163_:
{
uint8_t v___x_3165_; 
v___x_3165_ = lean_nat_dec_lt(v_start_3158_, v___y_3164_);
if (v___x_3165_ == 0)
{
lean_dec(v___y_3164_);
lean_dec_ref(v___f_3162_);
lean_dec_ref(v_as_3156_);
return v___x_3165_;
}
else
{
size_t v___x_3166_; size_t v___x_3167_; lean_object* v___x_3168_; uint8_t v___x_3169_; 
v___x_3166_ = lean_usize_of_nat(v_start_3158_);
v___x_3167_ = lean_usize_of_nat(v___y_3164_);
lean_dec(v___y_3164_);
v___x_3168_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3160_, v___f_3162_, v_as_3156_, v___x_3166_, v___x_3167_);
v___x_3169_ = lean_unbox(v___x_3168_);
lean_dec(v___x_3168_);
return v___x_3169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___boxed(lean_object* v_00_u03b1_3172_, lean_object* v_as_3173_, lean_object* v_p_3174_, lean_object* v_start_3175_, lean_object* v_stop_3176_){
_start:
{
uint8_t v_res_3177_; lean_object* v_r_3178_; 
v_res_3177_ = l_Array_any(v_00_u03b1_3172_, v_as_3173_, v_p_3174_, v_start_3175_, v_stop_3176_);
lean_dec(v_start_3175_);
v_r_3178_ = lean_box(v_res_3177_);
return v_r_3178_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg___lam__0(lean_object* v_p_3179_, uint8_t v___x_3180_, lean_object* v_v_3181_){
_start:
{
lean_object* v___x_3182_; uint8_t v___x_3183_; 
v___x_3182_ = lean_apply_1(v_p_3179_, v_v_3181_);
v___x_3183_ = lean_unbox(v___x_3182_);
if (v___x_3183_ == 0)
{
return v___x_3180_;
}
else
{
uint8_t v___x_3184_; 
v___x_3184_ = 0;
return v___x_3184_;
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___lam__0___boxed(lean_object* v_p_3185_, lean_object* v___x_3186_, lean_object* v_v_3187_){
_start:
{
uint8_t v___x_339__boxed_3188_; uint8_t v_res_3189_; lean_object* v_r_3190_; 
v___x_339__boxed_3188_ = lean_unbox(v___x_3186_);
v_res_3189_ = l_Array_all___redArg___lam__0(v_p_3185_, v___x_339__boxed_3188_, v_v_3187_);
v_r_3190_ = lean_box(v_res_3189_);
return v_r_3190_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg(lean_object* v_as_3191_, lean_object* v_p_3192_, lean_object* v_start_3193_, lean_object* v_stop_3194_){
_start:
{
lean_object* v___x_3195_; uint8_t v___x_3196_; 
v___x_3195_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3196_ = lean_nat_dec_lt(v_start_3193_, v_stop_3194_);
if (v___x_3196_ == 0)
{
uint8_t v___x_3197_; 
lean_dec(v_stop_3194_);
lean_dec_ref(v_p_3192_);
lean_dec_ref(v_as_3191_);
v___x_3197_ = 1;
return v___x_3197_;
}
else
{
lean_object* v___x_3198_; lean_object* v___f_3199_; lean_object* v___y_3201_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v___x_3198_ = lean_box(v___x_3196_);
v___f_3199_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3199_, 0, v_p_3192_);
lean_closure_set(v___f_3199_, 1, v___x_3198_);
v___x_3208_ = lean_array_get_size(v_as_3191_);
v___x_3209_ = lean_nat_dec_le(v_stop_3194_, v___x_3208_);
if (v___x_3209_ == 0)
{
lean_dec(v_stop_3194_);
v___y_3201_ = v___x_3208_;
goto v___jp_3200_;
}
else
{
v___y_3201_ = v_stop_3194_;
goto v___jp_3200_;
}
v___jp_3200_:
{
uint8_t v___x_3202_; 
v___x_3202_ = lean_nat_dec_lt(v_start_3193_, v___y_3201_);
if (v___x_3202_ == 0)
{
lean_dec(v___y_3201_);
lean_dec_ref(v___f_3199_);
lean_dec_ref(v_as_3191_);
return v___x_3196_;
}
else
{
size_t v___x_3203_; size_t v___x_3204_; lean_object* v___x_3205_; uint8_t v___x_3206_; 
v___x_3203_ = lean_usize_of_nat(v_start_3193_);
v___x_3204_ = lean_usize_of_nat(v___y_3201_);
lean_dec(v___y_3201_);
v___x_3205_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3195_, v___f_3199_, v_as_3191_, v___x_3203_, v___x_3204_);
v___x_3206_ = lean_unbox(v___x_3205_);
lean_dec(v___x_3205_);
if (v___x_3206_ == 0)
{
return v___x_3202_;
}
else
{
uint8_t v___x_3207_; 
v___x_3207_ = 0;
return v___x_3207_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___boxed(lean_object* v_as_3210_, lean_object* v_p_3211_, lean_object* v_start_3212_, lean_object* v_stop_3213_){
_start:
{
uint8_t v_res_3214_; lean_object* v_r_3215_; 
v_res_3214_ = l_Array_all___redArg(v_as_3210_, v_p_3211_, v_start_3212_, v_stop_3213_);
lean_dec(v_start_3212_);
v_r_3215_ = lean_box(v_res_3214_);
return v_r_3215_;
}
}
LEAN_EXPORT uint8_t l_Array_all(lean_object* v_00_u03b1_3216_, lean_object* v_as_3217_, lean_object* v_p_3218_, lean_object* v_start_3219_, lean_object* v_stop_3220_){
_start:
{
lean_object* v___x_3221_; uint8_t v___x_3222_; 
v___x_3221_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3222_ = lean_nat_dec_lt(v_start_3219_, v_stop_3220_);
if (v___x_3222_ == 0)
{
uint8_t v___x_3223_; 
lean_dec(v_stop_3220_);
lean_dec_ref(v_p_3218_);
lean_dec_ref(v_as_3217_);
v___x_3223_ = 1;
return v___x_3223_;
}
else
{
lean_object* v___x_3224_; lean_object* v___f_3225_; lean_object* v___y_3227_; lean_object* v___x_3234_; uint8_t v___x_3235_; 
v___x_3224_ = lean_box(v___x_3222_);
v___f_3225_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3225_, 0, v_p_3218_);
lean_closure_set(v___f_3225_, 1, v___x_3224_);
v___x_3234_ = lean_array_get_size(v_as_3217_);
v___x_3235_ = lean_nat_dec_le(v_stop_3220_, v___x_3234_);
if (v___x_3235_ == 0)
{
lean_dec(v_stop_3220_);
v___y_3227_ = v___x_3234_;
goto v___jp_3226_;
}
else
{
v___y_3227_ = v_stop_3220_;
goto v___jp_3226_;
}
v___jp_3226_:
{
uint8_t v___x_3228_; 
v___x_3228_ = lean_nat_dec_lt(v_start_3219_, v___y_3227_);
if (v___x_3228_ == 0)
{
lean_dec(v___y_3227_);
lean_dec_ref(v___f_3225_);
lean_dec_ref(v_as_3217_);
return v___x_3222_;
}
else
{
size_t v___x_3229_; size_t v___x_3230_; lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3229_ = lean_usize_of_nat(v_start_3219_);
v___x_3230_ = lean_usize_of_nat(v___y_3227_);
lean_dec(v___y_3227_);
v___x_3231_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3221_, v___f_3225_, v_as_3217_, v___x_3229_, v___x_3230_);
v___x_3232_ = lean_unbox(v___x_3231_);
lean_dec(v___x_3231_);
if (v___x_3232_ == 0)
{
return v___x_3228_;
}
else
{
uint8_t v___x_3233_; 
v___x_3233_ = 0;
return v___x_3233_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___boxed(lean_object* v_00_u03b1_3236_, lean_object* v_as_3237_, lean_object* v_p_3238_, lean_object* v_start_3239_, lean_object* v_stop_3240_){
_start:
{
uint8_t v_res_3241_; lean_object* v_r_3242_; 
v_res_3241_ = l_Array_all(v_00_u03b1_3236_, v_as_3237_, v_p_3238_, v_start_3239_, v_stop_3240_);
lean_dec(v_start_3239_);
v_r_3242_ = lean_box(v_res_3241_);
return v_r_3242_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg___lam__0(lean_object* v_inst_3243_, lean_object* v_a_3244_, lean_object* v_x_3245_){
_start:
{
lean_object* v___x_3246_; uint8_t v___x_3247_; 
v___x_3246_ = lean_apply_2(v_inst_3243_, v_a_3244_, v_x_3245_);
v___x_3247_ = lean_unbox(v___x_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___lam__0___boxed(lean_object* v_inst_3248_, lean_object* v_a_3249_, lean_object* v_x_3250_){
_start:
{
uint8_t v_res_3251_; lean_object* v_r_3252_; 
v_res_3251_ = l_Array_contains___redArg___lam__0(v_inst_3248_, v_a_3249_, v_x_3250_);
v_r_3252_ = lean_box(v_res_3251_);
return v_r_3252_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg(lean_object* v_inst_3253_, lean_object* v_as_3254_, lean_object* v_a_3255_){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
v___x_3256_ = lean_unsigned_to_nat(0u);
v___x_3257_ = lean_array_get_size(v_as_3254_);
v___x_3258_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3259_ = lean_nat_dec_lt(v___x_3256_, v___x_3257_);
if (v___x_3259_ == 0)
{
lean_dec(v_a_3255_);
lean_dec_ref(v_as_3254_);
lean_dec_ref(v_inst_3253_);
return v___x_3259_;
}
else
{
if (v___x_3259_ == 0)
{
lean_dec(v_a_3255_);
lean_dec_ref(v_as_3254_);
lean_dec_ref(v_inst_3253_);
return v___x_3259_;
}
else
{
lean_object* v___f_3260_; size_t v___x_3261_; size_t v___x_3262_; lean_object* v___x_3263_; uint8_t v___x_3264_; 
v___f_3260_ = lean_alloc_closure((void*)(l_Array_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3260_, 0, v_inst_3253_);
lean_closure_set(v___f_3260_, 1, v_a_3255_);
v___x_3261_ = ((size_t)0ULL);
v___x_3262_ = lean_usize_of_nat(v___x_3257_);
v___x_3263_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3258_, v___f_3260_, v_as_3254_, v___x_3261_, v___x_3262_);
v___x_3264_ = lean_unbox(v___x_3263_);
lean_dec(v___x_3263_);
return v___x_3264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___boxed(lean_object* v_inst_3265_, lean_object* v_as_3266_, lean_object* v_a_3267_){
_start:
{
uint8_t v_res_3268_; lean_object* v_r_3269_; 
v_res_3268_ = l_Array_contains___redArg(v_inst_3265_, v_as_3266_, v_a_3267_);
v_r_3269_ = lean_box(v_res_3268_);
return v_r_3269_;
}
}
LEAN_EXPORT uint8_t l_Array_contains(lean_object* v_00_u03b1_3270_, lean_object* v_inst_3271_, lean_object* v_as_3272_, lean_object* v_a_3273_){
_start:
{
uint8_t v___x_3274_; 
v___x_3274_ = l_Array_contains___redArg(v_inst_3271_, v_as_3272_, v_a_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___boxed(lean_object* v_00_u03b1_3275_, lean_object* v_inst_3276_, lean_object* v_as_3277_, lean_object* v_a_3278_){
_start:
{
uint8_t v_res_3279_; lean_object* v_r_3280_; 
v_res_3279_ = l_Array_contains(v_00_u03b1_3275_, v_inst_3276_, v_as_3277_, v_a_3278_);
v_r_3280_ = lean_box(v_res_3279_);
return v_r_3280_;
}
}
LEAN_EXPORT uint8_t l_Array_elem___redArg(lean_object* v_inst_3281_, lean_object* v_a_3282_, lean_object* v_as_3283_){
_start:
{
uint8_t v___x_3284_; 
v___x_3284_ = l_Array_contains___redArg(v_inst_3281_, v_as_3283_, v_a_3282_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___redArg___boxed(lean_object* v_inst_3285_, lean_object* v_a_3286_, lean_object* v_as_3287_){
_start:
{
uint8_t v_res_3288_; lean_object* v_r_3289_; 
v_res_3288_ = l_Array_elem___redArg(v_inst_3285_, v_a_3286_, v_as_3287_);
v_r_3289_ = lean_box(v_res_3288_);
return v_r_3289_;
}
}
LEAN_EXPORT uint8_t l_Array_elem(lean_object* v_00_u03b1_3290_, lean_object* v_inst_3291_, lean_object* v_a_3292_, lean_object* v_as_3293_){
_start:
{
uint8_t v___x_3294_; 
v___x_3294_ = l_Array_contains___redArg(v_inst_3291_, v_as_3293_, v_a_3292_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___boxed(lean_object* v_00_u03b1_3295_, lean_object* v_inst_3296_, lean_object* v_a_3297_, lean_object* v_as_3298_){
_start:
{
uint8_t v_res_3299_; lean_object* v_r_3300_; 
v_res_3299_ = l_Array_elem(v_00_u03b1_3295_, v_inst_3296_, v_a_3297_, v_as_3298_);
v_r_3300_ = lean_box(v_res_3299_);
return v_r_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(lean_object* v_as_3301_, size_t v_i_3302_, size_t v_stop_3303_, lean_object* v_b_3304_){
_start:
{
uint8_t v___x_3305_; 
v___x_3305_ = lean_usize_dec_eq(v_i_3302_, v_stop_3303_);
if (v___x_3305_ == 0)
{
size_t v___x_3306_; size_t v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3306_ = ((size_t)1ULL);
v___x_3307_ = lean_usize_sub(v_i_3302_, v___x_3306_);
v___x_3308_ = lean_array_uget_borrowed(v_as_3301_, v___x_3307_);
lean_inc(v___x_3308_);
v___x_3309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
lean_ctor_set(v___x_3309_, 1, v_b_3304_);
v_i_3302_ = v___x_3307_;
v_b_3304_ = v___x_3309_;
goto _start;
}
else
{
return v_b_3304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg___boxed(lean_object* v_as_3311_, lean_object* v_i_3312_, lean_object* v_stop_3313_, lean_object* v_b_3314_){
_start:
{
size_t v_i_boxed_3315_; size_t v_stop_boxed_3316_; lean_object* v_res_3317_; 
v_i_boxed_3315_ = lean_unbox_usize(v_i_3312_);
lean_dec(v_i_3312_);
v_stop_boxed_3316_ = lean_unbox_usize(v_stop_3313_);
lean_dec(v_stop_3313_);
v_res_3317_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3311_, v_i_boxed_3315_, v_stop_boxed_3316_, v_b_3314_);
lean_dec_ref(v_as_3311_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg(lean_object* v_as_3318_){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; uint8_t v___x_3322_; 
v___x_3319_ = lean_box(0);
v___x_3320_ = lean_array_get_size(v_as_3318_);
v___x_3321_ = lean_unsigned_to_nat(0u);
v___x_3322_ = lean_nat_dec_lt(v___x_3321_, v___x_3320_);
if (v___x_3322_ == 0)
{
return v___x_3319_;
}
else
{
size_t v___x_3323_; size_t v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = lean_usize_of_nat(v___x_3320_);
v___x_3324_ = ((size_t)0ULL);
v___x_3325_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3318_, v___x_3323_, v___x_3324_, v___x_3319_);
return v___x_3325_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg___boxed(lean_object* v_as_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_Array_toListImpl___redArg(v_as_3326_);
lean_dec_ref(v_as_3326_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* lean_array_to_list_impl(lean_object* v_00_u03b1_3328_, lean_object* v_as_3329_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Array_toListImpl___redArg(v_as_3329_);
lean_dec_ref(v_as_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(lean_object* v_00_u03b1_3331_, lean_object* v_as_3332_, size_t v_i_3333_, size_t v_stop_3334_, lean_object* v_b_3335_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3332_, v_i_3333_, v_stop_3334_, v_b_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___boxed(lean_object* v_00_u03b1_3337_, lean_object* v_as_3338_, lean_object* v_i_3339_, lean_object* v_stop_3340_, lean_object* v_b_3341_){
_start:
{
size_t v_i_boxed_3342_; size_t v_stop_boxed_3343_; lean_object* v_res_3344_; 
v_i_boxed_3342_ = lean_unbox_usize(v_i_3339_);
lean_dec(v_i_3339_);
v_stop_boxed_3343_ = lean_unbox_usize(v_stop_3340_);
lean_dec(v_stop_3340_);
v_res_3344_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(v_00_u03b1_3337_, v_as_3338_, v_i_boxed_3342_, v_stop_boxed_3343_, v_b_3341_);
lean_dec_ref(v_as_3338_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg___lam__0(lean_object* v_x1_3345_, lean_object* v_x2_3346_){
_start:
{
lean_object* v___x_3347_; 
v___x_3347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3347_, 0, v_x1_3345_);
lean_ctor_set(v___x_3347_, 1, v_x2_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg(lean_object* v_as_3349_, lean_object* v_l_3350_){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
v___x_3351_ = lean_array_get_size(v_as_3349_);
v___x_3352_ = lean_unsigned_to_nat(0u);
v___x_3353_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3354_ = lean_nat_dec_lt(v___x_3352_, v___x_3351_);
if (v___x_3354_ == 0)
{
lean_dec_ref(v_as_3349_);
return v_l_3350_;
}
else
{
lean_object* v___f_3355_; size_t v___x_3356_; size_t v___x_3357_; lean_object* v___x_3358_; 
v___f_3355_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3356_ = lean_usize_of_nat(v___x_3351_);
v___x_3357_ = ((size_t)0ULL);
v___x_3358_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3353_, v___f_3355_, v_as_3349_, v___x_3356_, v___x_3357_, v_l_3350_);
return v___x_3358_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend(lean_object* v_00_u03b1_3359_, lean_object* v_as_3360_, lean_object* v_l_3361_){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v___x_3362_ = lean_array_get_size(v_as_3360_);
v___x_3363_ = lean_unsigned_to_nat(0u);
v___x_3364_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3365_ = lean_nat_dec_lt(v___x_3363_, v___x_3362_);
if (v___x_3365_ == 0)
{
lean_dec_ref(v_as_3360_);
return v_l_3361_;
}
else
{
lean_object* v___f_3366_; size_t v___x_3367_; size_t v___x_3368_; lean_object* v___x_3369_; 
v___f_3366_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3367_ = lean_usize_of_nat(v___x_3362_);
v___x_3368_ = ((size_t)0ULL);
v___x_3369_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3364_, v___f_3366_, v_as_3360_, v___x_3367_, v___x_3368_, v_l_3361_);
return v___x_3369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(lean_object* v_as_3370_, size_t v_i_3371_, size_t v_stop_3372_, lean_object* v_b_3373_){
_start:
{
uint8_t v___x_3374_; 
v___x_3374_ = lean_usize_dec_eq(v_i_3371_, v_stop_3372_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; lean_object* v___x_3376_; size_t v___x_3377_; size_t v___x_3378_; 
v___x_3375_ = lean_array_uget_borrowed(v_as_3370_, v_i_3371_);
lean_inc(v___x_3375_);
v___x_3376_ = lean_array_push(v_b_3373_, v___x_3375_);
v___x_3377_ = ((size_t)1ULL);
v___x_3378_ = lean_usize_add(v_i_3371_, v___x_3377_);
v_i_3371_ = v___x_3378_;
v_b_3373_ = v___x_3376_;
goto _start;
}
else
{
return v_b_3373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg___boxed(lean_object* v_as_3380_, lean_object* v_i_3381_, lean_object* v_stop_3382_, lean_object* v_b_3383_){
_start:
{
size_t v_i_boxed_3384_; size_t v_stop_boxed_3385_; lean_object* v_res_3386_; 
v_i_boxed_3384_ = lean_unbox_usize(v_i_3381_);
lean_dec(v_i_3381_);
v_stop_boxed_3385_ = lean_unbox_usize(v_stop_3382_);
lean_dec(v_stop_3382_);
v_res_3386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3380_, v_i_boxed_3384_, v_stop_boxed_3385_, v_b_3383_);
lean_dec_ref(v_as_3380_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg(lean_object* v_as_3387_, lean_object* v_bs_3388_){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; uint8_t v___x_3391_; 
v___x_3389_ = lean_unsigned_to_nat(0u);
v___x_3390_ = lean_array_get_size(v_bs_3388_);
v___x_3391_ = lean_nat_dec_lt(v___x_3389_, v___x_3390_);
if (v___x_3391_ == 0)
{
return v_as_3387_;
}
else
{
uint8_t v___x_3392_; 
v___x_3392_ = lean_nat_dec_le(v___x_3390_, v___x_3390_);
if (v___x_3392_ == 0)
{
if (v___x_3391_ == 0)
{
return v_as_3387_;
}
else
{
size_t v___x_3393_; size_t v___x_3394_; lean_object* v___x_3395_; 
v___x_3393_ = ((size_t)0ULL);
v___x_3394_ = lean_usize_of_nat(v___x_3390_);
v___x_3395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3388_, v___x_3393_, v___x_3394_, v_as_3387_);
return v___x_3395_;
}
}
else
{
size_t v___x_3396_; size_t v___x_3397_; lean_object* v___x_3398_; 
v___x_3396_ = ((size_t)0ULL);
v___x_3397_ = lean_usize_of_nat(v___x_3390_);
v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3388_, v___x_3396_, v___x_3397_, v_as_3387_);
return v___x_3398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg___boxed(lean_object* v_as_3399_, lean_object* v_bs_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Array_append___redArg(v_as_3399_, v_bs_3400_);
lean_dec_ref(v_bs_3400_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Array_append(lean_object* v_00_u03b1_3402_, lean_object* v_as_3403_, lean_object* v_bs_3404_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Array_append___redArg(v_as_3403_, v_bs_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Array_append___boxed(lean_object* v_00_u03b1_3406_, lean_object* v_as_3407_, lean_object* v_bs_3408_){
_start:
{
lean_object* v_res_3409_; 
v_res_3409_ = l_Array_append(v_00_u03b1_3406_, v_as_3407_, v_bs_3408_);
lean_dec_ref(v_bs_3408_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(lean_object* v_00_u03b1_3410_, lean_object* v_as_3411_, size_t v_i_3412_, size_t v_stop_3413_, lean_object* v_b_3414_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3411_, v_i_3412_, v_stop_3413_, v_b_3414_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___boxed(lean_object* v_00_u03b1_3416_, lean_object* v_as_3417_, lean_object* v_i_3418_, lean_object* v_stop_3419_, lean_object* v_b_3420_){
_start:
{
size_t v_i_boxed_3421_; size_t v_stop_boxed_3422_; lean_object* v_res_3423_; 
v_i_boxed_3421_ = lean_unbox_usize(v_i_3418_);
lean_dec(v_i_3418_);
v_stop_boxed_3422_ = lean_unbox_usize(v_stop_3419_);
lean_dec(v_stop_3419_);
v_res_3423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(v_00_u03b1_3416_, v_as_3417_, v_i_boxed_3421_, v_stop_boxed_3422_, v_b_3420_);
lean_dec_ref(v_as_3417_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend(lean_object* v_00_u03b1_3425_){
_start:
{
lean_object* v___x_3426_; 
v___x_3426_ = ((lean_object*)(l_Array_instAppend___closed__0));
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object* v_x_3427_, lean_object* v_x_3428_){
_start:
{
if (lean_obj_tag(v_x_3428_) == 0)
{
return v_x_3427_;
}
else
{
lean_object* v_head_3429_; lean_object* v_tail_3430_; lean_object* v___x_3431_; 
v_head_3429_ = lean_ctor_get(v_x_3428_, 0);
lean_inc(v_head_3429_);
v_tail_3430_ = lean_ctor_get(v_x_3428_, 1);
lean_inc(v_tail_3430_);
lean_dec_ref(v_x_3428_);
v___x_3431_ = lean_array_push(v_x_3427_, v_head_3429_);
v_x_3427_ = v___x_3431_;
v_x_3428_ = v_tail_3430_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_appendList___redArg(lean_object* v_as_3433_, lean_object* v_bs_3434_){
_start:
{
lean_object* v___x_3435_; 
v___x_3435_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3433_, v_bs_3434_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Array_appendList(lean_object* v_00_u03b1_3436_, lean_object* v_as_3437_, lean_object* v_bs_3438_){
_start:
{
lean_object* v___x_3439_; 
v___x_3439_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3437_, v_bs_3438_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0(lean_object* v_00_u03b1_3440_, lean_object* v_x_3441_, lean_object* v_x_3442_){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_3441_, v_x_3442_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList(lean_object* v_00_u03b1_3445_){
_start:
{
lean_object* v___x_3446_; 
v___x_3446_ = ((lean_object*)(l_Array_instHAppendList___closed__0));
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0(lean_object* v_bs_3447_, lean_object* v_toPure_3448_, lean_object* v_____do__lift_3449_){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = l_Array_append___redArg(v_bs_3447_, v_____do__lift_3449_);
v___x_3451_ = lean_apply_2(v_toPure_3448_, lean_box(0), v___x_3450_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0___boxed(lean_object* v_bs_3452_, lean_object* v_toPure_3453_, lean_object* v_____do__lift_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Array_flatMapM___redArg___lam__0(v_bs_3452_, v_toPure_3453_, v_____do__lift_3454_);
lean_dec_ref(v_____do__lift_3454_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__1(lean_object* v_toPure_3456_, lean_object* v_f_3457_, lean_object* v_toBind_3458_, lean_object* v_bs_3459_, lean_object* v_a_3460_){
_start:
{
lean_object* v___f_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___f_3461_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3461_, 0, v_bs_3459_);
lean_closure_set(v___f_3461_, 1, v_toPure_3456_);
v___x_3462_ = lean_apply_1(v_f_3457_, v_a_3460_);
v___x_3463_ = lean_apply_4(v_toBind_3458_, lean_box(0), lean_box(0), v___x_3462_, v___f_3461_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg(lean_object* v_inst_3464_, lean_object* v_f_3465_, lean_object* v_as_3466_){
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
LEAN_EXPORT lean_object* l_Array_flatMapM(lean_object* v_00_u03b1_3484_, lean_object* v_m_3485_, lean_object* v_00_u03b2_3486_, lean_object* v_inst_3487_, lean_object* v_f_3488_, lean_object* v_as_3489_){
_start:
{
lean_object* v_toApplicative_3490_; lean_object* v_toBind_3491_; lean_object* v_toPure_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; uint8_t v___x_3496_; 
v_toApplicative_3490_ = lean_ctor_get(v_inst_3487_, 0);
v_toBind_3491_ = lean_ctor_get(v_inst_3487_, 1);
v_toPure_3492_ = lean_ctor_get(v_toApplicative_3490_, 1);
v___x_3493_ = lean_unsigned_to_nat(0u);
v___x_3494_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3495_ = lean_array_get_size(v_as_3489_);
v___x_3496_ = lean_nat_dec_lt(v___x_3493_, v___x_3495_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
lean_inc(v_toPure_3492_);
lean_dec_ref(v_as_3489_);
lean_dec(v_f_3488_);
lean_dec_ref(v_inst_3487_);
v___x_3497_ = lean_apply_2(v_toPure_3492_, lean_box(0), v___x_3494_);
return v___x_3497_;
}
else
{
lean_object* v___f_3498_; uint8_t v___x_3499_; 
lean_inc(v_toBind_3491_);
lean_inc(v_toPure_3492_);
v___f_3498_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3498_, 0, v_toPure_3492_);
lean_closure_set(v___f_3498_, 1, v_f_3488_);
lean_closure_set(v___f_3498_, 2, v_toBind_3491_);
v___x_3499_ = lean_nat_dec_le(v___x_3495_, v___x_3495_);
if (v___x_3499_ == 0)
{
if (v___x_3496_ == 0)
{
lean_object* v___x_3500_; 
lean_inc(v_toPure_3492_);
lean_dec_ref(v___f_3498_);
lean_dec_ref(v_as_3489_);
lean_dec_ref(v_inst_3487_);
v___x_3500_ = lean_apply_2(v_toPure_3492_, lean_box(0), v___x_3494_);
return v___x_3500_;
}
else
{
size_t v___x_3501_; size_t v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = ((size_t)0ULL);
v___x_3502_ = lean_usize_of_nat(v___x_3495_);
v___x_3503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3487_, v___f_3498_, v_as_3489_, v___x_3501_, v___x_3502_, v___x_3494_);
return v___x_3503_;
}
}
else
{
size_t v___x_3504_; size_t v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = ((size_t)0ULL);
v___x_3505_ = lean_usize_of_nat(v___x_3495_);
v___x_3506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3487_, v___f_3498_, v_as_3489_, v___x_3504_, v___x_3505_, v___x_3494_);
return v___x_3506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg___lam__0(lean_object* v_f_3507_, lean_object* v_x1_3508_, lean_object* v_x2_3509_){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = lean_apply_1(v_f_3507_, v_x2_3509_);
v___x_3511_ = l_Array_append___redArg(v_x1_3508_, v___x_3510_);
lean_dec_ref(v___x_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg(lean_object* v_f_3512_, lean_object* v_as_3513_){
_start:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; uint8_t v___x_3518_; 
v___x_3514_ = lean_unsigned_to_nat(0u);
v___x_3515_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3516_ = lean_array_get_size(v_as_3513_);
v___x_3517_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3518_ = lean_nat_dec_lt(v___x_3514_, v___x_3516_);
if (v___x_3518_ == 0)
{
lean_dec_ref(v_as_3513_);
lean_dec_ref(v_f_3512_);
return v___x_3515_;
}
else
{
lean_object* v___f_3519_; uint8_t v___x_3520_; 
v___f_3519_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3519_, 0, v_f_3512_);
v___x_3520_ = lean_nat_dec_le(v___x_3516_, v___x_3516_);
if (v___x_3520_ == 0)
{
if (v___x_3518_ == 0)
{
lean_dec_ref(v___f_3519_);
lean_dec_ref(v_as_3513_);
return v___x_3515_;
}
else
{
size_t v___x_3521_; size_t v___x_3522_; lean_object* v___x_3523_; 
v___x_3521_ = ((size_t)0ULL);
v___x_3522_ = lean_usize_of_nat(v___x_3516_);
v___x_3523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3517_, v___f_3519_, v_as_3513_, v___x_3521_, v___x_3522_, v___x_3515_);
return v___x_3523_;
}
}
else
{
size_t v___x_3524_; size_t v___x_3525_; lean_object* v___x_3526_; 
v___x_3524_ = ((size_t)0ULL);
v___x_3525_ = lean_usize_of_nat(v___x_3516_);
v___x_3526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3517_, v___f_3519_, v_as_3513_, v___x_3524_, v___x_3525_, v___x_3515_);
return v___x_3526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap(lean_object* v_00_u03b1_3527_, lean_object* v_00_u03b2_3528_, lean_object* v_f_3529_, lean_object* v_as_3530_){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; 
v___x_3531_ = lean_unsigned_to_nat(0u);
v___x_3532_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3533_ = lean_array_get_size(v_as_3530_);
v___x_3534_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3535_ = lean_nat_dec_lt(v___x_3531_, v___x_3533_);
if (v___x_3535_ == 0)
{
lean_dec_ref(v_as_3530_);
lean_dec_ref(v_f_3529_);
return v___x_3532_;
}
else
{
lean_object* v___f_3536_; uint8_t v___x_3537_; 
v___f_3536_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3536_, 0, v_f_3529_);
v___x_3537_ = lean_nat_dec_le(v___x_3533_, v___x_3533_);
if (v___x_3537_ == 0)
{
if (v___x_3535_ == 0)
{
lean_dec_ref(v___f_3536_);
lean_dec_ref(v_as_3530_);
return v___x_3532_;
}
else
{
size_t v___x_3538_; size_t v___x_3539_; lean_object* v___x_3540_; 
v___x_3538_ = ((size_t)0ULL);
v___x_3539_ = lean_usize_of_nat(v___x_3533_);
v___x_3540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3534_, v___f_3536_, v_as_3530_, v___x_3538_, v___x_3539_, v___x_3532_);
return v___x_3540_;
}
}
else
{
size_t v___x_3541_; size_t v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = ((size_t)0ULL);
v___x_3542_ = lean_usize_of_nat(v___x_3533_);
v___x_3543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3534_, v___f_3536_, v_as_3530_, v___x_3541_, v___x_3542_, v___x_3532_);
return v___x_3543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten___redArg(lean_object* v_xss_3545_){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; uint8_t v___x_3550_; 
v___x_3546_ = lean_unsigned_to_nat(0u);
v___x_3547_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3548_ = lean_array_get_size(v_xss_3545_);
v___x_3549_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3550_ = lean_nat_dec_lt(v___x_3546_, v___x_3548_);
if (v___x_3550_ == 0)
{
lean_dec_ref(v_xss_3545_);
return v___x_3547_;
}
else
{
lean_object* v___f_3551_; uint8_t v___x_3552_; 
v___f_3551_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3552_ = lean_nat_dec_le(v___x_3548_, v___x_3548_);
if (v___x_3552_ == 0)
{
if (v___x_3550_ == 0)
{
lean_dec_ref(v_xss_3545_);
return v___x_3547_;
}
else
{
size_t v___x_3553_; size_t v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = ((size_t)0ULL);
v___x_3554_ = lean_usize_of_nat(v___x_3548_);
v___x_3555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3549_, v___f_3551_, v_xss_3545_, v___x_3553_, v___x_3554_, v___x_3547_);
return v___x_3555_;
}
}
else
{
size_t v___x_3556_; size_t v___x_3557_; lean_object* v___x_3558_; 
v___x_3556_ = ((size_t)0ULL);
v___x_3557_ = lean_usize_of_nat(v___x_3548_);
v___x_3558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3549_, v___f_3551_, v_xss_3545_, v___x_3556_, v___x_3557_, v___x_3547_);
return v___x_3558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten(lean_object* v_00_u03b1_3559_, lean_object* v_xss_3560_){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
v___x_3561_ = lean_unsigned_to_nat(0u);
v___x_3562_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3563_ = lean_array_get_size(v_xss_3560_);
v___x_3564_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3565_ = lean_nat_dec_lt(v___x_3561_, v___x_3563_);
if (v___x_3565_ == 0)
{
lean_dec_ref(v_xss_3560_);
return v___x_3562_;
}
else
{
lean_object* v___f_3566_; uint8_t v___x_3567_; 
v___f_3566_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3567_ = lean_nat_dec_le(v___x_3563_, v___x_3563_);
if (v___x_3567_ == 0)
{
if (v___x_3565_ == 0)
{
lean_dec_ref(v_xss_3560_);
return v___x_3562_;
}
else
{
size_t v___x_3568_; size_t v___x_3569_; lean_object* v___x_3570_; 
v___x_3568_ = ((size_t)0ULL);
v___x_3569_ = lean_usize_of_nat(v___x_3563_);
v___x_3570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3564_, v___f_3566_, v_xss_3560_, v___x_3568_, v___x_3569_, v___x_3562_);
return v___x_3570_;
}
}
else
{
size_t v___x_3571_; size_t v___x_3572_; lean_object* v___x_3573_; 
v___x_3571_ = ((size_t)0ULL);
v___x_3572_ = lean_usize_of_nat(v___x_3563_);
v___x_3573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3564_, v___f_3566_, v_xss_3560_, v___x_3571_, v___x_3572_, v___x_3562_);
return v___x_3573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop___redArg(lean_object* v_as_3574_, lean_object* v_i_3575_, lean_object* v_j_3576_){
_start:
{
uint8_t v___x_3577_; 
v___x_3577_ = lean_nat_dec_lt(v_i_3575_, v_j_3576_);
if (v___x_3577_ == 0)
{
lean_dec(v_j_3576_);
lean_dec(v_i_3575_);
return v_as_3574_;
}
else
{
lean_object* v_as_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v_as_3578_ = lean_array_fswap(v_as_3574_, v_i_3575_, v_j_3576_);
v___x_3579_ = lean_unsigned_to_nat(1u);
v___x_3580_ = lean_nat_add(v_i_3575_, v___x_3579_);
lean_dec(v_i_3575_);
v___x_3581_ = lean_nat_sub(v_j_3576_, v___x_3579_);
lean_dec(v_j_3576_);
v_as_3574_ = v_as_3578_;
v_i_3575_ = v___x_3580_;
v_j_3576_ = v___x_3581_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop(lean_object* v_00_u03b1_3583_, lean_object* v_as_3584_, lean_object* v_i_3585_, lean_object* v_j_3586_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Array_reverse_loop___redArg(v_as_3584_, v_i_3585_, v_j_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Array_reverse___redArg(lean_object* v_as_3588_){
_start:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; uint8_t v___x_3591_; 
v___x_3589_ = lean_array_get_size(v_as_3588_);
v___x_3590_ = lean_unsigned_to_nat(1u);
v___x_3591_ = lean_nat_dec_le(v___x_3589_, v___x_3590_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3592_ = lean_unsigned_to_nat(0u);
v___x_3593_ = lean_nat_sub(v___x_3589_, v___x_3590_);
v___x_3594_ = l_Array_reverse_loop___redArg(v_as_3588_, v___x_3592_, v___x_3593_);
return v___x_3594_;
}
else
{
return v_as_3588_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse(lean_object* v_00_u03b1_3595_, lean_object* v_as_3596_){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l_Array_reverse___redArg(v_as_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___lam__0(lean_object* v_p_3598_, lean_object* v_x1_3599_, lean_object* v_x2_3600_){
_start:
{
lean_object* v___x_3601_; uint8_t v___x_3602_; 
lean_inc(v_x2_3600_);
v___x_3601_ = lean_apply_1(v_p_3598_, v_x2_3600_);
v___x_3602_ = lean_unbox(v___x_3601_);
if (v___x_3602_ == 0)
{
lean_dec(v_x2_3600_);
return v_x1_3599_;
}
else
{
lean_object* v___x_3603_; 
v___x_3603_ = lean_array_push(v_x1_3599_, v_x2_3600_);
return v___x_3603_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg(lean_object* v_p_3606_, lean_object* v_as_3607_, lean_object* v_start_3608_, lean_object* v_stop_3609_){
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
LEAN_EXPORT lean_object* l_Array_filter___redArg___boxed(lean_object* v_p_3623_, lean_object* v_as_3624_, lean_object* v_start_3625_, lean_object* v_stop_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Array_filter___redArg(v_p_3623_, v_as_3624_, v_start_3625_, v_stop_3626_);
lean_dec(v_stop_3626_);
lean_dec(v_start_3625_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Array_filter(lean_object* v_00_u03b1_3628_, lean_object* v_p_3629_, lean_object* v_as_3630_, lean_object* v_start_3631_, lean_object* v_stop_3632_){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; uint8_t v___x_3635_; 
v___x_3633_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3634_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3635_ = lean_nat_dec_lt(v_start_3631_, v_stop_3632_);
if (v___x_3635_ == 0)
{
lean_dec_ref(v_as_3630_);
lean_dec_ref(v_p_3629_);
return v___x_3633_;
}
else
{
lean_object* v___f_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; 
v___f_3636_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3636_, 0, v_p_3629_);
v___x_3637_ = lean_array_get_size(v_as_3630_);
v___x_3638_ = lean_nat_dec_le(v_stop_3632_, v___x_3637_);
if (v___x_3638_ == 0)
{
uint8_t v___x_3639_; 
v___x_3639_ = lean_nat_dec_lt(v_start_3631_, v___x_3637_);
if (v___x_3639_ == 0)
{
lean_dec_ref(v___f_3636_);
lean_dec_ref(v_as_3630_);
return v___x_3633_;
}
else
{
size_t v___x_3640_; size_t v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = lean_usize_of_nat(v_start_3631_);
v___x_3641_ = lean_usize_of_nat(v___x_3637_);
v___x_3642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3634_, v___f_3636_, v_as_3630_, v___x_3640_, v___x_3641_, v___x_3633_);
return v___x_3642_;
}
}
else
{
size_t v___x_3643_; size_t v___x_3644_; lean_object* v___x_3645_; 
v___x_3643_ = lean_usize_of_nat(v_start_3631_);
v___x_3644_ = lean_usize_of_nat(v_stop_3632_);
v___x_3645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3634_, v___f_3636_, v_as_3630_, v___x_3643_, v___x_3644_, v___x_3633_);
return v___x_3645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___boxed(lean_object* v_00_u03b1_3646_, lean_object* v_p_3647_, lean_object* v_as_3648_, lean_object* v_start_3649_, lean_object* v_stop_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Array_filter(v_00_u03b1_3646_, v_p_3647_, v_as_3648_, v_start_3649_, v_stop_3650_);
lean_dec(v_stop_3650_);
lean_dec(v_start_3649_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0(lean_object* v_toApplicative_3652_, lean_object* v_acc_3653_, lean_object* v_a_3654_, uint8_t v_____do__lift_3655_){
_start:
{
if (v_____do__lift_3655_ == 0)
{
lean_object* v_toPure_3656_; lean_object* v___x_3657_; 
lean_dec(v_a_3654_);
v_toPure_3656_ = lean_ctor_get(v_toApplicative_3652_, 1);
lean_inc(v_toPure_3656_);
lean_dec_ref(v_toApplicative_3652_);
v___x_3657_ = lean_apply_2(v_toPure_3656_, lean_box(0), v_acc_3653_);
return v___x_3657_;
}
else
{
lean_object* v_toPure_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v_toPure_3658_ = lean_ctor_get(v_toApplicative_3652_, 1);
lean_inc(v_toPure_3658_);
lean_dec_ref(v_toApplicative_3652_);
v___x_3659_ = lean_array_push(v_acc_3653_, v_a_3654_);
v___x_3660_ = lean_apply_2(v_toPure_3658_, lean_box(0), v___x_3659_);
return v___x_3660_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0___boxed(lean_object* v_toApplicative_3661_, lean_object* v_acc_3662_, lean_object* v_a_3663_, lean_object* v_____do__lift_3664_){
_start:
{
uint8_t v_____do__lift_119__boxed_3665_; lean_object* v_res_3666_; 
v_____do__lift_119__boxed_3665_ = lean_unbox(v_____do__lift_3664_);
v_res_3666_ = l_Array_filterM___redArg___lam__0(v_toApplicative_3661_, v_acc_3662_, v_a_3663_, v_____do__lift_119__boxed_3665_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__1(lean_object* v_toApplicative_3667_, lean_object* v_p_3668_, lean_object* v_toBind_3669_, lean_object* v_acc_3670_, lean_object* v_a_3671_){
_start:
{
lean_object* v___f_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
lean_inc(v_a_3671_);
v___f_3672_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3672_, 0, v_toApplicative_3667_);
lean_closure_set(v___f_3672_, 1, v_acc_3670_);
lean_closure_set(v___f_3672_, 2, v_a_3671_);
v___x_3673_ = lean_apply_1(v_p_3668_, v_a_3671_);
v___x_3674_ = lean_apply_4(v_toBind_3669_, lean_box(0), lean_box(0), v___x_3673_, v___f_3672_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg(lean_object* v_inst_3675_, lean_object* v_p_3676_, lean_object* v_as_3677_, lean_object* v_start_3678_, lean_object* v_stop_3679_){
_start:
{
lean_object* v_toApplicative_3680_; lean_object* v_toBind_3681_; lean_object* v___x_3682_; uint8_t v___x_3683_; 
v_toApplicative_3680_ = lean_ctor_get(v_inst_3675_, 0);
v_toBind_3681_ = lean_ctor_get(v_inst_3675_, 1);
v___x_3682_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3683_ = lean_nat_dec_lt(v_start_3678_, v_stop_3679_);
if (v___x_3683_ == 0)
{
lean_object* v_toPure_3684_; lean_object* v___x_3685_; 
lean_inc_ref(v_toApplicative_3680_);
lean_dec_ref(v_as_3677_);
lean_dec(v_p_3676_);
lean_dec_ref(v_inst_3675_);
v_toPure_3684_ = lean_ctor_get(v_toApplicative_3680_, 1);
lean_inc(v_toPure_3684_);
lean_dec_ref(v_toApplicative_3680_);
v___x_3685_ = lean_apply_2(v_toPure_3684_, lean_box(0), v___x_3682_);
return v___x_3685_;
}
else
{
lean_object* v___f_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; 
lean_inc(v_toBind_3681_);
lean_inc_ref(v_toApplicative_3680_);
v___f_3686_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3686_, 0, v_toApplicative_3680_);
lean_closure_set(v___f_3686_, 1, v_p_3676_);
lean_closure_set(v___f_3686_, 2, v_toBind_3681_);
v___x_3687_ = lean_array_get_size(v_as_3677_);
v___x_3688_ = lean_nat_dec_le(v_stop_3679_, v___x_3687_);
if (v___x_3688_ == 0)
{
uint8_t v___x_3689_; 
v___x_3689_ = lean_nat_dec_lt(v_start_3678_, v___x_3687_);
if (v___x_3689_ == 0)
{
lean_object* v_toPure_3690_; lean_object* v___x_3691_; 
lean_inc_ref(v_toApplicative_3680_);
lean_dec_ref(v___f_3686_);
lean_dec_ref(v_as_3677_);
lean_dec_ref(v_inst_3675_);
v_toPure_3690_ = lean_ctor_get(v_toApplicative_3680_, 1);
lean_inc(v_toPure_3690_);
lean_dec_ref(v_toApplicative_3680_);
v___x_3691_ = lean_apply_2(v_toPure_3690_, lean_box(0), v___x_3682_);
return v___x_3691_;
}
else
{
size_t v___x_3692_; size_t v___x_3693_; lean_object* v___x_3694_; 
v___x_3692_ = lean_usize_of_nat(v_start_3678_);
v___x_3693_ = lean_usize_of_nat(v___x_3687_);
v___x_3694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3675_, v___f_3686_, v_as_3677_, v___x_3692_, v___x_3693_, v___x_3682_);
return v___x_3694_;
}
}
else
{
size_t v___x_3695_; size_t v___x_3696_; lean_object* v___x_3697_; 
v___x_3695_ = lean_usize_of_nat(v_start_3678_);
v___x_3696_ = lean_usize_of_nat(v_stop_3679_);
v___x_3697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3675_, v___f_3686_, v_as_3677_, v___x_3695_, v___x_3696_, v___x_3682_);
return v___x_3697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___boxed(lean_object* v_inst_3698_, lean_object* v_p_3699_, lean_object* v_as_3700_, lean_object* v_start_3701_, lean_object* v_stop_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Array_filterM___redArg(v_inst_3698_, v_p_3699_, v_as_3700_, v_start_3701_, v_stop_3702_);
lean_dec(v_stop_3702_);
lean_dec(v_start_3701_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM(lean_object* v_m_3704_, lean_object* v_00_u03b1_3705_, lean_object* v_inst_3706_, lean_object* v_p_3707_, lean_object* v_as_3708_, lean_object* v_start_3709_, lean_object* v_stop_3710_){
_start:
{
lean_object* v_toApplicative_3711_; lean_object* v_toBind_3712_; lean_object* v___x_3713_; uint8_t v___x_3714_; 
v_toApplicative_3711_ = lean_ctor_get(v_inst_3706_, 0);
v_toBind_3712_ = lean_ctor_get(v_inst_3706_, 1);
v___x_3713_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3714_ = lean_nat_dec_lt(v_start_3709_, v_stop_3710_);
if (v___x_3714_ == 0)
{
lean_object* v_toPure_3715_; lean_object* v___x_3716_; 
lean_inc_ref(v_toApplicative_3711_);
lean_dec_ref(v_as_3708_);
lean_dec(v_p_3707_);
lean_dec_ref(v_inst_3706_);
v_toPure_3715_ = lean_ctor_get(v_toApplicative_3711_, 1);
lean_inc(v_toPure_3715_);
lean_dec_ref(v_toApplicative_3711_);
v___x_3716_ = lean_apply_2(v_toPure_3715_, lean_box(0), v___x_3713_);
return v___x_3716_;
}
else
{
lean_object* v___f_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
lean_inc(v_toBind_3712_);
lean_inc_ref(v_toApplicative_3711_);
v___f_3717_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3717_, 0, v_toApplicative_3711_);
lean_closure_set(v___f_3717_, 1, v_p_3707_);
lean_closure_set(v___f_3717_, 2, v_toBind_3712_);
v___x_3718_ = lean_array_get_size(v_as_3708_);
v___x_3719_ = lean_nat_dec_le(v_stop_3710_, v___x_3718_);
if (v___x_3719_ == 0)
{
uint8_t v___x_3720_; 
v___x_3720_ = lean_nat_dec_lt(v_start_3709_, v___x_3718_);
if (v___x_3720_ == 0)
{
lean_object* v_toPure_3721_; lean_object* v___x_3722_; 
lean_inc_ref(v_toApplicative_3711_);
lean_dec_ref(v___f_3717_);
lean_dec_ref(v_as_3708_);
lean_dec_ref(v_inst_3706_);
v_toPure_3721_ = lean_ctor_get(v_toApplicative_3711_, 1);
lean_inc(v_toPure_3721_);
lean_dec_ref(v_toApplicative_3711_);
v___x_3722_ = lean_apply_2(v_toPure_3721_, lean_box(0), v___x_3713_);
return v___x_3722_;
}
else
{
size_t v___x_3723_; size_t v___x_3724_; lean_object* v___x_3725_; 
v___x_3723_ = lean_usize_of_nat(v_start_3709_);
v___x_3724_ = lean_usize_of_nat(v___x_3718_);
v___x_3725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3706_, v___f_3717_, v_as_3708_, v___x_3723_, v___x_3724_, v___x_3713_);
return v___x_3725_;
}
}
else
{
size_t v___x_3726_; size_t v___x_3727_; lean_object* v___x_3728_; 
v___x_3726_ = lean_usize_of_nat(v_start_3709_);
v___x_3727_ = lean_usize_of_nat(v_stop_3710_);
v___x_3728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3706_, v___f_3717_, v_as_3708_, v___x_3726_, v___x_3727_, v___x_3713_);
return v___x_3728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___boxed(lean_object* v_m_3729_, lean_object* v_00_u03b1_3730_, lean_object* v_inst_3731_, lean_object* v_p_3732_, lean_object* v_as_3733_, lean_object* v_start_3734_, lean_object* v_stop_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l_Array_filterM(v_m_3729_, v_00_u03b1_3730_, v_inst_3731_, v_p_3732_, v_as_3733_, v_start_3734_, v_stop_3735_);
lean_dec(v_stop_3735_);
lean_dec(v_start_3734_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__0(lean_object* v_toPure_3737_, lean_object* v_acc_3738_, lean_object* v_a_3739_, uint8_t v_____do__lift_3740_){
_start:
{
if (v_____do__lift_3740_ == 0)
{
lean_object* v___x_3741_; 
lean_dec(v_a_3739_);
v___x_3741_ = lean_apply_2(v_toPure_3737_, lean_box(0), v_acc_3738_);
return v___x_3741_;
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3742_ = lean_array_push(v_acc_3738_, v_a_3739_);
v___x_3743_ = lean_apply_2(v_toPure_3737_, lean_box(0), v___x_3742_);
return v___x_3743_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__0___boxed(lean_object* v_toPure_3744_, lean_object* v_acc_3745_, lean_object* v_a_3746_, lean_object* v_____do__lift_3747_){
_start:
{
uint8_t v_____do__lift_129__boxed_3748_; lean_object* v_res_3749_; 
v_____do__lift_129__boxed_3748_ = lean_unbox(v_____do__lift_3747_);
v_res_3749_ = l_Array_filterRevM___redArg___lam__0(v_toPure_3744_, v_acc_3745_, v_a_3746_, v_____do__lift_129__boxed_3748_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__1(lean_object* v_toPure_3750_, lean_object* v_p_3751_, lean_object* v_toBind_3752_, lean_object* v_a_3753_, lean_object* v_acc_3754_){
_start:
{
lean_object* v___f_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
lean_inc(v_a_3753_);
v___f_3755_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3755_, 0, v_toPure_3750_);
lean_closure_set(v___f_3755_, 1, v_acc_3754_);
lean_closure_set(v___f_3755_, 2, v_a_3753_);
v___x_3756_ = lean_apply_1(v_p_3751_, v_a_3753_);
v___x_3757_ = lean_apply_4(v_toBind_3752_, lean_box(0), lean_box(0), v___x_3756_, v___f_3755_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg(lean_object* v_inst_3759_, lean_object* v_p_3760_, lean_object* v_as_3761_, lean_object* v_start_3762_, lean_object* v_stop_3763_){
_start:
{
lean_object* v_toApplicative_3764_; lean_object* v_toFunctor_3765_; lean_object* v_toBind_3766_; lean_object* v_toPure_3767_; lean_object* v_map_3768_; lean_object* v___f_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; uint8_t v___x_3773_; 
v_toApplicative_3764_ = lean_ctor_get(v_inst_3759_, 0);
v_toFunctor_3765_ = lean_ctor_get(v_toApplicative_3764_, 0);
v_toBind_3766_ = lean_ctor_get(v_inst_3759_, 1);
v_toPure_3767_ = lean_ctor_get(v_toApplicative_3764_, 1);
v_map_3768_ = lean_ctor_get(v_toFunctor_3765_, 0);
lean_inc(v_map_3768_);
lean_inc(v_toBind_3766_);
lean_inc(v_toPure_3767_);
v___f_3769_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3769_, 0, v_toPure_3767_);
lean_closure_set(v___f_3769_, 1, v_p_3760_);
lean_closure_set(v___f_3769_, 2, v_toBind_3766_);
v___x_3770_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3771_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3772_ = lean_array_get_size(v_as_3761_);
v___x_3773_ = lean_nat_dec_le(v_start_3762_, v___x_3772_);
if (v___x_3773_ == 0)
{
uint8_t v___x_3774_; 
v___x_3774_ = lean_nat_dec_lt(v_stop_3763_, v___x_3772_);
if (v___x_3774_ == 0)
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
lean_inc(v_toPure_3767_);
lean_dec_ref(v___f_3769_);
lean_dec_ref(v_as_3761_);
lean_dec_ref(v_inst_3759_);
v___x_3775_ = lean_apply_2(v_toPure_3767_, lean_box(0), v___x_3771_);
v___x_3776_ = lean_apply_4(v_map_3768_, lean_box(0), lean_box(0), v___x_3770_, v___x_3775_);
return v___x_3776_;
}
else
{
size_t v___x_3777_; size_t v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3777_ = lean_usize_of_nat(v___x_3772_);
v___x_3778_ = lean_usize_of_nat(v_stop_3763_);
v___x_3779_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3759_, v___f_3769_, v_as_3761_, v___x_3777_, v___x_3778_, v___x_3771_);
v___x_3780_ = lean_apply_4(v_map_3768_, lean_box(0), lean_box(0), v___x_3770_, v___x_3779_);
return v___x_3780_;
}
}
else
{
uint8_t v___x_3781_; 
v___x_3781_ = lean_nat_dec_lt(v_stop_3763_, v_start_3762_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; lean_object* v___x_3783_; 
lean_inc(v_toPure_3767_);
lean_dec_ref(v___f_3769_);
lean_dec_ref(v_as_3761_);
lean_dec_ref(v_inst_3759_);
v___x_3782_ = lean_apply_2(v_toPure_3767_, lean_box(0), v___x_3771_);
v___x_3783_ = lean_apply_4(v_map_3768_, lean_box(0), lean_box(0), v___x_3770_, v___x_3782_);
return v___x_3783_;
}
else
{
size_t v___x_3784_; size_t v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3784_ = lean_usize_of_nat(v_start_3762_);
v___x_3785_ = lean_usize_of_nat(v_stop_3763_);
v___x_3786_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3759_, v___f_3769_, v_as_3761_, v___x_3784_, v___x_3785_, v___x_3771_);
v___x_3787_ = lean_apply_4(v_map_3768_, lean_box(0), lean_box(0), v___x_3770_, v___x_3786_);
return v___x_3787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___boxed(lean_object* v_inst_3788_, lean_object* v_p_3789_, lean_object* v_as_3790_, lean_object* v_start_3791_, lean_object* v_stop_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Array_filterRevM___redArg(v_inst_3788_, v_p_3789_, v_as_3790_, v_start_3791_, v_stop_3792_);
lean_dec(v_stop_3792_);
lean_dec(v_start_3791_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM(lean_object* v_m_3794_, lean_object* v_00_u03b1_3795_, lean_object* v_inst_3796_, lean_object* v_p_3797_, lean_object* v_as_3798_, lean_object* v_start_3799_, lean_object* v_stop_3800_){
_start:
{
lean_object* v_toApplicative_3801_; lean_object* v_toFunctor_3802_; lean_object* v_toBind_3803_; lean_object* v_toPure_3804_; lean_object* v_map_3805_; lean_object* v___f_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; uint8_t v___x_3810_; 
v_toApplicative_3801_ = lean_ctor_get(v_inst_3796_, 0);
v_toFunctor_3802_ = lean_ctor_get(v_toApplicative_3801_, 0);
v_toBind_3803_ = lean_ctor_get(v_inst_3796_, 1);
v_toPure_3804_ = lean_ctor_get(v_toApplicative_3801_, 1);
v_map_3805_ = lean_ctor_get(v_toFunctor_3802_, 0);
lean_inc(v_map_3805_);
lean_inc(v_toBind_3803_);
lean_inc(v_toPure_3804_);
v___f_3806_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3806_, 0, v_toPure_3804_);
lean_closure_set(v___f_3806_, 1, v_p_3797_);
lean_closure_set(v___f_3806_, 2, v_toBind_3803_);
v___x_3807_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3808_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3809_ = lean_array_get_size(v_as_3798_);
v___x_3810_ = lean_nat_dec_le(v_start_3799_, v___x_3809_);
if (v___x_3810_ == 0)
{
uint8_t v___x_3811_; 
v___x_3811_ = lean_nat_dec_lt(v_stop_3800_, v___x_3809_);
if (v___x_3811_ == 0)
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
lean_inc(v_toPure_3804_);
lean_dec_ref(v___f_3806_);
lean_dec_ref(v_as_3798_);
lean_dec_ref(v_inst_3796_);
v___x_3812_ = lean_apply_2(v_toPure_3804_, lean_box(0), v___x_3808_);
v___x_3813_ = lean_apply_4(v_map_3805_, lean_box(0), lean_box(0), v___x_3807_, v___x_3812_);
return v___x_3813_;
}
else
{
size_t v___x_3814_; size_t v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3814_ = lean_usize_of_nat(v___x_3809_);
v___x_3815_ = lean_usize_of_nat(v_stop_3800_);
v___x_3816_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3796_, v___f_3806_, v_as_3798_, v___x_3814_, v___x_3815_, v___x_3808_);
v___x_3817_ = lean_apply_4(v_map_3805_, lean_box(0), lean_box(0), v___x_3807_, v___x_3816_);
return v___x_3817_;
}
}
else
{
uint8_t v___x_3818_; 
v___x_3818_ = lean_nat_dec_lt(v_stop_3800_, v_start_3799_);
if (v___x_3818_ == 0)
{
lean_object* v___x_3819_; lean_object* v___x_3820_; 
lean_inc(v_toPure_3804_);
lean_dec_ref(v___f_3806_);
lean_dec_ref(v_as_3798_);
lean_dec_ref(v_inst_3796_);
v___x_3819_ = lean_apply_2(v_toPure_3804_, lean_box(0), v___x_3808_);
v___x_3820_ = lean_apply_4(v_map_3805_, lean_box(0), lean_box(0), v___x_3807_, v___x_3819_);
return v___x_3820_;
}
else
{
size_t v___x_3821_; size_t v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3821_ = lean_usize_of_nat(v_start_3799_);
v___x_3822_ = lean_usize_of_nat(v_stop_3800_);
v___x_3823_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3796_, v___f_3806_, v_as_3798_, v___x_3821_, v___x_3822_, v___x_3808_);
v___x_3824_ = lean_apply_4(v_map_3805_, lean_box(0), lean_box(0), v___x_3807_, v___x_3823_);
return v___x_3824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___boxed(lean_object* v_m_3825_, lean_object* v_00_u03b1_3826_, lean_object* v_inst_3827_, lean_object* v_p_3828_, lean_object* v_as_3829_, lean_object* v_start_3830_, lean_object* v_stop_3831_){
_start:
{
lean_object* v_res_3832_; 
v_res_3832_ = l_Array_filterRevM(v_m_3825_, v_00_u03b1_3826_, v_inst_3827_, v_p_3828_, v_as_3829_, v_start_3830_, v_stop_3831_);
lean_dec(v_stop_3831_);
lean_dec(v_start_3830_);
return v_res_3832_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__0(lean_object* v_toPure_3833_, lean_object* v_bs_3834_, lean_object* v_____do__lift_3835_){
_start:
{
if (lean_obj_tag(v_____do__lift_3835_) == 0)
{
lean_object* v___x_3836_; 
v___x_3836_ = lean_apply_2(v_toPure_3833_, lean_box(0), v_bs_3834_);
return v___x_3836_;
}
else
{
lean_object* v_val_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v_val_3837_ = lean_ctor_get(v_____do__lift_3835_, 0);
lean_inc(v_val_3837_);
lean_dec_ref(v_____do__lift_3835_);
v___x_3838_ = lean_array_push(v_bs_3834_, v_val_3837_);
v___x_3839_ = lean_apply_2(v_toPure_3833_, lean_box(0), v___x_3838_);
return v___x_3839_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__1(lean_object* v_toPure_3840_, lean_object* v_f_3841_, lean_object* v_toBind_3842_, lean_object* v_bs_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v___f_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___f_3845_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3845_, 0, v_toPure_3840_);
lean_closure_set(v___f_3845_, 1, v_bs_3843_);
v___x_3846_ = lean_apply_1(v_f_3841_, v_a_3844_);
v___x_3847_ = lean_apply_4(v_toBind_3842_, lean_box(0), lean_box(0), v___x_3846_, v___f_3845_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg(lean_object* v_inst_3848_, lean_object* v_f_3849_, lean_object* v_as_3850_, lean_object* v_start_3851_, lean_object* v_stop_3852_){
_start:
{
lean_object* v_toApplicative_3853_; lean_object* v_toBind_3854_; lean_object* v_toPure_3855_; lean_object* v___x_3856_; uint8_t v___x_3857_; 
v_toApplicative_3853_ = lean_ctor_get(v_inst_3848_, 0);
v_toBind_3854_ = lean_ctor_get(v_inst_3848_, 1);
v_toPure_3855_ = lean_ctor_get(v_toApplicative_3853_, 1);
v___x_3856_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3857_ = lean_nat_dec_lt(v_start_3851_, v_stop_3852_);
if (v___x_3857_ == 0)
{
lean_object* v___x_3858_; 
lean_inc(v_toPure_3855_);
lean_dec_ref(v_as_3850_);
lean_dec(v_f_3849_);
lean_dec_ref(v_inst_3848_);
v___x_3858_ = lean_apply_2(v_toPure_3855_, lean_box(0), v___x_3856_);
return v___x_3858_;
}
else
{
lean_object* v___f_3859_; lean_object* v___x_3860_; uint8_t v___x_3861_; 
lean_inc(v_toBind_3854_);
lean_inc(v_toPure_3855_);
v___f_3859_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3859_, 0, v_toPure_3855_);
lean_closure_set(v___f_3859_, 1, v_f_3849_);
lean_closure_set(v___f_3859_, 2, v_toBind_3854_);
v___x_3860_ = lean_array_get_size(v_as_3850_);
v___x_3861_ = lean_nat_dec_le(v_stop_3852_, v___x_3860_);
if (v___x_3861_ == 0)
{
uint8_t v___x_3862_; 
v___x_3862_ = lean_nat_dec_lt(v_start_3851_, v___x_3860_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; 
lean_inc(v_toPure_3855_);
lean_dec_ref(v___f_3859_);
lean_dec_ref(v_as_3850_);
lean_dec_ref(v_inst_3848_);
v___x_3863_ = lean_apply_2(v_toPure_3855_, lean_box(0), v___x_3856_);
return v___x_3863_;
}
else
{
size_t v___x_3864_; size_t v___x_3865_; lean_object* v___x_3866_; 
v___x_3864_ = lean_usize_of_nat(v_start_3851_);
v___x_3865_ = lean_usize_of_nat(v___x_3860_);
v___x_3866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3848_, v___f_3859_, v_as_3850_, v___x_3864_, v___x_3865_, v___x_3856_);
return v___x_3866_;
}
}
else
{
size_t v___x_3867_; size_t v___x_3868_; lean_object* v___x_3869_; 
v___x_3867_ = lean_usize_of_nat(v_start_3851_);
v___x_3868_ = lean_usize_of_nat(v_stop_3852_);
v___x_3869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3848_, v___f_3859_, v_as_3850_, v___x_3867_, v___x_3868_, v___x_3856_);
return v___x_3869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___boxed(lean_object* v_inst_3870_, lean_object* v_f_3871_, lean_object* v_as_3872_, lean_object* v_start_3873_, lean_object* v_stop_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l_Array_filterMapM___redArg(v_inst_3870_, v_f_3871_, v_as_3872_, v_start_3873_, v_stop_3874_);
lean_dec(v_stop_3874_);
lean_dec(v_start_3873_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM(lean_object* v_00_u03b1_3876_, lean_object* v_m_3877_, lean_object* v_00_u03b2_3878_, lean_object* v_inst_3879_, lean_object* v_f_3880_, lean_object* v_as_3881_, lean_object* v_start_3882_, lean_object* v_stop_3883_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l_Array_filterMapM___redArg(v_inst_3879_, v_f_3880_, v_as_3881_, v_start_3882_, v_stop_3883_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___boxed(lean_object* v_00_u03b1_3885_, lean_object* v_m_3886_, lean_object* v_00_u03b2_3887_, lean_object* v_inst_3888_, lean_object* v_f_3889_, lean_object* v_as_3890_, lean_object* v_start_3891_, lean_object* v_stop_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Array_filterMapM(v_00_u03b1_3885_, v_m_3886_, v_00_u03b2_3887_, v_inst_3888_, v_f_3889_, v_as_3890_, v_start_3891_, v_stop_3892_);
lean_dec(v_stop_3892_);
lean_dec(v_start_3891_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg(lean_object* v_f_3894_, lean_object* v_as_3895_, lean_object* v_start_3896_, lean_object* v_stop_3897_){
_start:
{
lean_object* v___f_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___f_3898_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3898_, 0, v_f_3894_);
v___x_3899_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3900_ = l_Array_filterMapM___redArg(v___x_3899_, v___f_3898_, v_as_3895_, v_start_3896_, v_stop_3897_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg___boxed(lean_object* v_f_3901_, lean_object* v_as_3902_, lean_object* v_start_3903_, lean_object* v_stop_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Array_filterMap___redArg(v_f_3901_, v_as_3902_, v_start_3903_, v_stop_3904_);
lean_dec(v_stop_3904_);
lean_dec(v_start_3903_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap(lean_object* v_00_u03b1_3906_, lean_object* v_00_u03b2_3907_, lean_object* v_f_3908_, lean_object* v_as_3909_, lean_object* v_start_3910_, lean_object* v_stop_3911_){
_start:
{
lean_object* v___f_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___f_3912_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3912_, 0, v_f_3908_);
v___x_3913_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3914_ = l_Array_filterMapM___redArg(v___x_3913_, v___f_3912_, v_as_3909_, v_start_3910_, v_stop_3911_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___boxed(lean_object* v_00_u03b1_3915_, lean_object* v_00_u03b2_3916_, lean_object* v_f_3917_, lean_object* v_as_3918_, lean_object* v_start_3919_, lean_object* v_stop_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l_Array_filterMap(v_00_u03b1_3915_, v_00_u03b2_3916_, v_f_3917_, v_as_3918_, v_start_3919_, v_stop_3920_);
lean_dec(v_stop_3920_);
lean_dec(v_start_3919_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg___lam__0(lean_object* v_lt_3922_, lean_object* v_x1_3923_, lean_object* v_x2_3924_){
_start:
{
lean_object* v___x_3925_; uint8_t v___x_3926_; 
lean_inc(v_x2_3924_);
lean_inc(v_x1_3923_);
v___x_3925_ = lean_apply_2(v_lt_3922_, v_x1_3923_, v_x2_3924_);
v___x_3926_ = lean_unbox(v___x_3925_);
if (v___x_3926_ == 0)
{
lean_dec(v_x2_3924_);
return v_x1_3923_;
}
else
{
lean_dec(v_x1_3923_);
return v_x2_3924_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg(lean_object* v_as_3927_, lean_object* v_lt_3928_){
_start:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; uint8_t v___x_3931_; 
v___x_3929_ = lean_unsigned_to_nat(0u);
v___x_3930_ = lean_array_get_size(v_as_3927_);
v___x_3931_ = lean_nat_dec_lt(v___x_3929_, v___x_3930_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3932_; 
lean_dec_ref(v_lt_3928_);
lean_dec_ref(v_as_3927_);
v___x_3932_ = lean_box(0);
return v___x_3932_;
}
else
{
lean_object* v_a0_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; uint8_t v___x_3936_; 
v_a0_3933_ = lean_array_fget(v_as_3927_, v___x_3929_);
v___x_3934_ = lean_unsigned_to_nat(1u);
v___x_3935_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3936_ = lean_nat_dec_lt(v___x_3934_, v___x_3930_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; 
lean_dec_ref(v_lt_3928_);
lean_dec_ref(v_as_3927_);
v___x_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3937_, 0, v_a0_3933_);
return v___x_3937_;
}
else
{
lean_object* v___f_3938_; uint8_t v___x_3939_; 
v___f_3938_ = lean_alloc_closure((void*)(l_Array_getMax_x3f___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3938_, 0, v_lt_3928_);
v___x_3939_ = lean_nat_dec_le(v___x_3930_, v___x_3930_);
if (v___x_3939_ == 0)
{
if (v___x_3936_ == 0)
{
lean_object* v___x_3940_; 
lean_dec_ref(v___f_3938_);
lean_dec_ref(v_as_3927_);
v___x_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3940_, 0, v_a0_3933_);
return v___x_3940_;
}
else
{
size_t v___x_3941_; size_t v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3941_ = ((size_t)1ULL);
v___x_3942_ = lean_usize_of_nat(v___x_3930_);
v___x_3943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3935_, v___f_3938_, v_as_3927_, v___x_3941_, v___x_3942_, v_a0_3933_);
v___x_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
return v___x_3944_;
}
}
else
{
size_t v___x_3945_; size_t v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3945_ = ((size_t)1ULL);
v___x_3946_ = lean_usize_of_nat(v___x_3930_);
v___x_3947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3935_, v___f_3938_, v_as_3927_, v___x_3945_, v___x_3946_, v_a0_3933_);
v___x_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3947_);
return v___x_3948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f(lean_object* v_00_u03b1_3949_, lean_object* v_as_3950_, lean_object* v_lt_3951_){
_start:
{
lean_object* v___x_3952_; 
v___x_3952_ = l_Array_getMax_x3f___redArg(v_as_3950_, v_lt_3951_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg___lam__0(lean_object* v_p_3953_, lean_object* v_a_3954_, lean_object* v_x_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v_fst_3957_; lean_object* v_snd_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3974_; 
v_fst_3957_ = lean_ctor_get(v___y_3956_, 0);
v_snd_3958_ = lean_ctor_get(v___y_3956_, 1);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___y_3956_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3960_ = v___y_3956_;
v_isShared_3961_ = v_isSharedCheck_3974_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_snd_3958_);
lean_inc(v_fst_3957_);
lean_dec(v___y_3956_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3974_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3962_; uint8_t v___x_3963_; 
lean_inc(v_a_3954_);
v___x_3962_ = lean_apply_1(v_p_3953_, v_a_3954_);
v___x_3963_ = lean_unbox(v___x_3962_);
if (v___x_3963_ == 0)
{
lean_object* v___x_3964_; lean_object* v___x_3966_; 
v___x_3964_ = lean_array_push(v_snd_3958_, v_a_3954_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 1, v___x_3964_);
v___x_3966_ = v___x_3960_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_fst_3957_);
lean_ctor_set(v_reuseFailAlloc_3968_, 1, v___x_3964_);
v___x_3966_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
lean_object* v___x_3967_; 
v___x_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
return v___x_3967_;
}
}
else
{
lean_object* v___x_3969_; lean_object* v___x_3971_; 
v___x_3969_ = lean_array_push(v_fst_3957_, v_a_3954_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_3969_);
v___x_3971_ = v___x_3960_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3969_);
lean_ctor_set(v_reuseFailAlloc_3973_, 1, v_snd_3958_);
v___x_3971_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
lean_object* v___x_3972_; 
v___x_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
return v___x_3972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg(lean_object* v_p_3977_, lean_object* v_as_3978_){
_start:
{
lean_object* v___f_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; size_t v_sz_3982_; size_t v___x_3983_; lean_object* v___x_3984_; lean_object* v_fst_3985_; lean_object* v_snd_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
v___f_3979_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3979_, 0, v_p_3977_);
v___x_3980_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3981_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_3982_ = lean_array_size(v_as_3978_);
v___x_3983_ = ((size_t)0ULL);
v___x_3984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_3980_, v_as_3978_, v___f_3979_, v_sz_3982_, v___x_3983_, v___x_3981_);
v_fst_3985_ = lean_ctor_get(v___x_3984_, 0);
v_snd_3986_ = lean_ctor_get(v___x_3984_, 1);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3984_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_snd_3986_);
lean_inc(v_fst_3985_);
lean_dec(v___x_3984_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_fst_3985_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v_snd_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition(lean_object* v_00_u03b1_3994_, lean_object* v_p_3995_, lean_object* v_as_3996_){
_start:
{
lean_object* v___f_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; size_t v_sz_4000_; size_t v___x_4001_; lean_object* v___x_4002_; lean_object* v_fst_4003_; lean_object* v_snd_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
v___f_3997_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3997_, 0, v_p_3995_);
v___x_3998_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3999_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_4000_ = lean_array_size(v_as_3996_);
v___x_4001_ = ((size_t)0ULL);
v___x_4002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_3998_, v_as_3996_, v___f_3997_, v_sz_4000_, v___x_4001_, v___x_3999_);
v_fst_4003_ = lean_ctor_get(v___x_4002_, 0);
v_snd_4004_ = lean_ctor_get(v___x_4002_, 1);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_4002_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_snd_4004_);
lean_inc(v_fst_4003_);
lean_dec(v___x_4002_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_fst_4003_);
lean_ctor_set(v_reuseFailAlloc_4010_, 1, v_snd_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile___redArg(lean_object* v_p_4012_, lean_object* v_as_4013_){
_start:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; uint8_t v___x_4016_; 
v___x_4014_ = lean_unsigned_to_nat(0u);
v___x_4015_ = lean_array_get_size(v_as_4013_);
v___x_4016_ = lean_nat_dec_lt(v___x_4014_, v___x_4015_);
if (v___x_4016_ == 0)
{
lean_dec_ref(v_p_4012_);
return v_as_4013_;
}
else
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; uint8_t v___x_4021_; 
v___x_4017_ = lean_unsigned_to_nat(1u);
v___x_4018_ = lean_nat_sub(v___x_4015_, v___x_4017_);
v___x_4019_ = lean_array_fget_borrowed(v_as_4013_, v___x_4018_);
lean_dec(v___x_4018_);
lean_inc_ref(v_p_4012_);
lean_inc(v___x_4019_);
v___x_4020_ = lean_apply_1(v_p_4012_, v___x_4019_);
v___x_4021_ = lean_unbox(v___x_4020_);
if (v___x_4021_ == 0)
{
lean_dec_ref(v_p_4012_);
return v_as_4013_;
}
else
{
lean_object* v___x_4022_; 
v___x_4022_ = lean_array_pop(v_as_4013_);
v_as_4013_ = v___x_4022_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile(lean_object* v_00_u03b1_4024_, lean_object* v_p_4025_, lean_object* v_as_4026_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Array_popWhile___redArg(v_p_4025_, v_as_4026_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(lean_object* v_p_4028_, lean_object* v_as_4029_, lean_object* v_i_4030_, lean_object* v_acc_4031_){
_start:
{
lean_object* v___x_4032_; uint8_t v___x_4033_; 
v___x_4032_ = lean_array_get_size(v_as_4029_);
v___x_4033_ = lean_nat_dec_lt(v_i_4030_, v___x_4032_);
if (v___x_4033_ == 0)
{
lean_dec(v_i_4030_);
lean_dec_ref(v_p_4028_);
return v_acc_4031_;
}
else
{
lean_object* v_a_4034_; lean_object* v___x_4035_; uint8_t v___x_4036_; 
v_a_4034_ = lean_array_fget_borrowed(v_as_4029_, v_i_4030_);
lean_inc_ref(v_p_4028_);
lean_inc(v_a_4034_);
v___x_4035_ = lean_apply_1(v_p_4028_, v_a_4034_);
v___x_4036_ = lean_unbox(v___x_4035_);
if (v___x_4036_ == 0)
{
lean_dec(v_i_4030_);
lean_dec_ref(v_p_4028_);
return v_acc_4031_;
}
else
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4037_ = lean_unsigned_to_nat(1u);
v___x_4038_ = lean_nat_add(v_i_4030_, v___x_4037_);
lean_dec(v_i_4030_);
lean_inc(v_a_4034_);
v___x_4039_ = lean_array_push(v_acc_4031_, v_a_4034_);
v_i_4030_ = v___x_4038_;
v_acc_4031_ = v___x_4039_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg___boxed(lean_object* v_p_4041_, lean_object* v_as_4042_, lean_object* v_i_4043_, lean_object* v_acc_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4041_, v_as_4042_, v_i_4043_, v_acc_4044_);
lean_dec_ref(v_as_4042_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(lean_object* v_00_u03b1_4046_, lean_object* v_p_4047_, lean_object* v_as_4048_, lean_object* v_i_4049_, lean_object* v_acc_4050_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4047_, v_as_4048_, v_i_4049_, v_acc_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___boxed(lean_object* v_00_u03b1_4052_, lean_object* v_p_4053_, lean_object* v_as_4054_, lean_object* v_i_4055_, lean_object* v_acc_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(v_00_u03b1_4052_, v_p_4053_, v_as_4054_, v_i_4055_, v_acc_4056_);
lean_dec_ref(v_as_4054_);
return v_res_4057_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg(lean_object* v_p_4058_, lean_object* v_as_4059_){
_start:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4060_ = lean_unsigned_to_nat(0u);
v___x_4061_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4062_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4058_, v_as_4059_, v___x_4060_, v___x_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg___boxed(lean_object* v_p_4063_, lean_object* v_as_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l_Array_takeWhile___redArg(v_p_4063_, v_as_4064_);
lean_dec_ref(v_as_4064_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile(lean_object* v_00_u03b1_4066_, lean_object* v_p_4067_, lean_object* v_as_4068_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Array_takeWhile___redArg(v_p_4067_, v_as_4068_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___boxed(lean_object* v_00_u03b1_4070_, lean_object* v_p_4071_, lean_object* v_as_4072_){
_start:
{
lean_object* v_res_4073_; 
v_res_4073_ = l_Array_takeWhile(v_00_u03b1_4070_, v_p_4071_, v_as_4072_);
lean_dec_ref(v_as_4072_);
return v_res_4073_;
}
}
static lean_object* _init_l_Array_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_4074_; 
v___x_4074_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx___redArg(lean_object* v_xs_4075_, lean_object* v_i_4076_){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; uint8_t v___x_4080_; 
v___x_4077_ = lean_unsigned_to_nat(1u);
v___x_4078_ = lean_nat_add(v_i_4076_, v___x_4077_);
v___x_4079_ = lean_array_get_size(v_xs_4075_);
v___x_4080_ = lean_nat_dec_lt(v___x_4078_, v___x_4079_);
if (v___x_4080_ == 0)
{
lean_object* v___x_4081_; 
lean_dec(v___x_4078_);
lean_dec(v_i_4076_);
v___x_4081_ = lean_array_pop(v_xs_4075_);
return v___x_4081_;
}
else
{
lean_object* v_xs_x27_4082_; 
v_xs_x27_4082_ = lean_array_fswap(v_xs_4075_, v___x_4078_, v_i_4076_);
lean_dec(v_i_4076_);
v_xs_4075_ = v_xs_x27_4082_;
v_i_4076_ = v___x_4078_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx(lean_object* v_00_u03b1_4084_, lean_object* v_xs_4085_, lean_object* v_i_4086_, lean_object* v_h_4087_){
_start:
{
lean_object* v___x_4088_; 
v___x_4088_ = l_Array_eraseIdx___redArg(v_xs_4085_, v_i_4086_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds___redArg(lean_object* v_xs_4089_, lean_object* v_i_4090_){
_start:
{
lean_object* v___x_4091_; uint8_t v___x_4092_; 
v___x_4091_ = lean_array_get_size(v_xs_4089_);
v___x_4092_ = lean_nat_dec_lt(v_i_4090_, v___x_4091_);
if (v___x_4092_ == 0)
{
lean_dec(v_i_4090_);
return v_xs_4089_;
}
else
{
lean_object* v___x_4093_; 
v___x_4093_ = l_Array_eraseIdx___redArg(v_xs_4089_, v_i_4090_);
return v___x_4093_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds(lean_object* v_00_u03b1_4094_, lean_object* v_xs_4095_, lean_object* v_i_4096_){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = l_Array_eraseIdxIfInBounds___redArg(v_xs_4095_, v_i_4096_);
return v___x_4097_;
}
}
static lean_object* _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Array_instInhabited(lean_box(0));
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(lean_object* v_msg_4099_){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4100_ = lean_obj_once(&l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0, &l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0_once, _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0);
v___x_4101_ = lean_panic_fn_borrowed(v___x_4100_, v_msg_4099_);
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0(lean_object* v_00_u03b1_4102_, lean_object* v_msg_4103_){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v_msg_4103_);
return v___x_4104_;
}
}
static lean_object* _init_l_Array_eraseIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4107_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4108_ = lean_unsigned_to_nat(47u);
v___x_4109_ = lean_unsigned_to_nat(1819u);
v___x_4110_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__0));
v___x_4111_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4112_ = l_mkPanicMessageWithDecl(v___x_4111_, v___x_4110_, v___x_4109_, v___x_4108_, v___x_4107_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21___redArg(lean_object* v_xs_4113_, lean_object* v_i_4114_){
_start:
{
lean_object* v___x_4115_; uint8_t v___x_4116_; 
v___x_4115_ = lean_array_get_size(v_xs_4113_);
v___x_4116_ = lean_nat_dec_lt(v_i_4114_, v___x_4115_);
if (v___x_4116_ == 0)
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
lean_dec(v_i_4114_);
lean_dec_ref(v_xs_4113_);
v___x_4117_ = lean_obj_once(&l_Array_eraseIdx_x21___redArg___closed__2, &l_Array_eraseIdx_x21___redArg___closed__2_once, _init_l_Array_eraseIdx_x21___redArg___closed__2);
v___x_4118_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4117_);
return v___x_4118_;
}
else
{
lean_object* v___x_4119_; 
v___x_4119_ = l_Array_eraseIdx___redArg(v_xs_4113_, v_i_4114_);
return v___x_4119_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21(lean_object* v_00_u03b1_4120_, lean_object* v_xs_4121_, lean_object* v_i_4122_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_Array_eraseIdx_x21___redArg(v_xs_4121_, v_i_4122_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Array_erase___redArg(lean_object* v_inst_4124_, lean_object* v_as_4125_, lean_object* v_a_4126_){
_start:
{
lean_object* v___x_4127_; 
v___x_4127_ = l_Array_finIdxOf_x3f___redArg(v_inst_4124_, v_as_4125_, v_a_4126_);
if (lean_obj_tag(v___x_4127_) == 0)
{
return v_as_4125_;
}
else
{
lean_object* v_val_4128_; lean_object* v___x_4129_; 
v_val_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_val_4128_);
lean_dec_ref(v___x_4127_);
v___x_4129_ = l_Array_eraseIdx___redArg(v_as_4125_, v_val_4128_);
return v___x_4129_;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase(lean_object* v_00_u03b1_4130_, lean_object* v_inst_4131_, lean_object* v_as_4132_, lean_object* v_a_4133_){
_start:
{
lean_object* v___x_4134_; 
v___x_4134_ = l_Array_erase___redArg(v_inst_4131_, v_as_4132_, v_a_4133_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseP___redArg(lean_object* v_as_4135_, lean_object* v_p_4136_){
_start:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4137_ = lean_unsigned_to_nat(0u);
v___x_4138_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_4136_, v_as_4135_, v___x_4137_);
if (lean_obj_tag(v___x_4138_) == 0)
{
return v_as_4135_;
}
else
{
lean_object* v_val_4139_; lean_object* v___x_4140_; 
v_val_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_val_4139_);
lean_dec_ref(v___x_4138_);
v___x_4140_ = l_Array_eraseIdx___redArg(v_as_4135_, v_val_4139_);
return v___x_4140_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseP(lean_object* v_00_u03b1_4141_, lean_object* v_as_4142_, lean_object* v_p_4143_){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = l_Array_eraseP___redArg(v_as_4142_, v_p_4143_);
return v___x_4144_;
}
}
static lean_object* _init_l_Array_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_4145_; 
v___x_4145_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(lean_object* v_i_4146_, lean_object* v_as_4147_, lean_object* v_j_4148_){
_start:
{
uint8_t v___x_4149_; 
v___x_4149_ = lean_nat_dec_lt(v_i_4146_, v_j_4148_);
if (v___x_4149_ == 0)
{
lean_dec(v_j_4148_);
return v_as_4147_;
}
else
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v_as_4152_; 
v___x_4150_ = lean_unsigned_to_nat(1u);
v___x_4151_ = lean_nat_sub(v_j_4148_, v___x_4150_);
v_as_4152_ = lean_array_fswap(v_as_4147_, v___x_4151_, v_j_4148_);
lean_dec(v_j_4148_);
v_as_4147_ = v_as_4152_;
v_j_4148_ = v___x_4151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg___boxed(lean_object* v_i_4154_, lean_object* v_as_4155_, lean_object* v_j_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4154_, v_as_4155_, v_j_4156_);
lean_dec(v_i_4154_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object* v_00_u03b1_4158_, lean_object* v_i_4159_, lean_object* v_as_4160_, lean_object* v_j_4161_){
_start:
{
lean_object* v___x_4162_; 
v___x_4162_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4159_, v_as_4160_, v_j_4161_);
return v___x_4162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___boxed(lean_object* v_00_u03b1_4163_, lean_object* v_i_4164_, lean_object* v_as_4165_, lean_object* v_j_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(v_00_u03b1_4163_, v_i_4164_, v_as_4165_, v_j_4166_);
lean_dec(v_i_4164_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg(lean_object* v_as_4168_, lean_object* v_i_4169_, lean_object* v_a_4170_){
_start:
{
lean_object* v_j_4171_; lean_object* v_as_4172_; lean_object* v___x_4173_; 
v_j_4171_ = lean_array_get_size(v_as_4168_);
v_as_4172_ = lean_array_push(v_as_4168_, v_a_4170_);
v___x_4173_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4169_, v_as_4172_, v_j_4171_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg___boxed(lean_object* v_as_4174_, lean_object* v_i_4175_, lean_object* v_a_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Array_insertIdx___redArg(v_as_4174_, v_i_4175_, v_a_4176_);
lean_dec(v_i_4175_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx(lean_object* v_00_u03b1_4178_, lean_object* v_as_4179_, lean_object* v_i_4180_, lean_object* v_a_4181_, lean_object* v_x_4182_){
_start:
{
lean_object* v_j_4183_; lean_object* v_as_4184_; lean_object* v___x_4185_; 
v_j_4183_ = lean_array_get_size(v_as_4179_);
v_as_4184_ = lean_array_push(v_as_4179_, v_a_4181_);
v___x_4185_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4180_, v_as_4184_, v_j_4183_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___boxed(lean_object* v_00_u03b1_4186_, lean_object* v_as_4187_, lean_object* v_i_4188_, lean_object* v_a_4189_, lean_object* v_x_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l_Array_insertIdx(v_00_u03b1_4186_, v_as_4187_, v_i_4188_, v_a_4189_, v_x_4190_);
lean_dec(v_i_4188_);
return v_res_4191_;
}
}
static lean_object* _init_l_Array_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4193_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4194_ = lean_unsigned_to_nat(7u);
v___x_4195_ = lean_unsigned_to_nat(1901u);
v___x_4196_ = ((lean_object*)(l_Array_insertIdx_x21___redArg___closed__0));
v___x_4197_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4198_ = l_mkPanicMessageWithDecl(v___x_4197_, v___x_4196_, v___x_4195_, v___x_4194_, v___x_4193_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg(lean_object* v_as_4199_, lean_object* v_i_4200_, lean_object* v_a_4201_){
_start:
{
lean_object* v___x_4202_; uint8_t v___x_4203_; 
v___x_4202_ = lean_array_get_size(v_as_4199_);
v___x_4203_ = lean_nat_dec_le(v_i_4200_, v___x_4202_);
if (v___x_4203_ == 0)
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_dec(v_a_4201_);
lean_dec_ref(v_as_4199_);
v___x_4204_ = lean_obj_once(&l_Array_insertIdx_x21___redArg___closed__1, &l_Array_insertIdx_x21___redArg___closed__1_once, _init_l_Array_insertIdx_x21___redArg___closed__1);
v___x_4205_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4204_);
return v___x_4205_;
}
else
{
lean_object* v_as_4206_; lean_object* v___x_4207_; 
v_as_4206_ = lean_array_push(v_as_4199_, v_a_4201_);
v___x_4207_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4200_, v_as_4206_, v___x_4202_);
return v___x_4207_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg___boxed(lean_object* v_as_4208_, lean_object* v_i_4209_, lean_object* v_a_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Array_insertIdx_x21___redArg(v_as_4208_, v_i_4209_, v_a_4210_);
lean_dec(v_i_4209_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21(lean_object* v_00_u03b1_4212_, lean_object* v_as_4213_, lean_object* v_i_4214_, lean_object* v_a_4215_){
_start:
{
lean_object* v___x_4216_; 
v___x_4216_ = l_Array_insertIdx_x21___redArg(v_as_4213_, v_i_4214_, v_a_4215_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___boxed(lean_object* v_00_u03b1_4217_, lean_object* v_as_4218_, lean_object* v_i_4219_, lean_object* v_a_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l_Array_insertIdx_x21(v_00_u03b1_4217_, v_as_4218_, v_i_4219_, v_a_4220_);
lean_dec(v_i_4219_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg(lean_object* v_as_4222_, lean_object* v_i_4223_, lean_object* v_a_4224_){
_start:
{
lean_object* v___x_4225_; uint8_t v___x_4226_; 
v___x_4225_ = lean_array_get_size(v_as_4222_);
v___x_4226_ = lean_nat_dec_le(v_i_4223_, v___x_4225_);
if (v___x_4226_ == 0)
{
lean_dec(v_a_4224_);
return v_as_4222_;
}
else
{
lean_object* v_as_4227_; lean_object* v___x_4228_; 
v_as_4227_ = lean_array_push(v_as_4222_, v_a_4224_);
v___x_4228_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4223_, v_as_4227_, v___x_4225_);
return v___x_4228_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg___boxed(lean_object* v_as_4229_, lean_object* v_i_4230_, lean_object* v_a_4231_){
_start:
{
lean_object* v_res_4232_; 
v_res_4232_ = l_Array_insertIdxIfInBounds___redArg(v_as_4229_, v_i_4230_, v_a_4231_);
lean_dec(v_i_4230_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds(lean_object* v_00_u03b1_4233_, lean_object* v_as_4234_, lean_object* v_i_4235_, lean_object* v_a_4236_){
_start:
{
lean_object* v___x_4237_; 
v___x_4237_ = l_Array_insertIdxIfInBounds___redArg(v_as_4234_, v_i_4235_, v_a_4236_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___boxed(lean_object* v_00_u03b1_4238_, lean_object* v_as_4239_, lean_object* v_i_4240_, lean_object* v_a_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Array_insertIdxIfInBounds(v_00_u03b1_4238_, v_as_4239_, v_i_4240_, v_a_4241_);
lean_dec(v_i_4240_);
return v_res_4242_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux___redArg(lean_object* v_inst_4243_, lean_object* v_as_4244_, lean_object* v_bs_4245_, lean_object* v_i_4246_){
_start:
{
lean_object* v___x_4247_; uint8_t v___x_4248_; 
v___x_4247_ = lean_array_get_size(v_as_4244_);
v___x_4248_ = lean_nat_dec_lt(v_i_4246_, v___x_4247_);
if (v___x_4248_ == 0)
{
uint8_t v___x_4249_; 
lean_dec(v_i_4246_);
lean_dec_ref(v_inst_4243_);
v___x_4249_ = 1;
return v___x_4249_;
}
else
{
lean_object* v_a_4250_; lean_object* v_b_4251_; lean_object* v___x_4252_; uint8_t v___x_4253_; 
v_a_4250_ = lean_array_fget_borrowed(v_as_4244_, v_i_4246_);
v_b_4251_ = lean_array_fget_borrowed(v_bs_4245_, v_i_4246_);
lean_inc_ref(v_inst_4243_);
lean_inc(v_b_4251_);
lean_inc(v_a_4250_);
v___x_4252_ = lean_apply_2(v_inst_4243_, v_a_4250_, v_b_4251_);
v___x_4253_ = lean_unbox(v___x_4252_);
if (v___x_4253_ == 0)
{
uint8_t v___x_4254_; 
lean_dec(v_i_4246_);
lean_dec_ref(v_inst_4243_);
v___x_4254_ = lean_unbox(v___x_4252_);
return v___x_4254_;
}
else
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4255_ = lean_unsigned_to_nat(1u);
v___x_4256_ = lean_nat_add(v_i_4246_, v___x_4255_);
lean_dec(v_i_4246_);
v_i_4246_ = v___x_4256_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___redArg___boxed(lean_object* v_inst_4258_, lean_object* v_as_4259_, lean_object* v_bs_4260_, lean_object* v_i_4261_){
_start:
{
uint8_t v_res_4262_; lean_object* v_r_4263_; 
v_res_4262_ = l_Array_isPrefixOfAux___redArg(v_inst_4258_, v_as_4259_, v_bs_4260_, v_i_4261_);
lean_dec_ref(v_bs_4260_);
lean_dec_ref(v_as_4259_);
v_r_4263_ = lean_box(v_res_4262_);
return v_r_4263_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux(lean_object* v_00_u03b1_4264_, lean_object* v_inst_4265_, lean_object* v_as_4266_, lean_object* v_bs_4267_, lean_object* v_hle_4268_, lean_object* v_i_4269_){
_start:
{
uint8_t v___x_4270_; 
v___x_4270_ = l_Array_isPrefixOfAux___redArg(v_inst_4265_, v_as_4266_, v_bs_4267_, v_i_4269_);
return v___x_4270_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___boxed(lean_object* v_00_u03b1_4271_, lean_object* v_inst_4272_, lean_object* v_as_4273_, lean_object* v_bs_4274_, lean_object* v_hle_4275_, lean_object* v_i_4276_){
_start:
{
uint8_t v_res_4277_; lean_object* v_r_4278_; 
v_res_4277_ = l_Array_isPrefixOfAux(v_00_u03b1_4271_, v_inst_4272_, v_as_4273_, v_bs_4274_, v_hle_4275_, v_i_4276_);
lean_dec_ref(v_bs_4274_);
lean_dec_ref(v_as_4273_);
v_r_4278_ = lean_box(v_res_4277_);
return v_r_4278_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf___redArg(lean_object* v_inst_4279_, lean_object* v_as_4280_, lean_object* v_bs_4281_){
_start:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; uint8_t v___x_4284_; 
v___x_4282_ = lean_array_get_size(v_as_4280_);
v___x_4283_ = lean_array_get_size(v_bs_4281_);
v___x_4284_ = lean_nat_dec_le(v___x_4282_, v___x_4283_);
if (v___x_4284_ == 0)
{
lean_dec_ref(v_inst_4279_);
return v___x_4284_;
}
else
{
lean_object* v___x_4285_; uint8_t v___x_4286_; 
v___x_4285_ = lean_unsigned_to_nat(0u);
v___x_4286_ = l_Array_isPrefixOfAux___redArg(v_inst_4279_, v_as_4280_, v_bs_4281_, v___x_4285_);
return v___x_4286_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___redArg___boxed(lean_object* v_inst_4287_, lean_object* v_as_4288_, lean_object* v_bs_4289_){
_start:
{
uint8_t v_res_4290_; lean_object* v_r_4291_; 
v_res_4290_ = l_Array_isPrefixOf___redArg(v_inst_4287_, v_as_4288_, v_bs_4289_);
lean_dec_ref(v_bs_4289_);
lean_dec_ref(v_as_4288_);
v_r_4291_ = lean_box(v_res_4290_);
return v_r_4291_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf(lean_object* v_00_u03b1_4292_, lean_object* v_inst_4293_, lean_object* v_as_4294_, lean_object* v_bs_4295_){
_start:
{
uint8_t v___x_4296_; 
v___x_4296_ = l_Array_isPrefixOf___redArg(v_inst_4293_, v_as_4294_, v_bs_4295_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___boxed(lean_object* v_00_u03b1_4297_, lean_object* v_inst_4298_, lean_object* v_as_4299_, lean_object* v_bs_4300_){
_start:
{
uint8_t v_res_4301_; lean_object* v_r_4302_; 
v_res_4301_ = l_Array_isPrefixOf(v_00_u03b1_4297_, v_inst_4298_, v_as_4299_, v_bs_4300_);
lean_dec_ref(v_bs_4300_);
lean_dec_ref(v_as_4299_);
v_r_4302_ = lean_box(v_res_4301_);
return v_r_4302_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0___boxed(lean_object* v_i_4303_, lean_object* v_cs_4304_, lean_object* v_inst_4305_, lean_object* v_as_4306_, lean_object* v_bs_4307_, lean_object* v_f_4308_, lean_object* v_____do__lift_4309_){
_start:
{
lean_object* v_res_4310_; 
v_res_4310_ = l_Array_zipWithMAux___redArg___lam__0(v_i_4303_, v_cs_4304_, v_inst_4305_, v_as_4306_, v_bs_4307_, v_f_4308_, v_____do__lift_4309_);
lean_dec(v_i_4303_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg(lean_object* v_inst_4311_, lean_object* v_as_4312_, lean_object* v_bs_4313_, lean_object* v_f_4314_, lean_object* v_i_4315_, lean_object* v_cs_4316_){
_start:
{
lean_object* v___x_4317_; uint8_t v___x_4318_; 
v___x_4317_ = lean_array_get_size(v_as_4312_);
v___x_4318_ = lean_nat_dec_lt(v_i_4315_, v___x_4317_);
if (v___x_4318_ == 0)
{
lean_object* v_toApplicative_4319_; lean_object* v_toPure_4320_; lean_object* v___x_4321_; 
lean_dec(v_i_4315_);
lean_dec(v_f_4314_);
lean_dec_ref(v_bs_4313_);
lean_dec_ref(v_as_4312_);
v_toApplicative_4319_ = lean_ctor_get(v_inst_4311_, 0);
lean_inc_ref(v_toApplicative_4319_);
lean_dec_ref(v_inst_4311_);
v_toPure_4320_ = lean_ctor_get(v_toApplicative_4319_, 1);
lean_inc(v_toPure_4320_);
lean_dec_ref(v_toApplicative_4319_);
v___x_4321_ = lean_apply_2(v_toPure_4320_, lean_box(0), v_cs_4316_);
return v___x_4321_;
}
else
{
lean_object* v___x_4322_; uint8_t v___x_4323_; 
v___x_4322_ = lean_array_get_size(v_bs_4313_);
v___x_4323_ = lean_nat_dec_lt(v_i_4315_, v___x_4322_);
if (v___x_4323_ == 0)
{
lean_object* v_toApplicative_4324_; lean_object* v_toPure_4325_; lean_object* v___x_4326_; 
lean_dec(v_i_4315_);
lean_dec(v_f_4314_);
lean_dec_ref(v_bs_4313_);
lean_dec_ref(v_as_4312_);
v_toApplicative_4324_ = lean_ctor_get(v_inst_4311_, 0);
lean_inc_ref(v_toApplicative_4324_);
lean_dec_ref(v_inst_4311_);
v_toPure_4325_ = lean_ctor_get(v_toApplicative_4324_, 1);
lean_inc(v_toPure_4325_);
lean_dec_ref(v_toApplicative_4324_);
v___x_4326_ = lean_apply_2(v_toPure_4325_, lean_box(0), v_cs_4316_);
return v___x_4326_;
}
else
{
lean_object* v_toBind_4327_; lean_object* v___f_4328_; lean_object* v_a_4329_; lean_object* v_b_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
v_toBind_4327_ = lean_ctor_get(v_inst_4311_, 1);
lean_inc(v_toBind_4327_);
lean_inc(v_f_4314_);
lean_inc_ref(v_bs_4313_);
lean_inc_ref(v_as_4312_);
lean_inc(v_i_4315_);
v___f_4328_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4328_, 0, v_i_4315_);
lean_closure_set(v___f_4328_, 1, v_cs_4316_);
lean_closure_set(v___f_4328_, 2, v_inst_4311_);
lean_closure_set(v___f_4328_, 3, v_as_4312_);
lean_closure_set(v___f_4328_, 4, v_bs_4313_);
lean_closure_set(v___f_4328_, 5, v_f_4314_);
v_a_4329_ = lean_array_fget(v_as_4312_, v_i_4315_);
lean_dec_ref(v_as_4312_);
v_b_4330_ = lean_array_fget(v_bs_4313_, v_i_4315_);
lean_dec(v_i_4315_);
lean_dec_ref(v_bs_4313_);
v___x_4331_ = lean_apply_2(v_f_4314_, v_a_4329_, v_b_4330_);
v___x_4332_ = lean_apply_4(v_toBind_4327_, lean_box(0), lean_box(0), v___x_4331_, v___f_4328_);
return v___x_4332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0(lean_object* v_i_4333_, lean_object* v_cs_4334_, lean_object* v_inst_4335_, lean_object* v_as_4336_, lean_object* v_bs_4337_, lean_object* v_f_4338_, lean_object* v_____do__lift_4339_){
_start:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4340_ = lean_unsigned_to_nat(1u);
v___x_4341_ = lean_nat_add(v_i_4333_, v___x_4340_);
v___x_4342_ = lean_array_push(v_cs_4334_, v_____do__lift_4339_);
v___x_4343_ = l_Array_zipWithMAux___redArg(v_inst_4335_, v_as_4336_, v_bs_4337_, v_f_4338_, v___x_4341_, v___x_4342_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux(lean_object* v_00_u03b1_4344_, lean_object* v_00_u03b2_4345_, lean_object* v_00_u03b3_4346_, lean_object* v_m_4347_, lean_object* v_inst_4348_, lean_object* v_as_4349_, lean_object* v_bs_4350_, lean_object* v_f_4351_, lean_object* v_i_4352_, lean_object* v_cs_4353_){
_start:
{
lean_object* v___x_4354_; 
v___x_4354_ = l_Array_zipWithMAux___redArg(v_inst_4348_, v_as_4349_, v_bs_4350_, v_f_4351_, v_i_4352_, v_cs_4353_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith___redArg(lean_object* v_f_4355_, lean_object* v_as_4356_, lean_object* v_bs_4357_){
_start:
{
lean_object* v___f_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___f_4358_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4358_, 0, v_f_4355_);
v___x_4359_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4360_ = lean_unsigned_to_nat(0u);
v___x_4361_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4362_ = l_Array_zipWithMAux___redArg(v___x_4359_, v_as_4356_, v_bs_4357_, v___f_4358_, v___x_4360_, v___x_4361_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith(lean_object* v_00_u03b1_4363_, lean_object* v_00_u03b2_4364_, lean_object* v_00_u03b3_4365_, lean_object* v_f_4366_, lean_object* v_as_4367_, lean_object* v_bs_4368_){
_start:
{
lean_object* v___f_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___f_4369_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4369_, 0, v_f_4366_);
v___x_4370_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4371_ = lean_unsigned_to_nat(0u);
v___x_4372_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4373_ = l_Array_zipWithMAux___redArg(v___x_4370_, v_as_4367_, v_bs_4368_, v___f_4369_, v___x_4371_, v___x_4372_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(lean_object* v_as_4374_, lean_object* v_bs_4375_, lean_object* v_i_4376_, lean_object* v_cs_4377_){
_start:
{
lean_object* v___x_4378_; uint8_t v___x_4379_; 
v___x_4378_ = lean_array_get_size(v_as_4374_);
v___x_4379_ = lean_nat_dec_lt(v_i_4376_, v___x_4378_);
if (v___x_4379_ == 0)
{
lean_dec(v_i_4376_);
return v_cs_4377_;
}
else
{
lean_object* v___x_4380_; uint8_t v___x_4381_; 
v___x_4380_ = lean_array_get_size(v_bs_4375_);
v___x_4381_ = lean_nat_dec_lt(v_i_4376_, v___x_4380_);
if (v___x_4381_ == 0)
{
lean_dec(v_i_4376_);
return v_cs_4377_;
}
else
{
lean_object* v_a_4382_; lean_object* v_b_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v_a_4382_ = lean_array_fget_borrowed(v_as_4374_, v_i_4376_);
v_b_4383_ = lean_array_fget_borrowed(v_bs_4375_, v_i_4376_);
lean_inc(v_b_4383_);
lean_inc(v_a_4382_);
v___x_4384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4384_, 0, v_a_4382_);
lean_ctor_set(v___x_4384_, 1, v_b_4383_);
v___x_4385_ = lean_unsigned_to_nat(1u);
v___x_4386_ = lean_nat_add(v_i_4376_, v___x_4385_);
lean_dec(v_i_4376_);
v___x_4387_ = lean_array_push(v_cs_4377_, v___x_4384_);
v_i_4376_ = v___x_4386_;
v_cs_4377_ = v___x_4387_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg___boxed(lean_object* v_as_4389_, lean_object* v_bs_4390_, lean_object* v_i_4391_, lean_object* v_cs_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4389_, v_bs_4390_, v_i_4391_, v_cs_4392_);
lean_dec_ref(v_bs_4390_);
lean_dec_ref(v_as_4389_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg(lean_object* v_as_4396_, lean_object* v_bs_4397_){
_start:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4398_ = lean_unsigned_to_nat(0u);
v___x_4399_ = ((lean_object*)(l_Array_zip___redArg___closed__0));
v___x_4400_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4396_, v_bs_4397_, v___x_4398_, v___x_4399_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg___boxed(lean_object* v_as_4401_, lean_object* v_bs_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l_Array_zip___redArg(v_as_4401_, v_bs_4402_);
lean_dec_ref(v_bs_4402_);
lean_dec_ref(v_as_4401_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_Array_zip(lean_object* v_00_u03b1_4404_, lean_object* v_00_u03b2_4405_, lean_object* v_as_4406_, lean_object* v_bs_4407_){
_start:
{
lean_object* v___x_4408_; 
v___x_4408_ = l_Array_zip___redArg(v_as_4406_, v_bs_4407_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___boxed(lean_object* v_00_u03b1_4409_, lean_object* v_00_u03b2_4410_, lean_object* v_as_4411_, lean_object* v_bs_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l_Array_zip(v_00_u03b1_4409_, v_00_u03b2_4410_, v_as_4411_, v_bs_4412_);
lean_dec_ref(v_bs_4412_);
lean_dec_ref(v_as_4411_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0(lean_object* v_00_u03b1_4414_, lean_object* v_00_u03b2_4415_, lean_object* v_as_4416_, lean_object* v_bs_4417_, lean_object* v_i_4418_, lean_object* v_cs_4419_){
_start:
{
lean_object* v___x_4420_; 
v___x_4420_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4416_, v_bs_4417_, v_i_4418_, v_cs_4419_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___boxed(lean_object* v_00_u03b1_4421_, lean_object* v_00_u03b2_4422_, lean_object* v_as_4423_, lean_object* v_bs_4424_, lean_object* v_i_4425_, lean_object* v_cs_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l_Array_zipWithMAux___at___00Array_zip_spec__0(v_00_u03b1_4421_, v_00_u03b2_4422_, v_as_4423_, v_bs_4424_, v_i_4425_, v_cs_4426_);
lean_dec_ref(v_bs_4424_);
lean_dec_ref(v_as_4423_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(lean_object* v_f_4428_, lean_object* v_as_4429_, lean_object* v_bs_4430_, lean_object* v_i_4431_, lean_object* v_cs_4432_){
_start:
{
lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4442_; lean_object* v___y_4449_; lean_object* v___x_4456_; lean_object* v___x_4457_; uint8_t v___x_4458_; 
v___x_4456_ = lean_array_get_size(v_as_4429_);
v___x_4457_ = lean_array_get_size(v_bs_4430_);
v___x_4458_ = lean_nat_dec_le(v___x_4456_, v___x_4457_);
if (v___x_4458_ == 0)
{
v___y_4449_ = v___x_4456_;
goto v___jp_4448_;
}
else
{
v___y_4449_ = v___x_4457_;
goto v___jp_4448_;
}
v___jp_4433_:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4436_ = lean_unsigned_to_nat(1u);
v___x_4437_ = lean_nat_add(v_i_4431_, v___x_4436_);
lean_dec(v_i_4431_);
lean_inc(v_f_4428_);
v___x_4438_ = lean_apply_2(v_f_4428_, v___y_4434_, v___y_4435_);
v___x_4439_ = lean_array_push(v_cs_4432_, v___x_4438_);
v_i_4431_ = v___x_4437_;
v_cs_4432_ = v___x_4439_;
goto _start;
}
v___jp_4441_:
{
lean_object* v___x_4443_; uint8_t v___x_4444_; 
v___x_4443_ = lean_array_get_size(v_bs_4430_);
v___x_4444_ = lean_nat_dec_lt(v_i_4431_, v___x_4443_);
if (v___x_4444_ == 0)
{
lean_object* v___x_4445_; 
v___x_4445_ = lean_box(0);
v___y_4434_ = v___y_4442_;
v___y_4435_ = v___x_4445_;
goto v___jp_4433_;
}
else
{
lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4446_ = lean_array_fget_borrowed(v_bs_4430_, v_i_4431_);
lean_inc(v___x_4446_);
v___x_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4447_, 0, v___x_4446_);
v___y_4434_ = v___y_4442_;
v___y_4435_ = v___x_4447_;
goto v___jp_4433_;
}
}
v___jp_4448_:
{
uint8_t v___x_4450_; 
v___x_4450_ = lean_nat_dec_lt(v_i_4431_, v___y_4449_);
lean_dec(v___y_4449_);
if (v___x_4450_ == 0)
{
lean_dec(v_i_4431_);
lean_dec(v_f_4428_);
return v_cs_4432_;
}
else
{
lean_object* v___x_4451_; uint8_t v___x_4452_; 
v___x_4451_ = lean_array_get_size(v_as_4429_);
v___x_4452_ = lean_nat_dec_lt(v_i_4431_, v___x_4451_);
if (v___x_4452_ == 0)
{
lean_object* v___x_4453_; 
v___x_4453_ = lean_box(0);
v___y_4442_ = v___x_4453_;
goto v___jp_4441_;
}
else
{
lean_object* v___x_4454_; lean_object* v___x_4455_; 
v___x_4454_ = lean_array_fget_borrowed(v_as_4429_, v_i_4431_);
lean_inc(v___x_4454_);
v___x_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4455_, 0, v___x_4454_);
v___y_4442_ = v___x_4455_;
goto v___jp_4441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg___boxed(lean_object* v_f_4459_, lean_object* v_as_4460_, lean_object* v_bs_4461_, lean_object* v_i_4462_, lean_object* v_cs_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4459_, v_as_4460_, v_bs_4461_, v_i_4462_, v_cs_4463_);
lean_dec_ref(v_bs_4461_);
lean_dec_ref(v_as_4460_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(lean_object* v_00_u03b1_4465_, lean_object* v_00_u03b2_4466_, lean_object* v_00_u03b3_4467_, lean_object* v_f_4468_, lean_object* v_as_4469_, lean_object* v_bs_4470_, lean_object* v_i_4471_, lean_object* v_cs_4472_){
_start:
{
lean_object* v___x_4473_; 
v___x_4473_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4468_, v_as_4469_, v_bs_4470_, v_i_4471_, v_cs_4472_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___boxed(lean_object* v_00_u03b1_4474_, lean_object* v_00_u03b2_4475_, lean_object* v_00_u03b3_4476_, lean_object* v_f_4477_, lean_object* v_as_4478_, lean_object* v_bs_4479_, lean_object* v_i_4480_, lean_object* v_cs_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(v_00_u03b1_4474_, v_00_u03b2_4475_, v_00_u03b3_4476_, v_f_4477_, v_as_4478_, v_bs_4479_, v_i_4480_, v_cs_4481_);
lean_dec_ref(v_bs_4479_);
lean_dec_ref(v_as_4478_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg(lean_object* v_f_4483_, lean_object* v_as_4484_, lean_object* v_bs_4485_){
_start:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4486_ = lean_unsigned_to_nat(0u);
v___x_4487_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4488_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4483_, v_as_4484_, v_bs_4485_, v___x_4486_, v___x_4487_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg___boxed(lean_object* v_f_4489_, lean_object* v_as_4490_, lean_object* v_bs_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l_Array_zipWithAll___redArg(v_f_4489_, v_as_4490_, v_bs_4491_);
lean_dec_ref(v_bs_4491_);
lean_dec_ref(v_as_4490_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll(lean_object* v_00_u03b1_4493_, lean_object* v_00_u03b2_4494_, lean_object* v_00_u03b3_4495_, lean_object* v_f_4496_, lean_object* v_as_4497_, lean_object* v_bs_4498_){
_start:
{
lean_object* v___x_4499_; 
v___x_4499_ = l_Array_zipWithAll___redArg(v_f_4496_, v_as_4497_, v_bs_4498_);
return v___x_4499_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___boxed(lean_object* v_00_u03b1_4500_, lean_object* v_00_u03b2_4501_, lean_object* v_00_u03b3_4502_, lean_object* v_f_4503_, lean_object* v_as_4504_, lean_object* v_bs_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_Array_zipWithAll(v_00_u03b1_4500_, v_00_u03b2_4501_, v_00_u03b3_4502_, v_f_4503_, v_as_4504_, v_bs_4505_);
lean_dec_ref(v_bs_4505_);
lean_dec_ref(v_as_4504_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM___redArg(lean_object* v_inst_4507_, lean_object* v_f_4508_, lean_object* v_as_4509_, lean_object* v_bs_4510_){
_start:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4511_ = lean_unsigned_to_nat(0u);
v___x_4512_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4513_ = l_Array_zipWithMAux___redArg(v_inst_4507_, v_as_4509_, v_bs_4510_, v_f_4508_, v___x_4511_, v___x_4512_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM(lean_object* v_00_u03b1_4514_, lean_object* v_00_u03b2_4515_, lean_object* v_00_u03b3_4516_, lean_object* v_m_4517_, lean_object* v_inst_4518_, lean_object* v_f_4519_, lean_object* v_as_4520_, lean_object* v_bs_4521_){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4522_ = lean_unsigned_to_nat(0u);
v___x_4523_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4524_ = l_Array_zipWithMAux___redArg(v_inst_4518_, v_as_4520_, v_bs_4521_, v_f_4519_, v___x_4522_, v___x_4523_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(lean_object* v_as_4525_, size_t v_i_4526_, size_t v_stop_4527_, lean_object* v_b_4528_){
_start:
{
uint8_t v___x_4529_; 
v___x_4529_ = lean_usize_dec_eq(v_i_4526_, v_stop_4527_);
if (v___x_4529_ == 0)
{
lean_object* v_fst_4530_; lean_object* v_snd_4531_; lean_object* v___x_4532_; lean_object* v_fst_4533_; lean_object* v_snd_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4546_; 
v_fst_4530_ = lean_ctor_get(v_b_4528_, 0);
lean_inc(v_fst_4530_);
v_snd_4531_ = lean_ctor_get(v_b_4528_, 1);
lean_inc(v_snd_4531_);
lean_dec_ref(v_b_4528_);
v___x_4532_ = lean_array_uget(v_as_4525_, v_i_4526_);
v_fst_4533_ = lean_ctor_get(v___x_4532_, 0);
v_snd_4534_ = lean_ctor_get(v___x_4532_, 1);
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4536_ = v___x_4532_;
v_isShared_4537_ = v_isSharedCheck_4546_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_snd_4534_);
lean_inc(v_fst_4533_);
lean_dec(v___x_4532_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4546_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4541_; 
v___x_4538_ = lean_array_push(v_fst_4530_, v_fst_4533_);
v___x_4539_ = lean_array_push(v_snd_4531_, v_snd_4534_);
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 1, v___x_4539_);
lean_ctor_set(v___x_4536_, 0, v___x_4538_);
v___x_4541_ = v___x_4536_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4538_);
lean_ctor_set(v_reuseFailAlloc_4545_, 1, v___x_4539_);
v___x_4541_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
size_t v___x_4542_; size_t v___x_4543_; 
v___x_4542_ = ((size_t)1ULL);
v___x_4543_ = lean_usize_add(v_i_4526_, v___x_4542_);
v_i_4526_ = v___x_4543_;
v_b_4528_ = v___x_4541_;
goto _start;
}
}
}
else
{
return v_b_4528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg___boxed(lean_object* v_as_4547_, lean_object* v_i_4548_, lean_object* v_stop_4549_, lean_object* v_b_4550_){
_start:
{
size_t v_i_boxed_4551_; size_t v_stop_boxed_4552_; lean_object* v_res_4553_; 
v_i_boxed_4551_ = lean_unbox_usize(v_i_4548_);
lean_dec(v_i_4548_);
v_stop_boxed_4552_ = lean_unbox_usize(v_stop_4549_);
lean_dec(v_stop_4549_);
v_res_4553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4547_, v_i_boxed_4551_, v_stop_boxed_4552_, v_b_4550_);
lean_dec_ref(v_as_4547_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg(lean_object* v_as_4554_){
_start:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; uint8_t v___x_4558_; 
v___x_4555_ = lean_unsigned_to_nat(0u);
v___x_4556_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v___x_4557_ = lean_array_get_size(v_as_4554_);
v___x_4558_ = lean_nat_dec_lt(v___x_4555_, v___x_4557_);
if (v___x_4558_ == 0)
{
return v___x_4556_;
}
else
{
uint8_t v___x_4559_; 
v___x_4559_ = lean_nat_dec_le(v___x_4557_, v___x_4557_);
if (v___x_4559_ == 0)
{
if (v___x_4558_ == 0)
{
return v___x_4556_;
}
else
{
size_t v___x_4560_; size_t v___x_4561_; lean_object* v___x_4562_; 
v___x_4560_ = ((size_t)0ULL);
v___x_4561_ = lean_usize_of_nat(v___x_4557_);
v___x_4562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4554_, v___x_4560_, v___x_4561_, v___x_4556_);
return v___x_4562_;
}
}
else
{
size_t v___x_4563_; size_t v___x_4564_; lean_object* v___x_4565_; 
v___x_4563_ = ((size_t)0ULL);
v___x_4564_ = lean_usize_of_nat(v___x_4557_);
v___x_4565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4554_, v___x_4563_, v___x_4564_, v___x_4556_);
return v___x_4565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg___boxed(lean_object* v_as_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l_Array_unzip___redArg(v_as_4566_);
lean_dec_ref(v_as_4566_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip(lean_object* v_00_u03b1_4568_, lean_object* v_00_u03b2_4569_, lean_object* v_as_4570_){
_start:
{
lean_object* v___x_4571_; 
v___x_4571_ = l_Array_unzip___redArg(v_as_4570_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___boxed(lean_object* v_00_u03b1_4572_, lean_object* v_00_u03b2_4573_, lean_object* v_as_4574_){
_start:
{
lean_object* v_res_4575_; 
v_res_4575_ = l_Array_unzip(v_00_u03b1_4572_, v_00_u03b2_4573_, v_as_4574_);
lean_dec_ref(v_as_4574_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(lean_object* v_00_u03b1_4576_, lean_object* v_00_u03b2_4577_, lean_object* v_as_4578_, size_t v_i_4579_, size_t v_stop_4580_, lean_object* v_b_4581_){
_start:
{
lean_object* v___x_4582_; 
v___x_4582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4578_, v_i_4579_, v_stop_4580_, v_b_4581_);
return v___x_4582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___boxed(lean_object* v_00_u03b1_4583_, lean_object* v_00_u03b2_4584_, lean_object* v_as_4585_, lean_object* v_i_4586_, lean_object* v_stop_4587_, lean_object* v_b_4588_){
_start:
{
size_t v_i_boxed_4589_; size_t v_stop_boxed_4590_; lean_object* v_res_4591_; 
v_i_boxed_4589_ = lean_unbox_usize(v_i_4586_);
lean_dec(v_i_4586_);
v_stop_boxed_4590_ = lean_unbox_usize(v_stop_4587_);
lean_dec(v_stop_4587_);
v_res_4591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(v_00_u03b1_4583_, v_00_u03b2_4584_, v_as_4585_, v_i_boxed_4589_, v_stop_boxed_4590_, v_b_4588_);
lean_dec_ref(v_as_4585_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l_Array_replace___redArg(lean_object* v_inst_4592_, lean_object* v_xs_4593_, lean_object* v_a_4594_, lean_object* v_b_4595_){
_start:
{
lean_object* v___x_4596_; 
v___x_4596_ = l_Array_finIdxOf_x3f___redArg(v_inst_4592_, v_xs_4593_, v_a_4594_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_dec(v_b_4595_);
return v_xs_4593_;
}
else
{
lean_object* v_val_4597_; lean_object* v___x_4598_; 
v_val_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_val_4597_);
lean_dec_ref(v___x_4596_);
v___x_4598_ = lean_array_fset(v_xs_4593_, v_val_4597_, v_b_4595_);
lean_dec(v_val_4597_);
return v___x_4598_;
}
}
}
LEAN_EXPORT lean_object* l_Array_replace(lean_object* v_00_u03b1_4599_, lean_object* v_inst_4600_, lean_object* v_xs_4601_, lean_object* v_a_4602_, lean_object* v_b_4603_){
_start:
{
lean_object* v___x_4604_; 
v___x_4604_ = l_Array_replace___redArg(v_inst_4600_, v_xs_4601_, v_a_4602_, v_b_4603_);
return v___x_4604_;
}
}
LEAN_EXPORT lean_object* l_Array_instLT(lean_object* v_00_u03b1_4605_, lean_object* v_inst_4606_){
_start:
{
lean_object* v___x_4607_; 
v___x_4607_ = lean_box(0);
return v___x_4607_;
}
}
LEAN_EXPORT lean_object* l_Array_instLE(lean_object* v_00_u03b1_4608_, lean_object* v_inst_4609_){
_start:
{
lean_object* v___x_4610_; 
v___x_4610_ = lean_box(0);
return v___x_4610_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg(lean_object* v_n_4611_, lean_object* v_a_4612_, lean_object* v_xs_4613_){
_start:
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4614_ = lean_array_get_size(v_xs_4613_);
v___x_4615_ = lean_nat_sub(v_n_4611_, v___x_4614_);
v___x_4616_ = lean_mk_array(v___x_4615_, v_a_4612_);
v___x_4617_ = l_Array_append___redArg(v___x_4616_, v_xs_4613_);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg___boxed(lean_object* v_n_4618_, lean_object* v_a_4619_, lean_object* v_xs_4620_){
_start:
{
lean_object* v_res_4621_; 
v_res_4621_ = l_Array_leftpad___redArg(v_n_4618_, v_a_4619_, v_xs_4620_);
lean_dec_ref(v_xs_4620_);
lean_dec(v_n_4618_);
return v_res_4621_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad(lean_object* v_00_u03b1_4622_, lean_object* v_n_4623_, lean_object* v_a_4624_, lean_object* v_xs_4625_){
_start:
{
lean_object* v___x_4626_; 
v___x_4626_ = l_Array_leftpad___redArg(v_n_4623_, v_a_4624_, v_xs_4625_);
return v___x_4626_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___boxed(lean_object* v_00_u03b1_4627_, lean_object* v_n_4628_, lean_object* v_a_4629_, lean_object* v_xs_4630_){
_start:
{
lean_object* v_res_4631_; 
v_res_4631_ = l_Array_leftpad(v_00_u03b1_4627_, v_n_4628_, v_a_4629_, v_xs_4630_);
lean_dec_ref(v_xs_4630_);
lean_dec(v_n_4628_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg(lean_object* v_n_4632_, lean_object* v_a_4633_, lean_object* v_xs_4634_){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4635_ = lean_array_get_size(v_xs_4634_);
v___x_4636_ = lean_nat_sub(v_n_4632_, v___x_4635_);
v___x_4637_ = lean_mk_array(v___x_4636_, v_a_4633_);
v___x_4638_ = l_Array_append___redArg(v_xs_4634_, v___x_4637_);
lean_dec_ref(v___x_4637_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg___boxed(lean_object* v_n_4639_, lean_object* v_a_4640_, lean_object* v_xs_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l_Array_rightpad___redArg(v_n_4639_, v_a_4640_, v_xs_4641_);
lean_dec(v_n_4639_);
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad(lean_object* v_00_u03b1_4643_, lean_object* v_n_4644_, lean_object* v_a_4645_, lean_object* v_xs_4646_){
_start:
{
lean_object* v___x_4647_; 
v___x_4647_ = l_Array_rightpad___redArg(v_n_4644_, v_a_4645_, v_xs_4646_);
return v___x_4647_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___boxed(lean_object* v_00_u03b1_4648_, lean_object* v_n_4649_, lean_object* v_a_4650_, lean_object* v_xs_4651_){
_start:
{
lean_object* v_res_4652_; 
v_res_4652_ = l_Array_rightpad(v_00_u03b1_4648_, v_n_4649_, v_a_4650_, v_xs_4651_);
lean_dec(v_n_4649_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0(lean_object* v_x_4653_){
_start:
{
lean_inc(v_x_4653_);
return v_x_4653_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0___boxed(lean_object* v_x_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_Array_reduceOption___redArg___lam__0(v_x_4654_);
lean_dec(v_x_4654_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg(lean_object* v_as_4657_){
_start:
{
lean_object* v___f_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___f_4658_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4659_ = lean_unsigned_to_nat(0u);
v___x_4660_ = lean_array_get_size(v_as_4657_);
v___x_4661_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4662_ = l_Array_filterMapM___redArg(v___x_4661_, v___f_4658_, v_as_4657_, v___x_4659_, v___x_4660_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption(lean_object* v_00_u03b1_4663_, lean_object* v_as_4664_){
_start:
{
lean_object* v___f_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___f_4665_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4666_ = lean_unsigned_to_nat(0u);
v___x_4667_ = lean_array_get_size(v_as_4664_);
v___x_4668_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4669_ = l_Array_filterMapM___redArg(v___x_4668_, v___f_4665_, v_as_4664_, v___x_4666_, v___x_4667_);
return v___x_4669_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg___lam__0(lean_object* v_inst_4670_, lean_object* v_x1_4671_, lean_object* v_x2_4672_){
_start:
{
lean_object* v_fst_4673_; lean_object* v_snd_4674_; lean_object* v___x_4675_; uint8_t v___x_4676_; 
v_fst_4673_ = lean_ctor_get(v_x1_4671_, 0);
v_snd_4674_ = lean_ctor_get(v_x1_4671_, 1);
lean_inc(v_fst_4673_);
lean_inc(v_x2_4672_);
v___x_4675_ = lean_apply_2(v_inst_4670_, v_x2_4672_, v_fst_4673_);
v___x_4676_ = lean_unbox(v___x_4675_);
if (v___x_4676_ == 0)
{
lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4684_; 
lean_inc(v_snd_4674_);
lean_inc(v_fst_4673_);
v_isSharedCheck_4684_ = !lean_is_exclusive(v_x1_4671_);
if (v_isSharedCheck_4684_ == 0)
{
lean_object* v_unused_4685_; lean_object* v_unused_4686_; 
v_unused_4685_ = lean_ctor_get(v_x1_4671_, 1);
lean_dec(v_unused_4685_);
v_unused_4686_ = lean_ctor_get(v_x1_4671_, 0);
lean_dec(v_unused_4686_);
v___x_4678_ = v_x1_4671_;
v_isShared_4679_ = v_isSharedCheck_4684_;
goto v_resetjp_4677_;
}
else
{
lean_dec(v_x1_4671_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4684_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4680_; lean_object* v___x_4682_; 
v___x_4680_ = lean_array_push(v_snd_4674_, v_fst_4673_);
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 1, v___x_4680_);
lean_ctor_set(v___x_4678_, 0, v_x2_4672_);
v___x_4682_ = v___x_4678_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_x2_4672_);
lean_ctor_set(v_reuseFailAlloc_4683_, 1, v___x_4680_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
else
{
lean_dec(v_x2_4672_);
return v_x1_4671_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg(lean_object* v_inst_4687_, lean_object* v_as_4688_){
_start:
{
lean_object* v___y_4690_; lean_object* v___x_4694_; lean_object* v___x_4695_; uint8_t v___x_4696_; 
v___x_4694_ = lean_unsigned_to_nat(0u);
v___x_4695_ = lean_array_get_size(v_as_4688_);
v___x_4696_ = lean_nat_dec_lt(v___x_4694_, v___x_4695_);
if (v___x_4696_ == 0)
{
lean_object* v___x_4697_; 
lean_dec_ref(v_as_4688_);
lean_dec_ref(v_inst_4687_);
v___x_4697_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
return v___x_4697_;
}
else
{
lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; 
v___x_4698_ = lean_array_fget_borrowed(v_as_4688_, v___x_4694_);
v___x_4699_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4700_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
if (v___x_4696_ == 0)
{
lean_object* v___x_4701_; 
lean_inc(v___x_4698_);
lean_dec_ref(v_as_4688_);
lean_dec_ref(v_inst_4687_);
v___x_4701_ = lean_array_push(v___x_4699_, v___x_4698_);
return v___x_4701_;
}
else
{
lean_object* v___f_4702_; lean_object* v___x_4703_; uint8_t v___x_4704_; 
v___f_4702_ = lean_alloc_closure((void*)(l_Array_eraseReps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4702_, 0, v_inst_4687_);
lean_inc(v___x_4698_);
v___x_4703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4703_, 0, v___x_4698_);
lean_ctor_set(v___x_4703_, 1, v___x_4699_);
v___x_4704_ = lean_nat_dec_le(v___x_4695_, v___x_4695_);
if (v___x_4704_ == 0)
{
if (v___x_4696_ == 0)
{
lean_object* v___x_4705_; 
lean_inc(v___x_4698_);
lean_dec_ref(v___x_4703_);
lean_dec_ref(v___f_4702_);
lean_dec_ref(v_as_4688_);
v___x_4705_ = lean_array_push(v___x_4699_, v___x_4698_);
return v___x_4705_;
}
else
{
size_t v___x_4706_; size_t v___x_4707_; lean_object* v___x_4708_; 
v___x_4706_ = ((size_t)0ULL);
v___x_4707_ = lean_usize_of_nat(v___x_4695_);
v___x_4708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4700_, v___f_4702_, v_as_4688_, v___x_4706_, v___x_4707_, v___x_4703_);
v___y_4690_ = v___x_4708_;
goto v___jp_4689_;
}
}
else
{
size_t v___x_4709_; size_t v___x_4710_; lean_object* v___x_4711_; 
v___x_4709_ = ((size_t)0ULL);
v___x_4710_ = lean_usize_of_nat(v___x_4695_);
v___x_4711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4700_, v___f_4702_, v_as_4688_, v___x_4709_, v___x_4710_, v___x_4703_);
v___y_4690_ = v___x_4711_;
goto v___jp_4689_;
}
}
}
v___jp_4689_:
{
lean_object* v_fst_4691_; lean_object* v_snd_4692_; lean_object* v___x_4693_; 
v_fst_4691_ = lean_ctor_get(v___y_4690_, 0);
lean_inc(v_fst_4691_);
v_snd_4692_ = lean_ctor_get(v___y_4690_, 1);
lean_inc(v_snd_4692_);
lean_dec_ref(v___y_4690_);
v___x_4693_ = lean_array_push(v_snd_4692_, v_fst_4691_);
return v___x_4693_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps(lean_object* v_00_u03b1_4712_, lean_object* v_inst_4713_, lean_object* v_as_4714_){
_start:
{
lean_object* v___x_4715_; 
v___x_4715_ = l_Array_eraseReps___redArg(v_inst_4713_, v_as_4714_);
return v___x_4715_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(lean_object* v_inst_4716_, lean_object* v_as_4717_, lean_object* v_a_4718_, lean_object* v_x_4719_){
_start:
{
lean_object* v_zero_4720_; uint8_t v_isZero_4721_; 
v_zero_4720_ = lean_unsigned_to_nat(0u);
v_isZero_4721_ = lean_nat_dec_eq(v_x_4719_, v_zero_4720_);
if (v_isZero_4721_ == 1)
{
lean_dec(v_x_4719_);
lean_dec(v_a_4718_);
lean_dec_ref(v_inst_4716_);
return v_isZero_4721_;
}
else
{
lean_object* v_one_4722_; lean_object* v_n_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; uint8_t v___x_4726_; 
v_one_4722_ = lean_unsigned_to_nat(1u);
v_n_4723_ = lean_nat_sub(v_x_4719_, v_one_4722_);
lean_dec(v_x_4719_);
v___x_4724_ = lean_array_fget_borrowed(v_as_4717_, v_n_4723_);
lean_inc_ref(v_inst_4716_);
lean_inc(v___x_4724_);
lean_inc(v_a_4718_);
v___x_4725_ = lean_apply_2(v_inst_4716_, v_a_4718_, v___x_4724_);
v___x_4726_ = lean_unbox(v___x_4725_);
if (v___x_4726_ == 0)
{
v_x_4719_ = v_n_4723_;
goto _start;
}
else
{
lean_dec(v_n_4723_);
lean_dec(v_a_4718_);
lean_dec_ref(v_inst_4716_);
return v_isZero_4721_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg___boxed(lean_object* v_inst_4728_, lean_object* v_as_4729_, lean_object* v_a_4730_, lean_object* v_x_4731_){
_start:
{
uint8_t v_res_4732_; lean_object* v_r_4733_; 
v_res_4732_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4728_, v_as_4729_, v_a_4730_, v_x_4731_);
lean_dec_ref(v_as_4729_);
v_r_4733_ = lean_box(v_res_4732_);
return v_r_4733_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(lean_object* v_00_u03b1_4734_, lean_object* v_inst_4735_, lean_object* v_as_4736_, lean_object* v_a_4737_, lean_object* v_x_4738_, lean_object* v_x_4739_){
_start:
{
uint8_t v___x_4740_; 
v___x_4740_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4735_, v_as_4736_, v_a_4737_, v_x_4738_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___boxed(lean_object* v_00_u03b1_4741_, lean_object* v_inst_4742_, lean_object* v_as_4743_, lean_object* v_a_4744_, lean_object* v_x_4745_, lean_object* v_x_4746_){
_start:
{
uint8_t v_res_4747_; lean_object* v_r_4748_; 
v_res_4747_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(v_00_u03b1_4741_, v_inst_4742_, v_as_4743_, v_a_4744_, v_x_4745_, v_x_4746_);
lean_dec_ref(v_as_4743_);
v_r_4748_ = lean_box(v_res_4747_);
return v_r_4748_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(lean_object* v_inst_4749_, lean_object* v_as_4750_, lean_object* v_i_4751_){
_start:
{
lean_object* v___x_4752_; uint8_t v___x_4753_; 
v___x_4752_ = lean_array_get_size(v_as_4750_);
v___x_4753_ = lean_nat_dec_lt(v_i_4751_, v___x_4752_);
if (v___x_4753_ == 0)
{
uint8_t v___x_4754_; 
lean_dec(v_i_4751_);
lean_dec_ref(v_inst_4749_);
v___x_4754_ = 1;
return v___x_4754_;
}
else
{
lean_object* v___x_4755_; uint8_t v___x_4756_; 
v___x_4755_ = lean_array_fget_borrowed(v_as_4750_, v_i_4751_);
lean_inc(v_i_4751_);
lean_inc(v___x_4755_);
lean_inc_ref(v_inst_4749_);
v___x_4756_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4749_, v_as_4750_, v___x_4755_, v_i_4751_);
if (v___x_4756_ == 0)
{
lean_dec(v_i_4751_);
lean_dec_ref(v_inst_4749_);
return v___x_4756_;
}
else
{
lean_object* v___x_4757_; lean_object* v___x_4758_; 
v___x_4757_ = lean_unsigned_to_nat(1u);
v___x_4758_ = lean_nat_add(v_i_4751_, v___x_4757_);
lean_dec(v_i_4751_);
v_i_4751_ = v___x_4758_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg___boxed(lean_object* v_inst_4760_, lean_object* v_as_4761_, lean_object* v_i_4762_){
_start:
{
uint8_t v_res_4763_; lean_object* v_r_4764_; 
v_res_4763_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4760_, v_as_4761_, v_i_4762_);
lean_dec_ref(v_as_4761_);
v_r_4764_ = lean_box(v_res_4763_);
return v_r_4764_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux(lean_object* v_00_u03b1_4765_, lean_object* v_inst_4766_, lean_object* v_as_4767_, lean_object* v_i_4768_){
_start:
{
uint8_t v___x_4769_; 
v___x_4769_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4766_, v_as_4767_, v_i_4768_);
return v___x_4769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___boxed(lean_object* v_00_u03b1_4770_, lean_object* v_inst_4771_, lean_object* v_as_4772_, lean_object* v_i_4773_){
_start:
{
uint8_t v_res_4774_; lean_object* v_r_4775_; 
v_res_4774_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux(v_00_u03b1_4770_, v_inst_4771_, v_as_4772_, v_i_4773_);
lean_dec_ref(v_as_4772_);
v_r_4775_ = lean_box(v_res_4774_);
return v_r_4775_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___redArg(lean_object* v_inst_4776_, lean_object* v_as_4777_){
_start:
{
lean_object* v___x_4778_; uint8_t v___x_4779_; 
v___x_4778_ = lean_unsigned_to_nat(0u);
v___x_4779_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4776_, v_as_4777_, v___x_4778_);
return v___x_4779_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___redArg___boxed(lean_object* v_inst_4780_, lean_object* v_as_4781_){
_start:
{
uint8_t v_res_4782_; lean_object* v_r_4783_; 
v_res_4782_ = l_Array_allDiff___redArg(v_inst_4780_, v_as_4781_);
lean_dec_ref(v_as_4781_);
v_r_4783_ = lean_box(v_res_4782_);
return v_r_4783_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff(lean_object* v_00_u03b1_4784_, lean_object* v_inst_4785_, lean_object* v_as_4786_){
_start:
{
uint8_t v___x_4787_; 
v___x_4787_ = l_Array_allDiff___redArg(v_inst_4785_, v_as_4786_);
return v___x_4787_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___boxed(lean_object* v_00_u03b1_4788_, lean_object* v_inst_4789_, lean_object* v_as_4790_){
_start:
{
uint8_t v_res_4791_; lean_object* v_r_4792_; 
v_res_4791_ = l_Array_allDiff(v_00_u03b1_4788_, v_inst_4789_, v_as_4790_);
lean_dec_ref(v_as_4790_);
v_r_4792_ = lean_box(v_res_4791_);
return v_r_4792_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0(uint8_t v___x_4793_, lean_object* v_x1_4794_, lean_object* v_x2_4795_){
_start:
{
lean_object* v_fst_4796_; uint8_t v___x_4797_; 
v_fst_4796_ = lean_ctor_get(v_x1_4794_, 0);
v___x_4797_ = lean_unbox(v_fst_4796_);
if (v___x_4797_ == 0)
{
lean_object* v_snd_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4806_; 
lean_dec(v_x2_4795_);
v_snd_4798_ = lean_ctor_get(v_x1_4794_, 1);
v_isSharedCheck_4806_ = !lean_is_exclusive(v_x1_4794_);
if (v_isSharedCheck_4806_ == 0)
{
lean_object* v_unused_4807_; 
v_unused_4807_ = lean_ctor_get(v_x1_4794_, 0);
lean_dec(v_unused_4807_);
v___x_4800_ = v_x1_4794_;
v_isShared_4801_ = v_isSharedCheck_4806_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_snd_4798_);
lean_dec(v_x1_4794_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4806_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4802_; lean_object* v___x_4804_; 
v___x_4802_ = lean_box(v___x_4793_);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 0, v___x_4802_);
v___x_4804_ = v___x_4800_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v___x_4802_);
lean_ctor_set(v_reuseFailAlloc_4805_, 1, v_snd_4798_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
else
{
lean_object* v_snd_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4818_; 
v_snd_4808_ = lean_ctor_get(v_x1_4794_, 1);
v_isSharedCheck_4818_ = !lean_is_exclusive(v_x1_4794_);
if (v_isSharedCheck_4818_ == 0)
{
lean_object* v_unused_4819_; 
v_unused_4819_ = lean_ctor_get(v_x1_4794_, 0);
lean_dec(v_unused_4819_);
v___x_4810_ = v_x1_4794_;
v_isShared_4811_ = v_isSharedCheck_4818_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_snd_4808_);
lean_dec(v_x1_4794_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4818_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
uint8_t v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4816_; 
v___x_4812_ = 0;
v___x_4813_ = lean_array_push(v_snd_4808_, v_x2_4795_);
v___x_4814_ = lean_box(v___x_4812_);
if (v_isShared_4811_ == 0)
{
lean_ctor_set(v___x_4810_, 1, v___x_4813_);
lean_ctor_set(v___x_4810_, 0, v___x_4814_);
v___x_4816_ = v___x_4810_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4814_);
lean_ctor_set(v_reuseFailAlloc_4817_, 1, v___x_4813_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0___boxed(lean_object* v___x_4820_, lean_object* v_x1_4821_, lean_object* v_x2_4822_){
_start:
{
uint8_t v___x_172__boxed_4823_; lean_object* v_res_4824_; 
v___x_172__boxed_4823_ = lean_unbox(v___x_4820_);
v_res_4824_ = l_Array_getEvenElems___redArg___lam__0(v___x_172__boxed_4823_, v_x1_4821_, v_x2_4822_);
return v_res_4824_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg(lean_object* v_as_4825_){
_start:
{
lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; uint8_t v___x_4830_; 
v___x_4826_ = lean_unsigned_to_nat(0u);
v___x_4827_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_4828_ = lean_array_get_size(v_as_4825_);
v___x_4829_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4830_ = lean_nat_dec_lt(v___x_4826_, v___x_4828_);
if (v___x_4830_ == 0)
{
lean_dec_ref(v_as_4825_);
return v___x_4827_;
}
else
{
lean_object* v___x_4831_; lean_object* v___f_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; uint8_t v___x_4835_; 
v___x_4831_ = lean_box(v___x_4830_);
v___f_4832_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4832_, 0, v___x_4831_);
v___x_4833_ = lean_box(v___x_4830_);
v___x_4834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4833_);
lean_ctor_set(v___x_4834_, 1, v___x_4827_);
v___x_4835_ = lean_nat_dec_le(v___x_4828_, v___x_4828_);
if (v___x_4835_ == 0)
{
if (v___x_4830_ == 0)
{
lean_dec_ref(v___x_4834_);
lean_dec_ref(v___f_4832_);
lean_dec_ref(v_as_4825_);
return v___x_4827_;
}
else
{
size_t v___x_4836_; size_t v___x_4837_; lean_object* v___x_4838_; lean_object* v_snd_4839_; 
v___x_4836_ = ((size_t)0ULL);
v___x_4837_ = lean_usize_of_nat(v___x_4828_);
v___x_4838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4829_, v___f_4832_, v_as_4825_, v___x_4836_, v___x_4837_, v___x_4834_);
v_snd_4839_ = lean_ctor_get(v___x_4838_, 1);
lean_inc(v_snd_4839_);
lean_dec(v___x_4838_);
return v_snd_4839_;
}
}
else
{
size_t v___x_4840_; size_t v___x_4841_; lean_object* v___x_4842_; lean_object* v_snd_4843_; 
v___x_4840_ = ((size_t)0ULL);
v___x_4841_ = lean_usize_of_nat(v___x_4828_);
v___x_4842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4829_, v___f_4832_, v_as_4825_, v___x_4840_, v___x_4841_, v___x_4834_);
v_snd_4843_ = lean_ctor_get(v___x_4842_, 1);
lean_inc(v_snd_4843_);
lean_dec(v___x_4842_);
return v_snd_4843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems(lean_object* v_00_u03b1_4844_, lean_object* v_as_4845_){
_start:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; uint8_t v___x_4850_; 
v___x_4846_ = lean_unsigned_to_nat(0u);
v___x_4847_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_4848_ = lean_array_get_size(v_as_4845_);
v___x_4849_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4850_ = lean_nat_dec_lt(v___x_4846_, v___x_4848_);
if (v___x_4850_ == 0)
{
lean_dec_ref(v_as_4845_);
return v___x_4847_;
}
else
{
lean_object* v___x_4851_; lean_object* v___f_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; uint8_t v___x_4855_; 
v___x_4851_ = lean_box(v___x_4850_);
v___f_4852_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4852_, 0, v___x_4851_);
v___x_4853_ = lean_box(v___x_4850_);
v___x_4854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4854_, 0, v___x_4853_);
lean_ctor_set(v___x_4854_, 1, v___x_4847_);
v___x_4855_ = lean_nat_dec_le(v___x_4848_, v___x_4848_);
if (v___x_4855_ == 0)
{
if (v___x_4850_ == 0)
{
lean_dec_ref(v___x_4854_);
lean_dec_ref(v___f_4852_);
lean_dec_ref(v_as_4845_);
return v___x_4847_;
}
else
{
size_t v___x_4856_; size_t v___x_4857_; lean_object* v___x_4858_; lean_object* v_snd_4859_; 
v___x_4856_ = ((size_t)0ULL);
v___x_4857_ = lean_usize_of_nat(v___x_4848_);
v___x_4858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4849_, v___f_4852_, v_as_4845_, v___x_4856_, v___x_4857_, v___x_4854_);
v_snd_4859_ = lean_ctor_get(v___x_4858_, 1);
lean_inc(v_snd_4859_);
lean_dec(v___x_4858_);
return v_snd_4859_;
}
}
else
{
size_t v___x_4860_; size_t v___x_4861_; lean_object* v___x_4862_; lean_object* v_snd_4863_; 
v___x_4860_ = ((size_t)0ULL);
v___x_4861_ = lean_usize_of_nat(v___x_4848_);
v___x_4862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4849_, v___f_4852_, v_as_4845_, v___x_4860_, v___x_4861_, v___x_4854_);
v_snd_4863_ = lean_ctor_get(v___x_4862_, 1);
lean_inc(v_snd_4863_);
lean_dec(v___x_4862_);
return v_snd_4863_;
}
}
}
}
static lean_object* _init_l_Array_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4869_ = ((lean_object*)(l_term_x23_x5b___x2c_x5d___closed__4));
v___x_4870_ = lean_string_length(v___x_4869_);
return v___x_4870_;
}
}
static lean_object* _init_l_Array_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4871_ = lean_obj_once(&l_Array_repr___redArg___closed__2, &l_Array_repr___redArg___closed__2_once, _init_l_Array_repr___redArg___closed__2);
v___x_4872_ = lean_nat_to_int(v___x_4871_);
return v___x_4872_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___redArg(lean_object* v_inst_4880_, lean_object* v_xs_4881_){
_start:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; uint8_t v___x_4884_; 
v___x_4882_ = lean_array_get_size(v_xs_4881_);
v___x_4883_ = lean_unsigned_to_nat(0u);
v___x_4884_ = lean_nat_dec_eq(v___x_4882_, v___x_4883_);
if (v___x_4884_ == 0)
{
lean_object* v_x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; 
v_x_4885_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_4885_, 0, lean_box(0));
lean_closure_set(v_x_4885_, 1, v_inst_4880_);
v___x_4886_ = lean_array_to_list(v_xs_4881_);
v___x_4887_ = ((lean_object*)(l_Array_repr___redArg___closed__1));
v___x_4888_ = l_Std_Format_joinSep___redArg(v_x_4885_, v___x_4886_, v___x_4887_);
v___x_4889_ = lean_obj_once(&l_Array_repr___redArg___closed__3, &l_Array_repr___redArg___closed__3_once, _init_l_Array_repr___redArg___closed__3);
v___x_4890_ = ((lean_object*)(l_Array_repr___redArg___closed__4));
v___x_4891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4891_, 0, v___x_4890_);
lean_ctor_set(v___x_4891_, 1, v___x_4888_);
v___x_4892_ = ((lean_object*)(l_Array_repr___redArg___closed__5));
v___x_4893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4891_);
lean_ctor_set(v___x_4893_, 1, v___x_4892_);
v___x_4894_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4894_, 0, v___x_4889_);
lean_ctor_set(v___x_4894_, 1, v___x_4893_);
v___x_4895_ = l_Std_Format_fill(v___x_4894_);
return v___x_4895_;
}
else
{
lean_object* v___x_4896_; 
lean_dec_ref(v_xs_4881_);
lean_dec_ref(v_inst_4880_);
v___x_4896_ = ((lean_object*)(l_Array_repr___redArg___closed__7));
return v___x_4896_;
}
}
}
LEAN_EXPORT lean_object* l_Array_repr(lean_object* v_00_u03b1_4897_, lean_object* v_inst_4898_, lean_object* v_xs_4899_){
_start:
{
lean_object* v___x_4900_; 
v___x_4900_ = l_Array_repr___redArg(v_inst_4898_, v_xs_4899_);
return v___x_4900_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0(lean_object* v_inst_4901_, lean_object* v_xs_4902_, lean_object* v_x_4903_){
_start:
{
lean_object* v___x_4904_; 
v___x_4904_ = l_Array_repr___redArg(v_inst_4901_, v_xs_4902_);
return v___x_4904_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object* v_inst_4905_, lean_object* v_xs_4906_, lean_object* v_x_4907_){
_start:
{
lean_object* v_res_4908_; 
v_res_4908_ = l_Array_instRepr___redArg___lam__0(v_inst_4905_, v_xs_4906_, v_x_4907_);
lean_dec(v_x_4907_);
return v_res_4908_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg(lean_object* v_inst_4909_){
_start:
{
lean_object* v___f_4910_; 
v___f_4910_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4910_, 0, v_inst_4909_);
return v___f_4910_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr(lean_object* v_00_u03b1_4911_, lean_object* v_inst_4912_){
_start:
{
lean_object* v___f_4913_; 
v___f_4913_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4913_, 0, v_inst_4912_);
return v___f_4913_;
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
