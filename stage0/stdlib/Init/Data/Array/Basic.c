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
if (v_____do__lift_2053_ == 0)
{
uint8_t v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = 1;
v___x_2055_ = lean_box(v___x_2054_);
v___x_2056_ = lean_apply_2(v_toPure_2052_, lean_box(0), v___x_2055_);
return v___x_2056_;
}
else
{
uint8_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = 0;
v___x_2058_ = lean_box(v___x_2057_);
v___x_2059_ = lean_apply_2(v_toPure_2052_, lean_box(0), v___x_2058_);
return v___x_2059_;
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0___boxed(lean_object* v_toPure_2060_, lean_object* v_____do__lift_2061_){
_start:
{
uint8_t v_____do__lift_123__boxed_2062_; lean_object* v_res_2063_; 
v_____do__lift_123__boxed_2062_ = lean_unbox(v_____do__lift_2061_);
v_res_2063_ = l_Array_allM___redArg___lam__0(v_toPure_2060_, v_____do__lift_123__boxed_2062_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1(lean_object* v_toPure_2064_, uint8_t v___x_2065_, uint8_t v_____do__lift_2066_){
_start:
{
if (v_____do__lift_2066_ == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_box(v___x_2065_);
v___x_2068_ = lean_apply_2(v_toPure_2064_, lean_box(0), v___x_2067_);
return v___x_2068_;
}
else
{
uint8_t v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = 0;
v___x_2070_ = lean_box(v___x_2069_);
v___x_2071_ = lean_apply_2(v_toPure_2064_, lean_box(0), v___x_2070_);
return v___x_2071_;
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1___boxed(lean_object* v_toPure_2072_, lean_object* v___x_2073_, lean_object* v_____do__lift_2074_){
_start:
{
uint8_t v___x_138__boxed_2075_; uint8_t v_____do__lift_139__boxed_2076_; lean_object* v_res_2077_; 
v___x_138__boxed_2075_ = lean_unbox(v___x_2073_);
v_____do__lift_139__boxed_2076_ = lean_unbox(v_____do__lift_2074_);
v_res_2077_ = l_Array_allM___redArg___lam__1(v_toPure_2072_, v___x_138__boxed_2075_, v_____do__lift_139__boxed_2076_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__2(lean_object* v_p_2078_, lean_object* v_toBind_2079_, lean_object* v___f_2080_, lean_object* v_v_2081_){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = lean_apply_1(v_p_2078_, v_v_2081_);
v___x_2083_ = lean_apply_4(v_toBind_2079_, lean_box(0), lean_box(0), v___x_2082_, v___f_2080_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg(lean_object* v_inst_2084_, lean_object* v_p_2085_, lean_object* v_as_2086_, lean_object* v_start_2087_, lean_object* v_stop_2088_){
_start:
{
lean_object* v_toApplicative_2089_; lean_object* v_toBind_2090_; lean_object* v_toPure_2091_; lean_object* v___f_2092_; uint8_t v___x_2093_; 
v_toApplicative_2089_ = lean_ctor_get(v_inst_2084_, 0);
v_toBind_2090_ = lean_ctor_get(v_inst_2084_, 1);
lean_inc(v_toBind_2090_);
v_toPure_2091_ = lean_ctor_get(v_toApplicative_2089_, 1);
lean_inc(v_toPure_2091_);
v___f_2092_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2092_, 0, v_toPure_2091_);
v___x_2093_ = lean_nat_dec_lt(v_start_2087_, v_stop_2088_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_inc(v_toPure_2091_);
lean_dec(v_stop_2088_);
lean_dec_ref(v_as_2086_);
lean_dec(v_p_2085_);
lean_dec_ref(v_inst_2084_);
v___x_2094_ = lean_box(v___x_2093_);
v___x_2095_ = lean_apply_2(v_toPure_2091_, lean_box(0), v___x_2094_);
v___x_2096_ = lean_apply_4(v_toBind_2090_, lean_box(0), lean_box(0), v___x_2095_, v___f_2092_);
return v___x_2096_;
}
else
{
lean_object* v___x_2097_; lean_object* v___f_2098_; lean_object* v___f_2099_; lean_object* v___y_2101_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2097_ = lean_box(v___x_2093_);
lean_inc(v_toPure_2091_);
v___f_2098_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2098_, 0, v_toPure_2091_);
lean_closure_set(v___f_2098_, 1, v___x_2097_);
lean_inc(v_toBind_2090_);
v___f_2099_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2099_, 0, v_p_2085_);
lean_closure_set(v___f_2099_, 1, v_toBind_2090_);
lean_closure_set(v___f_2099_, 2, v___f_2098_);
v___x_2110_ = lean_array_get_size(v_as_2086_);
v___x_2111_ = lean_nat_dec_le(v_stop_2088_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_dec(v_stop_2088_);
v___y_2101_ = v___x_2110_;
goto v___jp_2100_;
}
else
{
v___y_2101_ = v_stop_2088_;
goto v___jp_2100_;
}
v___jp_2100_:
{
uint8_t v___x_2102_; 
v___x_2102_ = lean_nat_dec_lt(v_start_2087_, v___y_2101_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
lean_inc(v_toPure_2091_);
lean_dec(v___y_2101_);
lean_dec_ref(v___f_2099_);
lean_dec_ref(v_as_2086_);
lean_dec_ref(v_inst_2084_);
v___x_2103_ = lean_box(v___x_2102_);
v___x_2104_ = lean_apply_2(v_toPure_2091_, lean_box(0), v___x_2103_);
v___x_2105_ = lean_apply_4(v_toBind_2090_, lean_box(0), lean_box(0), v___x_2104_, v___f_2092_);
return v___x_2105_;
}
else
{
size_t v___x_2106_; size_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2106_ = lean_usize_of_nat(v_start_2087_);
v___x_2107_ = lean_usize_of_nat(v___y_2101_);
lean_dec(v___y_2101_);
v___x_2108_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2084_, v___f_2099_, v_as_2086_, v___x_2106_, v___x_2107_);
v___x_2109_ = lean_apply_4(v_toBind_2090_, lean_box(0), lean_box(0), v___x_2108_, v___f_2092_);
return v___x_2109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___boxed(lean_object* v_inst_2112_, lean_object* v_p_2113_, lean_object* v_as_2114_, lean_object* v_start_2115_, lean_object* v_stop_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Array_allM___redArg(v_inst_2112_, v_p_2113_, v_as_2114_, v_start_2115_, v_stop_2116_);
lean_dec(v_start_2115_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Array_allM(lean_object* v_00_u03b1_2118_, lean_object* v_m_2119_, lean_object* v_inst_2120_, lean_object* v_p_2121_, lean_object* v_as_2122_, lean_object* v_start_2123_, lean_object* v_stop_2124_){
_start:
{
lean_object* v_toApplicative_2125_; lean_object* v_toBind_2126_; lean_object* v_toPure_2127_; lean_object* v___f_2128_; uint8_t v___x_2129_; 
v_toApplicative_2125_ = lean_ctor_get(v_inst_2120_, 0);
v_toBind_2126_ = lean_ctor_get(v_inst_2120_, 1);
lean_inc(v_toBind_2126_);
v_toPure_2127_ = lean_ctor_get(v_toApplicative_2125_, 1);
lean_inc(v_toPure_2127_);
v___f_2128_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2128_, 0, v_toPure_2127_);
v___x_2129_ = lean_nat_dec_lt(v_start_2123_, v_stop_2124_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_inc(v_toPure_2127_);
lean_dec(v_stop_2124_);
lean_dec_ref(v_as_2122_);
lean_dec(v_p_2121_);
lean_dec_ref(v_inst_2120_);
v___x_2130_ = lean_box(v___x_2129_);
v___x_2131_ = lean_apply_2(v_toPure_2127_, lean_box(0), v___x_2130_);
v___x_2132_ = lean_apply_4(v_toBind_2126_, lean_box(0), lean_box(0), v___x_2131_, v___f_2128_);
return v___x_2132_;
}
else
{
lean_object* v___x_2133_; lean_object* v___f_2134_; lean_object* v___f_2135_; lean_object* v___y_2137_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2133_ = lean_box(v___x_2129_);
lean_inc(v_toPure_2127_);
v___f_2134_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2134_, 0, v_toPure_2127_);
lean_closure_set(v___f_2134_, 1, v___x_2133_);
lean_inc(v_toBind_2126_);
v___f_2135_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2135_, 0, v_p_2121_);
lean_closure_set(v___f_2135_, 1, v_toBind_2126_);
lean_closure_set(v___f_2135_, 2, v___f_2134_);
v___x_2146_ = lean_array_get_size(v_as_2122_);
v___x_2147_ = lean_nat_dec_le(v_stop_2124_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_dec(v_stop_2124_);
v___y_2137_ = v___x_2146_;
goto v___jp_2136_;
}
else
{
v___y_2137_ = v_stop_2124_;
goto v___jp_2136_;
}
v___jp_2136_:
{
uint8_t v___x_2138_; 
v___x_2138_ = lean_nat_dec_lt(v_start_2123_, v___y_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
lean_inc(v_toPure_2127_);
lean_dec(v___y_2137_);
lean_dec_ref(v___f_2135_);
lean_dec_ref(v_as_2122_);
lean_dec_ref(v_inst_2120_);
v___x_2139_ = lean_box(v___x_2138_);
v___x_2140_ = lean_apply_2(v_toPure_2127_, lean_box(0), v___x_2139_);
v___x_2141_ = lean_apply_4(v_toBind_2126_, lean_box(0), lean_box(0), v___x_2140_, v___f_2128_);
return v___x_2141_;
}
else
{
size_t v___x_2142_; size_t v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2142_ = lean_usize_of_nat(v_start_2123_);
v___x_2143_ = lean_usize_of_nat(v___y_2137_);
lean_dec(v___y_2137_);
v___x_2144_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2120_, v___f_2135_, v_as_2122_, v___x_2142_, v___x_2143_);
v___x_2145_ = lean_apply_4(v_toBind_2126_, lean_box(0), lean_box(0), v___x_2144_, v___f_2128_);
return v___x_2145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___boxed(lean_object* v_00_u03b1_2148_, lean_object* v_m_2149_, lean_object* v_inst_2150_, lean_object* v_p_2151_, lean_object* v_as_2152_, lean_object* v_start_2153_, lean_object* v_stop_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Array_allM(v_00_u03b1_2148_, v_m_2149_, v_inst_2150_, v_p_2151_, v_as_2152_, v_start_2153_, v_stop_2154_);
lean_dec(v_start_2153_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed(lean_object* v_inst_2156_, lean_object* v_f_2157_, lean_object* v_as_2158_, lean_object* v_n_2159_, lean_object* v_toPure_2160_, lean_object* v_r_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(v_inst_2156_, v_f_2157_, v_as_2158_, v_n_2159_, v_toPure_2160_, v_r_2161_);
lean_dec(v_n_2159_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(lean_object* v_inst_2163_, lean_object* v_f_2164_, lean_object* v_as_2165_, lean_object* v_i_2166_){
_start:
{
lean_object* v_toApplicative_2167_; lean_object* v_toBind_2168_; lean_object* v_toPure_2169_; lean_object* v_zero_2170_; uint8_t v_isZero_2171_; 
v_toApplicative_2167_ = lean_ctor_get(v_inst_2163_, 0);
v_toBind_2168_ = lean_ctor_get(v_inst_2163_, 1);
lean_inc(v_toBind_2168_);
v_toPure_2169_ = lean_ctor_get(v_toApplicative_2167_, 1);
lean_inc(v_toPure_2169_);
v_zero_2170_ = lean_unsigned_to_nat(0u);
v_isZero_2171_ = lean_nat_dec_eq(v_i_2166_, v_zero_2170_);
if (v_isZero_2171_ == 1)
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec(v_toBind_2168_);
lean_dec_ref(v_as_2165_);
lean_dec(v_f_2164_);
lean_dec_ref(v_inst_2163_);
v___x_2172_ = lean_box(0);
v___x_2173_ = lean_apply_2(v_toPure_2169_, lean_box(0), v___x_2172_);
return v___x_2173_;
}
else
{
lean_object* v_one_2174_; lean_object* v_n_2175_; lean_object* v___f_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v_one_2174_ = lean_unsigned_to_nat(1u);
v_n_2175_ = lean_nat_sub(v_i_2166_, v_one_2174_);
lean_inc(v_n_2175_);
lean_inc_ref(v_as_2165_);
lean_inc(v_f_2164_);
v___f_2176_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2176_, 0, v_inst_2163_);
lean_closure_set(v___f_2176_, 1, v_f_2164_);
lean_closure_set(v___f_2176_, 2, v_as_2165_);
lean_closure_set(v___f_2176_, 3, v_n_2175_);
lean_closure_set(v___f_2176_, 4, v_toPure_2169_);
v___x_2177_ = lean_array_fget(v_as_2165_, v_n_2175_);
lean_dec(v_n_2175_);
lean_dec_ref(v_as_2165_);
v___x_2178_ = lean_apply_1(v_f_2164_, v___x_2177_);
v___x_2179_ = lean_apply_4(v_toBind_2168_, lean_box(0), lean_box(0), v___x_2178_, v___f_2176_);
return v___x_2179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(lean_object* v_inst_2180_, lean_object* v_f_2181_, lean_object* v_as_2182_, lean_object* v_n_2183_, lean_object* v_toPure_2184_, lean_object* v_r_2185_){
_start:
{
if (lean_obj_tag(v_r_2185_) == 0)
{
lean_object* v___x_2186_; 
lean_dec(v_toPure_2184_);
v___x_2186_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2180_, v_f_2181_, v_as_2182_, v_n_2183_);
return v___x_2186_;
}
else
{
lean_object* v___x_2187_; 
lean_dec_ref(v_as_2182_);
lean_dec(v_f_2181_);
lean_dec_ref(v_inst_2180_);
v___x_2187_ = lean_apply_2(v_toPure_2184_, lean_box(0), v_r_2185_);
return v___x_2187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___boxed(lean_object* v_inst_2188_, lean_object* v_f_2189_, lean_object* v_as_2190_, lean_object* v_i_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2188_, v_f_2189_, v_as_2190_, v_i_2191_);
lean_dec(v_i_2191_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_object* v_00_u03b1_2193_, lean_object* v_00_u03b2_2194_, lean_object* v_m_2195_, lean_object* v_inst_2196_, lean_object* v_f_2197_, lean_object* v_as_2198_, lean_object* v_i_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2196_, v_f_2197_, v_as_2198_, v_i_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___boxed(lean_object* v_00_u03b1_2202_, lean_object* v_00_u03b2_2203_, lean_object* v_m_2204_, lean_object* v_inst_2205_, lean_object* v_f_2206_, lean_object* v_as_2207_, lean_object* v_i_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(v_00_u03b1_2202_, v_00_u03b2_2203_, v_m_2204_, v_inst_2205_, v_f_2206_, v_as_2207_, v_i_2208_, v_a_2209_);
lean_dec(v_i_2208_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f___redArg(lean_object* v_inst_2211_, lean_object* v_f_2212_, lean_object* v_as_2213_){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = lean_array_get_size(v_as_2213_);
v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2211_, v_f_2212_, v_as_2213_, v___x_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f(lean_object* v_00_u03b1_2216_, lean_object* v_00_u03b2_2217_, lean_object* v_m_2218_, lean_object* v_inst_2219_, lean_object* v_f_2220_, lean_object* v_as_2221_){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = lean_array_get_size(v_as_2221_);
v___x_2223_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2219_, v_f_2220_, v_as_2221_, v___x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2224_, lean_object* v_a_2225_, uint8_t v_____do__lift_2226_){
_start:
{
if (v_____do__lift_2226_ == 0)
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec(v_a_2225_);
v___x_2227_ = lean_box(0);
v___x_2228_ = lean_apply_2(v_toPure_2224_, lean_box(0), v___x_2227_);
return v___x_2228_;
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_a_2225_);
v___x_2230_ = lean_apply_2(v_toPure_2224_, lean_box(0), v___x_2229_);
return v___x_2230_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2231_, lean_object* v_a_2232_, lean_object* v_____do__lift_2233_){
_start:
{
uint8_t v_____do__lift_74__boxed_2234_; lean_object* v_res_2235_; 
v_____do__lift_74__boxed_2234_ = lean_unbox(v_____do__lift_2233_);
v_res_2235_ = l_Array_findRevM_x3f___redArg___lam__0(v_toPure_2231_, v_a_2232_, v_____do__lift_74__boxed_2234_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2236_, lean_object* v_p_2237_, lean_object* v_toBind_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v___f_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_inc(v_a_2239_);
v___f_2240_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2240_, 0, v_toPure_2236_);
lean_closure_set(v___f_2240_, 1, v_a_2239_);
v___x_2241_ = lean_apply_1(v_p_2237_, v_a_2239_);
v___x_2242_ = lean_apply_4(v_toBind_2238_, lean_box(0), lean_box(0), v___x_2241_, v___f_2240_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg(lean_object* v_inst_2243_, lean_object* v_p_2244_, lean_object* v_as_2245_){
_start:
{
lean_object* v_toApplicative_2246_; lean_object* v_toBind_2247_; lean_object* v_toPure_2248_; lean_object* v___f_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v_toApplicative_2246_ = lean_ctor_get(v_inst_2243_, 0);
v_toBind_2247_ = lean_ctor_get(v_inst_2243_, 1);
v_toPure_2248_ = lean_ctor_get(v_toApplicative_2246_, 1);
lean_inc(v_toBind_2247_);
lean_inc(v_toPure_2248_);
v___f_2249_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2249_, 0, v_toPure_2248_);
lean_closure_set(v___f_2249_, 1, v_p_2244_);
lean_closure_set(v___f_2249_, 2, v_toBind_2247_);
v___x_2250_ = lean_array_get_size(v_as_2245_);
v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2243_, v___f_2249_, v_as_2245_, v___x_2250_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f(lean_object* v_00_u03b1_2252_, lean_object* v_m_2253_, lean_object* v_inst_2254_, lean_object* v_p_2255_, lean_object* v_as_2256_){
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
LEAN_EXPORT lean_object* l_Array_forM___redArg___lam__0(lean_object* v_f_2263_, lean_object* v_x_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_apply_1(v_f_2263_, v___y_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg(lean_object* v_inst_2267_, lean_object* v_f_2268_, lean_object* v_as_2269_, lean_object* v_start_2270_, lean_object* v_stop_2271_){
_start:
{
lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2272_ = lean_box(0);
v___x_2273_ = lean_nat_dec_lt(v_start_2270_, v_stop_2271_);
if (v___x_2273_ == 0)
{
lean_object* v_toApplicative_2274_; lean_object* v_toPure_2275_; lean_object* v___x_2276_; 
lean_dec_ref(v_as_2269_);
lean_dec(v_f_2268_);
v_toApplicative_2274_ = lean_ctor_get(v_inst_2267_, 0);
lean_inc_ref(v_toApplicative_2274_);
lean_dec_ref(v_inst_2267_);
v_toPure_2275_ = lean_ctor_get(v_toApplicative_2274_, 1);
lean_inc(v_toPure_2275_);
lean_dec_ref(v_toApplicative_2274_);
v___x_2276_ = lean_apply_2(v_toPure_2275_, lean_box(0), v___x_2272_);
return v___x_2276_;
}
else
{
lean_object* v___f_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___f_2277_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2277_, 0, v_f_2268_);
v___x_2278_ = lean_array_get_size(v_as_2269_);
v___x_2279_ = lean_nat_dec_le(v_stop_2271_, v___x_2278_);
if (v___x_2279_ == 0)
{
uint8_t v___x_2280_; 
v___x_2280_ = lean_nat_dec_lt(v_start_2270_, v___x_2278_);
if (v___x_2280_ == 0)
{
lean_object* v_toApplicative_2281_; lean_object* v_toPure_2282_; lean_object* v___x_2283_; 
lean_dec_ref(v___f_2277_);
lean_dec_ref(v_as_2269_);
v_toApplicative_2281_ = lean_ctor_get(v_inst_2267_, 0);
lean_inc_ref(v_toApplicative_2281_);
lean_dec_ref(v_inst_2267_);
v_toPure_2282_ = lean_ctor_get(v_toApplicative_2281_, 1);
lean_inc(v_toPure_2282_);
lean_dec_ref(v_toApplicative_2281_);
v___x_2283_ = lean_apply_2(v_toPure_2282_, lean_box(0), v___x_2272_);
return v___x_2283_;
}
else
{
size_t v___x_2284_; size_t v___x_2285_; lean_object* v___x_2286_; 
v___x_2284_ = lean_usize_of_nat(v_start_2270_);
v___x_2285_ = lean_usize_of_nat(v___x_2278_);
v___x_2286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2267_, v___f_2277_, v_as_2269_, v___x_2284_, v___x_2285_, v___x_2272_);
return v___x_2286_;
}
}
else
{
size_t v___x_2287_; size_t v___x_2288_; lean_object* v___x_2289_; 
v___x_2287_ = lean_usize_of_nat(v_start_2270_);
v___x_2288_ = lean_usize_of_nat(v_stop_2271_);
v___x_2289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2267_, v___f_2277_, v_as_2269_, v___x_2287_, v___x_2288_, v___x_2272_);
return v___x_2289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___boxed(lean_object* v_inst_2290_, lean_object* v_f_2291_, lean_object* v_as_2292_, lean_object* v_start_2293_, lean_object* v_stop_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Array_forM___redArg(v_inst_2290_, v_f_2291_, v_as_2292_, v_start_2293_, v_stop_2294_);
lean_dec(v_stop_2294_);
lean_dec(v_start_2293_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Array_forM(lean_object* v_00_u03b1_2296_, lean_object* v_m_2297_, lean_object* v_inst_2298_, lean_object* v_f_2299_, lean_object* v_as_2300_, lean_object* v_start_2301_, lean_object* v_stop_2302_){
_start:
{
lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2303_ = lean_box(0);
v___x_2304_ = lean_nat_dec_lt(v_start_2301_, v_stop_2302_);
if (v___x_2304_ == 0)
{
lean_object* v_toApplicative_2305_; lean_object* v_toPure_2306_; lean_object* v___x_2307_; 
lean_dec_ref(v_as_2300_);
lean_dec(v_f_2299_);
v_toApplicative_2305_ = lean_ctor_get(v_inst_2298_, 0);
lean_inc_ref(v_toApplicative_2305_);
lean_dec_ref(v_inst_2298_);
v_toPure_2306_ = lean_ctor_get(v_toApplicative_2305_, 1);
lean_inc(v_toPure_2306_);
lean_dec_ref(v_toApplicative_2305_);
v___x_2307_ = lean_apply_2(v_toPure_2306_, lean_box(0), v___x_2303_);
return v___x_2307_;
}
else
{
lean_object* v___f_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___f_2308_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2308_, 0, v_f_2299_);
v___x_2309_ = lean_array_get_size(v_as_2300_);
v___x_2310_ = lean_nat_dec_le(v_stop_2302_, v___x_2309_);
if (v___x_2310_ == 0)
{
uint8_t v___x_2311_; 
v___x_2311_ = lean_nat_dec_lt(v_start_2301_, v___x_2309_);
if (v___x_2311_ == 0)
{
lean_object* v_toApplicative_2312_; lean_object* v_toPure_2313_; lean_object* v___x_2314_; 
lean_dec_ref(v___f_2308_);
lean_dec_ref(v_as_2300_);
v_toApplicative_2312_ = lean_ctor_get(v_inst_2298_, 0);
lean_inc_ref(v_toApplicative_2312_);
lean_dec_ref(v_inst_2298_);
v_toPure_2313_ = lean_ctor_get(v_toApplicative_2312_, 1);
lean_inc(v_toPure_2313_);
lean_dec_ref(v_toApplicative_2312_);
v___x_2314_ = lean_apply_2(v_toPure_2313_, lean_box(0), v___x_2303_);
return v___x_2314_;
}
else
{
size_t v___x_2315_; size_t v___x_2316_; lean_object* v___x_2317_; 
v___x_2315_ = lean_usize_of_nat(v_start_2301_);
v___x_2316_ = lean_usize_of_nat(v___x_2309_);
v___x_2317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2298_, v___f_2308_, v_as_2300_, v___x_2315_, v___x_2316_, v___x_2303_);
return v___x_2317_;
}
}
else
{
size_t v___x_2318_; size_t v___x_2319_; lean_object* v___x_2320_; 
v___x_2318_ = lean_usize_of_nat(v_start_2301_);
v___x_2319_ = lean_usize_of_nat(v_stop_2302_);
v___x_2320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2298_, v___f_2308_, v_as_2300_, v___x_2318_, v___x_2319_, v___x_2303_);
return v___x_2320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___boxed(lean_object* v_00_u03b1_2321_, lean_object* v_m_2322_, lean_object* v_inst_2323_, lean_object* v_f_2324_, lean_object* v_as_2325_, lean_object* v_start_2326_, lean_object* v_stop_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Array_forM(v_00_u03b1_2321_, v_m_2322_, v_inst_2323_, v_f_2324_, v_as_2325_, v_start_2326_, v_stop_2327_);
lean_dec(v_stop_2327_);
lean_dec(v_start_2326_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg___lam__1(lean_object* v_inst_2329_, lean_object* v_xs_2330_, lean_object* v_f_2331_){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___x_2332_ = lean_unsigned_to_nat(0u);
v___x_2333_ = lean_array_get_size(v_xs_2330_);
v___x_2334_ = lean_box(0);
v___x_2335_ = lean_nat_dec_lt(v___x_2332_, v___x_2333_);
if (v___x_2335_ == 0)
{
lean_object* v_toApplicative_2336_; lean_object* v_toPure_2337_; lean_object* v___x_2338_; 
lean_dec(v_f_2331_);
lean_dec_ref(v_xs_2330_);
v_toApplicative_2336_ = lean_ctor_get(v_inst_2329_, 0);
lean_inc_ref(v_toApplicative_2336_);
lean_dec_ref(v_inst_2329_);
v_toPure_2337_ = lean_ctor_get(v_toApplicative_2336_, 1);
lean_inc(v_toPure_2337_);
lean_dec_ref(v_toApplicative_2336_);
v___x_2338_ = lean_apply_2(v_toPure_2337_, lean_box(0), v___x_2334_);
return v___x_2338_;
}
else
{
lean_object* v___f_2339_; uint8_t v___x_2340_; 
v___f_2339_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2339_, 0, v_f_2331_);
v___x_2340_ = lean_nat_dec_le(v___x_2333_, v___x_2333_);
if (v___x_2340_ == 0)
{
if (v___x_2335_ == 0)
{
lean_object* v_toApplicative_2341_; lean_object* v_toPure_2342_; lean_object* v___x_2343_; 
lean_dec_ref(v___f_2339_);
lean_dec_ref(v_xs_2330_);
v_toApplicative_2341_ = lean_ctor_get(v_inst_2329_, 0);
lean_inc_ref(v_toApplicative_2341_);
lean_dec_ref(v_inst_2329_);
v_toPure_2342_ = lean_ctor_get(v_toApplicative_2341_, 1);
lean_inc(v_toPure_2342_);
lean_dec_ref(v_toApplicative_2341_);
v___x_2343_ = lean_apply_2(v_toPure_2342_, lean_box(0), v___x_2334_);
return v___x_2343_;
}
else
{
size_t v___x_2344_; size_t v___x_2345_; lean_object* v___x_2346_; 
v___x_2344_ = ((size_t)0ULL);
v___x_2345_ = lean_usize_of_nat(v___x_2333_);
v___x_2346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2329_, v___f_2339_, v_xs_2330_, v___x_2344_, v___x_2345_, v___x_2334_);
return v___x_2346_;
}
}
else
{
size_t v___x_2347_; size_t v___x_2348_; lean_object* v___x_2349_; 
v___x_2347_ = ((size_t)0ULL);
v___x_2348_ = lean_usize_of_nat(v___x_2333_);
v___x_2349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2329_, v___f_2339_, v_xs_2330_, v___x_2347_, v___x_2348_, v___x_2334_);
return v___x_2349_;
}
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
lean_object* v___f_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___f_2365_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2365_, 0, v_f_2361_);
v___x_2366_ = lean_box(0);
v___x_2367_ = lean_array_get_size(v_as_2362_);
v___x_2368_ = lean_nat_dec_le(v_start_2363_, v___x_2367_);
if (v___x_2368_ == 0)
{
uint8_t v___x_2369_; 
v___x_2369_ = lean_nat_dec_lt(v_stop_2364_, v___x_2367_);
if (v___x_2369_ == 0)
{
lean_object* v_toApplicative_2370_; lean_object* v_toPure_2371_; lean_object* v___x_2372_; 
lean_dec_ref(v___f_2365_);
lean_dec_ref(v_as_2362_);
v_toApplicative_2370_ = lean_ctor_get(v_inst_2360_, 0);
lean_inc_ref(v_toApplicative_2370_);
lean_dec_ref(v_inst_2360_);
v_toPure_2371_ = lean_ctor_get(v_toApplicative_2370_, 1);
lean_inc(v_toPure_2371_);
lean_dec_ref(v_toApplicative_2370_);
v___x_2372_ = lean_apply_2(v_toPure_2371_, lean_box(0), v___x_2366_);
return v___x_2372_;
}
else
{
size_t v___x_2373_; size_t v___x_2374_; lean_object* v___x_2375_; 
v___x_2373_ = lean_usize_of_nat(v___x_2367_);
v___x_2374_ = lean_usize_of_nat(v_stop_2364_);
v___x_2375_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2360_, v___f_2365_, v_as_2362_, v___x_2373_, v___x_2374_, v___x_2366_);
return v___x_2375_;
}
}
else
{
uint8_t v___x_2376_; 
v___x_2376_ = lean_nat_dec_lt(v_stop_2364_, v_start_2363_);
if (v___x_2376_ == 0)
{
lean_object* v_toApplicative_2377_; lean_object* v_toPure_2378_; lean_object* v___x_2379_; 
lean_dec_ref(v___f_2365_);
lean_dec_ref(v_as_2362_);
v_toApplicative_2377_ = lean_ctor_get(v_inst_2360_, 0);
lean_inc_ref(v_toApplicative_2377_);
lean_dec_ref(v_inst_2360_);
v_toPure_2378_ = lean_ctor_get(v_toApplicative_2377_, 1);
lean_inc(v_toPure_2378_);
lean_dec_ref(v_toApplicative_2377_);
v___x_2379_ = lean_apply_2(v_toPure_2378_, lean_box(0), v___x_2366_);
return v___x_2379_;
}
else
{
size_t v___x_2380_; size_t v___x_2381_; lean_object* v___x_2382_; 
v___x_2380_ = lean_usize_of_nat(v_start_2363_);
v___x_2381_ = lean_usize_of_nat(v_stop_2364_);
v___x_2382_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2360_, v___f_2365_, v_as_2362_, v___x_2380_, v___x_2381_, v___x_2366_);
return v___x_2382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___boxed(lean_object* v_inst_2383_, lean_object* v_f_2384_, lean_object* v_as_2385_, lean_object* v_start_2386_, lean_object* v_stop_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Array_forRevM___redArg(v_inst_2383_, v_f_2384_, v_as_2385_, v_start_2386_, v_stop_2387_);
lean_dec(v_stop_2387_);
lean_dec(v_start_2386_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM(lean_object* v_00_u03b1_2389_, lean_object* v_m_2390_, lean_object* v_inst_2391_, lean_object* v_f_2392_, lean_object* v_as_2393_, lean_object* v_start_2394_, lean_object* v_stop_2395_){
_start:
{
lean_object* v___f_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v___f_2396_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2396_, 0, v_f_2392_);
v___x_2397_ = lean_box(0);
v___x_2398_ = lean_array_get_size(v_as_2393_);
v___x_2399_ = lean_nat_dec_le(v_start_2394_, v___x_2398_);
if (v___x_2399_ == 0)
{
uint8_t v___x_2400_; 
v___x_2400_ = lean_nat_dec_lt(v_stop_2395_, v___x_2398_);
if (v___x_2400_ == 0)
{
lean_object* v_toApplicative_2401_; lean_object* v_toPure_2402_; lean_object* v___x_2403_; 
lean_dec_ref(v___f_2396_);
lean_dec_ref(v_as_2393_);
v_toApplicative_2401_ = lean_ctor_get(v_inst_2391_, 0);
lean_inc_ref(v_toApplicative_2401_);
lean_dec_ref(v_inst_2391_);
v_toPure_2402_ = lean_ctor_get(v_toApplicative_2401_, 1);
lean_inc(v_toPure_2402_);
lean_dec_ref(v_toApplicative_2401_);
v___x_2403_ = lean_apply_2(v_toPure_2402_, lean_box(0), v___x_2397_);
return v___x_2403_;
}
else
{
size_t v___x_2404_; size_t v___x_2405_; lean_object* v___x_2406_; 
v___x_2404_ = lean_usize_of_nat(v___x_2398_);
v___x_2405_ = lean_usize_of_nat(v_stop_2395_);
v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2391_, v___f_2396_, v_as_2393_, v___x_2404_, v___x_2405_, v___x_2397_);
return v___x_2406_;
}
}
else
{
uint8_t v___x_2407_; 
v___x_2407_ = lean_nat_dec_lt(v_stop_2395_, v_start_2394_);
if (v___x_2407_ == 0)
{
lean_object* v_toApplicative_2408_; lean_object* v_toPure_2409_; lean_object* v___x_2410_; 
lean_dec_ref(v___f_2396_);
lean_dec_ref(v_as_2393_);
v_toApplicative_2408_ = lean_ctor_get(v_inst_2391_, 0);
lean_inc_ref(v_toApplicative_2408_);
lean_dec_ref(v_inst_2391_);
v_toPure_2409_ = lean_ctor_get(v_toApplicative_2408_, 1);
lean_inc(v_toPure_2409_);
lean_dec_ref(v_toApplicative_2408_);
v___x_2410_ = lean_apply_2(v_toPure_2409_, lean_box(0), v___x_2397_);
return v___x_2410_;
}
else
{
size_t v___x_2411_; size_t v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = lean_usize_of_nat(v_start_2394_);
v___x_2412_ = lean_usize_of_nat(v_stop_2395_);
v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2391_, v___f_2396_, v_as_2393_, v___x_2411_, v___x_2412_, v___x_2397_);
return v___x_2413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___boxed(lean_object* v_00_u03b1_2414_, lean_object* v_m_2415_, lean_object* v_inst_2416_, lean_object* v_f_2417_, lean_object* v_as_2418_, lean_object* v_start_2419_, lean_object* v_stop_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Array_forRevM(v_00_u03b1_2414_, v_m_2415_, v_inst_2416_, v_f_2417_, v_as_2418_, v_start_2419_, v_stop_2420_);
lean_dec(v_stop_2420_);
lean_dec(v_start_2419_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___lam__0(lean_object* v_f_2422_, lean_object* v_x1_2423_, lean_object* v_x2_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_apply_2(v_f_2422_, v_x1_2423_, v_x2_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg(lean_object* v_f_2445_, lean_object* v_init_2446_, lean_object* v_as_2447_, lean_object* v_start_2448_, lean_object* v_stop_2449_){
_start:
{
lean_object* v___x_2450_; uint8_t v___x_2451_; 
v___x_2450_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2451_ = lean_nat_dec_lt(v_start_2448_, v_stop_2449_);
if (v___x_2451_ == 0)
{
lean_dec_ref(v_as_2447_);
lean_dec(v_f_2445_);
return v_init_2446_;
}
else
{
lean_object* v___f_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___f_2452_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2452_, 0, v_f_2445_);
v___x_2453_ = lean_array_get_size(v_as_2447_);
v___x_2454_ = lean_nat_dec_le(v_stop_2449_, v___x_2453_);
if (v___x_2454_ == 0)
{
uint8_t v___x_2455_; 
v___x_2455_ = lean_nat_dec_lt(v_start_2448_, v___x_2453_);
if (v___x_2455_ == 0)
{
lean_dec_ref(v___f_2452_);
lean_dec_ref(v_as_2447_);
return v_init_2446_;
}
else
{
size_t v___x_2456_; size_t v___x_2457_; lean_object* v___x_2458_; 
v___x_2456_ = lean_usize_of_nat(v_start_2448_);
v___x_2457_ = lean_usize_of_nat(v___x_2453_);
v___x_2458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2450_, v___f_2452_, v_as_2447_, v___x_2456_, v___x_2457_, v_init_2446_);
return v___x_2458_;
}
}
else
{
size_t v___x_2459_; size_t v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = lean_usize_of_nat(v_start_2448_);
v___x_2460_ = lean_usize_of_nat(v_stop_2449_);
v___x_2461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2450_, v___f_2452_, v_as_2447_, v___x_2459_, v___x_2460_, v_init_2446_);
return v___x_2461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___boxed(lean_object* v_f_2462_, lean_object* v_init_2463_, lean_object* v_as_2464_, lean_object* v_start_2465_, lean_object* v_stop_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Array_foldl___redArg(v_f_2462_, v_init_2463_, v_as_2464_, v_start_2465_, v_stop_2466_);
lean_dec(v_stop_2466_);
lean_dec(v_start_2465_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl(lean_object* v_00_u03b1_2468_, lean_object* v_00_u03b2_2469_, lean_object* v_f_2470_, lean_object* v_init_2471_, lean_object* v_as_2472_, lean_object* v_start_2473_, lean_object* v_stop_2474_){
_start:
{
lean_object* v___x_2475_; uint8_t v___x_2476_; 
v___x_2475_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2476_ = lean_nat_dec_lt(v_start_2473_, v_stop_2474_);
if (v___x_2476_ == 0)
{
lean_dec_ref(v_as_2472_);
lean_dec(v_f_2470_);
return v_init_2471_;
}
else
{
lean_object* v___f_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v___f_2477_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2477_, 0, v_f_2470_);
v___x_2478_ = lean_array_get_size(v_as_2472_);
v___x_2479_ = lean_nat_dec_le(v_stop_2474_, v___x_2478_);
if (v___x_2479_ == 0)
{
uint8_t v___x_2480_; 
v___x_2480_ = lean_nat_dec_lt(v_start_2473_, v___x_2478_);
if (v___x_2480_ == 0)
{
lean_dec_ref(v___f_2477_);
lean_dec_ref(v_as_2472_);
return v_init_2471_;
}
else
{
size_t v___x_2481_; size_t v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = lean_usize_of_nat(v_start_2473_);
v___x_2482_ = lean_usize_of_nat(v___x_2478_);
v___x_2483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2475_, v___f_2477_, v_as_2472_, v___x_2481_, v___x_2482_, v_init_2471_);
return v___x_2483_;
}
}
else
{
size_t v___x_2484_; size_t v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = lean_usize_of_nat(v_start_2473_);
v___x_2485_ = lean_usize_of_nat(v_stop_2474_);
v___x_2486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2475_, v___f_2477_, v_as_2472_, v___x_2484_, v___x_2485_, v_init_2471_);
return v___x_2486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___boxed(lean_object* v_00_u03b1_2487_, lean_object* v_00_u03b2_2488_, lean_object* v_f_2489_, lean_object* v_init_2490_, lean_object* v_as_2491_, lean_object* v_start_2492_, lean_object* v_stop_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Array_foldl(v_00_u03b1_2487_, v_00_u03b2_2488_, v_f_2489_, v_init_2490_, v_as_2491_, v_start_2492_, v_stop_2493_);
lean_dec(v_stop_2493_);
lean_dec(v_start_2492_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg(lean_object* v_f_2495_, lean_object* v_init_2496_, lean_object* v_as_2497_, lean_object* v_start_2498_, lean_object* v_stop_2499_){
_start:
{
lean_object* v___f_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v___f_2500_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2500_, 0, v_f_2495_);
v___x_2501_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2502_ = lean_array_get_size(v_as_2497_);
v___x_2503_ = lean_nat_dec_le(v_start_2498_, v___x_2502_);
if (v___x_2503_ == 0)
{
uint8_t v___x_2504_; 
v___x_2504_ = lean_nat_dec_lt(v_stop_2499_, v___x_2502_);
if (v___x_2504_ == 0)
{
lean_dec_ref(v___f_2500_);
lean_dec_ref(v_as_2497_);
return v_init_2496_;
}
else
{
size_t v___x_2505_; size_t v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = lean_usize_of_nat(v___x_2502_);
v___x_2506_ = lean_usize_of_nat(v_stop_2499_);
v___x_2507_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2501_, v___f_2500_, v_as_2497_, v___x_2505_, v___x_2506_, v_init_2496_);
return v___x_2507_;
}
}
else
{
uint8_t v___x_2508_; 
v___x_2508_ = lean_nat_dec_lt(v_stop_2499_, v_start_2498_);
if (v___x_2508_ == 0)
{
lean_dec_ref(v___f_2500_);
lean_dec_ref(v_as_2497_);
return v_init_2496_;
}
else
{
size_t v___x_2509_; size_t v___x_2510_; lean_object* v___x_2511_; 
v___x_2509_ = lean_usize_of_nat(v_start_2498_);
v___x_2510_ = lean_usize_of_nat(v_stop_2499_);
v___x_2511_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2501_, v___f_2500_, v_as_2497_, v___x_2509_, v___x_2510_, v_init_2496_);
return v___x_2511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg___boxed(lean_object* v_f_2512_, lean_object* v_init_2513_, lean_object* v_as_2514_, lean_object* v_start_2515_, lean_object* v_stop_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Array_foldr___redArg(v_f_2512_, v_init_2513_, v_as_2514_, v_start_2515_, v_stop_2516_);
lean_dec(v_stop_2516_);
lean_dec(v_start_2515_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr(lean_object* v_00_u03b1_2518_, lean_object* v_00_u03b2_2519_, lean_object* v_f_2520_, lean_object* v_init_2521_, lean_object* v_as_2522_, lean_object* v_start_2523_, lean_object* v_stop_2524_){
_start:
{
lean_object* v___f_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; uint8_t v___x_2528_; 
v___f_2525_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2525_, 0, v_f_2520_);
v___x_2526_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2527_ = lean_array_get_size(v_as_2522_);
v___x_2528_ = lean_nat_dec_le(v_start_2523_, v___x_2527_);
if (v___x_2528_ == 0)
{
uint8_t v___x_2529_; 
v___x_2529_ = lean_nat_dec_lt(v_stop_2524_, v___x_2527_);
if (v___x_2529_ == 0)
{
lean_dec_ref(v___f_2525_);
lean_dec_ref(v_as_2522_);
return v_init_2521_;
}
else
{
size_t v___x_2530_; size_t v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = lean_usize_of_nat(v___x_2527_);
v___x_2531_ = lean_usize_of_nat(v_stop_2524_);
v___x_2532_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2526_, v___f_2525_, v_as_2522_, v___x_2530_, v___x_2531_, v_init_2521_);
return v___x_2532_;
}
}
else
{
uint8_t v___x_2533_; 
v___x_2533_ = lean_nat_dec_lt(v_stop_2524_, v_start_2523_);
if (v___x_2533_ == 0)
{
lean_dec_ref(v___f_2525_);
lean_dec_ref(v_as_2522_);
return v_init_2521_;
}
else
{
size_t v___x_2534_; size_t v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = lean_usize_of_nat(v_start_2523_);
v___x_2535_ = lean_usize_of_nat(v_stop_2524_);
v___x_2536_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2526_, v___f_2525_, v_as_2522_, v___x_2534_, v___x_2535_, v_init_2521_);
return v___x_2536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___boxed(lean_object* v_00_u03b1_2537_, lean_object* v_00_u03b2_2538_, lean_object* v_f_2539_, lean_object* v_init_2540_, lean_object* v_as_2541_, lean_object* v_start_2542_, lean_object* v_stop_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Array_foldr(v_00_u03b1_2537_, v_00_u03b2_2538_, v_f_2539_, v_init_2540_, v_as_2541_, v_start_2542_, v_stop_2543_);
lean_dec(v_stop_2543_);
lean_dec(v_start_2542_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg___lam__0(lean_object* v_inst_2545_, lean_object* v_x1_2546_, lean_object* v_x2_2547_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_apply_2(v_inst_2545_, v_x1_2546_, v_x2_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg(lean_object* v_inst_2549_, lean_object* v_inst_2550_, lean_object* v_as_2551_){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; 
v___x_2552_ = lean_array_get_size(v_as_2551_);
v___x_2553_ = lean_unsigned_to_nat(0u);
v___x_2554_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2555_ = lean_nat_dec_lt(v___x_2553_, v___x_2552_);
if (v___x_2555_ == 0)
{
lean_dec_ref(v_as_2551_);
lean_dec(v_inst_2549_);
return v_inst_2550_;
}
else
{
lean_object* v___f_2556_; size_t v___x_2557_; size_t v___x_2558_; lean_object* v___x_2559_; 
v___f_2556_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2556_, 0, v_inst_2549_);
v___x_2557_ = lean_usize_of_nat(v___x_2552_);
v___x_2558_ = ((size_t)0ULL);
v___x_2559_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2554_, v___f_2556_, v_as_2551_, v___x_2557_, v___x_2558_, v_inst_2550_);
return v___x_2559_;
}
}
}
LEAN_EXPORT lean_object* l_Array_sum(lean_object* v_00_u03b1_2560_, lean_object* v_inst_2561_, lean_object* v_inst_2562_, lean_object* v_as_2563_){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
v___x_2564_ = lean_array_get_size(v_as_2563_);
v___x_2565_ = lean_unsigned_to_nat(0u);
v___x_2566_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2567_ = lean_nat_dec_lt(v___x_2565_, v___x_2564_);
if (v___x_2567_ == 0)
{
lean_dec_ref(v_as_2563_);
lean_dec(v_inst_2561_);
return v_inst_2562_;
}
else
{
lean_object* v___f_2568_; size_t v___x_2569_; size_t v___x_2570_; lean_object* v___x_2571_; 
v___f_2568_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2568_, 0, v_inst_2561_);
v___x_2569_ = lean_usize_of_nat(v___x_2564_);
v___x_2570_ = ((size_t)0ULL);
v___x_2571_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2566_, v___f_2568_, v_as_2563_, v___x_2569_, v___x_2570_, v_inst_2562_);
return v___x_2571_;
}
}
}
LEAN_EXPORT lean_object* l_Array_prod___redArg(lean_object* v_inst_2572_, lean_object* v_inst_2573_, lean_object* v_as_2574_){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2575_ = lean_array_get_size(v_as_2574_);
v___x_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2578_ = lean_nat_dec_lt(v___x_2576_, v___x_2575_);
if (v___x_2578_ == 0)
{
lean_dec_ref(v_as_2574_);
lean_dec(v_inst_2572_);
return v_inst_2573_;
}
else
{
lean_object* v___f_2579_; size_t v___x_2580_; size_t v___x_2581_; lean_object* v___x_2582_; 
v___f_2579_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2579_, 0, v_inst_2572_);
v___x_2580_ = lean_usize_of_nat(v___x_2575_);
v___x_2581_ = ((size_t)0ULL);
v___x_2582_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2577_, v___f_2579_, v_as_2574_, v___x_2580_, v___x_2581_, v_inst_2573_);
return v___x_2582_;
}
}
}
LEAN_EXPORT lean_object* l_Array_prod(lean_object* v_00_u03b1_2583_, lean_object* v_inst_2584_, lean_object* v_inst_2585_, lean_object* v_as_2586_){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2587_ = lean_array_get_size(v_as_2586_);
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2590_ = lean_nat_dec_lt(v___x_2588_, v___x_2587_);
if (v___x_2590_ == 0)
{
lean_dec_ref(v_as_2586_);
lean_dec(v_inst_2584_);
return v_inst_2585_;
}
else
{
lean_object* v___f_2591_; size_t v___x_2592_; size_t v___x_2593_; lean_object* v___x_2594_; 
v___f_2591_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2591_, 0, v_inst_2584_);
v___x_2592_ = lean_usize_of_nat(v___x_2587_);
v___x_2593_ = ((size_t)0ULL);
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2589_, v___f_2591_, v_as_2586_, v___x_2592_, v___x_2593_, v_inst_2585_);
return v___x_2594_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0(lean_object* v_p_2595_, lean_object* v_x1_2596_, lean_object* v_x2_2597_){
_start:
{
lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2598_ = lean_apply_1(v_p_2595_, v_x1_2596_);
v___x_2599_ = lean_unbox(v___x_2598_);
if (v___x_2599_ == 0)
{
lean_inc(v_x2_2597_);
return v_x2_2597_;
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = lean_unsigned_to_nat(1u);
v___x_2601_ = lean_nat_add(v_x2_2597_, v___x_2600_);
return v___x_2601_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0___boxed(lean_object* v_p_2602_, lean_object* v_x1_2603_, lean_object* v_x2_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Array_countP___redArg___lam__0(v_p_2602_, v_x1_2603_, v_x2_2604_);
lean_dec(v_x2_2604_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg(lean_object* v_p_2606_, lean_object* v_as_2607_){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2608_ = lean_unsigned_to_nat(0u);
v___x_2609_ = lean_array_get_size(v_as_2607_);
v___x_2610_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2611_ = lean_nat_dec_lt(v___x_2608_, v___x_2609_);
if (v___x_2611_ == 0)
{
lean_dec_ref(v_as_2607_);
lean_dec_ref(v_p_2606_);
return v___x_2608_;
}
else
{
lean_object* v___f_2612_; size_t v___x_2613_; size_t v___x_2614_; lean_object* v___x_2615_; 
v___f_2612_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2612_, 0, v_p_2606_);
v___x_2613_ = lean_usize_of_nat(v___x_2609_);
v___x_2614_ = ((size_t)0ULL);
v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2610_, v___f_2612_, v_as_2607_, v___x_2613_, v___x_2614_, v___x_2608_);
return v___x_2615_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP(lean_object* v_00_u03b1_2616_, lean_object* v_p_2617_, lean_object* v_as_2618_){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2619_ = lean_unsigned_to_nat(0u);
v___x_2620_ = lean_array_get_size(v_as_2618_);
v___x_2621_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2622_ = lean_nat_dec_lt(v___x_2619_, v___x_2620_);
if (v___x_2622_ == 0)
{
lean_dec_ref(v_as_2618_);
lean_dec_ref(v_p_2617_);
return v___x_2619_;
}
else
{
lean_object* v___f_2623_; size_t v___x_2624_; size_t v___x_2625_; lean_object* v___x_2626_; 
v___f_2623_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2623_, 0, v_p_2617_);
v___x_2624_ = lean_usize_of_nat(v___x_2620_);
v___x_2625_ = ((size_t)0ULL);
v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2621_, v___f_2623_, v_as_2618_, v___x_2624_, v___x_2625_, v___x_2619_);
return v___x_2626_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0(lean_object* v_inst_2627_, lean_object* v_a_2628_, lean_object* v_x1_2629_, lean_object* v_x2_2630_){
_start:
{
lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2631_ = lean_apply_2(v_inst_2627_, v_x1_2629_, v_a_2628_);
v___x_2632_ = lean_unbox(v___x_2631_);
if (v___x_2632_ == 0)
{
lean_inc(v_x2_2630_);
return v_x2_2630_;
}
else
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2633_ = lean_unsigned_to_nat(1u);
v___x_2634_ = lean_nat_add(v_x2_2630_, v___x_2633_);
return v___x_2634_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0___boxed(lean_object* v_inst_2635_, lean_object* v_a_2636_, lean_object* v_x1_2637_, lean_object* v_x2_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l_Array_count___redArg___lam__0(v_inst_2635_, v_a_2636_, v_x1_2637_, v_x2_2638_);
lean_dec(v_x2_2638_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg(lean_object* v_inst_2640_, lean_object* v_a_2641_, lean_object* v_as_2642_){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = lean_array_get_size(v_as_2642_);
v___x_2645_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2646_ = lean_nat_dec_lt(v___x_2643_, v___x_2644_);
if (v___x_2646_ == 0)
{
lean_dec_ref(v_as_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_inst_2640_);
return v___x_2643_;
}
else
{
lean_object* v___f_2647_; size_t v___x_2648_; size_t v___x_2649_; lean_object* v___x_2650_; 
v___f_2647_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2647_, 0, v_inst_2640_);
lean_closure_set(v___f_2647_, 1, v_a_2641_);
v___x_2648_ = lean_usize_of_nat(v___x_2644_);
v___x_2649_ = ((size_t)0ULL);
v___x_2650_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2645_, v___f_2647_, v_as_2642_, v___x_2648_, v___x_2649_, v___x_2643_);
return v___x_2650_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count(lean_object* v_00_u03b1_2651_, lean_object* v_inst_2652_, lean_object* v_a_2653_, lean_object* v_as_2654_){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2655_ = lean_unsigned_to_nat(0u);
v___x_2656_ = lean_array_get_size(v_as_2654_);
v___x_2657_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2658_ = lean_nat_dec_lt(v___x_2655_, v___x_2656_);
if (v___x_2658_ == 0)
{
lean_dec_ref(v_as_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_inst_2652_);
return v___x_2655_;
}
else
{
lean_object* v___f_2659_; size_t v___x_2660_; size_t v___x_2661_; lean_object* v___x_2662_; 
v___f_2659_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2659_, 0, v_inst_2652_);
lean_closure_set(v___f_2659_, 1, v_a_2653_);
v___x_2660_ = lean_usize_of_nat(v___x_2656_);
v___x_2661_ = ((size_t)0ULL);
v___x_2662_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2657_, v___f_2659_, v_as_2654_, v___x_2660_, v___x_2661_, v___x_2655_);
return v___x_2662_;
}
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg___lam__0(lean_object* v_f_2663_, lean_object* v_x_2664_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = lean_apply_1(v_f_2663_, v_x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg(lean_object* v_f_2666_, lean_object* v_as_2667_){
_start:
{
lean_object* v___f_2668_; lean_object* v___x_2669_; size_t v_sz_2670_; size_t v___x_2671_; lean_object* v___x_2672_; 
v___f_2668_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2668_, 0, v_f_2666_);
v___x_2669_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2670_ = lean_array_size(v_as_2667_);
v___x_2671_ = ((size_t)0ULL);
v___x_2672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2669_, v___f_2668_, v_sz_2670_, v___x_2671_, v_as_2667_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Array_map(lean_object* v_00_u03b1_2673_, lean_object* v_00_u03b2_2674_, lean_object* v_f_2675_, lean_object* v_as_2676_){
_start:
{
lean_object* v___f_2677_; lean_object* v___x_2678_; size_t v_sz_2679_; size_t v___x_2680_; lean_object* v___x_2681_; 
v___f_2677_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2677_, 0, v_f_2675_);
v___x_2678_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2679_ = lean_array_size(v_as_2676_);
v___x_2680_ = ((size_t)0ULL);
v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2678_, v___f_2677_, v_sz_2679_, v___x_2680_, v_as_2676_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0(lean_object* v___y_2682_, lean_object* v_x_2683_){
_start:
{
lean_inc(v___y_2682_);
return v___y_2682_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0___boxed(lean_object* v___y_2684_, lean_object* v_x_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Array_instFunctor___lam__0(v___y_2684_, v_x_2685_);
lean_dec(v_x_2685_);
lean_dec(v___y_2684_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__1(lean_object* v_00_u03b1_2687_, lean_object* v_00_u03b2_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v___f_2691_; lean_object* v___x_2692_; size_t v_sz_2693_; size_t v___x_2694_; lean_object* v___x_2695_; 
v___f_2691_ = lean_alloc_closure((void*)(l_Array_instFunctor___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2691_, 0, v___y_2689_);
v___x_2692_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2693_ = lean_array_size(v___y_2690_);
v___x_2694_ = ((size_t)0ULL);
v___x_2695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2692_, v___f_2691_, v_sz_2693_, v___x_2694_, v___y_2690_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg___lam__0(lean_object* v_f_2702_, lean_object* v_x1_2703_, lean_object* v_x2_2704_, lean_object* v_x3_2705_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = lean_apply_3(v_f_2702_, v_x1_2703_, v_x2_2704_, lean_box(0));
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg(lean_object* v_as_2707_, lean_object* v_f_2708_){
_start:
{
lean_object* v___f_2709_; lean_object* v___x_2710_; size_t v_sz_2711_; size_t v___x_2712_; lean_object* v___x_2713_; 
v___f_2709_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2709_, 0, v_f_2708_);
v___x_2710_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2711_ = lean_array_size(v_as_2707_);
v___x_2712_ = ((size_t)0ULL);
v___x_2713_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2710_, v___f_2709_, v_sz_2711_, v___x_2712_, v_as_2707_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx(lean_object* v_00_u03b1_2714_, lean_object* v_00_u03b2_2715_, lean_object* v_as_2716_, lean_object* v_f_2717_){
_start:
{
lean_object* v___f_2718_; lean_object* v___x_2719_; size_t v_sz_2720_; size_t v___x_2721_; lean_object* v___x_2722_; 
v___f_2718_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2718_, 0, v_f_2717_);
v___x_2719_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2720_ = lean_array_size(v_as_2716_);
v___x_2721_ = ((size_t)0ULL);
v___x_2722_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2719_, v___f_2718_, v_sz_2720_, v___x_2721_, v_as_2716_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx___redArg(lean_object* v_f_2723_, lean_object* v_as_2724_){
_start:
{
lean_object* v___f_2725_; lean_object* v___x_2726_; size_t v_sz_2727_; size_t v___x_2728_; lean_object* v___x_2729_; 
v___f_2725_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2725_, 0, v_f_2723_);
v___x_2726_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2727_ = lean_array_size(v_as_2724_);
v___x_2728_ = ((size_t)0ULL);
v___x_2729_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2726_, v___f_2725_, v_sz_2727_, v___x_2728_, v_as_2724_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx(lean_object* v_00_u03b1_2730_, lean_object* v_00_u03b2_2731_, lean_object* v_f_2732_, lean_object* v_as_2733_){
_start:
{
lean_object* v___f_2734_; lean_object* v___x_2735_; size_t v_sz_2736_; size_t v___x_2737_; lean_object* v___x_2738_; 
v___f_2734_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2734_, 0, v_f_2732_);
v___x_2735_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2736_ = lean_array_size(v_as_2733_);
v___x_2737_ = ((size_t)0ULL);
v___x_2738_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2735_, v___f_2734_, v_sz_2736_, v___x_2737_, v_as_2733_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(lean_object* v_start_2739_, size_t v_sz_2740_, size_t v_i_2741_, lean_object* v_bs_2742_){
_start:
{
uint8_t v___x_2743_; 
v___x_2743_ = lean_usize_dec_lt(v_i_2741_, v_sz_2740_);
if (v___x_2743_ == 0)
{
return v_bs_2742_;
}
else
{
lean_object* v_v_2744_; lean_object* v___x_2745_; lean_object* v_bs_x27_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; size_t v___x_2750_; size_t v___x_2751_; lean_object* v___x_2752_; 
v_v_2744_ = lean_array_uget(v_bs_2742_, v_i_2741_);
v___x_2745_ = lean_unsigned_to_nat(0u);
v_bs_x27_2746_ = lean_array_uset(v_bs_2742_, v_i_2741_, v___x_2745_);
v___x_2747_ = lean_usize_to_nat(v_i_2741_);
v___x_2748_ = lean_nat_add(v_start_2739_, v___x_2747_);
lean_dec(v___x_2747_);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v_v_2744_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = ((size_t)1ULL);
v___x_2751_ = lean_usize_add(v_i_2741_, v___x_2750_);
v___x_2752_ = lean_array_uset(v_bs_x27_2746_, v_i_2741_, v___x_2749_);
v_i_2741_ = v___x_2751_;
v_bs_2742_ = v___x_2752_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg___boxed(lean_object* v_start_2754_, lean_object* v_sz_2755_, lean_object* v_i_2756_, lean_object* v_bs_2757_){
_start:
{
size_t v_sz_boxed_2758_; size_t v_i_boxed_2759_; lean_object* v_res_2760_; 
v_sz_boxed_2758_ = lean_unbox_usize(v_sz_2755_);
lean_dec(v_sz_2755_);
v_i_boxed_2759_ = lean_unbox_usize(v_i_2756_);
lean_dec(v_i_2756_);
v_res_2760_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2754_, v_sz_boxed_2758_, v_i_boxed_2759_, v_bs_2757_);
lean_dec(v_start_2754_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg(lean_object* v_xs_2761_, lean_object* v_start_2762_){
_start:
{
size_t v_sz_2763_; size_t v___x_2764_; lean_object* v___x_2765_; 
v_sz_2763_ = lean_array_size(v_xs_2761_);
v___x_2764_ = ((size_t)0ULL);
v___x_2765_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2762_, v_sz_2763_, v___x_2764_, v_xs_2761_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg___boxed(lean_object* v_xs_2766_, lean_object* v_start_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Array_zipIdx___redArg(v_xs_2766_, v_start_2767_);
lean_dec(v_start_2767_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx(lean_object* v_00_u03b1_2769_, lean_object* v_xs_2770_, lean_object* v_start_2771_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Array_zipIdx___redArg(v_xs_2770_, v_start_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___boxed(lean_object* v_00_u03b1_2773_, lean_object* v_xs_2774_, lean_object* v_start_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Array_zipIdx(v_00_u03b1_2773_, v_xs_2774_, v_start_2775_);
lean_dec(v_start_2775_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(lean_object* v_00_u03b1_2777_, lean_object* v_start_2778_, lean_object* v_as_2779_, size_t v_sz_2780_, size_t v_i_2781_, lean_object* v_bs_2782_){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2778_, v_sz_2780_, v_i_2781_, v_bs_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___boxed(lean_object* v_00_u03b1_2784_, lean_object* v_start_2785_, lean_object* v_as_2786_, lean_object* v_sz_2787_, lean_object* v_i_2788_, lean_object* v_bs_2789_){
_start:
{
size_t v_sz_boxed_2790_; size_t v_i_boxed_2791_; lean_object* v_res_2792_; 
v_sz_boxed_2790_ = lean_unbox_usize(v_sz_2787_);
lean_dec(v_sz_2787_);
v_i_boxed_2791_ = lean_unbox_usize(v_i_2788_);
lean_dec(v_i_2788_);
v_res_2792_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(v_00_u03b1_2784_, v_start_2785_, v_as_2786_, v_sz_boxed_2790_, v_i_boxed_2791_, v_bs_2789_);
lean_dec_ref(v_as_2786_);
lean_dec(v_start_2785_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0(lean_object* v_p_2793_, lean_object* v___x_2794_, lean_object* v___x_2795_, lean_object* v_a_2796_, lean_object* v_x_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___x_2799_; uint8_t v___x_2800_; 
lean_inc(v_a_2796_);
v___x_2799_ = lean_apply_1(v_p_2793_, v_a_2796_);
v___x_2800_ = lean_unbox(v___x_2799_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; 
lean_dec(v_a_2796_);
v___x_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2794_);
return v___x_2801_;
}
else
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
lean_dec_ref(v___x_2794_);
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v_a_2796_);
v___x_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
v___x_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
lean_ctor_set(v___x_2804_, 1, v___x_2795_);
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0___boxed(lean_object* v_p_2806_, lean_object* v___x_2807_, lean_object* v___x_2808_, lean_object* v_a_2809_, lean_object* v_x_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Array_find_x3f___redArg___lam__0(v_p_2806_, v___x_2807_, v___x_2808_, v_a_2809_, v_x_2810_, v___y_2811_);
lean_dec_ref(v___y_2811_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg(lean_object* v_p_2813_, lean_object* v_as_2814_){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___f_2819_; size_t v_sz_2820_; size_t v___x_2821_; lean_object* v___x_2822_; lean_object* v_fst_2823_; 
v___x_2815_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2816_ = lean_box(0);
v___x_2817_ = lean_box(0);
v___x_2818_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2819_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2819_, 0, v_p_2813_);
lean_closure_set(v___f_2819_, 1, v___x_2818_);
lean_closure_set(v___f_2819_, 2, v___x_2817_);
v_sz_2820_ = lean_array_size(v_as_2814_);
v___x_2821_ = ((size_t)0ULL);
v___x_2822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2815_, v_as_2814_, v___f_2819_, v_sz_2820_, v___x_2821_, v___x_2818_);
v_fst_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_fst_2823_);
lean_dec(v___x_2822_);
if (lean_obj_tag(v_fst_2823_) == 0)
{
return v___x_2816_;
}
else
{
lean_object* v_val_2824_; 
v_val_2824_ = lean_ctor_get(v_fst_2823_, 0);
lean_inc(v_val_2824_);
lean_dec_ref_known(v_fst_2823_, 1);
return v_val_2824_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f(lean_object* v_00_u03b1_2825_, lean_object* v_p_2826_, lean_object* v_as_2827_){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___f_2832_; size_t v_sz_2833_; size_t v___x_2834_; lean_object* v___x_2835_; lean_object* v_fst_2836_; 
v___x_2828_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2829_ = lean_box(0);
v___x_2830_ = lean_box(0);
v___x_2831_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2832_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2832_, 0, v_p_2826_);
lean_closure_set(v___f_2832_, 1, v___x_2831_);
lean_closure_set(v___f_2832_, 2, v___x_2830_);
v_sz_2833_ = lean_array_size(v_as_2827_);
v___x_2834_ = ((size_t)0ULL);
v___x_2835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2828_, v_as_2827_, v___f_2832_, v_sz_2833_, v___x_2834_, v___x_2831_);
v_fst_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_fst_2836_);
lean_dec(v___x_2835_);
if (lean_obj_tag(v_fst_2836_) == 0)
{
return v___x_2829_;
}
else
{
lean_object* v_val_2837_; 
v_val_2837_ = lean_ctor_get(v_fst_2836_, 0);
lean_inc(v_val_2837_);
lean_dec_ref_known(v_fst_2836_, 1);
return v_val_2837_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0(lean_object* v_f_2838_, lean_object* v___x_2839_, lean_object* v___x_2840_, lean_object* v_a_2841_, lean_object* v_x_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = lean_apply_1(v_f_2838_, v_a_2841_);
if (lean_obj_tag(v___x_2844_) == 1)
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
lean_dec_ref(v___x_2840_);
v___x_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
v___x_2846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
lean_ctor_set(v___x_2846_, 1, v___x_2839_);
v___x_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
return v___x_2847_;
}
else
{
lean_object* v___x_2848_; 
lean_dec(v___x_2844_);
v___x_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2840_);
return v___x_2848_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2849_, lean_object* v___x_2850_, lean_object* v___x_2851_, lean_object* v_a_2852_, lean_object* v_x_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Array_findSome_x3f___redArg___lam__0(v_f_2849_, v___x_2850_, v___x_2851_, v_a_2852_, v_x_2853_, v___y_2854_);
lean_dec_ref(v___y_2854_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg(lean_object* v_f_2856_, lean_object* v_as_2857_){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___f_2862_; size_t v_sz_2863_; size_t v___x_2864_; lean_object* v___x_2865_; lean_object* v_fst_2866_; 
v___x_2858_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2859_ = lean_box(0);
v___x_2860_ = lean_box(0);
v___x_2861_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2862_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2862_, 0, v_f_2856_);
lean_closure_set(v___f_2862_, 1, v___x_2860_);
lean_closure_set(v___f_2862_, 2, v___x_2861_);
v_sz_2863_ = lean_array_size(v_as_2857_);
v___x_2864_ = ((size_t)0ULL);
v___x_2865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2858_, v_as_2857_, v___f_2862_, v_sz_2863_, v___x_2864_, v___x_2861_);
v_fst_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_fst_2866_);
lean_dec(v___x_2865_);
if (lean_obj_tag(v_fst_2866_) == 0)
{
return v___x_2859_;
}
else
{
lean_object* v_val_2867_; 
v_val_2867_ = lean_ctor_get(v_fst_2866_, 0);
lean_inc(v_val_2867_);
lean_dec_ref_known(v_fst_2866_, 1);
return v_val_2867_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f(lean_object* v_00_u03b1_2868_, lean_object* v_00_u03b2_2869_, lean_object* v_f_2870_, lean_object* v_as_2871_){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___f_2876_; size_t v_sz_2877_; size_t v___x_2878_; lean_object* v___x_2879_; lean_object* v_fst_2880_; 
v___x_2872_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2873_ = lean_box(0);
v___x_2874_ = lean_box(0);
v___x_2875_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2876_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2876_, 0, v_f_2870_);
lean_closure_set(v___f_2876_, 1, v___x_2874_);
lean_closure_set(v___f_2876_, 2, v___x_2875_);
v_sz_2877_ = lean_array_size(v_as_2871_);
v___x_2878_ = ((size_t)0ULL);
v___x_2879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2872_, v_as_2871_, v___f_2876_, v_sz_2877_, v___x_2878_, v___x_2875_);
v_fst_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_fst_2880_);
lean_dec(v___x_2879_);
if (lean_obj_tag(v_fst_2880_) == 0)
{
return v___x_2873_;
}
else
{
lean_object* v_val_2881_; 
v_val_2881_ = lean_ctor_get(v_fst_2880_, 0);
lean_inc(v_val_2881_);
lean_dec_ref_known(v_fst_2880_, 1);
return v_val_2881_;
}
}
}
static lean_object* _init_l_Array_findSome_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2884_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__1));
v___x_2885_ = lean_unsigned_to_nat(14u);
v___x_2886_ = lean_unsigned_to_nat(1254u);
v___x_2887_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__0));
v___x_2888_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_2889_ = l_mkPanicMessageWithDecl(v___x_2888_, v___x_2887_, v___x_2886_, v___x_2885_, v___x_2884_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg(lean_object* v_inst_2890_, lean_object* v_f_2891_, lean_object* v_xs_2892_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___f_2899_; size_t v_sz_2900_; size_t v___x_2901_; lean_object* v___x_2902_; lean_object* v_fst_2903_; 
v___x_2896_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2897_ = lean_box(0);
v___x_2898_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2899_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2899_, 0, v_f_2891_);
lean_closure_set(v___f_2899_, 1, v___x_2897_);
lean_closure_set(v___f_2899_, 2, v___x_2898_);
v_sz_2900_ = lean_array_size(v_xs_2892_);
v___x_2901_ = ((size_t)0ULL);
v___x_2902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2896_, v_xs_2892_, v___f_2899_, v_sz_2900_, v___x_2901_, v___x_2898_);
v_fst_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_fst_2903_);
lean_dec(v___x_2902_);
if (lean_obj_tag(v_fst_2903_) == 0)
{
goto v___jp_2893_;
}
else
{
lean_object* v_val_2904_; 
v_val_2904_ = lean_ctor_get(v_fst_2903_, 0);
lean_inc(v_val_2904_);
lean_dec_ref_known(v_fst_2903_, 1);
if (lean_obj_tag(v_val_2904_) == 0)
{
goto v___jp_2893_;
}
else
{
lean_object* v_val_2905_; 
v_val_2905_ = lean_ctor_get(v_val_2904_, 0);
lean_inc(v_val_2905_);
lean_dec_ref_known(v_val_2904_, 1);
return v_val_2905_;
}
}
v___jp_2893_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2895_ = l_panic___redArg(v_inst_2890_, v___x_2894_);
return v___x_2895_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg___boxed(lean_object* v_inst_2906_, lean_object* v_f_2907_, lean_object* v_xs_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Array_findSome_x21___redArg(v_inst_2906_, v_f_2907_, v_xs_2908_);
lean_dec(v_inst_2906_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21(lean_object* v_00_u03b1_2910_, lean_object* v_00_u03b2_2911_, lean_object* v_inst_2912_, lean_object* v_f_2913_, lean_object* v_xs_2914_){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___f_2921_; size_t v_sz_2922_; size_t v___x_2923_; lean_object* v___x_2924_; lean_object* v_fst_2925_; 
v___x_2918_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2919_ = lean_box(0);
v___x_2920_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2921_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2921_, 0, v_f_2913_);
lean_closure_set(v___f_2921_, 1, v___x_2919_);
lean_closure_set(v___f_2921_, 2, v___x_2920_);
v_sz_2922_ = lean_array_size(v_xs_2914_);
v___x_2923_ = ((size_t)0ULL);
v___x_2924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2918_, v_xs_2914_, v___f_2921_, v_sz_2922_, v___x_2923_, v___x_2920_);
v_fst_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_fst_2925_);
lean_dec(v___x_2924_);
if (lean_obj_tag(v_fst_2925_) == 0)
{
goto v___jp_2915_;
}
else
{
lean_object* v_val_2926_; 
v_val_2926_ = lean_ctor_get(v_fst_2925_, 0);
lean_inc(v_val_2926_);
lean_dec_ref_known(v_fst_2925_, 1);
if (lean_obj_tag(v_val_2926_) == 0)
{
goto v___jp_2915_;
}
else
{
lean_object* v_val_2927_; 
v_val_2927_ = lean_ctor_get(v_val_2926_, 0);
lean_inc(v_val_2927_);
lean_dec_ref_known(v_val_2926_, 1);
return v_val_2927_;
}
}
v___jp_2915_:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2917_ = l_panic___redArg(v_inst_2912_, v___x_2916_);
return v___x_2917_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___boxed(lean_object* v_00_u03b1_2928_, lean_object* v_00_u03b2_2929_, lean_object* v_inst_2930_, lean_object* v_f_2931_, lean_object* v_xs_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Array_findSome_x21(v_00_u03b1_2928_, v_00_u03b2_2929_, v_inst_2930_, v_f_2931_, v_xs_2932_);
lean_dec(v_inst_2930_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2934_, lean_object* v_x_2935_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = lean_apply_1(v_f_2934_, v_x_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg(lean_object* v_f_2937_, lean_object* v_as_2938_){
_start:
{
lean_object* v___f_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___f_2939_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2939_, 0, v_f_2937_);
v___x_2940_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2941_ = lean_array_get_size(v_as_2938_);
v___x_2942_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2940_, v___f_2939_, v_as_2938_, v___x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f(lean_object* v_00_u03b1_2943_, lean_object* v_00_u03b2_2944_, lean_object* v_f_2945_, lean_object* v_as_2946_){
_start:
{
lean_object* v___f_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___f_2947_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2947_, 0, v_f_2945_);
v___x_2948_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2949_ = lean_array_get_size(v_as_2946_);
v___x_2950_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2948_, v___f_2947_, v_as_2946_, v___x_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg___lam__0(lean_object* v_p_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v___x_2953_; uint8_t v___x_2954_; 
lean_inc(v_a_2952_);
v___x_2953_ = lean_apply_1(v_p_2951_, v_a_2952_);
v___x_2954_ = lean_unbox(v___x_2953_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; 
lean_dec(v_a_2952_);
v___x_2955_ = lean_box(0);
return v___x_2955_;
}
else
{
lean_object* v___x_2956_; 
v___x_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2956_, 0, v_a_2952_);
return v___x_2956_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg(lean_object* v_p_2957_, lean_object* v_as_2958_){
_start:
{
lean_object* v___f_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___f_2959_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2959_, 0, v_p_2957_);
v___x_2960_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2961_ = lean_array_get_size(v_as_2958_);
v___x_2962_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2960_, v___f_2959_, v_as_2958_, v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f(lean_object* v_00_u03b1_2963_, lean_object* v_p_2964_, lean_object* v_as_2965_){
_start:
{
lean_object* v___f_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___f_2966_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2966_, 0, v_p_2964_);
v___x_2967_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2968_ = lean_array_get_size(v_as_2965_);
v___x_2969_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2967_, v___f_2966_, v_as_2965_, v___x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object* v_p_2970_, lean_object* v_as_2971_, lean_object* v_j_2972_){
_start:
{
lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2973_ = lean_array_get_size(v_as_2971_);
v___x_2974_ = lean_nat_dec_lt(v_j_2972_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; 
lean_dec(v_j_2972_);
lean_dec_ref(v_p_2970_);
v___x_2975_ = lean_box(0);
return v___x_2975_;
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2976_ = lean_array_fget_borrowed(v_as_2971_, v_j_2972_);
lean_inc_ref(v_p_2970_);
lean_inc(v___x_2976_);
v___x_2977_ = lean_apply_1(v_p_2970_, v___x_2976_);
v___x_2978_ = lean_unbox(v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = lean_unsigned_to_nat(1u);
v___x_2980_ = lean_nat_add(v_j_2972_, v___x_2979_);
lean_dec(v_j_2972_);
v_j_2972_ = v___x_2980_;
goto _start;
}
else
{
lean_object* v___x_2982_; 
lean_dec_ref(v_p_2970_);
v___x_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2982_, 0, v_j_2972_);
return v___x_2982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg___boxed(lean_object* v_p_2983_, lean_object* v_as_2984_, lean_object* v_j_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_Array_findIdx_x3f_loop___redArg(v_p_2983_, v_as_2984_, v_j_2985_);
lean_dec_ref(v_as_2984_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop(lean_object* v_00_u03b1_2987_, lean_object* v_p_2988_, lean_object* v_as_2989_, lean_object* v_j_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Array_findIdx_x3f_loop___redArg(v_p_2988_, v_as_2989_, v_j_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___boxed(lean_object* v_00_u03b1_2992_, lean_object* v_p_2993_, lean_object* v_as_2994_, lean_object* v_j_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Array_findIdx_x3f_loop(v_00_u03b1_2992_, v_p_2993_, v_as_2994_, v_j_2995_);
lean_dec_ref(v_as_2994_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg(lean_object* v_p_2997_, lean_object* v_as_2998_){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = lean_unsigned_to_nat(0u);
v___x_3000_ = l_Array_findIdx_x3f_loop___redArg(v_p_2997_, v_as_2998_, v___x_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg___boxed(lean_object* v_p_3001_, lean_object* v_as_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Array_findIdx_x3f___redArg(v_p_3001_, v_as_3002_);
lean_dec_ref(v_as_3002_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f(lean_object* v_00_u03b1_3004_, lean_object* v_p_3005_, lean_object* v_as_3006_){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = lean_unsigned_to_nat(0u);
v___x_3008_ = l_Array_findIdx_x3f_loop___redArg(v_p_3005_, v_as_3006_, v___x_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___boxed(lean_object* v_00_u03b1_3009_, lean_object* v_p_3010_, lean_object* v_as_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Array_findIdx_x3f(v_00_u03b1_3009_, v_p_3010_, v_as_3011_);
lean_dec_ref(v_as_3011_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(lean_object* v_p_3013_, lean_object* v_as_3014_, lean_object* v_j_3015_){
_start:
{
lean_object* v___x_3016_; uint8_t v___x_3017_; 
v___x_3016_ = lean_array_get_size(v_as_3014_);
v___x_3017_ = lean_nat_dec_lt(v_j_3015_, v___x_3016_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; 
lean_dec(v_j_3015_);
lean_dec_ref(v_p_3013_);
v___x_3018_ = lean_box(0);
return v___x_3018_;
}
else
{
lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; 
v___x_3019_ = lean_array_fget_borrowed(v_as_3014_, v_j_3015_);
lean_inc_ref(v_p_3013_);
lean_inc(v___x_3019_);
v___x_3020_ = lean_apply_1(v_p_3013_, v___x_3019_);
v___x_3021_ = lean_unbox(v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_unsigned_to_nat(1u);
v___x_3023_ = lean_nat_add(v_j_3015_, v___x_3022_);
lean_dec(v_j_3015_);
v_j_3015_ = v___x_3023_;
goto _start;
}
else
{
lean_object* v___x_3025_; 
lean_dec_ref(v_p_3013_);
v___x_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_j_3015_);
return v___x_3025_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg___boxed(lean_object* v_p_3026_, lean_object* v_as_3027_, lean_object* v_j_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3026_, v_as_3027_, v_j_3028_);
lean_dec_ref(v_as_3027_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object* v_00_u03b1_3030_, lean_object* v_p_3031_, lean_object* v_as_3032_, lean_object* v_j_3033_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3031_, v_as_3032_, v_j_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___boxed(lean_object* v_00_u03b1_3035_, lean_object* v_p_3036_, lean_object* v_as_3037_, lean_object* v_j_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(v_00_u03b1_3035_, v_p_3036_, v_as_3037_, v_j_3038_);
lean_dec_ref(v_as_3037_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg(lean_object* v_p_3040_, lean_object* v_as_3041_){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = lean_unsigned_to_nat(0u);
v___x_3043_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3040_, v_as_3041_, v___x_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg___boxed(lean_object* v_p_3044_, lean_object* v_as_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Array_findFinIdx_x3f___redArg(v_p_3044_, v_as_3045_);
lean_dec_ref(v_as_3045_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f(lean_object* v_00_u03b1_3047_, lean_object* v_p_3048_, lean_object* v_as_3049_){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_unsigned_to_nat(0u);
v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3048_, v_as_3049_, v___x_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_3052_, lean_object* v_p_3053_, lean_object* v_as_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Array_findFinIdx_x3f(v_00_u03b1_3052_, v_p_3053_, v_as_3054_);
lean_dec_ref(v_as_3054_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg(lean_object* v_p_3056_, lean_object* v_as_3057_){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = lean_unsigned_to_nat(0u);
v___x_3059_ = l_Array_findIdx_x3f_loop___redArg(v_p_3056_, v_as_3057_, v___x_3058_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v___x_3060_; 
v___x_3060_ = lean_array_get_size(v_as_3057_);
return v___x_3060_;
}
else
{
lean_object* v_val_3061_; 
v_val_3061_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_val_3061_);
lean_dec_ref_known(v___x_3059_, 1);
return v_val_3061_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg___boxed(lean_object* v_p_3062_, lean_object* v_as_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Array_findIdx___redArg(v_p_3062_, v_as_3063_);
lean_dec_ref(v_as_3063_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx(lean_object* v_00_u03b1_3065_, lean_object* v_p_3066_, lean_object* v_as_3067_){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_unsigned_to_nat(0u);
v___x_3069_ = l_Array_findIdx_x3f_loop___redArg(v_p_3066_, v_as_3067_, v___x_3068_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_array_get_size(v_as_3067_);
return v___x_3070_;
}
else
{
lean_object* v_val_3071_; 
v_val_3071_ = lean_ctor_get(v___x_3069_, 0);
lean_inc(v_val_3071_);
lean_dec_ref_known(v___x_3069_, 1);
return v_val_3071_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___boxed(lean_object* v_00_u03b1_3072_, lean_object* v_p_3073_, lean_object* v_as_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Array_findIdx(v_00_u03b1_3072_, v_p_3073_, v_as_3074_);
lean_dec_ref(v_as_3074_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg(lean_object* v_inst_3076_, lean_object* v_xs_3077_, lean_object* v_v_3078_, lean_object* v_i_3079_){
_start:
{
lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3080_ = lean_array_get_size(v_xs_3077_);
v___x_3081_ = lean_nat_dec_lt(v_i_3079_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; 
lean_dec(v_i_3079_);
lean_dec(v_v_3078_);
lean_dec_ref(v_inst_3076_);
v___x_3082_ = lean_box(0);
return v___x_3082_;
}
else
{
lean_object* v___x_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3083_ = lean_array_fget_borrowed(v_xs_3077_, v_i_3079_);
lean_inc_ref(v_inst_3076_);
lean_inc(v_v_3078_);
lean_inc(v___x_3083_);
v___x_3084_ = lean_apply_2(v_inst_3076_, v___x_3083_, v_v_3078_);
v___x_3085_ = lean_unbox(v___x_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = lean_unsigned_to_nat(1u);
v___x_3087_ = lean_nat_add(v_i_3079_, v___x_3086_);
lean_dec(v_i_3079_);
v_i_3079_ = v___x_3087_;
goto _start;
}
else
{
lean_object* v___x_3089_; 
lean_dec(v_v_3078_);
lean_dec_ref(v_inst_3076_);
v___x_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3089_, 0, v_i_3079_);
return v___x_3089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg___boxed(lean_object* v_inst_3090_, lean_object* v_xs_3091_, lean_object* v_v_3092_, lean_object* v_i_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Array_idxOfAux___redArg(v_inst_3090_, v_xs_3091_, v_v_3092_, v_i_3093_);
lean_dec_ref(v_xs_3091_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux(lean_object* v_00_u03b1_3095_, lean_object* v_inst_3096_, lean_object* v_xs_3097_, lean_object* v_v_3098_, lean_object* v_i_3099_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l_Array_idxOfAux___redArg(v_inst_3096_, v_xs_3097_, v_v_3098_, v_i_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___boxed(lean_object* v_00_u03b1_3101_, lean_object* v_inst_3102_, lean_object* v_xs_3103_, lean_object* v_v_3104_, lean_object* v_i_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Array_idxOfAux(v_00_u03b1_3101_, v_inst_3102_, v_xs_3103_, v_v_3104_, v_i_3105_);
lean_dec_ref(v_xs_3103_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg(lean_object* v_inst_3107_, lean_object* v_xs_3108_, lean_object* v_v_3109_){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = l_Array_idxOfAux___redArg(v_inst_3107_, v_xs_3108_, v_v_3109_, v___x_3110_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_3112_, lean_object* v_xs_3113_, lean_object* v_v_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Array_finIdxOf_x3f___redArg(v_inst_3112_, v_xs_3113_, v_v_3114_);
lean_dec_ref(v_xs_3113_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f(lean_object* v_00_u03b1_3116_, lean_object* v_inst_3117_, lean_object* v_xs_3118_, lean_object* v_v_3119_){
_start:
{
lean_object* v___x_3120_; 
v___x_3120_ = l_Array_finIdxOf_x3f___redArg(v_inst_3117_, v_xs_3118_, v_v_3119_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_3121_, lean_object* v_inst_3122_, lean_object* v_xs_3123_, lean_object* v_v_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Array_finIdxOf_x3f(v_00_u03b1_3121_, v_inst_3122_, v_xs_3123_, v_v_3124_);
lean_dec_ref(v_xs_3123_);
return v_res_3125_;
}
}
LEAN_EXPORT uint8_t l_Array_idxOf___redArg___lam__0(lean_object* v_inst_3126_, lean_object* v_a_3127_, lean_object* v_x_3128_){
_start:
{
lean_object* v___x_3129_; uint8_t v___x_3130_; 
v___x_3129_ = lean_apply_2(v_inst_3126_, v_x_3128_, v_a_3127_);
v___x_3130_ = lean_unbox(v___x_3129_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___lam__0___boxed(lean_object* v_inst_3131_, lean_object* v_a_3132_, lean_object* v_x_3133_){
_start:
{
uint8_t v_res_3134_; lean_object* v_r_3135_; 
v_res_3134_ = l_Array_idxOf___redArg___lam__0(v_inst_3131_, v_a_3132_, v_x_3133_);
v_r_3135_ = lean_box(v_res_3134_);
return v_r_3135_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg(lean_object* v_inst_3136_, lean_object* v_a_3137_, lean_object* v_as_3138_){
_start:
{
lean_object* v___f_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___f_3139_ = lean_alloc_closure((void*)(l_Array_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3139_, 0, v_inst_3136_);
lean_closure_set(v___f_3139_, 1, v_a_3137_);
v___x_3140_ = lean_unsigned_to_nat(0u);
v___x_3141_ = l_Array_findIdx_x3f_loop___redArg(v___f_3139_, v_as_3138_, v___x_3140_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v___x_3142_; 
v___x_3142_ = lean_array_get_size(v_as_3138_);
return v___x_3142_;
}
else
{
lean_object* v_val_3143_; 
v_val_3143_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_val_3143_);
lean_dec_ref_known(v___x_3141_, 1);
return v_val_3143_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___boxed(lean_object* v_inst_3144_, lean_object* v_a_3145_, lean_object* v_as_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l_Array_idxOf___redArg(v_inst_3144_, v_a_3145_, v_as_3146_);
lean_dec_ref(v_as_3146_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf(lean_object* v_00_u03b1_3148_, lean_object* v_inst_3149_, lean_object* v_a_3150_, lean_object* v_as_3151_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Array_idxOf___redArg(v_inst_3149_, v_a_3150_, v_as_3151_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___boxed(lean_object* v_00_u03b1_3153_, lean_object* v_inst_3154_, lean_object* v_a_3155_, lean_object* v_as_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_Array_idxOf(v_00_u03b1_3153_, v_inst_3154_, v_a_3155_, v_as_3156_);
lean_dec_ref(v_as_3156_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg(lean_object* v_inst_3158_, lean_object* v_xs_3159_, lean_object* v_v_3160_){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l_Array_finIdxOf_x3f___redArg(v_inst_3158_, v_xs_3159_, v_v_3160_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v___x_3162_; 
v___x_3162_ = lean_box(0);
return v___x_3162_;
}
else
{
lean_object* v_val_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
v_val_3163_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3161_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_val_3163_);
lean_dec(v___x_3161_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_val_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg___boxed(lean_object* v_inst_3171_, lean_object* v_xs_3172_, lean_object* v_v_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Array_idxOf_x3f___redArg(v_inst_3171_, v_xs_3172_, v_v_3173_);
lean_dec_ref(v_xs_3172_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f(lean_object* v_00_u03b1_3175_, lean_object* v_inst_3176_, lean_object* v_xs_3177_, lean_object* v_v_3178_){
_start:
{
lean_object* v___x_3179_; 
v___x_3179_ = l_Array_idxOf_x3f___redArg(v_inst_3176_, v_xs_3177_, v_v_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___boxed(lean_object* v_00_u03b1_3180_, lean_object* v_inst_3181_, lean_object* v_xs_3182_, lean_object* v_v_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Array_idxOf_x3f(v_00_u03b1_3180_, v_inst_3181_, v_xs_3182_, v_v_3183_);
lean_dec_ref(v_xs_3182_);
return v_res_3184_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg___lam__0(lean_object* v_p_3185_, lean_object* v_x_3186_){
_start:
{
lean_object* v___x_3187_; uint8_t v___x_3188_; 
v___x_3187_ = lean_apply_1(v_p_3185_, v_x_3186_);
v___x_3188_ = lean_unbox(v___x_3187_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___lam__0___boxed(lean_object* v_p_3189_, lean_object* v_x_3190_){
_start:
{
uint8_t v_res_3191_; lean_object* v_r_3192_; 
v_res_3191_ = l_Array_any___redArg___lam__0(v_p_3189_, v_x_3190_);
v_r_3192_ = lean_box(v_res_3191_);
return v_r_3192_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg(lean_object* v_as_3193_, lean_object* v_p_3194_, lean_object* v_start_3195_, lean_object* v_stop_3196_){
_start:
{
lean_object* v___x_3197_; uint8_t v___x_3198_; 
v___x_3197_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3198_ = lean_nat_dec_lt(v_start_3195_, v_stop_3196_);
if (v___x_3198_ == 0)
{
lean_dec(v_stop_3196_);
lean_dec_ref(v_p_3194_);
lean_dec_ref(v_as_3193_);
return v___x_3198_;
}
else
{
lean_object* v___f_3199_; lean_object* v___y_3201_; lean_object* v___x_3207_; uint8_t v___x_3208_; 
v___f_3199_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3199_, 0, v_p_3194_);
v___x_3207_ = lean_array_get_size(v_as_3193_);
v___x_3208_ = lean_nat_dec_le(v_stop_3196_, v___x_3207_);
if (v___x_3208_ == 0)
{
lean_dec(v_stop_3196_);
v___y_3201_ = v___x_3207_;
goto v___jp_3200_;
}
else
{
v___y_3201_ = v_stop_3196_;
goto v___jp_3200_;
}
v___jp_3200_:
{
uint8_t v___x_3202_; 
v___x_3202_ = lean_nat_dec_lt(v_start_3195_, v___y_3201_);
if (v___x_3202_ == 0)
{
lean_dec(v___y_3201_);
lean_dec_ref(v___f_3199_);
lean_dec_ref(v_as_3193_);
return v___x_3202_;
}
else
{
size_t v___x_3203_; size_t v___x_3204_; lean_object* v___x_3205_; uint8_t v___x_3206_; 
v___x_3203_ = lean_usize_of_nat(v_start_3195_);
v___x_3204_ = lean_usize_of_nat(v___y_3201_);
lean_dec(v___y_3201_);
v___x_3205_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3197_, v___f_3199_, v_as_3193_, v___x_3203_, v___x_3204_);
v___x_3206_ = lean_unbox(v___x_3205_);
lean_dec(v___x_3205_);
return v___x_3206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___boxed(lean_object* v_as_3209_, lean_object* v_p_3210_, lean_object* v_start_3211_, lean_object* v_stop_3212_){
_start:
{
uint8_t v_res_3213_; lean_object* v_r_3214_; 
v_res_3213_ = l_Array_any___redArg(v_as_3209_, v_p_3210_, v_start_3211_, v_stop_3212_);
lean_dec(v_start_3211_);
v_r_3214_ = lean_box(v_res_3213_);
return v_r_3214_;
}
}
LEAN_EXPORT uint8_t l_Array_any(lean_object* v_00_u03b1_3215_, lean_object* v_as_3216_, lean_object* v_p_3217_, lean_object* v_start_3218_, lean_object* v_stop_3219_){
_start:
{
lean_object* v___x_3220_; uint8_t v___x_3221_; 
v___x_3220_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3221_ = lean_nat_dec_lt(v_start_3218_, v_stop_3219_);
if (v___x_3221_ == 0)
{
lean_dec(v_stop_3219_);
lean_dec_ref(v_p_3217_);
lean_dec_ref(v_as_3216_);
return v___x_3221_;
}
else
{
lean_object* v___f_3222_; lean_object* v___y_3224_; lean_object* v___x_3230_; uint8_t v___x_3231_; 
v___f_3222_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3222_, 0, v_p_3217_);
v___x_3230_ = lean_array_get_size(v_as_3216_);
v___x_3231_ = lean_nat_dec_le(v_stop_3219_, v___x_3230_);
if (v___x_3231_ == 0)
{
lean_dec(v_stop_3219_);
v___y_3224_ = v___x_3230_;
goto v___jp_3223_;
}
else
{
v___y_3224_ = v_stop_3219_;
goto v___jp_3223_;
}
v___jp_3223_:
{
uint8_t v___x_3225_; 
v___x_3225_ = lean_nat_dec_lt(v_start_3218_, v___y_3224_);
if (v___x_3225_ == 0)
{
lean_dec(v___y_3224_);
lean_dec_ref(v___f_3222_);
lean_dec_ref(v_as_3216_);
return v___x_3225_;
}
else
{
size_t v___x_3226_; size_t v___x_3227_; lean_object* v___x_3228_; uint8_t v___x_3229_; 
v___x_3226_ = lean_usize_of_nat(v_start_3218_);
v___x_3227_ = lean_usize_of_nat(v___y_3224_);
lean_dec(v___y_3224_);
v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3220_, v___f_3222_, v_as_3216_, v___x_3226_, v___x_3227_);
v___x_3229_ = lean_unbox(v___x_3228_);
lean_dec(v___x_3228_);
return v___x_3229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___boxed(lean_object* v_00_u03b1_3232_, lean_object* v_as_3233_, lean_object* v_p_3234_, lean_object* v_start_3235_, lean_object* v_stop_3236_){
_start:
{
uint8_t v_res_3237_; lean_object* v_r_3238_; 
v_res_3237_ = l_Array_any(v_00_u03b1_3232_, v_as_3233_, v_p_3234_, v_start_3235_, v_stop_3236_);
lean_dec(v_start_3235_);
v_r_3238_ = lean_box(v_res_3237_);
return v_r_3238_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg___lam__0(lean_object* v_p_3239_, uint8_t v___x_3240_, lean_object* v_v_3241_){
_start:
{
lean_object* v___x_3242_; uint8_t v___x_3243_; 
v___x_3242_ = lean_apply_1(v_p_3239_, v_v_3241_);
v___x_3243_ = lean_unbox(v___x_3242_);
if (v___x_3243_ == 0)
{
return v___x_3240_;
}
else
{
uint8_t v___x_3244_; 
v___x_3244_ = 0;
return v___x_3244_;
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___lam__0___boxed(lean_object* v_p_3245_, lean_object* v___x_3246_, lean_object* v_v_3247_){
_start:
{
uint8_t v___x_339__boxed_3248_; uint8_t v_res_3249_; lean_object* v_r_3250_; 
v___x_339__boxed_3248_ = lean_unbox(v___x_3246_);
v_res_3249_ = l_Array_all___redArg___lam__0(v_p_3245_, v___x_339__boxed_3248_, v_v_3247_);
v_r_3250_ = lean_box(v_res_3249_);
return v_r_3250_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg(lean_object* v_as_3251_, lean_object* v_p_3252_, lean_object* v_start_3253_, lean_object* v_stop_3254_){
_start:
{
lean_object* v___x_3255_; uint8_t v___x_3256_; 
v___x_3255_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3256_ = lean_nat_dec_lt(v_start_3253_, v_stop_3254_);
if (v___x_3256_ == 0)
{
uint8_t v___x_3257_; 
lean_dec(v_stop_3254_);
lean_dec_ref(v_p_3252_);
lean_dec_ref(v_as_3251_);
v___x_3257_ = 1;
return v___x_3257_;
}
else
{
lean_object* v___x_3258_; lean_object* v___f_3259_; lean_object* v___y_3261_; lean_object* v___x_3268_; uint8_t v___x_3269_; 
v___x_3258_ = lean_box(v___x_3256_);
v___f_3259_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3259_, 0, v_p_3252_);
lean_closure_set(v___f_3259_, 1, v___x_3258_);
v___x_3268_ = lean_array_get_size(v_as_3251_);
v___x_3269_ = lean_nat_dec_le(v_stop_3254_, v___x_3268_);
if (v___x_3269_ == 0)
{
lean_dec(v_stop_3254_);
v___y_3261_ = v___x_3268_;
goto v___jp_3260_;
}
else
{
v___y_3261_ = v_stop_3254_;
goto v___jp_3260_;
}
v___jp_3260_:
{
uint8_t v___x_3262_; 
v___x_3262_ = lean_nat_dec_lt(v_start_3253_, v___y_3261_);
if (v___x_3262_ == 0)
{
lean_dec(v___y_3261_);
lean_dec_ref(v___f_3259_);
lean_dec_ref(v_as_3251_);
return v___x_3256_;
}
else
{
size_t v___x_3263_; size_t v___x_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; 
v___x_3263_ = lean_usize_of_nat(v_start_3253_);
v___x_3264_ = lean_usize_of_nat(v___y_3261_);
lean_dec(v___y_3261_);
v___x_3265_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3255_, v___f_3259_, v_as_3251_, v___x_3263_, v___x_3264_);
v___x_3266_ = lean_unbox(v___x_3265_);
lean_dec(v___x_3265_);
if (v___x_3266_ == 0)
{
return v___x_3262_;
}
else
{
uint8_t v___x_3267_; 
v___x_3267_ = 0;
return v___x_3267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___boxed(lean_object* v_as_3270_, lean_object* v_p_3271_, lean_object* v_start_3272_, lean_object* v_stop_3273_){
_start:
{
uint8_t v_res_3274_; lean_object* v_r_3275_; 
v_res_3274_ = l_Array_all___redArg(v_as_3270_, v_p_3271_, v_start_3272_, v_stop_3273_);
lean_dec(v_start_3272_);
v_r_3275_ = lean_box(v_res_3274_);
return v_r_3275_;
}
}
LEAN_EXPORT uint8_t l_Array_all(lean_object* v_00_u03b1_3276_, lean_object* v_as_3277_, lean_object* v_p_3278_, lean_object* v_start_3279_, lean_object* v_stop_3280_){
_start:
{
lean_object* v___x_3281_; uint8_t v___x_3282_; 
v___x_3281_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3282_ = lean_nat_dec_lt(v_start_3279_, v_stop_3280_);
if (v___x_3282_ == 0)
{
uint8_t v___x_3283_; 
lean_dec(v_stop_3280_);
lean_dec_ref(v_p_3278_);
lean_dec_ref(v_as_3277_);
v___x_3283_ = 1;
return v___x_3283_;
}
else
{
lean_object* v___x_3284_; lean_object* v___f_3285_; lean_object* v___y_3287_; lean_object* v___x_3294_; uint8_t v___x_3295_; 
v___x_3284_ = lean_box(v___x_3282_);
v___f_3285_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3285_, 0, v_p_3278_);
lean_closure_set(v___f_3285_, 1, v___x_3284_);
v___x_3294_ = lean_array_get_size(v_as_3277_);
v___x_3295_ = lean_nat_dec_le(v_stop_3280_, v___x_3294_);
if (v___x_3295_ == 0)
{
lean_dec(v_stop_3280_);
v___y_3287_ = v___x_3294_;
goto v___jp_3286_;
}
else
{
v___y_3287_ = v_stop_3280_;
goto v___jp_3286_;
}
v___jp_3286_:
{
uint8_t v___x_3288_; 
v___x_3288_ = lean_nat_dec_lt(v_start_3279_, v___y_3287_);
if (v___x_3288_ == 0)
{
lean_dec(v___y_3287_);
lean_dec_ref(v___f_3285_);
lean_dec_ref(v_as_3277_);
return v___x_3282_;
}
else
{
size_t v___x_3289_; size_t v___x_3290_; lean_object* v___x_3291_; uint8_t v___x_3292_; 
v___x_3289_ = lean_usize_of_nat(v_start_3279_);
v___x_3290_ = lean_usize_of_nat(v___y_3287_);
lean_dec(v___y_3287_);
v___x_3291_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3281_, v___f_3285_, v_as_3277_, v___x_3289_, v___x_3290_);
v___x_3292_ = lean_unbox(v___x_3291_);
lean_dec(v___x_3291_);
if (v___x_3292_ == 0)
{
return v___x_3288_;
}
else
{
uint8_t v___x_3293_; 
v___x_3293_ = 0;
return v___x_3293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___boxed(lean_object* v_00_u03b1_3296_, lean_object* v_as_3297_, lean_object* v_p_3298_, lean_object* v_start_3299_, lean_object* v_stop_3300_){
_start:
{
uint8_t v_res_3301_; lean_object* v_r_3302_; 
v_res_3301_ = l_Array_all(v_00_u03b1_3296_, v_as_3297_, v_p_3298_, v_start_3299_, v_stop_3300_);
lean_dec(v_start_3299_);
v_r_3302_ = lean_box(v_res_3301_);
return v_r_3302_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg___lam__0(lean_object* v_inst_3303_, lean_object* v_a_3304_, lean_object* v_x_3305_){
_start:
{
lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3306_ = lean_apply_2(v_inst_3303_, v_a_3304_, v_x_3305_);
v___x_3307_ = lean_unbox(v___x_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___lam__0___boxed(lean_object* v_inst_3308_, lean_object* v_a_3309_, lean_object* v_x_3310_){
_start:
{
uint8_t v_res_3311_; lean_object* v_r_3312_; 
v_res_3311_ = l_Array_contains___redArg___lam__0(v_inst_3308_, v_a_3309_, v_x_3310_);
v_r_3312_ = lean_box(v_res_3311_);
return v_r_3312_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg(lean_object* v_inst_3313_, lean_object* v_as_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; uint8_t v___x_3319_; 
v___x_3316_ = lean_unsigned_to_nat(0u);
v___x_3317_ = lean_array_get_size(v_as_3314_);
v___x_3318_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3319_ = lean_nat_dec_lt(v___x_3316_, v___x_3317_);
if (v___x_3319_ == 0)
{
lean_dec(v_a_3315_);
lean_dec_ref(v_as_3314_);
lean_dec_ref(v_inst_3313_);
return v___x_3319_;
}
else
{
if (v___x_3319_ == 0)
{
lean_dec(v_a_3315_);
lean_dec_ref(v_as_3314_);
lean_dec_ref(v_inst_3313_);
return v___x_3319_;
}
else
{
lean_object* v___f_3320_; size_t v___x_3321_; size_t v___x_3322_; lean_object* v___x_3323_; uint8_t v___x_3324_; 
v___f_3320_ = lean_alloc_closure((void*)(l_Array_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3320_, 0, v_inst_3313_);
lean_closure_set(v___f_3320_, 1, v_a_3315_);
v___x_3321_ = ((size_t)0ULL);
v___x_3322_ = lean_usize_of_nat(v___x_3317_);
v___x_3323_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3318_, v___f_3320_, v_as_3314_, v___x_3321_, v___x_3322_);
v___x_3324_ = lean_unbox(v___x_3323_);
lean_dec(v___x_3323_);
return v___x_3324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___boxed(lean_object* v_inst_3325_, lean_object* v_as_3326_, lean_object* v_a_3327_){
_start:
{
uint8_t v_res_3328_; lean_object* v_r_3329_; 
v_res_3328_ = l_Array_contains___redArg(v_inst_3325_, v_as_3326_, v_a_3327_);
v_r_3329_ = lean_box(v_res_3328_);
return v_r_3329_;
}
}
LEAN_EXPORT uint8_t l_Array_contains(lean_object* v_00_u03b1_3330_, lean_object* v_inst_3331_, lean_object* v_as_3332_, lean_object* v_a_3333_){
_start:
{
uint8_t v___x_3334_; 
v___x_3334_ = l_Array_contains___redArg(v_inst_3331_, v_as_3332_, v_a_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___boxed(lean_object* v_00_u03b1_3335_, lean_object* v_inst_3336_, lean_object* v_as_3337_, lean_object* v_a_3338_){
_start:
{
uint8_t v_res_3339_; lean_object* v_r_3340_; 
v_res_3339_ = l_Array_contains(v_00_u03b1_3335_, v_inst_3336_, v_as_3337_, v_a_3338_);
v_r_3340_ = lean_box(v_res_3339_);
return v_r_3340_;
}
}
LEAN_EXPORT uint8_t l_Array_elem___redArg(lean_object* v_inst_3341_, lean_object* v_a_3342_, lean_object* v_as_3343_){
_start:
{
uint8_t v___x_3344_; 
v___x_3344_ = l_Array_contains___redArg(v_inst_3341_, v_as_3343_, v_a_3342_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___redArg___boxed(lean_object* v_inst_3345_, lean_object* v_a_3346_, lean_object* v_as_3347_){
_start:
{
uint8_t v_res_3348_; lean_object* v_r_3349_; 
v_res_3348_ = l_Array_elem___redArg(v_inst_3345_, v_a_3346_, v_as_3347_);
v_r_3349_ = lean_box(v_res_3348_);
return v_r_3349_;
}
}
LEAN_EXPORT uint8_t l_Array_elem(lean_object* v_00_u03b1_3350_, lean_object* v_inst_3351_, lean_object* v_a_3352_, lean_object* v_as_3353_){
_start:
{
uint8_t v___x_3354_; 
v___x_3354_ = l_Array_contains___redArg(v_inst_3351_, v_as_3353_, v_a_3352_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___boxed(lean_object* v_00_u03b1_3355_, lean_object* v_inst_3356_, lean_object* v_a_3357_, lean_object* v_as_3358_){
_start:
{
uint8_t v_res_3359_; lean_object* v_r_3360_; 
v_res_3359_ = l_Array_elem(v_00_u03b1_3355_, v_inst_3356_, v_a_3357_, v_as_3358_);
v_r_3360_ = lean_box(v_res_3359_);
return v_r_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(lean_object* v_as_3361_, size_t v_i_3362_, size_t v_stop_3363_, lean_object* v_b_3364_){
_start:
{
uint8_t v___x_3365_; 
v___x_3365_ = lean_usize_dec_eq(v_i_3362_, v_stop_3363_);
if (v___x_3365_ == 0)
{
size_t v___x_3366_; size_t v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3366_ = ((size_t)1ULL);
v___x_3367_ = lean_usize_sub(v_i_3362_, v___x_3366_);
v___x_3368_ = lean_array_uget_borrowed(v_as_3361_, v___x_3367_);
lean_inc(v___x_3368_);
v___x_3369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
lean_ctor_set(v___x_3369_, 1, v_b_3364_);
v_i_3362_ = v___x_3367_;
v_b_3364_ = v___x_3369_;
goto _start;
}
else
{
return v_b_3364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg___boxed(lean_object* v_as_3371_, lean_object* v_i_3372_, lean_object* v_stop_3373_, lean_object* v_b_3374_){
_start:
{
size_t v_i_boxed_3375_; size_t v_stop_boxed_3376_; lean_object* v_res_3377_; 
v_i_boxed_3375_ = lean_unbox_usize(v_i_3372_);
lean_dec(v_i_3372_);
v_stop_boxed_3376_ = lean_unbox_usize(v_stop_3373_);
lean_dec(v_stop_3373_);
v_res_3377_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3371_, v_i_boxed_3375_, v_stop_boxed_3376_, v_b_3374_);
lean_dec_ref(v_as_3371_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg(lean_object* v_as_3378_){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3379_ = lean_box(0);
v___x_3380_ = lean_array_get_size(v_as_3378_);
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = lean_nat_dec_lt(v___x_3381_, v___x_3380_);
if (v___x_3382_ == 0)
{
return v___x_3379_;
}
else
{
size_t v___x_3383_; size_t v___x_3384_; lean_object* v___x_3385_; 
v___x_3383_ = lean_usize_of_nat(v___x_3380_);
v___x_3384_ = ((size_t)0ULL);
v___x_3385_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3378_, v___x_3383_, v___x_3384_, v___x_3379_);
return v___x_3385_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg___boxed(lean_object* v_as_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Array_toListImpl___redArg(v_as_3386_);
lean_dec_ref(v_as_3386_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* lean_array_to_list_impl(lean_object* v_00_u03b1_3388_, lean_object* v_as_3389_){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = l_Array_toListImpl___redArg(v_as_3389_);
lean_dec_ref(v_as_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(lean_object* v_00_u03b1_3391_, lean_object* v_as_3392_, size_t v_i_3393_, size_t v_stop_3394_, lean_object* v_b_3395_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3392_, v_i_3393_, v_stop_3394_, v_b_3395_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___boxed(lean_object* v_00_u03b1_3397_, lean_object* v_as_3398_, lean_object* v_i_3399_, lean_object* v_stop_3400_, lean_object* v_b_3401_){
_start:
{
size_t v_i_boxed_3402_; size_t v_stop_boxed_3403_; lean_object* v_res_3404_; 
v_i_boxed_3402_ = lean_unbox_usize(v_i_3399_);
lean_dec(v_i_3399_);
v_stop_boxed_3403_ = lean_unbox_usize(v_stop_3400_);
lean_dec(v_stop_3400_);
v_res_3404_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(v_00_u03b1_3397_, v_as_3398_, v_i_boxed_3402_, v_stop_boxed_3403_, v_b_3401_);
lean_dec_ref(v_as_3398_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg___lam__0(lean_object* v_x1_3405_, lean_object* v_x2_3406_){
_start:
{
lean_object* v___x_3407_; 
v___x_3407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3407_, 0, v_x1_3405_);
lean_ctor_set(v___x_3407_, 1, v_x2_3406_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg(lean_object* v_as_3409_, lean_object* v_l_3410_){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3411_ = lean_array_get_size(v_as_3409_);
v___x_3412_ = lean_unsigned_to_nat(0u);
v___x_3413_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3414_ = lean_nat_dec_lt(v___x_3412_, v___x_3411_);
if (v___x_3414_ == 0)
{
lean_dec_ref(v_as_3409_);
return v_l_3410_;
}
else
{
lean_object* v___f_3415_; size_t v___x_3416_; size_t v___x_3417_; lean_object* v___x_3418_; 
v___f_3415_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3416_ = lean_usize_of_nat(v___x_3411_);
v___x_3417_ = ((size_t)0ULL);
v___x_3418_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3413_, v___f_3415_, v_as_3409_, v___x_3416_, v___x_3417_, v_l_3410_);
return v___x_3418_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend(lean_object* v_00_u03b1_3419_, lean_object* v_as_3420_, lean_object* v_l_3421_){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v___x_3422_ = lean_array_get_size(v_as_3420_);
v___x_3423_ = lean_unsigned_to_nat(0u);
v___x_3424_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3425_ = lean_nat_dec_lt(v___x_3423_, v___x_3422_);
if (v___x_3425_ == 0)
{
lean_dec_ref(v_as_3420_);
return v_l_3421_;
}
else
{
lean_object* v___f_3426_; size_t v___x_3427_; size_t v___x_3428_; lean_object* v___x_3429_; 
v___f_3426_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3427_ = lean_usize_of_nat(v___x_3422_);
v___x_3428_ = ((size_t)0ULL);
v___x_3429_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3424_, v___f_3426_, v_as_3420_, v___x_3427_, v___x_3428_, v_l_3421_);
return v___x_3429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(lean_object* v_as_3430_, size_t v_i_3431_, size_t v_stop_3432_, lean_object* v_b_3433_){
_start:
{
uint8_t v___x_3434_; 
v___x_3434_ = lean_usize_dec_eq(v_i_3431_, v_stop_3432_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3436_; size_t v___x_3437_; size_t v___x_3438_; 
v___x_3435_ = lean_array_uget_borrowed(v_as_3430_, v_i_3431_);
lean_inc(v___x_3435_);
v___x_3436_ = lean_array_push(v_b_3433_, v___x_3435_);
v___x_3437_ = ((size_t)1ULL);
v___x_3438_ = lean_usize_add(v_i_3431_, v___x_3437_);
v_i_3431_ = v___x_3438_;
v_b_3433_ = v___x_3436_;
goto _start;
}
else
{
return v_b_3433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg___boxed(lean_object* v_as_3440_, lean_object* v_i_3441_, lean_object* v_stop_3442_, lean_object* v_b_3443_){
_start:
{
size_t v_i_boxed_3444_; size_t v_stop_boxed_3445_; lean_object* v_res_3446_; 
v_i_boxed_3444_ = lean_unbox_usize(v_i_3441_);
lean_dec(v_i_3441_);
v_stop_boxed_3445_ = lean_unbox_usize(v_stop_3442_);
lean_dec(v_stop_3442_);
v_res_3446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3440_, v_i_boxed_3444_, v_stop_boxed_3445_, v_b_3443_);
lean_dec_ref(v_as_3440_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg(lean_object* v_as_3447_, lean_object* v_bs_3448_){
_start:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; uint8_t v___x_3451_; 
v___x_3449_ = lean_unsigned_to_nat(0u);
v___x_3450_ = lean_array_get_size(v_bs_3448_);
v___x_3451_ = lean_nat_dec_lt(v___x_3449_, v___x_3450_);
if (v___x_3451_ == 0)
{
return v_as_3447_;
}
else
{
uint8_t v___x_3452_; 
v___x_3452_ = lean_nat_dec_le(v___x_3450_, v___x_3450_);
if (v___x_3452_ == 0)
{
if (v___x_3451_ == 0)
{
return v_as_3447_;
}
else
{
size_t v___x_3453_; size_t v___x_3454_; lean_object* v___x_3455_; 
v___x_3453_ = ((size_t)0ULL);
v___x_3454_ = lean_usize_of_nat(v___x_3450_);
v___x_3455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3448_, v___x_3453_, v___x_3454_, v_as_3447_);
return v___x_3455_;
}
}
else
{
size_t v___x_3456_; size_t v___x_3457_; lean_object* v___x_3458_; 
v___x_3456_ = ((size_t)0ULL);
v___x_3457_ = lean_usize_of_nat(v___x_3450_);
v___x_3458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3448_, v___x_3456_, v___x_3457_, v_as_3447_);
return v___x_3458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg___boxed(lean_object* v_as_3459_, lean_object* v_bs_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Array_append___redArg(v_as_3459_, v_bs_3460_);
lean_dec_ref(v_bs_3460_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Array_append(lean_object* v_00_u03b1_3462_, lean_object* v_as_3463_, lean_object* v_bs_3464_){
_start:
{
lean_object* v___x_3465_; 
v___x_3465_ = l_Array_append___redArg(v_as_3463_, v_bs_3464_);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l_Array_append___boxed(lean_object* v_00_u03b1_3466_, lean_object* v_as_3467_, lean_object* v_bs_3468_){
_start:
{
lean_object* v_res_3469_; 
v_res_3469_ = l_Array_append(v_00_u03b1_3466_, v_as_3467_, v_bs_3468_);
lean_dec_ref(v_bs_3468_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(lean_object* v_00_u03b1_3470_, lean_object* v_as_3471_, size_t v_i_3472_, size_t v_stop_3473_, lean_object* v_b_3474_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3471_, v_i_3472_, v_stop_3473_, v_b_3474_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___boxed(lean_object* v_00_u03b1_3476_, lean_object* v_as_3477_, lean_object* v_i_3478_, lean_object* v_stop_3479_, lean_object* v_b_3480_){
_start:
{
size_t v_i_boxed_3481_; size_t v_stop_boxed_3482_; lean_object* v_res_3483_; 
v_i_boxed_3481_ = lean_unbox_usize(v_i_3478_);
lean_dec(v_i_3478_);
v_stop_boxed_3482_ = lean_unbox_usize(v_stop_3479_);
lean_dec(v_stop_3479_);
v_res_3483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(v_00_u03b1_3476_, v_as_3477_, v_i_boxed_3481_, v_stop_boxed_3482_, v_b_3480_);
lean_dec_ref(v_as_3477_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend(lean_object* v_00_u03b1_3485_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = ((lean_object*)(l_Array_instAppend___closed__0));
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object* v_x_3487_, lean_object* v_x_3488_){
_start:
{
if (lean_obj_tag(v_x_3488_) == 0)
{
return v_x_3487_;
}
else
{
lean_object* v_head_3489_; lean_object* v_tail_3490_; lean_object* v___x_3491_; 
v_head_3489_ = lean_ctor_get(v_x_3488_, 0);
lean_inc(v_head_3489_);
v_tail_3490_ = lean_ctor_get(v_x_3488_, 1);
lean_inc(v_tail_3490_);
lean_dec_ref_known(v_x_3488_, 2);
v___x_3491_ = lean_array_push(v_x_3487_, v_head_3489_);
v_x_3487_ = v___x_3491_;
v_x_3488_ = v_tail_3490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_appendList___redArg(lean_object* v_as_3493_, lean_object* v_bs_3494_){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3493_, v_bs_3494_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Array_appendList(lean_object* v_00_u03b1_3496_, lean_object* v_as_3497_, lean_object* v_bs_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3497_, v_bs_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0(lean_object* v_00_u03b1_3500_, lean_object* v_x_3501_, lean_object* v_x_3502_){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_3501_, v_x_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList(lean_object* v_00_u03b1_3505_){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = ((lean_object*)(l_Array_instHAppendList___closed__0));
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
v___x_3531_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
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
lean_object* v___f_3535_; uint8_t v___x_3536_; 
lean_inc(v_toBind_3528_);
lean_inc(v_toPure_3529_);
v___f_3535_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3535_, 0, v_toPure_3529_);
lean_closure_set(v___f_3535_, 1, v_f_3525_);
lean_closure_set(v___f_3535_, 2, v_toBind_3528_);
v___x_3536_ = lean_nat_dec_le(v___x_3532_, v___x_3532_);
if (v___x_3536_ == 0)
{
if (v___x_3533_ == 0)
{
lean_object* v___x_3537_; 
lean_inc(v_toPure_3529_);
lean_dec_ref(v___f_3535_);
lean_dec_ref(v_as_3526_);
lean_dec_ref(v_inst_3524_);
v___x_3537_ = lean_apply_2(v_toPure_3529_, lean_box(0), v___x_3531_);
return v___x_3537_;
}
else
{
size_t v___x_3538_; size_t v___x_3539_; lean_object* v___x_3540_; 
v___x_3538_ = ((size_t)0ULL);
v___x_3539_ = lean_usize_of_nat(v___x_3532_);
v___x_3540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3524_, v___f_3535_, v_as_3526_, v___x_3538_, v___x_3539_, v___x_3531_);
return v___x_3540_;
}
}
else
{
size_t v___x_3541_; size_t v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = ((size_t)0ULL);
v___x_3542_ = lean_usize_of_nat(v___x_3532_);
v___x_3543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3524_, v___f_3535_, v_as_3526_, v___x_3541_, v___x_3542_, v___x_3531_);
return v___x_3543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM(lean_object* v_00_u03b1_3544_, lean_object* v_m_3545_, lean_object* v_00_u03b2_3546_, lean_object* v_inst_3547_, lean_object* v_f_3548_, lean_object* v_as_3549_){
_start:
{
lean_object* v_toApplicative_3550_; lean_object* v_toBind_3551_; lean_object* v_toPure_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
v_toApplicative_3550_ = lean_ctor_get(v_inst_3547_, 0);
v_toBind_3551_ = lean_ctor_get(v_inst_3547_, 1);
v_toPure_3552_ = lean_ctor_get(v_toApplicative_3550_, 1);
v___x_3553_ = lean_unsigned_to_nat(0u);
v___x_3554_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3555_ = lean_array_get_size(v_as_3549_);
v___x_3556_ = lean_nat_dec_lt(v___x_3553_, v___x_3555_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; 
lean_inc(v_toPure_3552_);
lean_dec_ref(v_as_3549_);
lean_dec(v_f_3548_);
lean_dec_ref(v_inst_3547_);
v___x_3557_ = lean_apply_2(v_toPure_3552_, lean_box(0), v___x_3554_);
return v___x_3557_;
}
else
{
lean_object* v___f_3558_; uint8_t v___x_3559_; 
lean_inc(v_toBind_3551_);
lean_inc(v_toPure_3552_);
v___f_3558_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3558_, 0, v_toPure_3552_);
lean_closure_set(v___f_3558_, 1, v_f_3548_);
lean_closure_set(v___f_3558_, 2, v_toBind_3551_);
v___x_3559_ = lean_nat_dec_le(v___x_3555_, v___x_3555_);
if (v___x_3559_ == 0)
{
if (v___x_3556_ == 0)
{
lean_object* v___x_3560_; 
lean_inc(v_toPure_3552_);
lean_dec_ref(v___f_3558_);
lean_dec_ref(v_as_3549_);
lean_dec_ref(v_inst_3547_);
v___x_3560_ = lean_apply_2(v_toPure_3552_, lean_box(0), v___x_3554_);
return v___x_3560_;
}
else
{
size_t v___x_3561_; size_t v___x_3562_; lean_object* v___x_3563_; 
v___x_3561_ = ((size_t)0ULL);
v___x_3562_ = lean_usize_of_nat(v___x_3555_);
v___x_3563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3547_, v___f_3558_, v_as_3549_, v___x_3561_, v___x_3562_, v___x_3554_);
return v___x_3563_;
}
}
else
{
size_t v___x_3564_; size_t v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = ((size_t)0ULL);
v___x_3565_ = lean_usize_of_nat(v___x_3555_);
v___x_3566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3547_, v___f_3558_, v_as_3549_, v___x_3564_, v___x_3565_, v___x_3554_);
return v___x_3566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg___lam__0(lean_object* v_f_3567_, lean_object* v_x1_3568_, lean_object* v_x2_3569_){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = lean_apply_1(v_f_3567_, v_x2_3569_);
v___x_3571_ = l_Array_append___redArg(v_x1_3568_, v___x_3570_);
lean_dec_ref(v___x_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg(lean_object* v_f_3572_, lean_object* v_as_3573_){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3574_ = lean_unsigned_to_nat(0u);
v___x_3575_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3576_ = lean_array_get_size(v_as_3573_);
v___x_3577_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3578_ = lean_nat_dec_lt(v___x_3574_, v___x_3576_);
if (v___x_3578_ == 0)
{
lean_dec_ref(v_as_3573_);
lean_dec_ref(v_f_3572_);
return v___x_3575_;
}
else
{
lean_object* v___f_3579_; uint8_t v___x_3580_; 
v___f_3579_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3579_, 0, v_f_3572_);
v___x_3580_ = lean_nat_dec_le(v___x_3576_, v___x_3576_);
if (v___x_3580_ == 0)
{
if (v___x_3578_ == 0)
{
lean_dec_ref(v___f_3579_);
lean_dec_ref(v_as_3573_);
return v___x_3575_;
}
else
{
size_t v___x_3581_; size_t v___x_3582_; lean_object* v___x_3583_; 
v___x_3581_ = ((size_t)0ULL);
v___x_3582_ = lean_usize_of_nat(v___x_3576_);
v___x_3583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3577_, v___f_3579_, v_as_3573_, v___x_3581_, v___x_3582_, v___x_3575_);
return v___x_3583_;
}
}
else
{
size_t v___x_3584_; size_t v___x_3585_; lean_object* v___x_3586_; 
v___x_3584_ = ((size_t)0ULL);
v___x_3585_ = lean_usize_of_nat(v___x_3576_);
v___x_3586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3577_, v___f_3579_, v_as_3573_, v___x_3584_, v___x_3585_, v___x_3575_);
return v___x_3586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap(lean_object* v_00_u03b1_3587_, lean_object* v_00_u03b2_3588_, lean_object* v_f_3589_, lean_object* v_as_3590_){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; uint8_t v___x_3595_; 
v___x_3591_ = lean_unsigned_to_nat(0u);
v___x_3592_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3593_ = lean_array_get_size(v_as_3590_);
v___x_3594_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3595_ = lean_nat_dec_lt(v___x_3591_, v___x_3593_);
if (v___x_3595_ == 0)
{
lean_dec_ref(v_as_3590_);
lean_dec_ref(v_f_3589_);
return v___x_3592_;
}
else
{
lean_object* v___f_3596_; uint8_t v___x_3597_; 
v___f_3596_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3596_, 0, v_f_3589_);
v___x_3597_ = lean_nat_dec_le(v___x_3593_, v___x_3593_);
if (v___x_3597_ == 0)
{
if (v___x_3595_ == 0)
{
lean_dec_ref(v___f_3596_);
lean_dec_ref(v_as_3590_);
return v___x_3592_;
}
else
{
size_t v___x_3598_; size_t v___x_3599_; lean_object* v___x_3600_; 
v___x_3598_ = ((size_t)0ULL);
v___x_3599_ = lean_usize_of_nat(v___x_3593_);
v___x_3600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3594_, v___f_3596_, v_as_3590_, v___x_3598_, v___x_3599_, v___x_3592_);
return v___x_3600_;
}
}
else
{
size_t v___x_3601_; size_t v___x_3602_; lean_object* v___x_3603_; 
v___x_3601_ = ((size_t)0ULL);
v___x_3602_ = lean_usize_of_nat(v___x_3593_);
v___x_3603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3594_, v___f_3596_, v_as_3590_, v___x_3601_, v___x_3602_, v___x_3592_);
return v___x_3603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten___redArg(lean_object* v_xss_3605_){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; 
v___x_3606_ = lean_unsigned_to_nat(0u);
v___x_3607_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3608_ = lean_array_get_size(v_xss_3605_);
v___x_3609_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3610_ = lean_nat_dec_lt(v___x_3606_, v___x_3608_);
if (v___x_3610_ == 0)
{
lean_dec_ref(v_xss_3605_);
return v___x_3607_;
}
else
{
lean_object* v___f_3611_; uint8_t v___x_3612_; 
v___f_3611_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3612_ = lean_nat_dec_le(v___x_3608_, v___x_3608_);
if (v___x_3612_ == 0)
{
if (v___x_3610_ == 0)
{
lean_dec_ref(v_xss_3605_);
return v___x_3607_;
}
else
{
size_t v___x_3613_; size_t v___x_3614_; lean_object* v___x_3615_; 
v___x_3613_ = ((size_t)0ULL);
v___x_3614_ = lean_usize_of_nat(v___x_3608_);
v___x_3615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3609_, v___f_3611_, v_xss_3605_, v___x_3613_, v___x_3614_, v___x_3607_);
return v___x_3615_;
}
}
else
{
size_t v___x_3616_; size_t v___x_3617_; lean_object* v___x_3618_; 
v___x_3616_ = ((size_t)0ULL);
v___x_3617_ = lean_usize_of_nat(v___x_3608_);
v___x_3618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3609_, v___f_3611_, v_xss_3605_, v___x_3616_, v___x_3617_, v___x_3607_);
return v___x_3618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten(lean_object* v_00_u03b1_3619_, lean_object* v_xss_3620_){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; 
v___x_3621_ = lean_unsigned_to_nat(0u);
v___x_3622_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3623_ = lean_array_get_size(v_xss_3620_);
v___x_3624_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3625_ = lean_nat_dec_lt(v___x_3621_, v___x_3623_);
if (v___x_3625_ == 0)
{
lean_dec_ref(v_xss_3620_);
return v___x_3622_;
}
else
{
lean_object* v___f_3626_; uint8_t v___x_3627_; 
v___f_3626_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3627_ = lean_nat_dec_le(v___x_3623_, v___x_3623_);
if (v___x_3627_ == 0)
{
if (v___x_3625_ == 0)
{
lean_dec_ref(v_xss_3620_);
return v___x_3622_;
}
else
{
size_t v___x_3628_; size_t v___x_3629_; lean_object* v___x_3630_; 
v___x_3628_ = ((size_t)0ULL);
v___x_3629_ = lean_usize_of_nat(v___x_3623_);
v___x_3630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3624_, v___f_3626_, v_xss_3620_, v___x_3628_, v___x_3629_, v___x_3622_);
return v___x_3630_;
}
}
else
{
size_t v___x_3631_; size_t v___x_3632_; lean_object* v___x_3633_; 
v___x_3631_ = ((size_t)0ULL);
v___x_3632_ = lean_usize_of_nat(v___x_3623_);
v___x_3633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3624_, v___f_3626_, v_xss_3620_, v___x_3631_, v___x_3632_, v___x_3622_);
return v___x_3633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop___redArg(lean_object* v_as_3634_, lean_object* v_i_3635_, lean_object* v_j_3636_){
_start:
{
uint8_t v___x_3637_; 
v___x_3637_ = lean_nat_dec_lt(v_i_3635_, v_j_3636_);
if (v___x_3637_ == 0)
{
lean_dec(v_j_3636_);
lean_dec(v_i_3635_);
return v_as_3634_;
}
else
{
lean_object* v_as_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v_as_3638_ = lean_array_fswap(v_as_3634_, v_i_3635_, v_j_3636_);
v___x_3639_ = lean_unsigned_to_nat(1u);
v___x_3640_ = lean_nat_add(v_i_3635_, v___x_3639_);
lean_dec(v_i_3635_);
v___x_3641_ = lean_nat_sub(v_j_3636_, v___x_3639_);
lean_dec(v_j_3636_);
v_as_3634_ = v_as_3638_;
v_i_3635_ = v___x_3640_;
v_j_3636_ = v___x_3641_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop(lean_object* v_00_u03b1_3643_, lean_object* v_as_3644_, lean_object* v_i_3645_, lean_object* v_j_3646_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Array_reverse_loop___redArg(v_as_3644_, v_i_3645_, v_j_3646_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Array_reverse___redArg(lean_object* v_as_3648_){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; uint8_t v___x_3651_; 
v___x_3649_ = lean_array_get_size(v_as_3648_);
v___x_3650_ = lean_unsigned_to_nat(1u);
v___x_3651_ = lean_nat_dec_le(v___x_3649_, v___x_3650_);
if (v___x_3651_ == 0)
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3652_ = lean_unsigned_to_nat(0u);
v___x_3653_ = lean_nat_sub(v___x_3649_, v___x_3650_);
v___x_3654_ = l_Array_reverse_loop___redArg(v_as_3648_, v___x_3652_, v___x_3653_);
return v___x_3654_;
}
else
{
return v_as_3648_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse(lean_object* v_00_u03b1_3655_, lean_object* v_as_3656_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Array_reverse___redArg(v_as_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___lam__0(lean_object* v_p_3658_, lean_object* v_x1_3659_, lean_object* v_x2_3660_){
_start:
{
lean_object* v___x_3661_; uint8_t v___x_3662_; 
lean_inc(v_x2_3660_);
v___x_3661_ = lean_apply_1(v_p_3658_, v_x2_3660_);
v___x_3662_ = lean_unbox(v___x_3661_);
if (v___x_3662_ == 0)
{
lean_dec(v_x2_3660_);
return v_x1_3659_;
}
else
{
lean_object* v___x_3663_; 
v___x_3663_ = lean_array_push(v_x1_3659_, v_x2_3660_);
return v___x_3663_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg(lean_object* v_p_3666_, lean_object* v_as_3667_, lean_object* v_start_3668_, lean_object* v_stop_3669_){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; uint8_t v___x_3672_; 
v___x_3670_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3671_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3672_ = lean_nat_dec_lt(v_start_3668_, v_stop_3669_);
if (v___x_3672_ == 0)
{
lean_dec_ref(v_as_3667_);
lean_dec_ref(v_p_3666_);
return v___x_3670_;
}
else
{
lean_object* v___f_3673_; lean_object* v___x_3674_; uint8_t v___x_3675_; 
v___f_3673_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3673_, 0, v_p_3666_);
v___x_3674_ = lean_array_get_size(v_as_3667_);
v___x_3675_ = lean_nat_dec_le(v_stop_3669_, v___x_3674_);
if (v___x_3675_ == 0)
{
uint8_t v___x_3676_; 
v___x_3676_ = lean_nat_dec_lt(v_start_3668_, v___x_3674_);
if (v___x_3676_ == 0)
{
lean_dec_ref(v___f_3673_);
lean_dec_ref(v_as_3667_);
return v___x_3670_;
}
else
{
size_t v___x_3677_; size_t v___x_3678_; lean_object* v___x_3679_; 
v___x_3677_ = lean_usize_of_nat(v_start_3668_);
v___x_3678_ = lean_usize_of_nat(v___x_3674_);
v___x_3679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3671_, v___f_3673_, v_as_3667_, v___x_3677_, v___x_3678_, v___x_3670_);
return v___x_3679_;
}
}
else
{
size_t v___x_3680_; size_t v___x_3681_; lean_object* v___x_3682_; 
v___x_3680_ = lean_usize_of_nat(v_start_3668_);
v___x_3681_ = lean_usize_of_nat(v_stop_3669_);
v___x_3682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3671_, v___f_3673_, v_as_3667_, v___x_3680_, v___x_3681_, v___x_3670_);
return v___x_3682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___boxed(lean_object* v_p_3683_, lean_object* v_as_3684_, lean_object* v_start_3685_, lean_object* v_stop_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Array_filter___redArg(v_p_3683_, v_as_3684_, v_start_3685_, v_stop_3686_);
lean_dec(v_stop_3686_);
lean_dec(v_start_3685_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Array_filter(lean_object* v_00_u03b1_3688_, lean_object* v_p_3689_, lean_object* v_as_3690_, lean_object* v_start_3691_, lean_object* v_stop_3692_){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; uint8_t v___x_3695_; 
v___x_3693_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3694_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3695_ = lean_nat_dec_lt(v_start_3691_, v_stop_3692_);
if (v___x_3695_ == 0)
{
lean_dec_ref(v_as_3690_);
lean_dec_ref(v_p_3689_);
return v___x_3693_;
}
else
{
lean_object* v___f_3696_; lean_object* v___x_3697_; uint8_t v___x_3698_; 
v___f_3696_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3696_, 0, v_p_3689_);
v___x_3697_ = lean_array_get_size(v_as_3690_);
v___x_3698_ = lean_nat_dec_le(v_stop_3692_, v___x_3697_);
if (v___x_3698_ == 0)
{
uint8_t v___x_3699_; 
v___x_3699_ = lean_nat_dec_lt(v_start_3691_, v___x_3697_);
if (v___x_3699_ == 0)
{
lean_dec_ref(v___f_3696_);
lean_dec_ref(v_as_3690_);
return v___x_3693_;
}
else
{
size_t v___x_3700_; size_t v___x_3701_; lean_object* v___x_3702_; 
v___x_3700_ = lean_usize_of_nat(v_start_3691_);
v___x_3701_ = lean_usize_of_nat(v___x_3697_);
v___x_3702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3694_, v___f_3696_, v_as_3690_, v___x_3700_, v___x_3701_, v___x_3693_);
return v___x_3702_;
}
}
else
{
size_t v___x_3703_; size_t v___x_3704_; lean_object* v___x_3705_; 
v___x_3703_ = lean_usize_of_nat(v_start_3691_);
v___x_3704_ = lean_usize_of_nat(v_stop_3692_);
v___x_3705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3694_, v___f_3696_, v_as_3690_, v___x_3703_, v___x_3704_, v___x_3693_);
return v___x_3705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___boxed(lean_object* v_00_u03b1_3706_, lean_object* v_p_3707_, lean_object* v_as_3708_, lean_object* v_start_3709_, lean_object* v_stop_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Array_filter(v_00_u03b1_3706_, v_p_3707_, v_as_3708_, v_start_3709_, v_stop_3710_);
lean_dec(v_stop_3710_);
lean_dec(v_start_3709_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0(lean_object* v_toApplicative_3712_, lean_object* v_acc_3713_, lean_object* v_a_3714_, uint8_t v_____do__lift_3715_){
_start:
{
if (v_____do__lift_3715_ == 0)
{
lean_object* v_toPure_3716_; lean_object* v___x_3717_; 
lean_dec(v_a_3714_);
v_toPure_3716_ = lean_ctor_get(v_toApplicative_3712_, 1);
lean_inc(v_toPure_3716_);
lean_dec_ref(v_toApplicative_3712_);
v___x_3717_ = lean_apply_2(v_toPure_3716_, lean_box(0), v_acc_3713_);
return v___x_3717_;
}
else
{
lean_object* v_toPure_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v_toPure_3718_ = lean_ctor_get(v_toApplicative_3712_, 1);
lean_inc(v_toPure_3718_);
lean_dec_ref(v_toApplicative_3712_);
v___x_3719_ = lean_array_push(v_acc_3713_, v_a_3714_);
v___x_3720_ = lean_apply_2(v_toPure_3718_, lean_box(0), v___x_3719_);
return v___x_3720_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0___boxed(lean_object* v_toApplicative_3721_, lean_object* v_acc_3722_, lean_object* v_a_3723_, lean_object* v_____do__lift_3724_){
_start:
{
uint8_t v_____do__lift_119__boxed_3725_; lean_object* v_res_3726_; 
v_____do__lift_119__boxed_3725_ = lean_unbox(v_____do__lift_3724_);
v_res_3726_ = l_Array_filterM___redArg___lam__0(v_toApplicative_3721_, v_acc_3722_, v_a_3723_, v_____do__lift_119__boxed_3725_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__1(lean_object* v_toApplicative_3727_, lean_object* v_p_3728_, lean_object* v_toBind_3729_, lean_object* v_acc_3730_, lean_object* v_a_3731_){
_start:
{
lean_object* v___f_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
lean_inc(v_a_3731_);
v___f_3732_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3732_, 0, v_toApplicative_3727_);
lean_closure_set(v___f_3732_, 1, v_acc_3730_);
lean_closure_set(v___f_3732_, 2, v_a_3731_);
v___x_3733_ = lean_apply_1(v_p_3728_, v_a_3731_);
v___x_3734_ = lean_apply_4(v_toBind_3729_, lean_box(0), lean_box(0), v___x_3733_, v___f_3732_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg(lean_object* v_inst_3735_, lean_object* v_p_3736_, lean_object* v_as_3737_, lean_object* v_start_3738_, lean_object* v_stop_3739_){
_start:
{
lean_object* v_toApplicative_3740_; lean_object* v_toBind_3741_; lean_object* v___x_3742_; uint8_t v___x_3743_; 
v_toApplicative_3740_ = lean_ctor_get(v_inst_3735_, 0);
v_toBind_3741_ = lean_ctor_get(v_inst_3735_, 1);
v___x_3742_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3743_ = lean_nat_dec_lt(v_start_3738_, v_stop_3739_);
if (v___x_3743_ == 0)
{
lean_object* v_toPure_3744_; lean_object* v___x_3745_; 
lean_inc_ref(v_toApplicative_3740_);
lean_dec_ref(v_as_3737_);
lean_dec(v_p_3736_);
lean_dec_ref(v_inst_3735_);
v_toPure_3744_ = lean_ctor_get(v_toApplicative_3740_, 1);
lean_inc(v_toPure_3744_);
lean_dec_ref(v_toApplicative_3740_);
v___x_3745_ = lean_apply_2(v_toPure_3744_, lean_box(0), v___x_3742_);
return v___x_3745_;
}
else
{
lean_object* v___f_3746_; lean_object* v___x_3747_; uint8_t v___x_3748_; 
lean_inc(v_toBind_3741_);
lean_inc_ref(v_toApplicative_3740_);
v___f_3746_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3746_, 0, v_toApplicative_3740_);
lean_closure_set(v___f_3746_, 1, v_p_3736_);
lean_closure_set(v___f_3746_, 2, v_toBind_3741_);
v___x_3747_ = lean_array_get_size(v_as_3737_);
v___x_3748_ = lean_nat_dec_le(v_stop_3739_, v___x_3747_);
if (v___x_3748_ == 0)
{
uint8_t v___x_3749_; 
v___x_3749_ = lean_nat_dec_lt(v_start_3738_, v___x_3747_);
if (v___x_3749_ == 0)
{
lean_object* v_toPure_3750_; lean_object* v___x_3751_; 
lean_inc_ref(v_toApplicative_3740_);
lean_dec_ref(v___f_3746_);
lean_dec_ref(v_as_3737_);
lean_dec_ref(v_inst_3735_);
v_toPure_3750_ = lean_ctor_get(v_toApplicative_3740_, 1);
lean_inc(v_toPure_3750_);
lean_dec_ref(v_toApplicative_3740_);
v___x_3751_ = lean_apply_2(v_toPure_3750_, lean_box(0), v___x_3742_);
return v___x_3751_;
}
else
{
size_t v___x_3752_; size_t v___x_3753_; lean_object* v___x_3754_; 
v___x_3752_ = lean_usize_of_nat(v_start_3738_);
v___x_3753_ = lean_usize_of_nat(v___x_3747_);
v___x_3754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3735_, v___f_3746_, v_as_3737_, v___x_3752_, v___x_3753_, v___x_3742_);
return v___x_3754_;
}
}
else
{
size_t v___x_3755_; size_t v___x_3756_; lean_object* v___x_3757_; 
v___x_3755_ = lean_usize_of_nat(v_start_3738_);
v___x_3756_ = lean_usize_of_nat(v_stop_3739_);
v___x_3757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3735_, v___f_3746_, v_as_3737_, v___x_3755_, v___x_3756_, v___x_3742_);
return v___x_3757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___boxed(lean_object* v_inst_3758_, lean_object* v_p_3759_, lean_object* v_as_3760_, lean_object* v_start_3761_, lean_object* v_stop_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Array_filterM___redArg(v_inst_3758_, v_p_3759_, v_as_3760_, v_start_3761_, v_stop_3762_);
lean_dec(v_stop_3762_);
lean_dec(v_start_3761_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM(lean_object* v_m_3764_, lean_object* v_00_u03b1_3765_, lean_object* v_inst_3766_, lean_object* v_p_3767_, lean_object* v_as_3768_, lean_object* v_start_3769_, lean_object* v_stop_3770_){
_start:
{
lean_object* v_toApplicative_3771_; lean_object* v_toBind_3772_; lean_object* v___x_3773_; uint8_t v___x_3774_; 
v_toApplicative_3771_ = lean_ctor_get(v_inst_3766_, 0);
v_toBind_3772_ = lean_ctor_get(v_inst_3766_, 1);
v___x_3773_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3774_ = lean_nat_dec_lt(v_start_3769_, v_stop_3770_);
if (v___x_3774_ == 0)
{
lean_object* v_toPure_3775_; lean_object* v___x_3776_; 
lean_inc_ref(v_toApplicative_3771_);
lean_dec_ref(v_as_3768_);
lean_dec(v_p_3767_);
lean_dec_ref(v_inst_3766_);
v_toPure_3775_ = lean_ctor_get(v_toApplicative_3771_, 1);
lean_inc(v_toPure_3775_);
lean_dec_ref(v_toApplicative_3771_);
v___x_3776_ = lean_apply_2(v_toPure_3775_, lean_box(0), v___x_3773_);
return v___x_3776_;
}
else
{
lean_object* v___f_3777_; lean_object* v___x_3778_; uint8_t v___x_3779_; 
lean_inc(v_toBind_3772_);
lean_inc_ref(v_toApplicative_3771_);
v___f_3777_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3777_, 0, v_toApplicative_3771_);
lean_closure_set(v___f_3777_, 1, v_p_3767_);
lean_closure_set(v___f_3777_, 2, v_toBind_3772_);
v___x_3778_ = lean_array_get_size(v_as_3768_);
v___x_3779_ = lean_nat_dec_le(v_stop_3770_, v___x_3778_);
if (v___x_3779_ == 0)
{
uint8_t v___x_3780_; 
v___x_3780_ = lean_nat_dec_lt(v_start_3769_, v___x_3778_);
if (v___x_3780_ == 0)
{
lean_object* v_toPure_3781_; lean_object* v___x_3782_; 
lean_inc_ref(v_toApplicative_3771_);
lean_dec_ref(v___f_3777_);
lean_dec_ref(v_as_3768_);
lean_dec_ref(v_inst_3766_);
v_toPure_3781_ = lean_ctor_get(v_toApplicative_3771_, 1);
lean_inc(v_toPure_3781_);
lean_dec_ref(v_toApplicative_3771_);
v___x_3782_ = lean_apply_2(v_toPure_3781_, lean_box(0), v___x_3773_);
return v___x_3782_;
}
else
{
size_t v___x_3783_; size_t v___x_3784_; lean_object* v___x_3785_; 
v___x_3783_ = lean_usize_of_nat(v_start_3769_);
v___x_3784_ = lean_usize_of_nat(v___x_3778_);
v___x_3785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3766_, v___f_3777_, v_as_3768_, v___x_3783_, v___x_3784_, v___x_3773_);
return v___x_3785_;
}
}
else
{
size_t v___x_3786_; size_t v___x_3787_; lean_object* v___x_3788_; 
v___x_3786_ = lean_usize_of_nat(v_start_3769_);
v___x_3787_ = lean_usize_of_nat(v_stop_3770_);
v___x_3788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3766_, v___f_3777_, v_as_3768_, v___x_3786_, v___x_3787_, v___x_3773_);
return v___x_3788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___boxed(lean_object* v_m_3789_, lean_object* v_00_u03b1_3790_, lean_object* v_inst_3791_, lean_object* v_p_3792_, lean_object* v_as_3793_, lean_object* v_start_3794_, lean_object* v_stop_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Array_filterM(v_m_3789_, v_00_u03b1_3790_, v_inst_3791_, v_p_3792_, v_as_3793_, v_start_3794_, v_stop_3795_);
lean_dec(v_stop_3795_);
lean_dec(v_start_3794_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__0(lean_object* v_toPure_3797_, lean_object* v_acc_3798_, lean_object* v_a_3799_, uint8_t v_____do__lift_3800_){
_start:
{
if (v_____do__lift_3800_ == 0)
{
lean_object* v___x_3801_; 
lean_dec(v_a_3799_);
v___x_3801_ = lean_apply_2(v_toPure_3797_, lean_box(0), v_acc_3798_);
return v___x_3801_;
}
else
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3802_ = lean_array_push(v_acc_3798_, v_a_3799_);
v___x_3803_ = lean_apply_2(v_toPure_3797_, lean_box(0), v___x_3802_);
return v___x_3803_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__0___boxed(lean_object* v_toPure_3804_, lean_object* v_acc_3805_, lean_object* v_a_3806_, lean_object* v_____do__lift_3807_){
_start:
{
uint8_t v_____do__lift_129__boxed_3808_; lean_object* v_res_3809_; 
v_____do__lift_129__boxed_3808_ = lean_unbox(v_____do__lift_3807_);
v_res_3809_ = l_Array_filterRevM___redArg___lam__0(v_toPure_3804_, v_acc_3805_, v_a_3806_, v_____do__lift_129__boxed_3808_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__1(lean_object* v_toPure_3810_, lean_object* v_p_3811_, lean_object* v_toBind_3812_, lean_object* v_a_3813_, lean_object* v_acc_3814_){
_start:
{
lean_object* v___f_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
lean_inc(v_a_3813_);
v___f_3815_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3815_, 0, v_toPure_3810_);
lean_closure_set(v___f_3815_, 1, v_acc_3814_);
lean_closure_set(v___f_3815_, 2, v_a_3813_);
v___x_3816_ = lean_apply_1(v_p_3811_, v_a_3813_);
v___x_3817_ = lean_apply_4(v_toBind_3812_, lean_box(0), lean_box(0), v___x_3816_, v___f_3815_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg(lean_object* v_inst_3819_, lean_object* v_p_3820_, lean_object* v_as_3821_, lean_object* v_start_3822_, lean_object* v_stop_3823_){
_start:
{
lean_object* v_toApplicative_3824_; lean_object* v_toFunctor_3825_; lean_object* v_toBind_3826_; lean_object* v_toPure_3827_; lean_object* v_map_3828_; lean_object* v___f_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
v_toApplicative_3824_ = lean_ctor_get(v_inst_3819_, 0);
v_toFunctor_3825_ = lean_ctor_get(v_toApplicative_3824_, 0);
v_toBind_3826_ = lean_ctor_get(v_inst_3819_, 1);
v_toPure_3827_ = lean_ctor_get(v_toApplicative_3824_, 1);
v_map_3828_ = lean_ctor_get(v_toFunctor_3825_, 0);
lean_inc(v_map_3828_);
lean_inc(v_toBind_3826_);
lean_inc(v_toPure_3827_);
v___f_3829_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3829_, 0, v_toPure_3827_);
lean_closure_set(v___f_3829_, 1, v_p_3820_);
lean_closure_set(v___f_3829_, 2, v_toBind_3826_);
v___x_3830_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3831_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3832_ = lean_array_get_size(v_as_3821_);
v___x_3833_ = lean_nat_dec_le(v_start_3822_, v___x_3832_);
if (v___x_3833_ == 0)
{
uint8_t v___x_3834_; 
v___x_3834_ = lean_nat_dec_lt(v_stop_3823_, v___x_3832_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
lean_inc(v_toPure_3827_);
lean_dec_ref(v___f_3829_);
lean_dec_ref(v_as_3821_);
lean_dec_ref(v_inst_3819_);
v___x_3835_ = lean_apply_2(v_toPure_3827_, lean_box(0), v___x_3831_);
v___x_3836_ = lean_apply_4(v_map_3828_, lean_box(0), lean_box(0), v___x_3830_, v___x_3835_);
return v___x_3836_;
}
else
{
size_t v___x_3837_; size_t v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3837_ = lean_usize_of_nat(v___x_3832_);
v___x_3838_ = lean_usize_of_nat(v_stop_3823_);
v___x_3839_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3819_, v___f_3829_, v_as_3821_, v___x_3837_, v___x_3838_, v___x_3831_);
v___x_3840_ = lean_apply_4(v_map_3828_, lean_box(0), lean_box(0), v___x_3830_, v___x_3839_);
return v___x_3840_;
}
}
else
{
uint8_t v___x_3841_; 
v___x_3841_ = lean_nat_dec_lt(v_stop_3823_, v_start_3822_);
if (v___x_3841_ == 0)
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
lean_inc(v_toPure_3827_);
lean_dec_ref(v___f_3829_);
lean_dec_ref(v_as_3821_);
lean_dec_ref(v_inst_3819_);
v___x_3842_ = lean_apply_2(v_toPure_3827_, lean_box(0), v___x_3831_);
v___x_3843_ = lean_apply_4(v_map_3828_, lean_box(0), lean_box(0), v___x_3830_, v___x_3842_);
return v___x_3843_;
}
else
{
size_t v___x_3844_; size_t v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3844_ = lean_usize_of_nat(v_start_3822_);
v___x_3845_ = lean_usize_of_nat(v_stop_3823_);
v___x_3846_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3819_, v___f_3829_, v_as_3821_, v___x_3844_, v___x_3845_, v___x_3831_);
v___x_3847_ = lean_apply_4(v_map_3828_, lean_box(0), lean_box(0), v___x_3830_, v___x_3846_);
return v___x_3847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___boxed(lean_object* v_inst_3848_, lean_object* v_p_3849_, lean_object* v_as_3850_, lean_object* v_start_3851_, lean_object* v_stop_3852_){
_start:
{
lean_object* v_res_3853_; 
v_res_3853_ = l_Array_filterRevM___redArg(v_inst_3848_, v_p_3849_, v_as_3850_, v_start_3851_, v_stop_3852_);
lean_dec(v_stop_3852_);
lean_dec(v_start_3851_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM(lean_object* v_m_3854_, lean_object* v_00_u03b1_3855_, lean_object* v_inst_3856_, lean_object* v_p_3857_, lean_object* v_as_3858_, lean_object* v_start_3859_, lean_object* v_stop_3860_){
_start:
{
lean_object* v_toApplicative_3861_; lean_object* v_toFunctor_3862_; lean_object* v_toBind_3863_; lean_object* v_toPure_3864_; lean_object* v_map_3865_; lean_object* v___f_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; uint8_t v___x_3870_; 
v_toApplicative_3861_ = lean_ctor_get(v_inst_3856_, 0);
v_toFunctor_3862_ = lean_ctor_get(v_toApplicative_3861_, 0);
v_toBind_3863_ = lean_ctor_get(v_inst_3856_, 1);
v_toPure_3864_ = lean_ctor_get(v_toApplicative_3861_, 1);
v_map_3865_ = lean_ctor_get(v_toFunctor_3862_, 0);
lean_inc(v_map_3865_);
lean_inc(v_toBind_3863_);
lean_inc(v_toPure_3864_);
v___f_3866_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3866_, 0, v_toPure_3864_);
lean_closure_set(v___f_3866_, 1, v_p_3857_);
lean_closure_set(v___f_3866_, 2, v_toBind_3863_);
v___x_3867_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3868_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3869_ = lean_array_get_size(v_as_3858_);
v___x_3870_ = lean_nat_dec_le(v_start_3859_, v___x_3869_);
if (v___x_3870_ == 0)
{
uint8_t v___x_3871_; 
v___x_3871_ = lean_nat_dec_lt(v_stop_3860_, v___x_3869_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
lean_inc(v_toPure_3864_);
lean_dec_ref(v___f_3866_);
lean_dec_ref(v_as_3858_);
lean_dec_ref(v_inst_3856_);
v___x_3872_ = lean_apply_2(v_toPure_3864_, lean_box(0), v___x_3868_);
v___x_3873_ = lean_apply_4(v_map_3865_, lean_box(0), lean_box(0), v___x_3867_, v___x_3872_);
return v___x_3873_;
}
else
{
size_t v___x_3874_; size_t v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3874_ = lean_usize_of_nat(v___x_3869_);
v___x_3875_ = lean_usize_of_nat(v_stop_3860_);
v___x_3876_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3856_, v___f_3866_, v_as_3858_, v___x_3874_, v___x_3875_, v___x_3868_);
v___x_3877_ = lean_apply_4(v_map_3865_, lean_box(0), lean_box(0), v___x_3867_, v___x_3876_);
return v___x_3877_;
}
}
else
{
uint8_t v___x_3878_; 
v___x_3878_ = lean_nat_dec_lt(v_stop_3860_, v_start_3859_);
if (v___x_3878_ == 0)
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
lean_inc(v_toPure_3864_);
lean_dec_ref(v___f_3866_);
lean_dec_ref(v_as_3858_);
lean_dec_ref(v_inst_3856_);
v___x_3879_ = lean_apply_2(v_toPure_3864_, lean_box(0), v___x_3868_);
v___x_3880_ = lean_apply_4(v_map_3865_, lean_box(0), lean_box(0), v___x_3867_, v___x_3879_);
return v___x_3880_;
}
else
{
size_t v___x_3881_; size_t v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3881_ = lean_usize_of_nat(v_start_3859_);
v___x_3882_ = lean_usize_of_nat(v_stop_3860_);
v___x_3883_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3856_, v___f_3866_, v_as_3858_, v___x_3881_, v___x_3882_, v___x_3868_);
v___x_3884_ = lean_apply_4(v_map_3865_, lean_box(0), lean_box(0), v___x_3867_, v___x_3883_);
return v___x_3884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___boxed(lean_object* v_m_3885_, lean_object* v_00_u03b1_3886_, lean_object* v_inst_3887_, lean_object* v_p_3888_, lean_object* v_as_3889_, lean_object* v_start_3890_, lean_object* v_stop_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Array_filterRevM(v_m_3885_, v_00_u03b1_3886_, v_inst_3887_, v_p_3888_, v_as_3889_, v_start_3890_, v_stop_3891_);
lean_dec(v_stop_3891_);
lean_dec(v_start_3890_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__0(lean_object* v_toPure_3893_, lean_object* v_bs_3894_, lean_object* v_____do__lift_3895_){
_start:
{
if (lean_obj_tag(v_____do__lift_3895_) == 0)
{
lean_object* v___x_3896_; 
v___x_3896_ = lean_apply_2(v_toPure_3893_, lean_box(0), v_bs_3894_);
return v___x_3896_;
}
else
{
lean_object* v_val_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v_val_3897_ = lean_ctor_get(v_____do__lift_3895_, 0);
lean_inc(v_val_3897_);
lean_dec_ref_known(v_____do__lift_3895_, 1);
v___x_3898_ = lean_array_push(v_bs_3894_, v_val_3897_);
v___x_3899_ = lean_apply_2(v_toPure_3893_, lean_box(0), v___x_3898_);
return v___x_3899_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__1(lean_object* v_toPure_3900_, lean_object* v_f_3901_, lean_object* v_toBind_3902_, lean_object* v_bs_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v___f_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___f_3905_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3905_, 0, v_toPure_3900_);
lean_closure_set(v___f_3905_, 1, v_bs_3903_);
v___x_3906_ = lean_apply_1(v_f_3901_, v_a_3904_);
v___x_3907_ = lean_apply_4(v_toBind_3902_, lean_box(0), lean_box(0), v___x_3906_, v___f_3905_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg(lean_object* v_inst_3908_, lean_object* v_f_3909_, lean_object* v_as_3910_, lean_object* v_start_3911_, lean_object* v_stop_3912_){
_start:
{
lean_object* v_toApplicative_3913_; lean_object* v_toBind_3914_; lean_object* v_toPure_3915_; lean_object* v___x_3916_; uint8_t v___x_3917_; 
v_toApplicative_3913_ = lean_ctor_get(v_inst_3908_, 0);
v_toBind_3914_ = lean_ctor_get(v_inst_3908_, 1);
v_toPure_3915_ = lean_ctor_get(v_toApplicative_3913_, 1);
v___x_3916_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3917_ = lean_nat_dec_lt(v_start_3911_, v_stop_3912_);
if (v___x_3917_ == 0)
{
lean_object* v___x_3918_; 
lean_inc(v_toPure_3915_);
lean_dec_ref(v_as_3910_);
lean_dec(v_f_3909_);
lean_dec_ref(v_inst_3908_);
v___x_3918_ = lean_apply_2(v_toPure_3915_, lean_box(0), v___x_3916_);
return v___x_3918_;
}
else
{
lean_object* v___f_3919_; lean_object* v___x_3920_; uint8_t v___x_3921_; 
lean_inc(v_toBind_3914_);
lean_inc(v_toPure_3915_);
v___f_3919_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3919_, 0, v_toPure_3915_);
lean_closure_set(v___f_3919_, 1, v_f_3909_);
lean_closure_set(v___f_3919_, 2, v_toBind_3914_);
v___x_3920_ = lean_array_get_size(v_as_3910_);
v___x_3921_ = lean_nat_dec_le(v_stop_3912_, v___x_3920_);
if (v___x_3921_ == 0)
{
uint8_t v___x_3922_; 
v___x_3922_ = lean_nat_dec_lt(v_start_3911_, v___x_3920_);
if (v___x_3922_ == 0)
{
lean_object* v___x_3923_; 
lean_inc(v_toPure_3915_);
lean_dec_ref(v___f_3919_);
lean_dec_ref(v_as_3910_);
lean_dec_ref(v_inst_3908_);
v___x_3923_ = lean_apply_2(v_toPure_3915_, lean_box(0), v___x_3916_);
return v___x_3923_;
}
else
{
size_t v___x_3924_; size_t v___x_3925_; lean_object* v___x_3926_; 
v___x_3924_ = lean_usize_of_nat(v_start_3911_);
v___x_3925_ = lean_usize_of_nat(v___x_3920_);
v___x_3926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3908_, v___f_3919_, v_as_3910_, v___x_3924_, v___x_3925_, v___x_3916_);
return v___x_3926_;
}
}
else
{
size_t v___x_3927_; size_t v___x_3928_; lean_object* v___x_3929_; 
v___x_3927_ = lean_usize_of_nat(v_start_3911_);
v___x_3928_ = lean_usize_of_nat(v_stop_3912_);
v___x_3929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3908_, v___f_3919_, v_as_3910_, v___x_3927_, v___x_3928_, v___x_3916_);
return v___x_3929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___boxed(lean_object* v_inst_3930_, lean_object* v_f_3931_, lean_object* v_as_3932_, lean_object* v_start_3933_, lean_object* v_stop_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l_Array_filterMapM___redArg(v_inst_3930_, v_f_3931_, v_as_3932_, v_start_3933_, v_stop_3934_);
lean_dec(v_stop_3934_);
lean_dec(v_start_3933_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM(lean_object* v_00_u03b1_3936_, lean_object* v_m_3937_, lean_object* v_00_u03b2_3938_, lean_object* v_inst_3939_, lean_object* v_f_3940_, lean_object* v_as_3941_, lean_object* v_start_3942_, lean_object* v_stop_3943_){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = l_Array_filterMapM___redArg(v_inst_3939_, v_f_3940_, v_as_3941_, v_start_3942_, v_stop_3943_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___boxed(lean_object* v_00_u03b1_3945_, lean_object* v_m_3946_, lean_object* v_00_u03b2_3947_, lean_object* v_inst_3948_, lean_object* v_f_3949_, lean_object* v_as_3950_, lean_object* v_start_3951_, lean_object* v_stop_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l_Array_filterMapM(v_00_u03b1_3945_, v_m_3946_, v_00_u03b2_3947_, v_inst_3948_, v_f_3949_, v_as_3950_, v_start_3951_, v_stop_3952_);
lean_dec(v_stop_3952_);
lean_dec(v_start_3951_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg(lean_object* v_f_3954_, lean_object* v_as_3955_, lean_object* v_start_3956_, lean_object* v_stop_3957_){
_start:
{
lean_object* v___f_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___f_3958_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3958_, 0, v_f_3954_);
v___x_3959_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3960_ = l_Array_filterMapM___redArg(v___x_3959_, v___f_3958_, v_as_3955_, v_start_3956_, v_stop_3957_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg___boxed(lean_object* v_f_3961_, lean_object* v_as_3962_, lean_object* v_start_3963_, lean_object* v_stop_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l_Array_filterMap___redArg(v_f_3961_, v_as_3962_, v_start_3963_, v_stop_3964_);
lean_dec(v_stop_3964_);
lean_dec(v_start_3963_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap(lean_object* v_00_u03b1_3966_, lean_object* v_00_u03b2_3967_, lean_object* v_f_3968_, lean_object* v_as_3969_, lean_object* v_start_3970_, lean_object* v_stop_3971_){
_start:
{
lean_object* v___f_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___f_3972_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3972_, 0, v_f_3968_);
v___x_3973_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3974_ = l_Array_filterMapM___redArg(v___x_3973_, v___f_3972_, v_as_3969_, v_start_3970_, v_stop_3971_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___boxed(lean_object* v_00_u03b1_3975_, lean_object* v_00_u03b2_3976_, lean_object* v_f_3977_, lean_object* v_as_3978_, lean_object* v_start_3979_, lean_object* v_stop_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Array_filterMap(v_00_u03b1_3975_, v_00_u03b2_3976_, v_f_3977_, v_as_3978_, v_start_3979_, v_stop_3980_);
lean_dec(v_stop_3980_);
lean_dec(v_start_3979_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg___lam__0(lean_object* v_lt_3982_, lean_object* v_x1_3983_, lean_object* v_x2_3984_){
_start:
{
lean_object* v___x_3985_; uint8_t v___x_3986_; 
lean_inc(v_x2_3984_);
lean_inc(v_x1_3983_);
v___x_3985_ = lean_apply_2(v_lt_3982_, v_x1_3983_, v_x2_3984_);
v___x_3986_ = lean_unbox(v___x_3985_);
if (v___x_3986_ == 0)
{
lean_dec(v_x2_3984_);
return v_x1_3983_;
}
else
{
lean_dec(v_x1_3983_);
return v_x2_3984_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg(lean_object* v_as_3987_, lean_object* v_lt_3988_){
_start:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; uint8_t v___x_3991_; 
v___x_3989_ = lean_unsigned_to_nat(0u);
v___x_3990_ = lean_array_get_size(v_as_3987_);
v___x_3991_ = lean_nat_dec_lt(v___x_3989_, v___x_3990_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; 
lean_dec_ref(v_lt_3988_);
lean_dec_ref(v_as_3987_);
v___x_3992_ = lean_box(0);
return v___x_3992_;
}
else
{
lean_object* v_a0_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; uint8_t v___x_3996_; 
v_a0_3993_ = lean_array_fget(v_as_3987_, v___x_3989_);
v___x_3994_ = lean_unsigned_to_nat(1u);
v___x_3995_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3996_ = lean_nat_dec_lt(v___x_3994_, v___x_3990_);
if (v___x_3996_ == 0)
{
lean_object* v___x_3997_; 
lean_dec_ref(v_lt_3988_);
lean_dec_ref(v_as_3987_);
v___x_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3997_, 0, v_a0_3993_);
return v___x_3997_;
}
else
{
lean_object* v___f_3998_; uint8_t v___x_3999_; 
v___f_3998_ = lean_alloc_closure((void*)(l_Array_getMax_x3f___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3998_, 0, v_lt_3988_);
v___x_3999_ = lean_nat_dec_le(v___x_3990_, v___x_3990_);
if (v___x_3999_ == 0)
{
if (v___x_3996_ == 0)
{
lean_object* v___x_4000_; 
lean_dec_ref(v___f_3998_);
lean_dec_ref(v_as_3987_);
v___x_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4000_, 0, v_a0_3993_);
return v___x_4000_;
}
else
{
size_t v___x_4001_; size_t v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4001_ = ((size_t)1ULL);
v___x_4002_ = lean_usize_of_nat(v___x_3990_);
v___x_4003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3995_, v___f_3998_, v_as_3987_, v___x_4001_, v___x_4002_, v_a0_3993_);
v___x_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4003_);
return v___x_4004_;
}
}
else
{
size_t v___x_4005_; size_t v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4005_ = ((size_t)1ULL);
v___x_4006_ = lean_usize_of_nat(v___x_3990_);
v___x_4007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3995_, v___f_3998_, v_as_3987_, v___x_4005_, v___x_4006_, v_a0_3993_);
v___x_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
return v___x_4008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f(lean_object* v_00_u03b1_4009_, lean_object* v_as_4010_, lean_object* v_lt_4011_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Array_getMax_x3f___redArg(v_as_4010_, v_lt_4011_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg___lam__0(lean_object* v_p_4013_, lean_object* v_a_4014_, lean_object* v_x_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v_fst_4017_; lean_object* v_snd_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4034_; 
v_fst_4017_ = lean_ctor_get(v___y_4016_, 0);
v_snd_4018_ = lean_ctor_get(v___y_4016_, 1);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___y_4016_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4020_ = v___y_4016_;
v_isShared_4021_ = v_isSharedCheck_4034_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_snd_4018_);
lean_inc(v_fst_4017_);
lean_dec(v___y_4016_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4034_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4022_; uint8_t v___x_4023_; 
lean_inc(v_a_4014_);
v___x_4022_ = lean_apply_1(v_p_4013_, v_a_4014_);
v___x_4023_ = lean_unbox(v___x_4022_);
if (v___x_4023_ == 0)
{
lean_object* v___x_4024_; lean_object* v___x_4026_; 
v___x_4024_ = lean_array_push(v_snd_4018_, v_a_4014_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 1, v___x_4024_);
v___x_4026_ = v___x_4020_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_fst_4017_);
lean_ctor_set(v_reuseFailAlloc_4028_, 1, v___x_4024_);
v___x_4026_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
lean_object* v___x_4027_; 
v___x_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4026_);
return v___x_4027_;
}
}
else
{
lean_object* v___x_4029_; lean_object* v___x_4031_; 
v___x_4029_ = lean_array_push(v_fst_4017_, v_a_4014_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 0, v___x_4029_);
v___x_4031_ = v___x_4020_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4029_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v_snd_4018_);
v___x_4031_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
lean_object* v___x_4032_; 
v___x_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
return v___x_4032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg(lean_object* v_p_4037_, lean_object* v_as_4038_){
_start:
{
lean_object* v___f_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; size_t v_sz_4042_; size_t v___x_4043_; lean_object* v___x_4044_; lean_object* v_fst_4045_; lean_object* v_snd_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
v___f_4039_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4039_, 0, v_p_4037_);
v___x_4040_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4041_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_4042_ = lean_array_size(v_as_4038_);
v___x_4043_ = ((size_t)0ULL);
v___x_4044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_4040_, v_as_4038_, v___f_4039_, v_sz_4042_, v___x_4043_, v___x_4041_);
v_fst_4045_ = lean_ctor_get(v___x_4044_, 0);
v_snd_4046_ = lean_ctor_get(v___x_4044_, 1);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4048_ = v___x_4044_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_snd_4046_);
lean_inc(v_fst_4045_);
lean_dec(v___x_4044_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_fst_4045_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v_snd_4046_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition(lean_object* v_00_u03b1_4054_, lean_object* v_p_4055_, lean_object* v_as_4056_){
_start:
{
lean_object* v___f_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; size_t v_sz_4060_; size_t v___x_4061_; lean_object* v___x_4062_; lean_object* v_fst_4063_; lean_object* v_snd_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
v___f_4057_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4057_, 0, v_p_4055_);
v___x_4058_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4059_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_4060_ = lean_array_size(v_as_4056_);
v___x_4061_ = ((size_t)0ULL);
v___x_4062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_4058_, v_as_4056_, v___f_4057_, v_sz_4060_, v___x_4061_, v___x_4059_);
v_fst_4063_ = lean_ctor_get(v___x_4062_, 0);
v_snd_4064_ = lean_ctor_get(v___x_4062_, 1);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4062_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_snd_4064_);
lean_inc(v_fst_4063_);
lean_dec(v___x_4062_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_fst_4063_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v_snd_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile___redArg(lean_object* v_p_4072_, lean_object* v_as_4073_){
_start:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; uint8_t v___x_4076_; 
v___x_4074_ = lean_unsigned_to_nat(0u);
v___x_4075_ = lean_array_get_size(v_as_4073_);
v___x_4076_ = lean_nat_dec_lt(v___x_4074_, v___x_4075_);
if (v___x_4076_ == 0)
{
lean_dec_ref(v_p_4072_);
return v_as_4073_;
}
else
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; uint8_t v___x_4081_; 
v___x_4077_ = lean_unsigned_to_nat(1u);
v___x_4078_ = lean_nat_sub(v___x_4075_, v___x_4077_);
v___x_4079_ = lean_array_fget_borrowed(v_as_4073_, v___x_4078_);
lean_dec(v___x_4078_);
lean_inc_ref(v_p_4072_);
lean_inc(v___x_4079_);
v___x_4080_ = lean_apply_1(v_p_4072_, v___x_4079_);
v___x_4081_ = lean_unbox(v___x_4080_);
if (v___x_4081_ == 0)
{
lean_dec_ref(v_p_4072_);
return v_as_4073_;
}
else
{
lean_object* v___x_4082_; 
v___x_4082_ = lean_array_pop(v_as_4073_);
v_as_4073_ = v___x_4082_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile(lean_object* v_00_u03b1_4084_, lean_object* v_p_4085_, lean_object* v_as_4086_){
_start:
{
lean_object* v___x_4087_; 
v___x_4087_ = l_Array_popWhile___redArg(v_p_4085_, v_as_4086_);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(lean_object* v_p_4088_, lean_object* v_as_4089_, lean_object* v_i_4090_, lean_object* v_acc_4091_){
_start:
{
lean_object* v___x_4092_; uint8_t v___x_4093_; 
v___x_4092_ = lean_array_get_size(v_as_4089_);
v___x_4093_ = lean_nat_dec_lt(v_i_4090_, v___x_4092_);
if (v___x_4093_ == 0)
{
lean_dec(v_i_4090_);
lean_dec_ref(v_p_4088_);
return v_acc_4091_;
}
else
{
lean_object* v_a_4094_; lean_object* v___x_4095_; uint8_t v___x_4096_; 
v_a_4094_ = lean_array_fget_borrowed(v_as_4089_, v_i_4090_);
lean_inc_ref(v_p_4088_);
lean_inc(v_a_4094_);
v___x_4095_ = lean_apply_1(v_p_4088_, v_a_4094_);
v___x_4096_ = lean_unbox(v___x_4095_);
if (v___x_4096_ == 0)
{
lean_dec(v_i_4090_);
lean_dec_ref(v_p_4088_);
return v_acc_4091_;
}
else
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4097_ = lean_unsigned_to_nat(1u);
v___x_4098_ = lean_nat_add(v_i_4090_, v___x_4097_);
lean_dec(v_i_4090_);
lean_inc(v_a_4094_);
v___x_4099_ = lean_array_push(v_acc_4091_, v_a_4094_);
v_i_4090_ = v___x_4098_;
v_acc_4091_ = v___x_4099_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg___boxed(lean_object* v_p_4101_, lean_object* v_as_4102_, lean_object* v_i_4103_, lean_object* v_acc_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4101_, v_as_4102_, v_i_4103_, v_acc_4104_);
lean_dec_ref(v_as_4102_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(lean_object* v_00_u03b1_4106_, lean_object* v_p_4107_, lean_object* v_as_4108_, lean_object* v_i_4109_, lean_object* v_acc_4110_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4107_, v_as_4108_, v_i_4109_, v_acc_4110_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___boxed(lean_object* v_00_u03b1_4112_, lean_object* v_p_4113_, lean_object* v_as_4114_, lean_object* v_i_4115_, lean_object* v_acc_4116_){
_start:
{
lean_object* v_res_4117_; 
v_res_4117_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(v_00_u03b1_4112_, v_p_4113_, v_as_4114_, v_i_4115_, v_acc_4116_);
lean_dec_ref(v_as_4114_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg(lean_object* v_p_4118_, lean_object* v_as_4119_){
_start:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4120_ = lean_unsigned_to_nat(0u);
v___x_4121_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4122_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4118_, v_as_4119_, v___x_4120_, v___x_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg___boxed(lean_object* v_p_4123_, lean_object* v_as_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l_Array_takeWhile___redArg(v_p_4123_, v_as_4124_);
lean_dec_ref(v_as_4124_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile(lean_object* v_00_u03b1_4126_, lean_object* v_p_4127_, lean_object* v_as_4128_){
_start:
{
lean_object* v___x_4129_; 
v___x_4129_ = l_Array_takeWhile___redArg(v_p_4127_, v_as_4128_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___boxed(lean_object* v_00_u03b1_4130_, lean_object* v_p_4131_, lean_object* v_as_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_Array_takeWhile(v_00_u03b1_4130_, v_p_4131_, v_as_4132_);
lean_dec_ref(v_as_4132_);
return v_res_4133_;
}
}
static lean_object* _init_l_Array_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_4134_; 
v___x_4134_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx___redArg(lean_object* v_xs_4135_, lean_object* v_i_4136_){
_start:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; uint8_t v___x_4140_; 
v___x_4137_ = lean_unsigned_to_nat(1u);
v___x_4138_ = lean_nat_add(v_i_4136_, v___x_4137_);
v___x_4139_ = lean_array_get_size(v_xs_4135_);
v___x_4140_ = lean_nat_dec_lt(v___x_4138_, v___x_4139_);
if (v___x_4140_ == 0)
{
lean_object* v___x_4141_; 
lean_dec(v___x_4138_);
lean_dec(v_i_4136_);
v___x_4141_ = lean_array_pop(v_xs_4135_);
return v___x_4141_;
}
else
{
lean_object* v_xs_x27_4142_; 
v_xs_x27_4142_ = lean_array_fswap(v_xs_4135_, v___x_4138_, v_i_4136_);
lean_dec(v_i_4136_);
v_xs_4135_ = v_xs_x27_4142_;
v_i_4136_ = v___x_4138_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx(lean_object* v_00_u03b1_4144_, lean_object* v_xs_4145_, lean_object* v_i_4146_, lean_object* v_h_4147_){
_start:
{
lean_object* v___x_4148_; 
v___x_4148_ = l_Array_eraseIdx___redArg(v_xs_4145_, v_i_4146_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds___redArg(lean_object* v_xs_4149_, lean_object* v_i_4150_){
_start:
{
lean_object* v___x_4151_; uint8_t v___x_4152_; 
v___x_4151_ = lean_array_get_size(v_xs_4149_);
v___x_4152_ = lean_nat_dec_lt(v_i_4150_, v___x_4151_);
if (v___x_4152_ == 0)
{
lean_dec(v_i_4150_);
return v_xs_4149_;
}
else
{
lean_object* v___x_4153_; 
v___x_4153_ = l_Array_eraseIdx___redArg(v_xs_4149_, v_i_4150_);
return v___x_4153_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds(lean_object* v_00_u03b1_4154_, lean_object* v_xs_4155_, lean_object* v_i_4156_){
_start:
{
lean_object* v___x_4157_; 
v___x_4157_ = l_Array_eraseIdxIfInBounds___redArg(v_xs_4155_, v_i_4156_);
return v___x_4157_;
}
}
static lean_object* _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4158_; 
v___x_4158_ = l_Array_instInhabited(lean_box(0));
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(lean_object* v_msg_4159_){
_start:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4160_ = lean_obj_once(&l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0, &l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0_once, _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0);
v___x_4161_ = lean_panic_fn_borrowed(v___x_4160_, v_msg_4159_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0(lean_object* v_00_u03b1_4162_, lean_object* v_msg_4163_){
_start:
{
lean_object* v___x_4164_; 
v___x_4164_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v_msg_4163_);
return v___x_4164_;
}
}
static lean_object* _init_l_Array_eraseIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4167_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4168_ = lean_unsigned_to_nat(47u);
v___x_4169_ = lean_unsigned_to_nat(1842u);
v___x_4170_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__0));
v___x_4171_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4172_ = l_mkPanicMessageWithDecl(v___x_4171_, v___x_4170_, v___x_4169_, v___x_4168_, v___x_4167_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21___redArg(lean_object* v_xs_4173_, lean_object* v_i_4174_){
_start:
{
lean_object* v___x_4175_; uint8_t v___x_4176_; 
v___x_4175_ = lean_array_get_size(v_xs_4173_);
v___x_4176_ = lean_nat_dec_lt(v_i_4174_, v___x_4175_);
if (v___x_4176_ == 0)
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
lean_dec(v_i_4174_);
lean_dec_ref(v_xs_4173_);
v___x_4177_ = lean_obj_once(&l_Array_eraseIdx_x21___redArg___closed__2, &l_Array_eraseIdx_x21___redArg___closed__2_once, _init_l_Array_eraseIdx_x21___redArg___closed__2);
v___x_4178_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4177_);
return v___x_4178_;
}
else
{
lean_object* v___x_4179_; 
v___x_4179_ = l_Array_eraseIdx___redArg(v_xs_4173_, v_i_4174_);
return v___x_4179_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21(lean_object* v_00_u03b1_4180_, lean_object* v_xs_4181_, lean_object* v_i_4182_){
_start:
{
lean_object* v___x_4183_; 
v___x_4183_ = l_Array_eraseIdx_x21___redArg(v_xs_4181_, v_i_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Array_erase___redArg(lean_object* v_inst_4184_, lean_object* v_as_4185_, lean_object* v_a_4186_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = l_Array_finIdxOf_x3f___redArg(v_inst_4184_, v_as_4185_, v_a_4186_);
if (lean_obj_tag(v___x_4187_) == 0)
{
return v_as_4185_;
}
else
{
lean_object* v_val_4188_; lean_object* v___x_4189_; 
v_val_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc(v_val_4188_);
lean_dec_ref_known(v___x_4187_, 1);
v___x_4189_ = l_Array_eraseIdx___redArg(v_as_4185_, v_val_4188_);
return v___x_4189_;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase(lean_object* v_00_u03b1_4190_, lean_object* v_inst_4191_, lean_object* v_as_4192_, lean_object* v_a_4193_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l_Array_erase___redArg(v_inst_4191_, v_as_4192_, v_a_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseP___redArg(lean_object* v_as_4195_, lean_object* v_p_4196_){
_start:
{
lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4197_ = lean_unsigned_to_nat(0u);
v___x_4198_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_4196_, v_as_4195_, v___x_4197_);
if (lean_obj_tag(v___x_4198_) == 0)
{
return v_as_4195_;
}
else
{
lean_object* v_val_4199_; lean_object* v___x_4200_; 
v_val_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_val_4199_);
lean_dec_ref_known(v___x_4198_, 1);
v___x_4200_ = l_Array_eraseIdx___redArg(v_as_4195_, v_val_4199_);
return v___x_4200_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseP(lean_object* v_00_u03b1_4201_, lean_object* v_as_4202_, lean_object* v_p_4203_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l_Array_eraseP___redArg(v_as_4202_, v_p_4203_);
return v___x_4204_;
}
}
static lean_object* _init_l_Array_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(lean_object* v_i_4206_, lean_object* v_as_4207_, lean_object* v_j_4208_){
_start:
{
uint8_t v___x_4209_; 
v___x_4209_ = lean_nat_dec_lt(v_i_4206_, v_j_4208_);
if (v___x_4209_ == 0)
{
lean_dec(v_j_4208_);
return v_as_4207_;
}
else
{
lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v_as_4212_; 
v___x_4210_ = lean_unsigned_to_nat(1u);
v___x_4211_ = lean_nat_sub(v_j_4208_, v___x_4210_);
v_as_4212_ = lean_array_fswap(v_as_4207_, v___x_4211_, v_j_4208_);
lean_dec(v_j_4208_);
v_as_4207_ = v_as_4212_;
v_j_4208_ = v___x_4211_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg___boxed(lean_object* v_i_4214_, lean_object* v_as_4215_, lean_object* v_j_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4214_, v_as_4215_, v_j_4216_);
lean_dec(v_i_4214_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object* v_00_u03b1_4218_, lean_object* v_i_4219_, lean_object* v_as_4220_, lean_object* v_j_4221_){
_start:
{
lean_object* v___x_4222_; 
v___x_4222_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4219_, v_as_4220_, v_j_4221_);
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___boxed(lean_object* v_00_u03b1_4223_, lean_object* v_i_4224_, lean_object* v_as_4225_, lean_object* v_j_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(v_00_u03b1_4223_, v_i_4224_, v_as_4225_, v_j_4226_);
lean_dec(v_i_4224_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg(lean_object* v_as_4228_, lean_object* v_i_4229_, lean_object* v_a_4230_){
_start:
{
lean_object* v_j_4231_; lean_object* v_as_4232_; lean_object* v___x_4233_; 
v_j_4231_ = lean_array_get_size(v_as_4228_);
v_as_4232_ = lean_array_push(v_as_4228_, v_a_4230_);
v___x_4233_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4229_, v_as_4232_, v_j_4231_);
return v___x_4233_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg___boxed(lean_object* v_as_4234_, lean_object* v_i_4235_, lean_object* v_a_4236_){
_start:
{
lean_object* v_res_4237_; 
v_res_4237_ = l_Array_insertIdx___redArg(v_as_4234_, v_i_4235_, v_a_4236_);
lean_dec(v_i_4235_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx(lean_object* v_00_u03b1_4238_, lean_object* v_as_4239_, lean_object* v_i_4240_, lean_object* v_a_4241_, lean_object* v_x_4242_){
_start:
{
lean_object* v_j_4243_; lean_object* v_as_4244_; lean_object* v___x_4245_; 
v_j_4243_ = lean_array_get_size(v_as_4239_);
v_as_4244_ = lean_array_push(v_as_4239_, v_a_4241_);
v___x_4245_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4240_, v_as_4244_, v_j_4243_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___boxed(lean_object* v_00_u03b1_4246_, lean_object* v_as_4247_, lean_object* v_i_4248_, lean_object* v_a_4249_, lean_object* v_x_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l_Array_insertIdx(v_00_u03b1_4246_, v_as_4247_, v_i_4248_, v_a_4249_, v_x_4250_);
lean_dec(v_i_4248_);
return v_res_4251_;
}
}
static lean_object* _init_l_Array_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4253_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4254_ = lean_unsigned_to_nat(7u);
v___x_4255_ = lean_unsigned_to_nat(1924u);
v___x_4256_ = ((lean_object*)(l_Array_insertIdx_x21___redArg___closed__0));
v___x_4257_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4258_ = l_mkPanicMessageWithDecl(v___x_4257_, v___x_4256_, v___x_4255_, v___x_4254_, v___x_4253_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg(lean_object* v_as_4259_, lean_object* v_i_4260_, lean_object* v_a_4261_){
_start:
{
lean_object* v___x_4262_; uint8_t v___x_4263_; 
v___x_4262_ = lean_array_get_size(v_as_4259_);
v___x_4263_ = lean_nat_dec_le(v_i_4260_, v___x_4262_);
if (v___x_4263_ == 0)
{
lean_object* v___x_4264_; lean_object* v___x_4265_; 
lean_dec(v_a_4261_);
lean_dec_ref(v_as_4259_);
v___x_4264_ = lean_obj_once(&l_Array_insertIdx_x21___redArg___closed__1, &l_Array_insertIdx_x21___redArg___closed__1_once, _init_l_Array_insertIdx_x21___redArg___closed__1);
v___x_4265_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4264_);
return v___x_4265_;
}
else
{
lean_object* v_as_4266_; lean_object* v___x_4267_; 
v_as_4266_ = lean_array_push(v_as_4259_, v_a_4261_);
v___x_4267_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4260_, v_as_4266_, v___x_4262_);
return v___x_4267_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg___boxed(lean_object* v_as_4268_, lean_object* v_i_4269_, lean_object* v_a_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l_Array_insertIdx_x21___redArg(v_as_4268_, v_i_4269_, v_a_4270_);
lean_dec(v_i_4269_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21(lean_object* v_00_u03b1_4272_, lean_object* v_as_4273_, lean_object* v_i_4274_, lean_object* v_a_4275_){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l_Array_insertIdx_x21___redArg(v_as_4273_, v_i_4274_, v_a_4275_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___boxed(lean_object* v_00_u03b1_4277_, lean_object* v_as_4278_, lean_object* v_i_4279_, lean_object* v_a_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Array_insertIdx_x21(v_00_u03b1_4277_, v_as_4278_, v_i_4279_, v_a_4280_);
lean_dec(v_i_4279_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg(lean_object* v_as_4282_, lean_object* v_i_4283_, lean_object* v_a_4284_){
_start:
{
lean_object* v___x_4285_; uint8_t v___x_4286_; 
v___x_4285_ = lean_array_get_size(v_as_4282_);
v___x_4286_ = lean_nat_dec_le(v_i_4283_, v___x_4285_);
if (v___x_4286_ == 0)
{
lean_dec(v_a_4284_);
return v_as_4282_;
}
else
{
lean_object* v_as_4287_; lean_object* v___x_4288_; 
v_as_4287_ = lean_array_push(v_as_4282_, v_a_4284_);
v___x_4288_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4283_, v_as_4287_, v___x_4285_);
return v___x_4288_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg___boxed(lean_object* v_as_4289_, lean_object* v_i_4290_, lean_object* v_a_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Array_insertIdxIfInBounds___redArg(v_as_4289_, v_i_4290_, v_a_4291_);
lean_dec(v_i_4290_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds(lean_object* v_00_u03b1_4293_, lean_object* v_as_4294_, lean_object* v_i_4295_, lean_object* v_a_4296_){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = l_Array_insertIdxIfInBounds___redArg(v_as_4294_, v_i_4295_, v_a_4296_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___boxed(lean_object* v_00_u03b1_4298_, lean_object* v_as_4299_, lean_object* v_i_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l_Array_insertIdxIfInBounds(v_00_u03b1_4298_, v_as_4299_, v_i_4300_, v_a_4301_);
lean_dec(v_i_4300_);
return v_res_4302_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux___redArg(lean_object* v_inst_4303_, lean_object* v_as_4304_, lean_object* v_bs_4305_, lean_object* v_i_4306_){
_start:
{
lean_object* v___x_4307_; uint8_t v___x_4308_; 
v___x_4307_ = lean_array_get_size(v_as_4304_);
v___x_4308_ = lean_nat_dec_lt(v_i_4306_, v___x_4307_);
if (v___x_4308_ == 0)
{
uint8_t v___x_4309_; 
lean_dec(v_i_4306_);
lean_dec_ref(v_inst_4303_);
v___x_4309_ = 1;
return v___x_4309_;
}
else
{
lean_object* v_a_4310_; lean_object* v_b_4311_; lean_object* v___x_4312_; uint8_t v___x_4313_; 
v_a_4310_ = lean_array_fget_borrowed(v_as_4304_, v_i_4306_);
v_b_4311_ = lean_array_fget_borrowed(v_bs_4305_, v_i_4306_);
lean_inc_ref(v_inst_4303_);
lean_inc(v_b_4311_);
lean_inc(v_a_4310_);
v___x_4312_ = lean_apply_2(v_inst_4303_, v_a_4310_, v_b_4311_);
v___x_4313_ = lean_unbox(v___x_4312_);
if (v___x_4313_ == 0)
{
uint8_t v___x_4314_; 
lean_dec(v_i_4306_);
lean_dec_ref(v_inst_4303_);
v___x_4314_ = lean_unbox(v___x_4312_);
return v___x_4314_;
}
else
{
lean_object* v___x_4315_; lean_object* v___x_4316_; 
v___x_4315_ = lean_unsigned_to_nat(1u);
v___x_4316_ = lean_nat_add(v_i_4306_, v___x_4315_);
lean_dec(v_i_4306_);
v_i_4306_ = v___x_4316_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___redArg___boxed(lean_object* v_inst_4318_, lean_object* v_as_4319_, lean_object* v_bs_4320_, lean_object* v_i_4321_){
_start:
{
uint8_t v_res_4322_; lean_object* v_r_4323_; 
v_res_4322_ = l_Array_isPrefixOfAux___redArg(v_inst_4318_, v_as_4319_, v_bs_4320_, v_i_4321_);
lean_dec_ref(v_bs_4320_);
lean_dec_ref(v_as_4319_);
v_r_4323_ = lean_box(v_res_4322_);
return v_r_4323_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux(lean_object* v_00_u03b1_4324_, lean_object* v_inst_4325_, lean_object* v_as_4326_, lean_object* v_bs_4327_, lean_object* v_hle_4328_, lean_object* v_i_4329_){
_start:
{
uint8_t v___x_4330_; 
v___x_4330_ = l_Array_isPrefixOfAux___redArg(v_inst_4325_, v_as_4326_, v_bs_4327_, v_i_4329_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___boxed(lean_object* v_00_u03b1_4331_, lean_object* v_inst_4332_, lean_object* v_as_4333_, lean_object* v_bs_4334_, lean_object* v_hle_4335_, lean_object* v_i_4336_){
_start:
{
uint8_t v_res_4337_; lean_object* v_r_4338_; 
v_res_4337_ = l_Array_isPrefixOfAux(v_00_u03b1_4331_, v_inst_4332_, v_as_4333_, v_bs_4334_, v_hle_4335_, v_i_4336_);
lean_dec_ref(v_bs_4334_);
lean_dec_ref(v_as_4333_);
v_r_4338_ = lean_box(v_res_4337_);
return v_r_4338_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf___redArg(lean_object* v_inst_4339_, lean_object* v_as_4340_, lean_object* v_bs_4341_){
_start:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; uint8_t v___x_4344_; 
v___x_4342_ = lean_array_get_size(v_as_4340_);
v___x_4343_ = lean_array_get_size(v_bs_4341_);
v___x_4344_ = lean_nat_dec_le(v___x_4342_, v___x_4343_);
if (v___x_4344_ == 0)
{
lean_dec_ref(v_inst_4339_);
return v___x_4344_;
}
else
{
lean_object* v___x_4345_; uint8_t v___x_4346_; 
v___x_4345_ = lean_unsigned_to_nat(0u);
v___x_4346_ = l_Array_isPrefixOfAux___redArg(v_inst_4339_, v_as_4340_, v_bs_4341_, v___x_4345_);
return v___x_4346_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___redArg___boxed(lean_object* v_inst_4347_, lean_object* v_as_4348_, lean_object* v_bs_4349_){
_start:
{
uint8_t v_res_4350_; lean_object* v_r_4351_; 
v_res_4350_ = l_Array_isPrefixOf___redArg(v_inst_4347_, v_as_4348_, v_bs_4349_);
lean_dec_ref(v_bs_4349_);
lean_dec_ref(v_as_4348_);
v_r_4351_ = lean_box(v_res_4350_);
return v_r_4351_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf(lean_object* v_00_u03b1_4352_, lean_object* v_inst_4353_, lean_object* v_as_4354_, lean_object* v_bs_4355_){
_start:
{
uint8_t v___x_4356_; 
v___x_4356_ = l_Array_isPrefixOf___redArg(v_inst_4353_, v_as_4354_, v_bs_4355_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___boxed(lean_object* v_00_u03b1_4357_, lean_object* v_inst_4358_, lean_object* v_as_4359_, lean_object* v_bs_4360_){
_start:
{
uint8_t v_res_4361_; lean_object* v_r_4362_; 
v_res_4361_ = l_Array_isPrefixOf(v_00_u03b1_4357_, v_inst_4358_, v_as_4359_, v_bs_4360_);
lean_dec_ref(v_bs_4360_);
lean_dec_ref(v_as_4359_);
v_r_4362_ = lean_box(v_res_4361_);
return v_r_4362_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0___boxed(lean_object* v_i_4363_, lean_object* v_cs_4364_, lean_object* v_inst_4365_, lean_object* v_as_4366_, lean_object* v_bs_4367_, lean_object* v_f_4368_, lean_object* v_____do__lift_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Array_zipWithMAux___redArg___lam__0(v_i_4363_, v_cs_4364_, v_inst_4365_, v_as_4366_, v_bs_4367_, v_f_4368_, v_____do__lift_4369_);
lean_dec(v_i_4363_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg(lean_object* v_inst_4371_, lean_object* v_as_4372_, lean_object* v_bs_4373_, lean_object* v_f_4374_, lean_object* v_i_4375_, lean_object* v_cs_4376_){
_start:
{
lean_object* v___x_4377_; uint8_t v___x_4378_; 
v___x_4377_ = lean_array_get_size(v_as_4372_);
v___x_4378_ = lean_nat_dec_lt(v_i_4375_, v___x_4377_);
if (v___x_4378_ == 0)
{
lean_object* v_toApplicative_4379_; lean_object* v_toPure_4380_; lean_object* v___x_4381_; 
lean_dec(v_i_4375_);
lean_dec(v_f_4374_);
lean_dec_ref(v_bs_4373_);
lean_dec_ref(v_as_4372_);
v_toApplicative_4379_ = lean_ctor_get(v_inst_4371_, 0);
lean_inc_ref(v_toApplicative_4379_);
lean_dec_ref(v_inst_4371_);
v_toPure_4380_ = lean_ctor_get(v_toApplicative_4379_, 1);
lean_inc(v_toPure_4380_);
lean_dec_ref(v_toApplicative_4379_);
v___x_4381_ = lean_apply_2(v_toPure_4380_, lean_box(0), v_cs_4376_);
return v___x_4381_;
}
else
{
lean_object* v___x_4382_; uint8_t v___x_4383_; 
v___x_4382_ = lean_array_get_size(v_bs_4373_);
v___x_4383_ = lean_nat_dec_lt(v_i_4375_, v___x_4382_);
if (v___x_4383_ == 0)
{
lean_object* v_toApplicative_4384_; lean_object* v_toPure_4385_; lean_object* v___x_4386_; 
lean_dec(v_i_4375_);
lean_dec(v_f_4374_);
lean_dec_ref(v_bs_4373_);
lean_dec_ref(v_as_4372_);
v_toApplicative_4384_ = lean_ctor_get(v_inst_4371_, 0);
lean_inc_ref(v_toApplicative_4384_);
lean_dec_ref(v_inst_4371_);
v_toPure_4385_ = lean_ctor_get(v_toApplicative_4384_, 1);
lean_inc(v_toPure_4385_);
lean_dec_ref(v_toApplicative_4384_);
v___x_4386_ = lean_apply_2(v_toPure_4385_, lean_box(0), v_cs_4376_);
return v___x_4386_;
}
else
{
lean_object* v_toBind_4387_; lean_object* v___f_4388_; lean_object* v_a_4389_; lean_object* v_b_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v_toBind_4387_ = lean_ctor_get(v_inst_4371_, 1);
lean_inc(v_toBind_4387_);
lean_inc(v_f_4374_);
lean_inc_ref(v_bs_4373_);
lean_inc_ref(v_as_4372_);
lean_inc(v_i_4375_);
v___f_4388_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4388_, 0, v_i_4375_);
lean_closure_set(v___f_4388_, 1, v_cs_4376_);
lean_closure_set(v___f_4388_, 2, v_inst_4371_);
lean_closure_set(v___f_4388_, 3, v_as_4372_);
lean_closure_set(v___f_4388_, 4, v_bs_4373_);
lean_closure_set(v___f_4388_, 5, v_f_4374_);
v_a_4389_ = lean_array_fget(v_as_4372_, v_i_4375_);
lean_dec_ref(v_as_4372_);
v_b_4390_ = lean_array_fget(v_bs_4373_, v_i_4375_);
lean_dec(v_i_4375_);
lean_dec_ref(v_bs_4373_);
v___x_4391_ = lean_apply_2(v_f_4374_, v_a_4389_, v_b_4390_);
v___x_4392_ = lean_apply_4(v_toBind_4387_, lean_box(0), lean_box(0), v___x_4391_, v___f_4388_);
return v___x_4392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0(lean_object* v_i_4393_, lean_object* v_cs_4394_, lean_object* v_inst_4395_, lean_object* v_as_4396_, lean_object* v_bs_4397_, lean_object* v_f_4398_, lean_object* v_____do__lift_4399_){
_start:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4400_ = lean_unsigned_to_nat(1u);
v___x_4401_ = lean_nat_add(v_i_4393_, v___x_4400_);
v___x_4402_ = lean_array_push(v_cs_4394_, v_____do__lift_4399_);
v___x_4403_ = l_Array_zipWithMAux___redArg(v_inst_4395_, v_as_4396_, v_bs_4397_, v_f_4398_, v___x_4401_, v___x_4402_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux(lean_object* v_00_u03b1_4404_, lean_object* v_00_u03b2_4405_, lean_object* v_00_u03b3_4406_, lean_object* v_m_4407_, lean_object* v_inst_4408_, lean_object* v_as_4409_, lean_object* v_bs_4410_, lean_object* v_f_4411_, lean_object* v_i_4412_, lean_object* v_cs_4413_){
_start:
{
lean_object* v___x_4414_; 
v___x_4414_ = l_Array_zipWithMAux___redArg(v_inst_4408_, v_as_4409_, v_bs_4410_, v_f_4411_, v_i_4412_, v_cs_4413_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith___redArg(lean_object* v_f_4415_, lean_object* v_as_4416_, lean_object* v_bs_4417_){
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
LEAN_EXPORT lean_object* l_Array_zipWith(lean_object* v_00_u03b1_4423_, lean_object* v_00_u03b2_4424_, lean_object* v_00_u03b3_4425_, lean_object* v_f_4426_, lean_object* v_as_4427_, lean_object* v_bs_4428_){
_start:
{
lean_object* v___f_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___f_4429_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4429_, 0, v_f_4426_);
v___x_4430_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4431_ = lean_unsigned_to_nat(0u);
v___x_4432_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4433_ = l_Array_zipWithMAux___redArg(v___x_4430_, v_as_4427_, v_bs_4428_, v___f_4429_, v___x_4431_, v___x_4432_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(lean_object* v_as_4434_, lean_object* v_bs_4435_, lean_object* v_i_4436_, lean_object* v_cs_4437_){
_start:
{
lean_object* v___x_4438_; uint8_t v___x_4439_; 
v___x_4438_ = lean_array_get_size(v_as_4434_);
v___x_4439_ = lean_nat_dec_lt(v_i_4436_, v___x_4438_);
if (v___x_4439_ == 0)
{
lean_dec(v_i_4436_);
return v_cs_4437_;
}
else
{
lean_object* v___x_4440_; uint8_t v___x_4441_; 
v___x_4440_ = lean_array_get_size(v_bs_4435_);
v___x_4441_ = lean_nat_dec_lt(v_i_4436_, v___x_4440_);
if (v___x_4441_ == 0)
{
lean_dec(v_i_4436_);
return v_cs_4437_;
}
else
{
lean_object* v_a_4442_; lean_object* v_b_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; 
v_a_4442_ = lean_array_fget_borrowed(v_as_4434_, v_i_4436_);
v_b_4443_ = lean_array_fget_borrowed(v_bs_4435_, v_i_4436_);
lean_inc(v_b_4443_);
lean_inc(v_a_4442_);
v___x_4444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4444_, 0, v_a_4442_);
lean_ctor_set(v___x_4444_, 1, v_b_4443_);
v___x_4445_ = lean_unsigned_to_nat(1u);
v___x_4446_ = lean_nat_add(v_i_4436_, v___x_4445_);
lean_dec(v_i_4436_);
v___x_4447_ = lean_array_push(v_cs_4437_, v___x_4444_);
v_i_4436_ = v___x_4446_;
v_cs_4437_ = v___x_4447_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg___boxed(lean_object* v_as_4449_, lean_object* v_bs_4450_, lean_object* v_i_4451_, lean_object* v_cs_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4449_, v_bs_4450_, v_i_4451_, v_cs_4452_);
lean_dec_ref(v_bs_4450_);
lean_dec_ref(v_as_4449_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg(lean_object* v_as_4456_, lean_object* v_bs_4457_){
_start:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4458_ = lean_unsigned_to_nat(0u);
v___x_4459_ = ((lean_object*)(l_Array_zip___redArg___closed__0));
v___x_4460_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4456_, v_bs_4457_, v___x_4458_, v___x_4459_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg___boxed(lean_object* v_as_4461_, lean_object* v_bs_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_Array_zip___redArg(v_as_4461_, v_bs_4462_);
lean_dec_ref(v_bs_4462_);
lean_dec_ref(v_as_4461_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l_Array_zip(lean_object* v_00_u03b1_4464_, lean_object* v_00_u03b2_4465_, lean_object* v_as_4466_, lean_object* v_bs_4467_){
_start:
{
lean_object* v___x_4468_; 
v___x_4468_ = l_Array_zip___redArg(v_as_4466_, v_bs_4467_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___boxed(lean_object* v_00_u03b1_4469_, lean_object* v_00_u03b2_4470_, lean_object* v_as_4471_, lean_object* v_bs_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l_Array_zip(v_00_u03b1_4469_, v_00_u03b2_4470_, v_as_4471_, v_bs_4472_);
lean_dec_ref(v_bs_4472_);
lean_dec_ref(v_as_4471_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0(lean_object* v_00_u03b1_4474_, lean_object* v_00_u03b2_4475_, lean_object* v_as_4476_, lean_object* v_bs_4477_, lean_object* v_i_4478_, lean_object* v_cs_4479_){
_start:
{
lean_object* v___x_4480_; 
v___x_4480_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4476_, v_bs_4477_, v_i_4478_, v_cs_4479_);
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___boxed(lean_object* v_00_u03b1_4481_, lean_object* v_00_u03b2_4482_, lean_object* v_as_4483_, lean_object* v_bs_4484_, lean_object* v_i_4485_, lean_object* v_cs_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l_Array_zipWithMAux___at___00Array_zip_spec__0(v_00_u03b1_4481_, v_00_u03b2_4482_, v_as_4483_, v_bs_4484_, v_i_4485_, v_cs_4486_);
lean_dec_ref(v_bs_4484_);
lean_dec_ref(v_as_4483_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(lean_object* v_f_4488_, lean_object* v_as_4489_, lean_object* v_bs_4490_, lean_object* v_i_4491_, lean_object* v_cs_4492_){
_start:
{
lean_object* v___y_4494_; lean_object* v___y_4495_; lean_object* v___y_4502_; lean_object* v___y_4509_; lean_object* v___x_4516_; lean_object* v___x_4517_; uint8_t v___x_4518_; 
v___x_4516_ = lean_array_get_size(v_as_4489_);
v___x_4517_ = lean_array_get_size(v_bs_4490_);
v___x_4518_ = lean_nat_dec_le(v___x_4516_, v___x_4517_);
if (v___x_4518_ == 0)
{
v___y_4509_ = v___x_4516_;
goto v___jp_4508_;
}
else
{
v___y_4509_ = v___x_4517_;
goto v___jp_4508_;
}
v___jp_4493_:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4496_ = lean_unsigned_to_nat(1u);
v___x_4497_ = lean_nat_add(v_i_4491_, v___x_4496_);
lean_dec(v_i_4491_);
lean_inc(v_f_4488_);
v___x_4498_ = lean_apply_2(v_f_4488_, v___y_4494_, v___y_4495_);
v___x_4499_ = lean_array_push(v_cs_4492_, v___x_4498_);
v_i_4491_ = v___x_4497_;
v_cs_4492_ = v___x_4499_;
goto _start;
}
v___jp_4501_:
{
lean_object* v___x_4503_; uint8_t v___x_4504_; 
v___x_4503_ = lean_array_get_size(v_bs_4490_);
v___x_4504_ = lean_nat_dec_lt(v_i_4491_, v___x_4503_);
if (v___x_4504_ == 0)
{
lean_object* v___x_4505_; 
v___x_4505_ = lean_box(0);
v___y_4494_ = v___y_4502_;
v___y_4495_ = v___x_4505_;
goto v___jp_4493_;
}
else
{
lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4506_ = lean_array_fget_borrowed(v_bs_4490_, v_i_4491_);
lean_inc(v___x_4506_);
v___x_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4506_);
v___y_4494_ = v___y_4502_;
v___y_4495_ = v___x_4507_;
goto v___jp_4493_;
}
}
v___jp_4508_:
{
uint8_t v___x_4510_; 
v___x_4510_ = lean_nat_dec_lt(v_i_4491_, v___y_4509_);
lean_dec(v___y_4509_);
if (v___x_4510_ == 0)
{
lean_dec(v_i_4491_);
lean_dec(v_f_4488_);
return v_cs_4492_;
}
else
{
lean_object* v___x_4511_; uint8_t v___x_4512_; 
v___x_4511_ = lean_array_get_size(v_as_4489_);
v___x_4512_ = lean_nat_dec_lt(v_i_4491_, v___x_4511_);
if (v___x_4512_ == 0)
{
lean_object* v___x_4513_; 
v___x_4513_ = lean_box(0);
v___y_4502_ = v___x_4513_;
goto v___jp_4501_;
}
else
{
lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4514_ = lean_array_fget_borrowed(v_as_4489_, v_i_4491_);
lean_inc(v___x_4514_);
v___x_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4515_, 0, v___x_4514_);
v___y_4502_ = v___x_4515_;
goto v___jp_4501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg___boxed(lean_object* v_f_4519_, lean_object* v_as_4520_, lean_object* v_bs_4521_, lean_object* v_i_4522_, lean_object* v_cs_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4519_, v_as_4520_, v_bs_4521_, v_i_4522_, v_cs_4523_);
lean_dec_ref(v_bs_4521_);
lean_dec_ref(v_as_4520_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(lean_object* v_00_u03b1_4525_, lean_object* v_00_u03b2_4526_, lean_object* v_00_u03b3_4527_, lean_object* v_f_4528_, lean_object* v_as_4529_, lean_object* v_bs_4530_, lean_object* v_i_4531_, lean_object* v_cs_4532_){
_start:
{
lean_object* v___x_4533_; 
v___x_4533_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4528_, v_as_4529_, v_bs_4530_, v_i_4531_, v_cs_4532_);
return v___x_4533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___boxed(lean_object* v_00_u03b1_4534_, lean_object* v_00_u03b2_4535_, lean_object* v_00_u03b3_4536_, lean_object* v_f_4537_, lean_object* v_as_4538_, lean_object* v_bs_4539_, lean_object* v_i_4540_, lean_object* v_cs_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(v_00_u03b1_4534_, v_00_u03b2_4535_, v_00_u03b3_4536_, v_f_4537_, v_as_4538_, v_bs_4539_, v_i_4540_, v_cs_4541_);
lean_dec_ref(v_bs_4539_);
lean_dec_ref(v_as_4538_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg(lean_object* v_f_4543_, lean_object* v_as_4544_, lean_object* v_bs_4545_){
_start:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4546_ = lean_unsigned_to_nat(0u);
v___x_4547_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4548_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4543_, v_as_4544_, v_bs_4545_, v___x_4546_, v___x_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg___boxed(lean_object* v_f_4549_, lean_object* v_as_4550_, lean_object* v_bs_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_Array_zipWithAll___redArg(v_f_4549_, v_as_4550_, v_bs_4551_);
lean_dec_ref(v_bs_4551_);
lean_dec_ref(v_as_4550_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll(lean_object* v_00_u03b1_4553_, lean_object* v_00_u03b2_4554_, lean_object* v_00_u03b3_4555_, lean_object* v_f_4556_, lean_object* v_as_4557_, lean_object* v_bs_4558_){
_start:
{
lean_object* v___x_4559_; 
v___x_4559_ = l_Array_zipWithAll___redArg(v_f_4556_, v_as_4557_, v_bs_4558_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___boxed(lean_object* v_00_u03b1_4560_, lean_object* v_00_u03b2_4561_, lean_object* v_00_u03b3_4562_, lean_object* v_f_4563_, lean_object* v_as_4564_, lean_object* v_bs_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Array_zipWithAll(v_00_u03b1_4560_, v_00_u03b2_4561_, v_00_u03b3_4562_, v_f_4563_, v_as_4564_, v_bs_4565_);
lean_dec_ref(v_bs_4565_);
lean_dec_ref(v_as_4564_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM___redArg(lean_object* v_inst_4567_, lean_object* v_f_4568_, lean_object* v_as_4569_, lean_object* v_bs_4570_){
_start:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4571_ = lean_unsigned_to_nat(0u);
v___x_4572_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4573_ = l_Array_zipWithMAux___redArg(v_inst_4567_, v_as_4569_, v_bs_4570_, v_f_4568_, v___x_4571_, v___x_4572_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM(lean_object* v_00_u03b1_4574_, lean_object* v_00_u03b2_4575_, lean_object* v_00_u03b3_4576_, lean_object* v_m_4577_, lean_object* v_inst_4578_, lean_object* v_f_4579_, lean_object* v_as_4580_, lean_object* v_bs_4581_){
_start:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4582_ = lean_unsigned_to_nat(0u);
v___x_4583_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4584_ = l_Array_zipWithMAux___redArg(v_inst_4578_, v_as_4580_, v_bs_4581_, v_f_4579_, v___x_4582_, v___x_4583_);
return v___x_4584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(lean_object* v_as_4585_, size_t v_i_4586_, size_t v_stop_4587_, lean_object* v_b_4588_){
_start:
{
uint8_t v___x_4589_; 
v___x_4589_ = lean_usize_dec_eq(v_i_4586_, v_stop_4587_);
if (v___x_4589_ == 0)
{
lean_object* v_fst_4590_; lean_object* v_snd_4591_; lean_object* v___x_4592_; lean_object* v_fst_4593_; lean_object* v_snd_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4606_; 
v_fst_4590_ = lean_ctor_get(v_b_4588_, 0);
lean_inc(v_fst_4590_);
v_snd_4591_ = lean_ctor_get(v_b_4588_, 1);
lean_inc(v_snd_4591_);
lean_dec_ref(v_b_4588_);
v___x_4592_ = lean_array_uget(v_as_4585_, v_i_4586_);
v_fst_4593_ = lean_ctor_get(v___x_4592_, 0);
v_snd_4594_ = lean_ctor_get(v___x_4592_, 1);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4596_ = v___x_4592_;
v_isShared_4597_ = v_isSharedCheck_4606_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_snd_4594_);
lean_inc(v_fst_4593_);
lean_dec(v___x_4592_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4606_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4601_; 
v___x_4598_ = lean_array_push(v_fst_4590_, v_fst_4593_);
v___x_4599_ = lean_array_push(v_snd_4591_, v_snd_4594_);
if (v_isShared_4597_ == 0)
{
lean_ctor_set(v___x_4596_, 1, v___x_4599_);
lean_ctor_set(v___x_4596_, 0, v___x_4598_);
v___x_4601_ = v___x_4596_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4598_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v___x_4599_);
v___x_4601_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
size_t v___x_4602_; size_t v___x_4603_; 
v___x_4602_ = ((size_t)1ULL);
v___x_4603_ = lean_usize_add(v_i_4586_, v___x_4602_);
v_i_4586_ = v___x_4603_;
v_b_4588_ = v___x_4601_;
goto _start;
}
}
}
else
{
return v_b_4588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg___boxed(lean_object* v_as_4607_, lean_object* v_i_4608_, lean_object* v_stop_4609_, lean_object* v_b_4610_){
_start:
{
size_t v_i_boxed_4611_; size_t v_stop_boxed_4612_; lean_object* v_res_4613_; 
v_i_boxed_4611_ = lean_unbox_usize(v_i_4608_);
lean_dec(v_i_4608_);
v_stop_boxed_4612_ = lean_unbox_usize(v_stop_4609_);
lean_dec(v_stop_4609_);
v_res_4613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4607_, v_i_boxed_4611_, v_stop_boxed_4612_, v_b_4610_);
lean_dec_ref(v_as_4607_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg(lean_object* v_as_4614_){
_start:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; uint8_t v___x_4618_; 
v___x_4615_ = lean_unsigned_to_nat(0u);
v___x_4616_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v___x_4617_ = lean_array_get_size(v_as_4614_);
v___x_4618_ = lean_nat_dec_lt(v___x_4615_, v___x_4617_);
if (v___x_4618_ == 0)
{
return v___x_4616_;
}
else
{
uint8_t v___x_4619_; 
v___x_4619_ = lean_nat_dec_le(v___x_4617_, v___x_4617_);
if (v___x_4619_ == 0)
{
if (v___x_4618_ == 0)
{
return v___x_4616_;
}
else
{
size_t v___x_4620_; size_t v___x_4621_; lean_object* v___x_4622_; 
v___x_4620_ = ((size_t)0ULL);
v___x_4621_ = lean_usize_of_nat(v___x_4617_);
v___x_4622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4614_, v___x_4620_, v___x_4621_, v___x_4616_);
return v___x_4622_;
}
}
else
{
size_t v___x_4623_; size_t v___x_4624_; lean_object* v___x_4625_; 
v___x_4623_ = ((size_t)0ULL);
v___x_4624_ = lean_usize_of_nat(v___x_4617_);
v___x_4625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4614_, v___x_4623_, v___x_4624_, v___x_4616_);
return v___x_4625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg___boxed(lean_object* v_as_4626_){
_start:
{
lean_object* v_res_4627_; 
v_res_4627_ = l_Array_unzip___redArg(v_as_4626_);
lean_dec_ref(v_as_4626_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip(lean_object* v_00_u03b1_4628_, lean_object* v_00_u03b2_4629_, lean_object* v_as_4630_){
_start:
{
lean_object* v___x_4631_; 
v___x_4631_ = l_Array_unzip___redArg(v_as_4630_);
return v___x_4631_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___boxed(lean_object* v_00_u03b1_4632_, lean_object* v_00_u03b2_4633_, lean_object* v_as_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l_Array_unzip(v_00_u03b1_4632_, v_00_u03b2_4633_, v_as_4634_);
lean_dec_ref(v_as_4634_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(lean_object* v_00_u03b1_4636_, lean_object* v_00_u03b2_4637_, lean_object* v_as_4638_, size_t v_i_4639_, size_t v_stop_4640_, lean_object* v_b_4641_){
_start:
{
lean_object* v___x_4642_; 
v___x_4642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4638_, v_i_4639_, v_stop_4640_, v_b_4641_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___boxed(lean_object* v_00_u03b1_4643_, lean_object* v_00_u03b2_4644_, lean_object* v_as_4645_, lean_object* v_i_4646_, lean_object* v_stop_4647_, lean_object* v_b_4648_){
_start:
{
size_t v_i_boxed_4649_; size_t v_stop_boxed_4650_; lean_object* v_res_4651_; 
v_i_boxed_4649_ = lean_unbox_usize(v_i_4646_);
lean_dec(v_i_4646_);
v_stop_boxed_4650_ = lean_unbox_usize(v_stop_4647_);
lean_dec(v_stop_4647_);
v_res_4651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(v_00_u03b1_4643_, v_00_u03b2_4644_, v_as_4645_, v_i_boxed_4649_, v_stop_boxed_4650_, v_b_4648_);
lean_dec_ref(v_as_4645_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l_Array_replace___redArg(lean_object* v_inst_4652_, lean_object* v_xs_4653_, lean_object* v_a_4654_, lean_object* v_b_4655_){
_start:
{
lean_object* v___x_4656_; 
v___x_4656_ = l_Array_finIdxOf_x3f___redArg(v_inst_4652_, v_xs_4653_, v_a_4654_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_dec(v_b_4655_);
return v_xs_4653_;
}
else
{
lean_object* v_val_4657_; lean_object* v___x_4658_; 
v_val_4657_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_val_4657_);
lean_dec_ref_known(v___x_4656_, 1);
v___x_4658_ = lean_array_fset(v_xs_4653_, v_val_4657_, v_b_4655_);
lean_dec(v_val_4657_);
return v___x_4658_;
}
}
}
LEAN_EXPORT lean_object* l_Array_replace(lean_object* v_00_u03b1_4659_, lean_object* v_inst_4660_, lean_object* v_xs_4661_, lean_object* v_a_4662_, lean_object* v_b_4663_){
_start:
{
lean_object* v___x_4664_; 
v___x_4664_ = l_Array_replace___redArg(v_inst_4660_, v_xs_4661_, v_a_4662_, v_b_4663_);
return v___x_4664_;
}
}
LEAN_EXPORT lean_object* l_Array_instLT(lean_object* v_00_u03b1_4665_, lean_object* v_inst_4666_){
_start:
{
lean_object* v___x_4667_; 
v___x_4667_ = lean_box(0);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Array_instLE(lean_object* v_00_u03b1_4668_, lean_object* v_inst_4669_){
_start:
{
lean_object* v___x_4670_; 
v___x_4670_ = lean_box(0);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg(lean_object* v_n_4671_, lean_object* v_a_4672_, lean_object* v_xs_4673_){
_start:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4674_ = lean_array_get_size(v_xs_4673_);
v___x_4675_ = lean_nat_sub(v_n_4671_, v___x_4674_);
v___x_4676_ = lean_mk_array(v___x_4675_, v_a_4672_);
v___x_4677_ = l_Array_append___redArg(v___x_4676_, v_xs_4673_);
return v___x_4677_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg___boxed(lean_object* v_n_4678_, lean_object* v_a_4679_, lean_object* v_xs_4680_){
_start:
{
lean_object* v_res_4681_; 
v_res_4681_ = l_Array_leftpad___redArg(v_n_4678_, v_a_4679_, v_xs_4680_);
lean_dec_ref(v_xs_4680_);
lean_dec(v_n_4678_);
return v_res_4681_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad(lean_object* v_00_u03b1_4682_, lean_object* v_n_4683_, lean_object* v_a_4684_, lean_object* v_xs_4685_){
_start:
{
lean_object* v___x_4686_; 
v___x_4686_ = l_Array_leftpad___redArg(v_n_4683_, v_a_4684_, v_xs_4685_);
return v___x_4686_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___boxed(lean_object* v_00_u03b1_4687_, lean_object* v_n_4688_, lean_object* v_a_4689_, lean_object* v_xs_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l_Array_leftpad(v_00_u03b1_4687_, v_n_4688_, v_a_4689_, v_xs_4690_);
lean_dec_ref(v_xs_4690_);
lean_dec(v_n_4688_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg(lean_object* v_n_4692_, lean_object* v_a_4693_, lean_object* v_xs_4694_){
_start:
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4695_ = lean_array_get_size(v_xs_4694_);
v___x_4696_ = lean_nat_sub(v_n_4692_, v___x_4695_);
v___x_4697_ = lean_mk_array(v___x_4696_, v_a_4693_);
v___x_4698_ = l_Array_append___redArg(v_xs_4694_, v___x_4697_);
lean_dec_ref(v___x_4697_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg___boxed(lean_object* v_n_4699_, lean_object* v_a_4700_, lean_object* v_xs_4701_){
_start:
{
lean_object* v_res_4702_; 
v_res_4702_ = l_Array_rightpad___redArg(v_n_4699_, v_a_4700_, v_xs_4701_);
lean_dec(v_n_4699_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad(lean_object* v_00_u03b1_4703_, lean_object* v_n_4704_, lean_object* v_a_4705_, lean_object* v_xs_4706_){
_start:
{
lean_object* v___x_4707_; 
v___x_4707_ = l_Array_rightpad___redArg(v_n_4704_, v_a_4705_, v_xs_4706_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___boxed(lean_object* v_00_u03b1_4708_, lean_object* v_n_4709_, lean_object* v_a_4710_, lean_object* v_xs_4711_){
_start:
{
lean_object* v_res_4712_; 
v_res_4712_ = l_Array_rightpad(v_00_u03b1_4708_, v_n_4709_, v_a_4710_, v_xs_4711_);
lean_dec(v_n_4709_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0(lean_object* v_x_4713_){
_start:
{
lean_inc(v_x_4713_);
return v_x_4713_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0___boxed(lean_object* v_x_4714_){
_start:
{
lean_object* v_res_4715_; 
v_res_4715_ = l_Array_reduceOption___redArg___lam__0(v_x_4714_);
lean_dec(v_x_4714_);
return v_res_4715_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg(lean_object* v_as_4717_){
_start:
{
lean_object* v___f_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___f_4718_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4719_ = lean_unsigned_to_nat(0u);
v___x_4720_ = lean_array_get_size(v_as_4717_);
v___x_4721_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4722_ = l_Array_filterMapM___redArg(v___x_4721_, v___f_4718_, v_as_4717_, v___x_4719_, v___x_4720_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption(lean_object* v_00_u03b1_4723_, lean_object* v_as_4724_){
_start:
{
lean_object* v___f_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___f_4725_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4726_ = lean_unsigned_to_nat(0u);
v___x_4727_ = lean_array_get_size(v_as_4724_);
v___x_4728_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4729_ = l_Array_filterMapM___redArg(v___x_4728_, v___f_4725_, v_as_4724_, v___x_4726_, v___x_4727_);
return v___x_4729_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg___lam__0(lean_object* v_inst_4730_, lean_object* v_x1_4731_, lean_object* v_x2_4732_){
_start:
{
lean_object* v_fst_4733_; lean_object* v_snd_4734_; lean_object* v___x_4735_; uint8_t v___x_4736_; 
v_fst_4733_ = lean_ctor_get(v_x1_4731_, 0);
v_snd_4734_ = lean_ctor_get(v_x1_4731_, 1);
lean_inc(v_fst_4733_);
lean_inc(v_x2_4732_);
v___x_4735_ = lean_apply_2(v_inst_4730_, v_x2_4732_, v_fst_4733_);
v___x_4736_ = lean_unbox(v___x_4735_);
if (v___x_4736_ == 0)
{
lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4744_; 
lean_inc(v_snd_4734_);
lean_inc(v_fst_4733_);
v_isSharedCheck_4744_ = !lean_is_exclusive(v_x1_4731_);
if (v_isSharedCheck_4744_ == 0)
{
lean_object* v_unused_4745_; lean_object* v_unused_4746_; 
v_unused_4745_ = lean_ctor_get(v_x1_4731_, 1);
lean_dec(v_unused_4745_);
v_unused_4746_ = lean_ctor_get(v_x1_4731_, 0);
lean_dec(v_unused_4746_);
v___x_4738_ = v_x1_4731_;
v_isShared_4739_ = v_isSharedCheck_4744_;
goto v_resetjp_4737_;
}
else
{
lean_dec(v_x1_4731_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4744_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4740_; lean_object* v___x_4742_; 
v___x_4740_ = lean_array_push(v_snd_4734_, v_fst_4733_);
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 1, v___x_4740_);
lean_ctor_set(v___x_4738_, 0, v_x2_4732_);
v___x_4742_ = v___x_4738_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_x2_4732_);
lean_ctor_set(v_reuseFailAlloc_4743_, 1, v___x_4740_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
else
{
lean_dec(v_x2_4732_);
return v_x1_4731_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg(lean_object* v_inst_4747_, lean_object* v_as_4748_){
_start:
{
lean_object* v___y_4750_; lean_object* v___x_4754_; lean_object* v___x_4755_; uint8_t v___x_4756_; 
v___x_4754_ = lean_unsigned_to_nat(0u);
v___x_4755_ = lean_array_get_size(v_as_4748_);
v___x_4756_ = lean_nat_dec_lt(v___x_4754_, v___x_4755_);
if (v___x_4756_ == 0)
{
lean_object* v___x_4757_; 
lean_dec_ref(v_as_4748_);
lean_dec_ref(v_inst_4747_);
v___x_4757_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
return v___x_4757_;
}
else
{
lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4758_ = lean_array_fget_borrowed(v_as_4748_, v___x_4754_);
v___x_4759_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4760_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
if (v___x_4756_ == 0)
{
lean_object* v___x_4761_; 
lean_inc(v___x_4758_);
lean_dec_ref(v_as_4748_);
lean_dec_ref(v_inst_4747_);
v___x_4761_ = lean_array_push(v___x_4759_, v___x_4758_);
return v___x_4761_;
}
else
{
lean_object* v___f_4762_; lean_object* v___x_4763_; uint8_t v___x_4764_; 
v___f_4762_ = lean_alloc_closure((void*)(l_Array_eraseReps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4762_, 0, v_inst_4747_);
lean_inc(v___x_4758_);
v___x_4763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4763_, 0, v___x_4758_);
lean_ctor_set(v___x_4763_, 1, v___x_4759_);
v___x_4764_ = lean_nat_dec_le(v___x_4755_, v___x_4755_);
if (v___x_4764_ == 0)
{
if (v___x_4756_ == 0)
{
lean_object* v___x_4765_; 
lean_inc(v___x_4758_);
lean_dec_ref_known(v___x_4763_, 2);
lean_dec_ref(v___f_4762_);
lean_dec_ref(v_as_4748_);
v___x_4765_ = lean_array_push(v___x_4759_, v___x_4758_);
return v___x_4765_;
}
else
{
size_t v___x_4766_; size_t v___x_4767_; lean_object* v___x_4768_; 
v___x_4766_ = ((size_t)0ULL);
v___x_4767_ = lean_usize_of_nat(v___x_4755_);
v___x_4768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4760_, v___f_4762_, v_as_4748_, v___x_4766_, v___x_4767_, v___x_4763_);
v___y_4750_ = v___x_4768_;
goto v___jp_4749_;
}
}
else
{
size_t v___x_4769_; size_t v___x_4770_; lean_object* v___x_4771_; 
v___x_4769_ = ((size_t)0ULL);
v___x_4770_ = lean_usize_of_nat(v___x_4755_);
v___x_4771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4760_, v___f_4762_, v_as_4748_, v___x_4769_, v___x_4770_, v___x_4763_);
v___y_4750_ = v___x_4771_;
goto v___jp_4749_;
}
}
}
v___jp_4749_:
{
lean_object* v_fst_4751_; lean_object* v_snd_4752_; lean_object* v___x_4753_; 
v_fst_4751_ = lean_ctor_get(v___y_4750_, 0);
lean_inc(v_fst_4751_);
v_snd_4752_ = lean_ctor_get(v___y_4750_, 1);
lean_inc(v_snd_4752_);
lean_dec_ref(v___y_4750_);
v___x_4753_ = lean_array_push(v_snd_4752_, v_fst_4751_);
return v___x_4753_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps(lean_object* v_00_u03b1_4772_, lean_object* v_inst_4773_, lean_object* v_as_4774_){
_start:
{
lean_object* v___x_4775_; 
v___x_4775_ = l_Array_eraseReps___redArg(v_inst_4773_, v_as_4774_);
return v___x_4775_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(lean_object* v_inst_4776_, lean_object* v_as_4777_, lean_object* v_a_4778_, lean_object* v_x_4779_){
_start:
{
lean_object* v_zero_4780_; uint8_t v_isZero_4781_; 
v_zero_4780_ = lean_unsigned_to_nat(0u);
v_isZero_4781_ = lean_nat_dec_eq(v_x_4779_, v_zero_4780_);
if (v_isZero_4781_ == 1)
{
lean_dec(v_x_4779_);
lean_dec(v_a_4778_);
lean_dec_ref(v_inst_4776_);
return v_isZero_4781_;
}
else
{
lean_object* v_one_4782_; lean_object* v_n_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; uint8_t v___x_4786_; 
v_one_4782_ = lean_unsigned_to_nat(1u);
v_n_4783_ = lean_nat_sub(v_x_4779_, v_one_4782_);
lean_dec(v_x_4779_);
v___x_4784_ = lean_array_fget_borrowed(v_as_4777_, v_n_4783_);
lean_inc_ref(v_inst_4776_);
lean_inc(v___x_4784_);
lean_inc(v_a_4778_);
v___x_4785_ = lean_apply_2(v_inst_4776_, v_a_4778_, v___x_4784_);
v___x_4786_ = lean_unbox(v___x_4785_);
if (v___x_4786_ == 0)
{
v_x_4779_ = v_n_4783_;
goto _start;
}
else
{
lean_dec(v_n_4783_);
lean_dec(v_a_4778_);
lean_dec_ref(v_inst_4776_);
return v_isZero_4781_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg___boxed(lean_object* v_inst_4788_, lean_object* v_as_4789_, lean_object* v_a_4790_, lean_object* v_x_4791_){
_start:
{
uint8_t v_res_4792_; lean_object* v_r_4793_; 
v_res_4792_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4788_, v_as_4789_, v_a_4790_, v_x_4791_);
lean_dec_ref(v_as_4789_);
v_r_4793_ = lean_box(v_res_4792_);
return v_r_4793_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(lean_object* v_00_u03b1_4794_, lean_object* v_inst_4795_, lean_object* v_as_4796_, lean_object* v_a_4797_, lean_object* v_x_4798_, lean_object* v_x_4799_){
_start:
{
uint8_t v___x_4800_; 
v___x_4800_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4795_, v_as_4796_, v_a_4797_, v_x_4798_);
return v___x_4800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___boxed(lean_object* v_00_u03b1_4801_, lean_object* v_inst_4802_, lean_object* v_as_4803_, lean_object* v_a_4804_, lean_object* v_x_4805_, lean_object* v_x_4806_){
_start:
{
uint8_t v_res_4807_; lean_object* v_r_4808_; 
v_res_4807_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(v_00_u03b1_4801_, v_inst_4802_, v_as_4803_, v_a_4804_, v_x_4805_, v_x_4806_);
lean_dec_ref(v_as_4803_);
v_r_4808_ = lean_box(v_res_4807_);
return v_r_4808_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(lean_object* v_inst_4809_, lean_object* v_as_4810_, lean_object* v_i_4811_){
_start:
{
lean_object* v___x_4812_; uint8_t v___x_4813_; 
v___x_4812_ = lean_array_get_size(v_as_4810_);
v___x_4813_ = lean_nat_dec_lt(v_i_4811_, v___x_4812_);
if (v___x_4813_ == 0)
{
uint8_t v___x_4814_; 
lean_dec(v_i_4811_);
lean_dec_ref(v_inst_4809_);
v___x_4814_ = 1;
return v___x_4814_;
}
else
{
lean_object* v___x_4815_; uint8_t v___x_4816_; 
v___x_4815_ = lean_array_fget_borrowed(v_as_4810_, v_i_4811_);
lean_inc(v_i_4811_);
lean_inc(v___x_4815_);
lean_inc_ref(v_inst_4809_);
v___x_4816_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4809_, v_as_4810_, v___x_4815_, v_i_4811_);
if (v___x_4816_ == 0)
{
lean_dec(v_i_4811_);
lean_dec_ref(v_inst_4809_);
return v___x_4816_;
}
else
{
lean_object* v___x_4817_; lean_object* v___x_4818_; 
v___x_4817_ = lean_unsigned_to_nat(1u);
v___x_4818_ = lean_nat_add(v_i_4811_, v___x_4817_);
lean_dec(v_i_4811_);
v_i_4811_ = v___x_4818_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg___boxed(lean_object* v_inst_4820_, lean_object* v_as_4821_, lean_object* v_i_4822_){
_start:
{
uint8_t v_res_4823_; lean_object* v_r_4824_; 
v_res_4823_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4820_, v_as_4821_, v_i_4822_);
lean_dec_ref(v_as_4821_);
v_r_4824_ = lean_box(v_res_4823_);
return v_r_4824_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux(lean_object* v_00_u03b1_4825_, lean_object* v_inst_4826_, lean_object* v_as_4827_, lean_object* v_i_4828_){
_start:
{
uint8_t v___x_4829_; 
v___x_4829_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4826_, v_as_4827_, v_i_4828_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___boxed(lean_object* v_00_u03b1_4830_, lean_object* v_inst_4831_, lean_object* v_as_4832_, lean_object* v_i_4833_){
_start:
{
uint8_t v_res_4834_; lean_object* v_r_4835_; 
v_res_4834_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux(v_00_u03b1_4830_, v_inst_4831_, v_as_4832_, v_i_4833_);
lean_dec_ref(v_as_4832_);
v_r_4835_ = lean_box(v_res_4834_);
return v_r_4835_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___redArg(lean_object* v_inst_4836_, lean_object* v_as_4837_){
_start:
{
lean_object* v___x_4838_; uint8_t v___x_4839_; 
v___x_4838_ = lean_unsigned_to_nat(0u);
v___x_4839_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4836_, v_as_4837_, v___x_4838_);
return v___x_4839_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___redArg___boxed(lean_object* v_inst_4840_, lean_object* v_as_4841_){
_start:
{
uint8_t v_res_4842_; lean_object* v_r_4843_; 
v_res_4842_ = l_Array_allDiff___redArg(v_inst_4840_, v_as_4841_);
lean_dec_ref(v_as_4841_);
v_r_4843_ = lean_box(v_res_4842_);
return v_r_4843_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff(lean_object* v_00_u03b1_4844_, lean_object* v_inst_4845_, lean_object* v_as_4846_){
_start:
{
uint8_t v___x_4847_; 
v___x_4847_ = l_Array_allDiff___redArg(v_inst_4845_, v_as_4846_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___boxed(lean_object* v_00_u03b1_4848_, lean_object* v_inst_4849_, lean_object* v_as_4850_){
_start:
{
uint8_t v_res_4851_; lean_object* v_r_4852_; 
v_res_4851_ = l_Array_allDiff(v_00_u03b1_4848_, v_inst_4849_, v_as_4850_);
lean_dec_ref(v_as_4850_);
v_r_4852_ = lean_box(v_res_4851_);
return v_r_4852_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0(uint8_t v___x_4853_, lean_object* v_x1_4854_, lean_object* v_x2_4855_){
_start:
{
lean_object* v_fst_4856_; uint8_t v___x_4857_; 
v_fst_4856_ = lean_ctor_get(v_x1_4854_, 0);
v___x_4857_ = lean_unbox(v_fst_4856_);
if (v___x_4857_ == 0)
{
lean_object* v_snd_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4866_; 
lean_dec(v_x2_4855_);
v_snd_4858_ = lean_ctor_get(v_x1_4854_, 1);
v_isSharedCheck_4866_ = !lean_is_exclusive(v_x1_4854_);
if (v_isSharedCheck_4866_ == 0)
{
lean_object* v_unused_4867_; 
v_unused_4867_ = lean_ctor_get(v_x1_4854_, 0);
lean_dec(v_unused_4867_);
v___x_4860_ = v_x1_4854_;
v_isShared_4861_ = v_isSharedCheck_4866_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_snd_4858_);
lean_dec(v_x1_4854_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4866_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v___x_4862_; lean_object* v___x_4864_; 
v___x_4862_ = lean_box(v___x_4853_);
if (v_isShared_4861_ == 0)
{
lean_ctor_set(v___x_4860_, 0, v___x_4862_);
v___x_4864_ = v___x_4860_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v___x_4862_);
lean_ctor_set(v_reuseFailAlloc_4865_, 1, v_snd_4858_);
v___x_4864_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
return v___x_4864_;
}
}
}
else
{
lean_object* v_snd_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4878_; 
v_snd_4868_ = lean_ctor_get(v_x1_4854_, 1);
v_isSharedCheck_4878_ = !lean_is_exclusive(v_x1_4854_);
if (v_isSharedCheck_4878_ == 0)
{
lean_object* v_unused_4879_; 
v_unused_4879_ = lean_ctor_get(v_x1_4854_, 0);
lean_dec(v_unused_4879_);
v___x_4870_ = v_x1_4854_;
v_isShared_4871_ = v_isSharedCheck_4878_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_snd_4868_);
lean_dec(v_x1_4854_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4878_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
uint8_t v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4876_; 
v___x_4872_ = 0;
v___x_4873_ = lean_array_push(v_snd_4868_, v_x2_4855_);
v___x_4874_ = lean_box(v___x_4872_);
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 1, v___x_4873_);
lean_ctor_set(v___x_4870_, 0, v___x_4874_);
v___x_4876_ = v___x_4870_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v___x_4874_);
lean_ctor_set(v_reuseFailAlloc_4877_, 1, v___x_4873_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0___boxed(lean_object* v___x_4880_, lean_object* v_x1_4881_, lean_object* v_x2_4882_){
_start:
{
uint8_t v___x_172__boxed_4883_; lean_object* v_res_4884_; 
v___x_172__boxed_4883_ = lean_unbox(v___x_4880_);
v_res_4884_ = l_Array_getEvenElems___redArg___lam__0(v___x_172__boxed_4883_, v_x1_4881_, v_x2_4882_);
return v_res_4884_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg(lean_object* v_as_4885_){
_start:
{
lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; uint8_t v___x_4890_; 
v___x_4886_ = lean_unsigned_to_nat(0u);
v___x_4887_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_4888_ = lean_array_get_size(v_as_4885_);
v___x_4889_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4890_ = lean_nat_dec_lt(v___x_4886_, v___x_4888_);
if (v___x_4890_ == 0)
{
lean_dec_ref(v_as_4885_);
return v___x_4887_;
}
else
{
lean_object* v___x_4891_; lean_object* v___f_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; uint8_t v___x_4895_; 
v___x_4891_ = lean_box(v___x_4890_);
v___f_4892_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4892_, 0, v___x_4891_);
v___x_4893_ = lean_box(v___x_4890_);
v___x_4894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4894_, 0, v___x_4893_);
lean_ctor_set(v___x_4894_, 1, v___x_4887_);
v___x_4895_ = lean_nat_dec_le(v___x_4888_, v___x_4888_);
if (v___x_4895_ == 0)
{
if (v___x_4890_ == 0)
{
lean_dec_ref_known(v___x_4894_, 2);
lean_dec_ref(v___f_4892_);
lean_dec_ref(v_as_4885_);
return v___x_4887_;
}
else
{
size_t v___x_4896_; size_t v___x_4897_; lean_object* v___x_4898_; lean_object* v_snd_4899_; 
v___x_4896_ = ((size_t)0ULL);
v___x_4897_ = lean_usize_of_nat(v___x_4888_);
v___x_4898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4889_, v___f_4892_, v_as_4885_, v___x_4896_, v___x_4897_, v___x_4894_);
v_snd_4899_ = lean_ctor_get(v___x_4898_, 1);
lean_inc(v_snd_4899_);
lean_dec(v___x_4898_);
return v_snd_4899_;
}
}
else
{
size_t v___x_4900_; size_t v___x_4901_; lean_object* v___x_4902_; lean_object* v_snd_4903_; 
v___x_4900_ = ((size_t)0ULL);
v___x_4901_ = lean_usize_of_nat(v___x_4888_);
v___x_4902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4889_, v___f_4892_, v_as_4885_, v___x_4900_, v___x_4901_, v___x_4894_);
v_snd_4903_ = lean_ctor_get(v___x_4902_, 1);
lean_inc(v_snd_4903_);
lean_dec(v___x_4902_);
return v_snd_4903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems(lean_object* v_00_u03b1_4904_, lean_object* v_as_4905_){
_start:
{
lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; uint8_t v___x_4910_; 
v___x_4906_ = lean_unsigned_to_nat(0u);
v___x_4907_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_4908_ = lean_array_get_size(v_as_4905_);
v___x_4909_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4910_ = lean_nat_dec_lt(v___x_4906_, v___x_4908_);
if (v___x_4910_ == 0)
{
lean_dec_ref(v_as_4905_);
return v___x_4907_;
}
else
{
lean_object* v___x_4911_; lean_object* v___f_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; uint8_t v___x_4915_; 
v___x_4911_ = lean_box(v___x_4910_);
v___f_4912_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4912_, 0, v___x_4911_);
v___x_4913_ = lean_box(v___x_4910_);
v___x_4914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4914_, 0, v___x_4913_);
lean_ctor_set(v___x_4914_, 1, v___x_4907_);
v___x_4915_ = lean_nat_dec_le(v___x_4908_, v___x_4908_);
if (v___x_4915_ == 0)
{
if (v___x_4910_ == 0)
{
lean_dec_ref_known(v___x_4914_, 2);
lean_dec_ref(v___f_4912_);
lean_dec_ref(v_as_4905_);
return v___x_4907_;
}
else
{
size_t v___x_4916_; size_t v___x_4917_; lean_object* v___x_4918_; lean_object* v_snd_4919_; 
v___x_4916_ = ((size_t)0ULL);
v___x_4917_ = lean_usize_of_nat(v___x_4908_);
v___x_4918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4909_, v___f_4912_, v_as_4905_, v___x_4916_, v___x_4917_, v___x_4914_);
v_snd_4919_ = lean_ctor_get(v___x_4918_, 1);
lean_inc(v_snd_4919_);
lean_dec(v___x_4918_);
return v_snd_4919_;
}
}
else
{
size_t v___x_4920_; size_t v___x_4921_; lean_object* v___x_4922_; lean_object* v_snd_4923_; 
v___x_4920_ = ((size_t)0ULL);
v___x_4921_ = lean_usize_of_nat(v___x_4908_);
v___x_4922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4909_, v___f_4912_, v_as_4905_, v___x_4920_, v___x_4921_, v___x_4914_);
v_snd_4923_ = lean_ctor_get(v___x_4922_, 1);
lean_inc(v_snd_4923_);
lean_dec(v___x_4922_);
return v_snd_4923_;
}
}
}
}
static lean_object* _init_l_Array_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_4929_; lean_object* v___x_4930_; 
v___x_4929_ = ((lean_object*)(l_term_x23_x5b___x2c_x5d___closed__4));
v___x_4930_ = lean_string_length(v___x_4929_);
return v___x_4930_;
}
}
static lean_object* _init_l_Array_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_4931_; lean_object* v___x_4932_; 
v___x_4931_ = lean_obj_once(&l_Array_repr___redArg___closed__2, &l_Array_repr___redArg___closed__2_once, _init_l_Array_repr___redArg___closed__2);
v___x_4932_ = lean_nat_to_int(v___x_4931_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___redArg(lean_object* v_inst_4940_, lean_object* v_xs_4941_){
_start:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; uint8_t v___x_4944_; 
v___x_4942_ = lean_array_get_size(v_xs_4941_);
v___x_4943_ = lean_unsigned_to_nat(0u);
v___x_4944_ = lean_nat_dec_eq(v___x_4942_, v___x_4943_);
if (v___x_4944_ == 0)
{
lean_object* v_x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; 
v_x_4945_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_4945_, 0, lean_box(0));
lean_closure_set(v_x_4945_, 1, v_inst_4940_);
v___x_4946_ = lean_array_to_list(v_xs_4941_);
v___x_4947_ = ((lean_object*)(l_Array_repr___redArg___closed__1));
v___x_4948_ = l_Std_Format_joinSep___redArg(v_x_4945_, v___x_4946_, v___x_4947_);
v___x_4949_ = lean_obj_once(&l_Array_repr___redArg___closed__3, &l_Array_repr___redArg___closed__3_once, _init_l_Array_repr___redArg___closed__3);
v___x_4950_ = ((lean_object*)(l_Array_repr___redArg___closed__4));
v___x_4951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4951_, 0, v___x_4950_);
lean_ctor_set(v___x_4951_, 1, v___x_4948_);
v___x_4952_ = ((lean_object*)(l_Array_repr___redArg___closed__5));
v___x_4953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4953_, 0, v___x_4951_);
lean_ctor_set(v___x_4953_, 1, v___x_4952_);
v___x_4954_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4954_, 0, v___x_4949_);
lean_ctor_set(v___x_4954_, 1, v___x_4953_);
v___x_4955_ = l_Std_Format_fill(v___x_4954_);
return v___x_4955_;
}
else
{
lean_object* v___x_4956_; 
lean_dec_ref(v_xs_4941_);
lean_dec_ref(v_inst_4940_);
v___x_4956_ = ((lean_object*)(l_Array_repr___redArg___closed__7));
return v___x_4956_;
}
}
}
LEAN_EXPORT lean_object* l_Array_repr(lean_object* v_00_u03b1_4957_, lean_object* v_inst_4958_, lean_object* v_xs_4959_){
_start:
{
lean_object* v___x_4960_; 
v___x_4960_ = l_Array_repr___redArg(v_inst_4958_, v_xs_4959_);
return v___x_4960_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0(lean_object* v_inst_4961_, lean_object* v_xs_4962_, lean_object* v_x_4963_){
_start:
{
lean_object* v___x_4964_; 
v___x_4964_ = l_Array_repr___redArg(v_inst_4961_, v_xs_4962_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object* v_inst_4965_, lean_object* v_xs_4966_, lean_object* v_x_4967_){
_start:
{
lean_object* v_res_4968_; 
v_res_4968_ = l_Array_instRepr___redArg___lam__0(v_inst_4965_, v_xs_4966_, v_x_4967_);
lean_dec(v_x_4967_);
return v_res_4968_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg(lean_object* v_inst_4969_){
_start:
{
lean_object* v___f_4970_; 
v___f_4970_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4970_, 0, v_inst_4969_);
return v___f_4970_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr(lean_object* v_00_u03b1_4971_, lean_object* v_inst_4972_){
_start:
{
lean_object* v___f_4973_; 
v___f_4973_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4973_, 0, v_inst_4972_);
return v___f_4973_;
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
