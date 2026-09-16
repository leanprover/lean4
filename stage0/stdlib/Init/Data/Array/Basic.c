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
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0(lean_object* v_xs_x27_650_, lean_object* v_i_651_, lean_object* v_toPure_652_, lean_object* v_v_653_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_array_fset(v_xs_x27_650_, v_i_651_, v_v_653_);
v___x_655_ = lean_apply_2(v_toPure_652_, lean_box(0), v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0___boxed(lean_object* v_xs_x27_656_, lean_object* v_i_657_, lean_object* v_toPure_658_, lean_object* v_v_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Array_modifyMUnsafe___redArg___lam__0(v_xs_x27_656_, v_i_657_, v_toPure_658_, v_v_659_);
lean_dec(v_i_657_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg(lean_object* v_inst_661_, lean_object* v_xs_662_, lean_object* v_i_663_, lean_object* v_f_664_){
_start:
{
lean_object* v_toApplicative_665_; lean_object* v_toBind_666_; lean_object* v_toPure_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_toApplicative_665_ = lean_ctor_get(v_inst_661_, 0);
lean_inc_ref(v_toApplicative_665_);
v_toBind_666_ = lean_ctor_get(v_inst_661_, 1);
lean_inc(v_toBind_666_);
lean_dec_ref(v_inst_661_);
v_toPure_667_ = lean_ctor_get(v_toApplicative_665_, 1);
lean_inc(v_toPure_667_);
lean_dec_ref(v_toApplicative_665_);
v___x_668_ = lean_array_get_size(v_xs_662_);
v___x_669_ = lean_nat_dec_lt(v_i_663_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v_toBind_666_);
lean_dec(v_f_664_);
lean_dec(v_i_663_);
v___x_670_ = lean_apply_2(v_toPure_667_, lean_box(0), v_xs_662_);
return v___x_670_;
}
else
{
lean_object* v_v_671_; lean_object* v___x_672_; lean_object* v_xs_x27_673_; lean_object* v___f_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_v_671_ = lean_array_fget(v_xs_662_, v_i_663_);
v___x_672_ = lean_box(0);
v_xs_x27_673_ = lean_array_fset(v_xs_662_, v_i_663_, v___x_672_);
v___f_674_ = lean_alloc_closure((void*)(l_Array_modifyMUnsafe___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_674_, 0, v_xs_x27_673_);
lean_closure_set(v___f_674_, 1, v_i_663_);
lean_closure_set(v___f_674_, 2, v_toPure_667_);
v___x_675_ = lean_apply_1(v_f_664_, v_v_671_);
v___x_676_ = lean_apply_4(v_toBind_666_, lean_box(0), lean_box(0), v___x_675_, v___f_674_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe(lean_object* v_00_u03b1_677_, lean_object* v_m_678_, lean_object* v_inst_679_, lean_object* v_xs_680_, lean_object* v_i_681_, lean_object* v_f_682_){
_start:
{
lean_object* v_toApplicative_683_; lean_object* v_toBind_684_; lean_object* v_toPure_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v_toApplicative_683_ = lean_ctor_get(v_inst_679_, 0);
lean_inc_ref(v_toApplicative_683_);
v_toBind_684_ = lean_ctor_get(v_inst_679_, 1);
lean_inc(v_toBind_684_);
lean_dec_ref(v_inst_679_);
v_toPure_685_ = lean_ctor_get(v_toApplicative_683_, 1);
lean_inc(v_toPure_685_);
lean_dec_ref(v_toApplicative_683_);
v___x_686_ = lean_array_get_size(v_xs_680_);
v___x_687_ = lean_nat_dec_lt(v_i_681_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
lean_dec(v_toBind_684_);
lean_dec(v_f_682_);
lean_dec(v_i_681_);
v___x_688_ = lean_apply_2(v_toPure_685_, lean_box(0), v_xs_680_);
return v___x_688_;
}
else
{
lean_object* v_v_689_; lean_object* v___x_690_; lean_object* v_xs_x27_691_; lean_object* v___f_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v_v_689_ = lean_array_fget(v_xs_680_, v_i_681_);
v___x_690_ = lean_box(0);
v_xs_x27_691_ = lean_array_fset(v_xs_680_, v_i_681_, v___x_690_);
v___f_692_ = lean_alloc_closure((void*)(l_Array_modifyMUnsafe___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_692_, 0, v_xs_x27_691_);
lean_closure_set(v___f_692_, 1, v_i_681_);
lean_closure_set(v___f_692_, 2, v_toPure_685_);
v___x_693_ = lean_apply_1(v_f_682_, v_v_689_);
v___x_694_ = lean_apply_4(v_toBind_684_, lean_box(0), lean_box(0), v___x_693_, v___f_692_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___redArg(lean_object* v_xs_695_, lean_object* v_i_696_, lean_object* v_f_697_){
_start:
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = lean_array_get_size(v_xs_695_);
v___x_699_ = lean_nat_dec_lt(v_i_696_, v___x_698_);
if (v___x_699_ == 0)
{
lean_dec(v_f_697_);
return v_xs_695_;
}
else
{
lean_object* v_v_700_; lean_object* v___x_701_; lean_object* v_xs_x27_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_v_700_ = lean_array_fget(v_xs_695_, v_i_696_);
v___x_701_ = lean_box(0);
v_xs_x27_702_ = lean_array_fset(v_xs_695_, v_i_696_, v___x_701_);
v___x_703_ = lean_apply_1(v_f_697_, v_v_700_);
v___x_704_ = lean_array_fset(v_xs_x27_702_, v_i_696_, v___x_703_);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___redArg___boxed(lean_object* v_xs_705_, lean_object* v_i_706_, lean_object* v_f_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Array_modify___redArg(v_xs_705_, v_i_706_, v_f_707_);
lean_dec(v_i_706_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Array_modify(lean_object* v_00_u03b1_709_, lean_object* v_xs_710_, lean_object* v_i_711_, lean_object* v_f_712_){
_start:
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = lean_array_get_size(v_xs_710_);
v___x_714_ = lean_nat_dec_lt(v_i_711_, v___x_713_);
if (v___x_714_ == 0)
{
lean_dec(v_f_712_);
return v_xs_710_;
}
else
{
lean_object* v_v_715_; lean_object* v___x_716_; lean_object* v_xs_x27_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_v_715_ = lean_array_fget(v_xs_710_, v_i_711_);
v___x_716_ = lean_box(0);
v_xs_x27_717_ = lean_array_fset(v_xs_710_, v_i_711_, v___x_716_);
v___x_718_ = lean_apply_1(v_f_712_, v_v_715_);
v___x_719_ = lean_array_fset(v_xs_x27_717_, v_i_711_, v___x_718_);
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___boxed(lean_object* v_00_u03b1_720_, lean_object* v_xs_721_, lean_object* v_i_722_, lean_object* v_f_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Array_modify(v_00_u03b1_720_, v_xs_721_, v_i_722_, v_f_723_);
lean_dec(v_i_722_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg(lean_object* v_xs_725_, lean_object* v_idx_726_, lean_object* v_f_727_){
_start:
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = lean_array_get_size(v_xs_725_);
v___x_729_ = lean_nat_dec_lt(v_idx_726_, v___x_728_);
if (v___x_729_ == 0)
{
lean_dec(v_f_727_);
return v_xs_725_;
}
else
{
lean_object* v_v_730_; lean_object* v___x_731_; lean_object* v_xs_x27_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_v_730_ = lean_array_fget(v_xs_725_, v_idx_726_);
v___x_731_ = lean_box(0);
v_xs_x27_732_ = lean_array_fset(v_xs_725_, v_idx_726_, v___x_731_);
v___x_733_ = lean_apply_1(v_f_727_, v_v_730_);
v___x_734_ = lean_array_fset(v_xs_x27_732_, v_idx_726_, v___x_733_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg___boxed(lean_object* v_xs_735_, lean_object* v_idx_736_, lean_object* v_f_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Array_modifyOp___redArg(v_xs_735_, v_idx_736_, v_f_737_);
lean_dec(v_idx_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp(lean_object* v_00_u03b1_739_, lean_object* v_xs_740_, lean_object* v_idx_741_, lean_object* v_f_742_){
_start:
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = lean_array_get_size(v_xs_740_);
v___x_744_ = lean_nat_dec_lt(v_idx_741_, v___x_743_);
if (v___x_744_ == 0)
{
lean_dec(v_f_742_);
return v_xs_740_;
}
else
{
lean_object* v_v_745_; lean_object* v___x_746_; lean_object* v_xs_x27_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_v_745_ = lean_array_fget(v_xs_740_, v_idx_741_);
v___x_746_ = lean_box(0);
v_xs_x27_747_ = lean_array_fset(v_xs_740_, v_idx_741_, v___x_746_);
v___x_748_ = lean_apply_1(v_f_742_, v_v_745_);
v___x_749_ = lean_array_fset(v_xs_x27_747_, v_idx_741_, v___x_748_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___boxed(lean_object* v_00_u03b1_750_, lean_object* v_xs_751_, lean_object* v_idx_752_, lean_object* v_f_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Array_modifyOp(v_00_u03b1_750_, v_xs_751_, v_idx_752_, v_f_753_);
lean_dec(v_idx_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed(lean_object* v_toPure_755_, lean_object* v_i_756_, lean_object* v_inst_757_, lean_object* v_as_758_, lean_object* v_f_759_, lean_object* v_sz_760_, lean_object* v_____do__lift_761_){
_start:
{
size_t v_i_boxed_762_; size_t v_sz_boxed_763_; lean_object* v_res_764_; 
v_i_boxed_762_ = lean_unbox_usize(v_i_756_);
lean_dec(v_i_756_);
v_sz_boxed_763_ = lean_unbox_usize(v_sz_760_);
lean_dec(v_sz_760_);
v_res_764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(v_toPure_755_, v_i_boxed_762_, v_inst_757_, v_as_758_, v_f_759_, v_sz_boxed_763_, v_____do__lift_761_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(lean_object* v_inst_765_, lean_object* v_as_766_, lean_object* v_f_767_, size_t v_sz_768_, size_t v_i_769_, lean_object* v_b_770_){
_start:
{
lean_object* v_toApplicative_771_; lean_object* v_toBind_772_; lean_object* v_toPure_773_; uint8_t v___x_774_; 
v_toApplicative_771_ = lean_ctor_get(v_inst_765_, 0);
v_toBind_772_ = lean_ctor_get(v_inst_765_, 1);
lean_inc(v_toBind_772_);
v_toPure_773_ = lean_ctor_get(v_toApplicative_771_, 1);
lean_inc(v_toPure_773_);
v___x_774_ = lean_usize_dec_lt(v_i_769_, v_sz_768_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_dec(v_toBind_772_);
lean_dec(v_f_767_);
lean_dec_ref(v_as_766_);
lean_dec_ref(v_inst_765_);
v___x_775_ = lean_apply_2(v_toPure_773_, lean_box(0), v_b_770_);
return v___x_775_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___f_778_; lean_object* v_a_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_776_ = lean_box_usize(v_i_769_);
v___x_777_ = lean_box_usize(v_sz_768_);
lean_inc(v_f_767_);
lean_inc_ref(v_as_766_);
v___f_778_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_778_, 0, v_toPure_773_);
lean_closure_set(v___f_778_, 1, v___x_776_);
lean_closure_set(v___f_778_, 2, v_inst_765_);
lean_closure_set(v___f_778_, 3, v_as_766_);
lean_closure_set(v___f_778_, 4, v_f_767_);
lean_closure_set(v___f_778_, 5, v___x_777_);
v_a_779_ = lean_array_uget(v_as_766_, v_i_769_);
lean_dec_ref(v_as_766_);
v___x_780_ = lean_apply_3(v_f_767_, v_a_779_, lean_box(0), v_b_770_);
v___x_781_ = lean_apply_4(v_toBind_772_, lean_box(0), lean_box(0), v___x_780_, v___f_778_);
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(lean_object* v_toPure_782_, size_t v_i_783_, lean_object* v_inst_784_, lean_object* v_as_785_, lean_object* v_f_786_, size_t v_sz_787_, lean_object* v_____do__lift_788_){
_start:
{
if (lean_obj_tag(v_____do__lift_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_790_; 
lean_dec(v_f_786_);
lean_dec_ref(v_as_785_);
lean_dec_ref(v_inst_784_);
v_a_789_ = lean_ctor_get(v_____do__lift_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v_____do__lift_788_, 1);
v___x_790_ = lean_apply_2(v_toPure_782_, lean_box(0), v_a_789_);
return v___x_790_;
}
else
{
lean_object* v_a_791_; size_t v___x_792_; size_t v___x_793_; lean_object* v___x_794_; 
lean_dec(v_toPure_782_);
v_a_791_ = lean_ctor_get(v_____do__lift_788_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v_____do__lift_788_, 1);
v___x_792_ = ((size_t)1ULL);
v___x_793_ = lean_usize_add(v_i_783_, v___x_792_);
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_784_, v_as_785_, v_f_786_, v_sz_787_, v___x_793_, v_a_791_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___boxed(lean_object* v_inst_795_, lean_object* v_as_796_, lean_object* v_f_797_, lean_object* v_sz_798_, lean_object* v_i_799_, lean_object* v_b_800_){
_start:
{
size_t v_sz_boxed_801_; size_t v_i_boxed_802_; lean_object* v_res_803_; 
v_sz_boxed_801_ = lean_unbox_usize(v_sz_798_);
lean_dec(v_sz_798_);
v_i_boxed_802_ = lean_unbox_usize(v_i_799_);
lean_dec(v_i_799_);
v_res_803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_795_, v_as_796_, v_f_797_, v_sz_boxed_801_, v_i_boxed_802_, v_b_800_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object* v_00_u03b1_804_, lean_object* v_00_u03b2_805_, lean_object* v_m_806_, lean_object* v_inst_807_, lean_object* v_as_808_, lean_object* v_f_809_, size_t v_sz_810_, size_t v_i_811_, lean_object* v_b_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_807_, v_as_808_, v_f_809_, v_sz_810_, v_i_811_, v_b_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___boxed(lean_object* v_00_u03b1_814_, lean_object* v_00_u03b2_815_, lean_object* v_m_816_, lean_object* v_inst_817_, lean_object* v_as_818_, lean_object* v_f_819_, lean_object* v_sz_820_, lean_object* v_i_821_, lean_object* v_b_822_){
_start:
{
size_t v_sz_boxed_823_; size_t v_i_boxed_824_; lean_object* v_res_825_; 
v_sz_boxed_823_ = lean_unbox_usize(v_sz_820_);
lean_dec(v_sz_820_);
v_i_boxed_824_ = lean_unbox_usize(v_i_821_);
lean_dec(v_i_821_);
v_res_825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(v_00_u03b1_814_, v_00_u03b2_815_, v_m_816_, v_inst_817_, v_as_818_, v_f_819_, v_sz_boxed_823_, v_i_boxed_824_, v_b_822_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe___redArg(lean_object* v_inst_826_, lean_object* v_as_827_, lean_object* v_b_828_, lean_object* v_f_829_){
_start:
{
size_t v_sz_830_; size_t v___x_831_; lean_object* v___x_832_; 
v_sz_830_ = lean_array_size(v_as_827_);
v___x_831_ = ((size_t)0ULL);
v___x_832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_826_, v_as_827_, v_f_829_, v_sz_830_, v___x_831_, v_b_828_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe(lean_object* v_00_u03b1_833_, lean_object* v_00_u03b2_834_, lean_object* v_m_835_, lean_object* v_inst_836_, lean_object* v_as_837_, lean_object* v_b_838_, lean_object* v_f_839_){
_start:
{
size_t v_sz_840_; size_t v___x_841_; lean_object* v___x_842_; 
v_sz_840_ = lean_array_size(v_as_837_);
v___x_841_ = ((size_t)0ULL);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_836_, v_as_837_, v_f_839_, v_sz_840_, v___x_841_, v_b_838_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0___boxed(lean_object* v_toPure_843_, lean_object* v_inst_844_, lean_object* v_as_845_, lean_object* v_f_846_, lean_object* v_n_847_, lean_object* v_____do__lift_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Array_forIn_x27_loop___redArg___lam__0(v_toPure_843_, v_inst_844_, v_as_845_, v_f_846_, v_n_847_, v_____do__lift_848_);
lean_dec(v_n_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg(lean_object* v_inst_850_, lean_object* v_as_851_, lean_object* v_f_852_, lean_object* v_i_853_, lean_object* v_b_854_){
_start:
{
lean_object* v_toApplicative_855_; lean_object* v_toBind_856_; lean_object* v_toPure_857_; lean_object* v_zero_858_; uint8_t v_isZero_859_; 
v_toApplicative_855_ = lean_ctor_get(v_inst_850_, 0);
v_toBind_856_ = lean_ctor_get(v_inst_850_, 1);
lean_inc(v_toBind_856_);
v_toPure_857_ = lean_ctor_get(v_toApplicative_855_, 1);
lean_inc(v_toPure_857_);
v_zero_858_ = lean_unsigned_to_nat(0u);
v_isZero_859_ = lean_nat_dec_eq(v_i_853_, v_zero_858_);
if (v_isZero_859_ == 1)
{
lean_object* v___x_860_; 
lean_dec(v_toBind_856_);
lean_dec(v_f_852_);
lean_dec_ref(v_as_851_);
lean_dec_ref(v_inst_850_);
v___x_860_ = lean_apply_2(v_toPure_857_, lean_box(0), v_b_854_);
return v___x_860_;
}
else
{
lean_object* v_one_861_; lean_object* v_n_862_; lean_object* v___f_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_one_861_ = lean_unsigned_to_nat(1u);
v_n_862_ = lean_nat_sub(v_i_853_, v_one_861_);
lean_inc(v_n_862_);
lean_inc(v_f_852_);
lean_inc_ref(v_as_851_);
v___f_863_ = lean_alloc_closure((void*)(l_Array_forIn_x27_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_863_, 0, v_toPure_857_);
lean_closure_set(v___f_863_, 1, v_inst_850_);
lean_closure_set(v___f_863_, 2, v_as_851_);
lean_closure_set(v___f_863_, 3, v_f_852_);
lean_closure_set(v___f_863_, 4, v_n_862_);
v___x_864_ = lean_array_get_size(v_as_851_);
v___x_865_ = lean_nat_sub(v___x_864_, v_one_861_);
v___x_866_ = lean_nat_sub(v___x_865_, v_n_862_);
lean_dec(v_n_862_);
lean_dec(v___x_865_);
v___x_867_ = lean_array_fget(v_as_851_, v___x_866_);
lean_dec(v___x_866_);
lean_dec_ref(v_as_851_);
v___x_868_ = lean_apply_3(v_f_852_, v___x_867_, lean_box(0), v_b_854_);
v___x_869_ = lean_apply_4(v_toBind_856_, lean_box(0), lean_box(0), v___x_868_, v___f_863_);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0(lean_object* v_toPure_870_, lean_object* v_inst_871_, lean_object* v_as_872_, lean_object* v_f_873_, lean_object* v_n_874_, lean_object* v_____do__lift_875_){
_start:
{
if (lean_obj_tag(v_____do__lift_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_877_; 
lean_dec(v_f_873_);
lean_dec_ref(v_as_872_);
lean_dec_ref(v_inst_871_);
v_a_876_ = lean_ctor_get(v_____do__lift_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v_____do__lift_875_, 1);
v___x_877_ = lean_apply_2(v_toPure_870_, lean_box(0), v_a_876_);
return v___x_877_;
}
else
{
lean_object* v_a_878_; lean_object* v___x_879_; 
lean_dec(v_toPure_870_);
v_a_878_ = lean_ctor_get(v_____do__lift_875_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v_____do__lift_875_, 1);
v___x_879_ = l_Array_forIn_x27_loop___redArg(v_inst_871_, v_as_872_, v_f_873_, v_n_874_, v_a_878_);
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___boxed(lean_object* v_inst_880_, lean_object* v_as_881_, lean_object* v_f_882_, lean_object* v_i_883_, lean_object* v_b_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Array_forIn_x27_loop___redArg(v_inst_880_, v_as_881_, v_f_882_, v_i_883_, v_b_884_);
lean_dec(v_i_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop(lean_object* v_00_u03b1_886_, lean_object* v_00_u03b2_887_, lean_object* v_m_888_, lean_object* v_inst_889_, lean_object* v_as_890_, lean_object* v_f_891_, lean_object* v_i_892_, lean_object* v_h_893_, lean_object* v_b_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Array_forIn_x27_loop___redArg(v_inst_889_, v_as_890_, v_f_891_, v_i_892_, v_b_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___boxed(lean_object* v_00_u03b1_896_, lean_object* v_00_u03b2_897_, lean_object* v_m_898_, lean_object* v_inst_899_, lean_object* v_as_900_, lean_object* v_f_901_, lean_object* v_i_902_, lean_object* v_h_903_, lean_object* v_b_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Array_forIn_x27_loop(v_00_u03b1_896_, v_00_u03b2_897_, v_m_898_, v_inst_899_, v_as_900_, v_f_901_, v_i_902_, v_h_903_, v_b_904_);
lean_dec(v_i_902_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_inst_906_, lean_object* v_00_u03b2_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
size_t v_sz_911_; size_t v___x_912_; lean_object* v___x_913_; 
v_sz_911_ = lean_array_size(v___y_908_);
v___x_912_ = ((size_t)0ULL);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_906_, v___y_908_, v___y_910_, v_sz_911_, v___x_912_, v___y_909_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_914_){
_start:
{
lean_object* v___f_915_; 
v___f_915_ = lean_alloc_closure((void*)(l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_915_, 0, v_inst_914_);
return v___f_915_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_00_u03b1_916_, lean_object* v_m_917_, lean_object* v_inst_918_){
_start:
{
lean_object* v___f_919_; 
v___f_919_ = lean_alloc_closure((void*)(l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_919_, 0, v_inst_918_);
return v___f_919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_920_, lean_object* v_inst_921_, lean_object* v_f_922_, lean_object* v_as_923_, lean_object* v_stop_924_, lean_object* v_____do__lift_925_){
_start:
{
size_t v_i_boxed_926_; size_t v_stop_boxed_927_; lean_object* v_res_928_; 
v_i_boxed_926_ = lean_unbox_usize(v_i_920_);
lean_dec(v_i_920_);
v_stop_boxed_927_ = lean_unbox_usize(v_stop_924_);
lean_dec(v_stop_924_);
v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_926_, v_inst_921_, v_f_922_, v_as_923_, v_stop_boxed_927_, v_____do__lift_925_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(lean_object* v_inst_929_, lean_object* v_f_930_, lean_object* v_as_931_, size_t v_i_932_, size_t v_stop_933_, lean_object* v_b_934_){
_start:
{
lean_object* v_toApplicative_935_; lean_object* v_toBind_936_; lean_object* v_toPure_937_; uint8_t v___x_938_; 
v_toApplicative_935_ = lean_ctor_get(v_inst_929_, 0);
v_toBind_936_ = lean_ctor_get(v_inst_929_, 1);
lean_inc(v_toBind_936_);
v_toPure_937_ = lean_ctor_get(v_toApplicative_935_, 1);
v___x_938_ = lean_usize_dec_eq(v_i_932_, v_stop_933_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___f_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_939_ = lean_box_usize(v_i_932_);
v___x_940_ = lean_box_usize(v_stop_933_);
lean_inc_ref(v_as_931_);
lean_inc(v_f_930_);
v___f_941_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_941_, 0, v___x_939_);
lean_closure_set(v___f_941_, 1, v_inst_929_);
lean_closure_set(v___f_941_, 2, v_f_930_);
lean_closure_set(v___f_941_, 3, v_as_931_);
lean_closure_set(v___f_941_, 4, v___x_940_);
v___x_942_ = lean_array_uget(v_as_931_, v_i_932_);
lean_dec_ref(v_as_931_);
v___x_943_ = lean_apply_2(v_f_930_, v_b_934_, v___x_942_);
v___x_944_ = lean_apply_4(v_toBind_936_, lean_box(0), lean_box(0), v___x_943_, v___f_941_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; 
lean_inc(v_toPure_937_);
lean_dec(v_toBind_936_);
lean_dec_ref(v_as_931_);
lean_dec(v_f_930_);
lean_dec_ref(v_inst_929_);
v___x_945_ = lean_apply_2(v_toPure_937_, lean_box(0), v_b_934_);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_946_, lean_object* v_inst_947_, lean_object* v_f_948_, lean_object* v_as_949_, size_t v_stop_950_, lean_object* v_____do__lift_951_){
_start:
{
size_t v___x_952_; size_t v___x_953_; lean_object* v___x_954_; 
v___x_952_ = ((size_t)1ULL);
v___x_953_ = lean_usize_add(v_i_946_, v___x_952_);
v___x_954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_947_, v_f_948_, v_as_949_, v___x_953_, v_stop_950_, v_____do__lift_951_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_955_, lean_object* v_f_956_, lean_object* v_as_957_, lean_object* v_i_958_, lean_object* v_stop_959_, lean_object* v_b_960_){
_start:
{
size_t v_i_boxed_961_; size_t v_stop_boxed_962_; lean_object* v_res_963_; 
v_i_boxed_961_ = lean_unbox_usize(v_i_958_);
lean_dec(v_i_958_);
v_stop_boxed_962_ = lean_unbox_usize(v_stop_959_);
lean_dec(v_stop_959_);
v_res_963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_955_, v_f_956_, v_as_957_, v_i_boxed_961_, v_stop_boxed_962_, v_b_960_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object* v_00_u03b1_964_, lean_object* v_00_u03b2_965_, lean_object* v_m_966_, lean_object* v_inst_967_, lean_object* v_f_968_, lean_object* v_as_969_, size_t v_i_970_, size_t v_stop_971_, lean_object* v_b_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_967_, v_f_968_, v_as_969_, v_i_970_, v_stop_971_, v_b_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b1_974_, lean_object* v_00_u03b2_975_, lean_object* v_m_976_, lean_object* v_inst_977_, lean_object* v_f_978_, lean_object* v_as_979_, lean_object* v_i_980_, lean_object* v_stop_981_, lean_object* v_b_982_){
_start:
{
size_t v_i_boxed_983_; size_t v_stop_boxed_984_; lean_object* v_res_985_; 
v_i_boxed_983_ = lean_unbox_usize(v_i_980_);
lean_dec(v_i_980_);
v_stop_boxed_984_ = lean_unbox_usize(v_stop_981_);
lean_dec(v_stop_981_);
v_res_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(v_00_u03b1_974_, v_00_u03b2_975_, v_m_976_, v_inst_977_, v_f_978_, v_as_979_, v_i_boxed_983_, v_stop_boxed_984_, v_b_982_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg(lean_object* v_inst_986_, lean_object* v_f_987_, lean_object* v_init_988_, lean_object* v_as_989_, lean_object* v_start_990_, lean_object* v_stop_991_){
_start:
{
lean_object* v_toApplicative_992_; lean_object* v_toPure_993_; uint8_t v___x_994_; 
v_toApplicative_992_ = lean_ctor_get(v_inst_986_, 0);
v_toPure_993_ = lean_ctor_get(v_toApplicative_992_, 1);
v___x_994_ = lean_nat_dec_lt(v_start_990_, v_stop_991_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; 
lean_inc(v_toPure_993_);
lean_dec_ref(v_as_989_);
lean_dec(v_f_987_);
lean_dec_ref(v_inst_986_);
v___x_995_ = lean_apply_2(v_toPure_993_, lean_box(0), v_init_988_);
return v___x_995_;
}
else
{
lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_996_ = lean_array_get_size(v_as_989_);
v___x_997_ = lean_nat_dec_le(v_stop_991_, v___x_996_);
if (v___x_997_ == 0)
{
uint8_t v___x_998_; 
v___x_998_ = lean_nat_dec_lt(v_start_990_, v___x_996_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; 
lean_inc(v_toPure_993_);
lean_dec_ref(v_as_989_);
lean_dec(v_f_987_);
lean_dec_ref(v_inst_986_);
v___x_999_ = lean_apply_2(v_toPure_993_, lean_box(0), v_init_988_);
return v___x_999_;
}
else
{
size_t v___x_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_usize_of_nat(v_start_990_);
v___x_1001_ = lean_usize_of_nat(v___x_996_);
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_986_, v_f_987_, v_as_989_, v___x_1000_, v___x_1001_, v_init_988_);
return v___x_1002_;
}
}
else
{
size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_usize_of_nat(v_start_990_);
v___x_1004_ = lean_usize_of_nat(v_stop_991_);
v___x_1005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_986_, v_f_987_, v_as_989_, v___x_1003_, v___x_1004_, v_init_988_);
return v___x_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg___boxed(lean_object* v_inst_1006_, lean_object* v_f_1007_, lean_object* v_init_1008_, lean_object* v_as_1009_, lean_object* v_start_1010_, lean_object* v_stop_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Array_foldlMUnsafe___redArg(v_inst_1006_, v_f_1007_, v_init_1008_, v_as_1009_, v_start_1010_, v_stop_1011_);
lean_dec(v_stop_1011_);
lean_dec(v_start_1010_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe(lean_object* v_00_u03b1_1013_, lean_object* v_00_u03b2_1014_, lean_object* v_m_1015_, lean_object* v_inst_1016_, lean_object* v_f_1017_, lean_object* v_init_1018_, lean_object* v_as_1019_, lean_object* v_start_1020_, lean_object* v_stop_1021_){
_start:
{
lean_object* v_toApplicative_1022_; lean_object* v_toPure_1023_; uint8_t v___x_1024_; 
v_toApplicative_1022_ = lean_ctor_get(v_inst_1016_, 0);
v_toPure_1023_ = lean_ctor_get(v_toApplicative_1022_, 1);
v___x_1024_ = lean_nat_dec_lt(v_start_1020_, v_stop_1021_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_inc(v_toPure_1023_);
lean_dec_ref(v_as_1019_);
lean_dec(v_f_1017_);
lean_dec_ref(v_inst_1016_);
v___x_1025_ = lean_apply_2(v_toPure_1023_, lean_box(0), v_init_1018_);
return v___x_1025_;
}
else
{
lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = lean_array_get_size(v_as_1019_);
v___x_1027_ = lean_nat_dec_le(v_stop_1021_, v___x_1026_);
if (v___x_1027_ == 0)
{
uint8_t v___x_1028_; 
v___x_1028_ = lean_nat_dec_lt(v_start_1020_, v___x_1026_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; 
lean_inc(v_toPure_1023_);
lean_dec_ref(v_as_1019_);
lean_dec(v_f_1017_);
lean_dec_ref(v_inst_1016_);
v___x_1029_ = lean_apply_2(v_toPure_1023_, lean_box(0), v_init_1018_);
return v___x_1029_;
}
else
{
size_t v___x_1030_; size_t v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = lean_usize_of_nat(v_start_1020_);
v___x_1031_ = lean_usize_of_nat(v___x_1026_);
v___x_1032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1016_, v_f_1017_, v_as_1019_, v___x_1030_, v___x_1031_, v_init_1018_);
return v___x_1032_;
}
}
else
{
size_t v___x_1033_; size_t v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = lean_usize_of_nat(v_start_1020_);
v___x_1034_ = lean_usize_of_nat(v_stop_1021_);
v___x_1035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1016_, v_f_1017_, v_as_1019_, v___x_1033_, v___x_1034_, v_init_1018_);
return v___x_1035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___boxed(lean_object* v_00_u03b1_1036_, lean_object* v_00_u03b2_1037_, lean_object* v_m_1038_, lean_object* v_inst_1039_, lean_object* v_f_1040_, lean_object* v_init_1041_, lean_object* v_as_1042_, lean_object* v_start_1043_, lean_object* v_stop_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Array_foldlMUnsafe(v_00_u03b1_1036_, v_00_u03b2_1037_, v_m_1038_, v_inst_1039_, v_f_1040_, v_init_1041_, v_as_1042_, v_start_1043_, v_stop_1044_);
lean_dec(v_stop_1044_);
lean_dec(v_start_1043_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_1046_, lean_object* v_inst_1047_, lean_object* v_f_1048_, lean_object* v_as_1049_, lean_object* v_stop_1050_, lean_object* v_n_1051_, lean_object* v_____do__lift_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Array_foldlM_loop___redArg___lam__0(v_j_1046_, v_inst_1047_, v_f_1048_, v_as_1049_, v_stop_1050_, v_n_1051_, v_____do__lift_1052_);
lean_dec(v_n_1051_);
lean_dec(v_j_1046_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg(lean_object* v_inst_1054_, lean_object* v_f_1055_, lean_object* v_as_1056_, lean_object* v_stop_1057_, lean_object* v_i_1058_, lean_object* v_j_1059_, lean_object* v_b_1060_){
_start:
{
lean_object* v_toApplicative_1061_; lean_object* v_toBind_1062_; lean_object* v_toPure_1063_; uint8_t v___x_1064_; 
v_toApplicative_1061_ = lean_ctor_get(v_inst_1054_, 0);
v_toBind_1062_ = lean_ctor_get(v_inst_1054_, 1);
lean_inc(v_toBind_1062_);
v_toPure_1063_ = lean_ctor_get(v_toApplicative_1061_, 1);
v___x_1064_ = lean_nat_dec_lt(v_j_1059_, v_stop_1057_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
lean_inc(v_toPure_1063_);
lean_dec(v_toBind_1062_);
lean_dec(v_j_1059_);
lean_dec(v_stop_1057_);
lean_dec_ref(v_as_1056_);
lean_dec(v_f_1055_);
lean_dec_ref(v_inst_1054_);
v___x_1065_ = lean_apply_2(v_toPure_1063_, lean_box(0), v_b_1060_);
return v___x_1065_;
}
else
{
lean_object* v_zero_1066_; uint8_t v_isZero_1067_; 
v_zero_1066_ = lean_unsigned_to_nat(0u);
v_isZero_1067_ = lean_nat_dec_eq(v_i_1058_, v_zero_1066_);
if (v_isZero_1067_ == 1)
{
lean_object* v___x_1068_; 
lean_inc(v_toPure_1063_);
lean_dec(v_toBind_1062_);
lean_dec(v_j_1059_);
lean_dec(v_stop_1057_);
lean_dec_ref(v_as_1056_);
lean_dec(v_f_1055_);
lean_dec_ref(v_inst_1054_);
v___x_1068_ = lean_apply_2(v_toPure_1063_, lean_box(0), v_b_1060_);
return v___x_1068_;
}
else
{
lean_object* v_one_1069_; lean_object* v_n_1070_; lean_object* v___f_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_one_1069_ = lean_unsigned_to_nat(1u);
v_n_1070_ = lean_nat_sub(v_i_1058_, v_one_1069_);
lean_inc_ref(v_as_1056_);
lean_inc(v_f_1055_);
lean_inc(v_j_1059_);
v___f_1071_ = lean_alloc_closure((void*)(l_Array_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1071_, 0, v_j_1059_);
lean_closure_set(v___f_1071_, 1, v_inst_1054_);
lean_closure_set(v___f_1071_, 2, v_f_1055_);
lean_closure_set(v___f_1071_, 3, v_as_1056_);
lean_closure_set(v___f_1071_, 4, v_stop_1057_);
lean_closure_set(v___f_1071_, 5, v_n_1070_);
v___x_1072_ = lean_array_fget(v_as_1056_, v_j_1059_);
lean_dec(v_j_1059_);
lean_dec_ref(v_as_1056_);
v___x_1073_ = lean_apply_2(v_f_1055_, v_b_1060_, v___x_1072_);
v___x_1074_ = lean_apply_4(v_toBind_1062_, lean_box(0), lean_box(0), v___x_1073_, v___f_1071_);
return v___x_1074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0(lean_object* v_j_1075_, lean_object* v_inst_1076_, lean_object* v_f_1077_, lean_object* v_as_1078_, lean_object* v_stop_1079_, lean_object* v_n_1080_, lean_object* v_____do__lift_1081_){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_unsigned_to_nat(1u);
v___x_1083_ = lean_nat_add(v_j_1075_, v___x_1082_);
v___x_1084_ = l_Array_foldlM_loop___redArg(v_inst_1076_, v_f_1077_, v_as_1078_, v_stop_1079_, v_n_1080_, v___x_1083_, v_____do__lift_1081_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___boxed(lean_object* v_inst_1085_, lean_object* v_f_1086_, lean_object* v_as_1087_, lean_object* v_stop_1088_, lean_object* v_i_1089_, lean_object* v_j_1090_, lean_object* v_b_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Array_foldlM_loop___redArg(v_inst_1085_, v_f_1086_, v_as_1087_, v_stop_1088_, v_i_1089_, v_j_1090_, v_b_1091_);
lean_dec(v_i_1089_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop(lean_object* v_00_u03b1_1093_, lean_object* v_00_u03b2_1094_, lean_object* v_m_1095_, lean_object* v_inst_1096_, lean_object* v_f_1097_, lean_object* v_as_1098_, lean_object* v_stop_1099_, lean_object* v_h_1100_, lean_object* v_i_1101_, lean_object* v_j_1102_, lean_object* v_b_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Array_foldlM_loop___redArg(v_inst_1096_, v_f_1097_, v_as_1098_, v_stop_1099_, v_i_1101_, v_j_1102_, v_b_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___boxed(lean_object* v_00_u03b1_1105_, lean_object* v_00_u03b2_1106_, lean_object* v_m_1107_, lean_object* v_inst_1108_, lean_object* v_f_1109_, lean_object* v_as_1110_, lean_object* v_stop_1111_, lean_object* v_h_1112_, lean_object* v_i_1113_, lean_object* v_j_1114_, lean_object* v_b_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Array_foldlM_loop(v_00_u03b1_1105_, v_00_u03b2_1106_, v_m_1107_, v_inst_1108_, v_f_1109_, v_as_1110_, v_stop_1111_, v_h_1112_, v_i_1113_, v_j_1114_, v_b_1115_);
lean_dec(v_i_1113_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_inst_1117_, lean_object* v_f_1118_, lean_object* v_as_1119_, lean_object* v___x_1120_, lean_object* v_stop_1121_, lean_object* v_____do__lift_1122_){
_start:
{
size_t v___x_63__boxed_1123_; size_t v_stop_boxed_1124_; lean_object* v_res_1125_; 
v___x_63__boxed_1123_ = lean_unbox_usize(v___x_1120_);
lean_dec(v___x_1120_);
v_stop_boxed_1124_ = lean_unbox_usize(v_stop_1121_);
lean_dec(v_stop_1121_);
v_res_1125_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(v_inst_1117_, v_f_1118_, v_as_1119_, v___x_63__boxed_1123_, v_stop_boxed_1124_, v_____do__lift_1122_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(lean_object* v_inst_1126_, lean_object* v_f_1127_, lean_object* v_as_1128_, size_t v_i_1129_, size_t v_stop_1130_, lean_object* v_b_1131_){
_start:
{
lean_object* v_toApplicative_1132_; lean_object* v_toBind_1133_; lean_object* v_toPure_1134_; uint8_t v___x_1135_; 
v_toApplicative_1132_ = lean_ctor_get(v_inst_1126_, 0);
v_toBind_1133_ = lean_ctor_get(v_inst_1126_, 1);
lean_inc(v_toBind_1133_);
v_toPure_1134_ = lean_ctor_get(v_toApplicative_1132_, 1);
v___x_1135_ = lean_usize_dec_eq(v_i_1129_, v_stop_1130_);
if (v___x_1135_ == 0)
{
size_t v___x_1136_; size_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1136_ = ((size_t)1ULL);
v___x_1137_ = lean_usize_sub(v_i_1129_, v___x_1136_);
v___x_1138_ = lean_box_usize(v___x_1137_);
v___x_1139_ = lean_box_usize(v_stop_1130_);
lean_inc_ref(v_as_1128_);
lean_inc(v_f_1127_);
v___f_1140_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1140_, 0, v_inst_1126_);
lean_closure_set(v___f_1140_, 1, v_f_1127_);
lean_closure_set(v___f_1140_, 2, v_as_1128_);
lean_closure_set(v___f_1140_, 3, v___x_1138_);
lean_closure_set(v___f_1140_, 4, v___x_1139_);
v___x_1141_ = lean_array_uget(v_as_1128_, v___x_1137_);
lean_dec_ref(v_as_1128_);
v___x_1142_ = lean_apply_2(v_f_1127_, v___x_1141_, v_b_1131_);
v___x_1143_ = lean_apply_4(v_toBind_1133_, lean_box(0), lean_box(0), v___x_1142_, v___f_1140_);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; 
lean_inc(v_toPure_1134_);
lean_dec(v_toBind_1133_);
lean_dec_ref(v_as_1128_);
lean_dec(v_f_1127_);
lean_dec_ref(v_inst_1126_);
v___x_1144_ = lean_apply_2(v_toPure_1134_, lean_box(0), v_b_1131_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(lean_object* v_inst_1145_, lean_object* v_f_1146_, lean_object* v_as_1147_, size_t v___x_1148_, size_t v_stop_1149_, lean_object* v_____do__lift_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1145_, v_f_1146_, v_as_1147_, v___x_1148_, v_stop_1149_, v_____do__lift_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___boxed(lean_object* v_inst_1152_, lean_object* v_f_1153_, lean_object* v_as_1154_, lean_object* v_i_1155_, lean_object* v_stop_1156_, lean_object* v_b_1157_){
_start:
{
size_t v_i_boxed_1158_; size_t v_stop_boxed_1159_; lean_object* v_res_1160_; 
v_i_boxed_1158_ = lean_unbox_usize(v_i_1155_);
lean_dec(v_i_1155_);
v_stop_boxed_1159_ = lean_unbox_usize(v_stop_1156_);
lean_dec(v_stop_1156_);
v_res_1160_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1152_, v_f_1153_, v_as_1154_, v_i_boxed_1158_, v_stop_boxed_1159_, v_b_1157_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object* v_00_u03b1_1161_, lean_object* v_00_u03b2_1162_, lean_object* v_m_1163_, lean_object* v_inst_1164_, lean_object* v_f_1165_, lean_object* v_as_1166_, size_t v_i_1167_, size_t v_stop_1168_, lean_object* v_b_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1164_, v_f_1165_, v_as_1166_, v_i_1167_, v_stop_1168_, v_b_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___boxed(lean_object* v_00_u03b1_1171_, lean_object* v_00_u03b2_1172_, lean_object* v_m_1173_, lean_object* v_inst_1174_, lean_object* v_f_1175_, lean_object* v_as_1176_, lean_object* v_i_1177_, lean_object* v_stop_1178_, lean_object* v_b_1179_){
_start:
{
size_t v_i_boxed_1180_; size_t v_stop_boxed_1181_; lean_object* v_res_1182_; 
v_i_boxed_1180_ = lean_unbox_usize(v_i_1177_);
lean_dec(v_i_1177_);
v_stop_boxed_1181_ = lean_unbox_usize(v_stop_1178_);
lean_dec(v_stop_1178_);
v_res_1182_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(v_00_u03b1_1171_, v_00_u03b2_1172_, v_m_1173_, v_inst_1174_, v_f_1175_, v_as_1176_, v_i_boxed_1180_, v_stop_boxed_1181_, v_b_1179_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg(lean_object* v_inst_1183_, lean_object* v_f_1184_, lean_object* v_init_1185_, lean_object* v_as_1186_, lean_object* v_start_1187_, lean_object* v_stop_1188_){
_start:
{
lean_object* v_toApplicative_1189_; lean_object* v_toPure_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v_toApplicative_1189_ = lean_ctor_get(v_inst_1183_, 0);
v_toPure_1190_ = lean_ctor_get(v_toApplicative_1189_, 1);
v___x_1191_ = lean_array_get_size(v_as_1186_);
v___x_1192_ = lean_nat_dec_le(v_start_1187_, v___x_1191_);
if (v___x_1192_ == 0)
{
uint8_t v___x_1193_; 
v___x_1193_ = lean_nat_dec_lt(v_stop_1188_, v___x_1191_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_inc(v_toPure_1190_);
lean_dec_ref(v_as_1186_);
lean_dec(v_f_1184_);
lean_dec_ref(v_inst_1183_);
v___x_1194_ = lean_apply_2(v_toPure_1190_, lean_box(0), v_init_1185_);
return v___x_1194_;
}
else
{
size_t v___x_1195_; size_t v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = lean_usize_of_nat(v___x_1191_);
v___x_1196_ = lean_usize_of_nat(v_stop_1188_);
v___x_1197_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1183_, v_f_1184_, v_as_1186_, v___x_1195_, v___x_1196_, v_init_1185_);
return v___x_1197_;
}
}
else
{
uint8_t v___x_1198_; 
v___x_1198_ = lean_nat_dec_lt(v_stop_1188_, v_start_1187_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
lean_inc(v_toPure_1190_);
lean_dec_ref(v_as_1186_);
lean_dec(v_f_1184_);
lean_dec_ref(v_inst_1183_);
v___x_1199_ = lean_apply_2(v_toPure_1190_, lean_box(0), v_init_1185_);
return v___x_1199_;
}
else
{
size_t v___x_1200_; size_t v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = lean_usize_of_nat(v_start_1187_);
v___x_1201_ = lean_usize_of_nat(v_stop_1188_);
v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1183_, v_f_1184_, v_as_1186_, v___x_1200_, v___x_1201_, v_init_1185_);
return v___x_1202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg___boxed(lean_object* v_inst_1203_, lean_object* v_f_1204_, lean_object* v_init_1205_, lean_object* v_as_1206_, lean_object* v_start_1207_, lean_object* v_stop_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Array_foldrMUnsafe___redArg(v_inst_1203_, v_f_1204_, v_init_1205_, v_as_1206_, v_start_1207_, v_stop_1208_);
lean_dec(v_stop_1208_);
lean_dec(v_start_1207_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe(lean_object* v_00_u03b1_1210_, lean_object* v_00_u03b2_1211_, lean_object* v_m_1212_, lean_object* v_inst_1213_, lean_object* v_f_1214_, lean_object* v_init_1215_, lean_object* v_as_1216_, lean_object* v_start_1217_, lean_object* v_stop_1218_){
_start:
{
lean_object* v_toApplicative_1219_; lean_object* v_toPure_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v_toApplicative_1219_ = lean_ctor_get(v_inst_1213_, 0);
v_toPure_1220_ = lean_ctor_get(v_toApplicative_1219_, 1);
v___x_1221_ = lean_array_get_size(v_as_1216_);
v___x_1222_ = lean_nat_dec_le(v_start_1217_, v___x_1221_);
if (v___x_1222_ == 0)
{
uint8_t v___x_1223_; 
v___x_1223_ = lean_nat_dec_lt(v_stop_1218_, v___x_1221_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_inc(v_toPure_1220_);
lean_dec_ref(v_as_1216_);
lean_dec(v_f_1214_);
lean_dec_ref(v_inst_1213_);
v___x_1224_ = lean_apply_2(v_toPure_1220_, lean_box(0), v_init_1215_);
return v___x_1224_;
}
else
{
size_t v___x_1225_; size_t v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_usize_of_nat(v___x_1221_);
v___x_1226_ = lean_usize_of_nat(v_stop_1218_);
v___x_1227_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1213_, v_f_1214_, v_as_1216_, v___x_1225_, v___x_1226_, v_init_1215_);
return v___x_1227_;
}
}
else
{
uint8_t v___x_1228_; 
v___x_1228_ = lean_nat_dec_lt(v_stop_1218_, v_start_1217_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; 
lean_inc(v_toPure_1220_);
lean_dec_ref(v_as_1216_);
lean_dec(v_f_1214_);
lean_dec_ref(v_inst_1213_);
v___x_1229_ = lean_apply_2(v_toPure_1220_, lean_box(0), v_init_1215_);
return v___x_1229_;
}
else
{
size_t v___x_1230_; size_t v___x_1231_; lean_object* v___x_1232_; 
v___x_1230_ = lean_usize_of_nat(v_start_1217_);
v___x_1231_ = lean_usize_of_nat(v_stop_1218_);
v___x_1232_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1213_, v_f_1214_, v_as_1216_, v___x_1230_, v___x_1231_, v_init_1215_);
return v___x_1232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___boxed(lean_object* v_00_u03b1_1233_, lean_object* v_00_u03b2_1234_, lean_object* v_m_1235_, lean_object* v_inst_1236_, lean_object* v_f_1237_, lean_object* v_init_1238_, lean_object* v_as_1239_, lean_object* v_start_1240_, lean_object* v_stop_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Array_foldrMUnsafe(v_00_u03b1_1233_, v_00_u03b2_1234_, v_m_1235_, v_inst_1236_, v_f_1237_, v_init_1238_, v_as_1239_, v_start_1240_, v_stop_1241_);
lean_dec(v_stop_1241_);
lean_dec(v_start_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0___boxed(lean_object* v_inst_1243_, lean_object* v_f_1244_, lean_object* v_as_1245_, lean_object* v_stop_1246_, lean_object* v_n_1247_, lean_object* v_____do__lift_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Array_foldrM_fold___redArg___lam__0(v_inst_1243_, v_f_1244_, v_as_1245_, v_stop_1246_, v_n_1247_, v_____do__lift_1248_);
lean_dec(v_n_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg(lean_object* v_inst_1250_, lean_object* v_f_1251_, lean_object* v_as_1252_, lean_object* v_stop_1253_, lean_object* v_i_1254_, lean_object* v_b_1255_){
_start:
{
lean_object* v_toApplicative_1256_; lean_object* v_toBind_1257_; lean_object* v_toPure_1258_; uint8_t v___x_1259_; 
v_toApplicative_1256_ = lean_ctor_get(v_inst_1250_, 0);
v_toBind_1257_ = lean_ctor_get(v_inst_1250_, 1);
lean_inc(v_toBind_1257_);
v_toPure_1258_ = lean_ctor_get(v_toApplicative_1256_, 1);
v___x_1259_ = lean_nat_dec_eq(v_i_1254_, v_stop_1253_);
if (v___x_1259_ == 0)
{
lean_object* v_zero_1260_; uint8_t v_isZero_1261_; 
v_zero_1260_ = lean_unsigned_to_nat(0u);
v_isZero_1261_ = lean_nat_dec_eq(v_i_1254_, v_zero_1260_);
if (v_isZero_1261_ == 1)
{
lean_object* v___x_1262_; 
lean_inc(v_toPure_1258_);
lean_dec(v_toBind_1257_);
lean_dec(v_stop_1253_);
lean_dec_ref(v_as_1252_);
lean_dec(v_f_1251_);
lean_dec_ref(v_inst_1250_);
v___x_1262_ = lean_apply_2(v_toPure_1258_, lean_box(0), v_b_1255_);
return v___x_1262_;
}
else
{
lean_object* v_one_1263_; lean_object* v_n_1264_; lean_object* v___f_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v_one_1263_ = lean_unsigned_to_nat(1u);
v_n_1264_ = lean_nat_sub(v_i_1254_, v_one_1263_);
lean_inc(v_n_1264_);
lean_inc_ref(v_as_1252_);
lean_inc(v_f_1251_);
v___f_1265_ = lean_alloc_closure((void*)(l_Array_foldrM_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1265_, 0, v_inst_1250_);
lean_closure_set(v___f_1265_, 1, v_f_1251_);
lean_closure_set(v___f_1265_, 2, v_as_1252_);
lean_closure_set(v___f_1265_, 3, v_stop_1253_);
lean_closure_set(v___f_1265_, 4, v_n_1264_);
v___x_1266_ = lean_array_fget(v_as_1252_, v_n_1264_);
lean_dec(v_n_1264_);
lean_dec_ref(v_as_1252_);
v___x_1267_ = lean_apply_2(v_f_1251_, v___x_1266_, v_b_1255_);
v___x_1268_ = lean_apply_4(v_toBind_1257_, lean_box(0), lean_box(0), v___x_1267_, v___f_1265_);
return v___x_1268_;
}
}
else
{
lean_object* v___x_1269_; 
lean_inc(v_toPure_1258_);
lean_dec(v_toBind_1257_);
lean_dec(v_stop_1253_);
lean_dec_ref(v_as_1252_);
lean_dec(v_f_1251_);
lean_dec_ref(v_inst_1250_);
v___x_1269_ = lean_apply_2(v_toPure_1258_, lean_box(0), v_b_1255_);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0(lean_object* v_inst_1270_, lean_object* v_f_1271_, lean_object* v_as_1272_, lean_object* v_stop_1273_, lean_object* v_n_1274_, lean_object* v_____do__lift_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Array_foldrM_fold___redArg(v_inst_1270_, v_f_1271_, v_as_1272_, v_stop_1273_, v_n_1274_, v_____do__lift_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___boxed(lean_object* v_inst_1277_, lean_object* v_f_1278_, lean_object* v_as_1279_, lean_object* v_stop_1280_, lean_object* v_i_1281_, lean_object* v_b_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Array_foldrM_fold___redArg(v_inst_1277_, v_f_1278_, v_as_1279_, v_stop_1280_, v_i_1281_, v_b_1282_);
lean_dec(v_i_1281_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold(lean_object* v_00_u03b1_1284_, lean_object* v_00_u03b2_1285_, lean_object* v_m_1286_, lean_object* v_inst_1287_, lean_object* v_f_1288_, lean_object* v_as_1289_, lean_object* v_stop_1290_, lean_object* v_i_1291_, lean_object* v_h_1292_, lean_object* v_b_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Array_foldrM_fold___redArg(v_inst_1287_, v_f_1288_, v_as_1289_, v_stop_1290_, v_i_1291_, v_b_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___boxed(lean_object* v_00_u03b1_1295_, lean_object* v_00_u03b2_1296_, lean_object* v_m_1297_, lean_object* v_inst_1298_, lean_object* v_f_1299_, lean_object* v_as_1300_, lean_object* v_stop_1301_, lean_object* v_i_1302_, lean_object* v_h_1303_, lean_object* v_b_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Array_foldrM_fold(v_00_u03b1_1295_, v_00_u03b2_1296_, v_m_1297_, v_inst_1298_, v_f_1299_, v_as_1300_, v_stop_1301_, v_i_1302_, v_h_1303_, v_b_1304_);
lean_dec(v_i_1302_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed(lean_object* v_i_1306_, lean_object* v_bs_x27_1307_, lean_object* v_inst_1308_, lean_object* v_f_1309_, lean_object* v_sz_1310_, lean_object* v_vNew_1311_){
_start:
{
size_t v_i_boxed_1312_; size_t v_sz_boxed_1313_; lean_object* v_res_1314_; 
v_i_boxed_1312_ = lean_unbox_usize(v_i_1306_);
lean_dec(v_i_1306_);
v_sz_boxed_1313_ = lean_unbox_usize(v_sz_1310_);
lean_dec(v_sz_1310_);
v_res_1314_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(v_i_boxed_1312_, v_bs_x27_1307_, v_inst_1308_, v_f_1309_, v_sz_boxed_1313_, v_vNew_1311_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(lean_object* v_inst_1315_, lean_object* v_f_1316_, size_t v_sz_1317_, size_t v_i_1318_, lean_object* v_bs_1319_){
_start:
{
lean_object* v_toApplicative_1320_; lean_object* v_toBind_1321_; lean_object* v_toPure_1322_; uint8_t v___x_1323_; 
v_toApplicative_1320_ = lean_ctor_get(v_inst_1315_, 0);
v_toBind_1321_ = lean_ctor_get(v_inst_1315_, 1);
lean_inc(v_toBind_1321_);
v_toPure_1322_ = lean_ctor_get(v_toApplicative_1320_, 1);
v___x_1323_ = lean_usize_dec_lt(v_i_1318_, v_sz_1317_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_inc(v_toPure_1322_);
lean_dec(v_toBind_1321_);
lean_dec(v_f_1316_);
lean_dec_ref(v_inst_1315_);
v___x_1324_ = lean_apply_2(v_toPure_1322_, lean_box(0), v_bs_1319_);
return v___x_1324_;
}
else
{
lean_object* v_v_1325_; lean_object* v___x_1326_; lean_object* v_bs_x27_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___f_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_v_1325_ = lean_array_uget(v_bs_1319_, v_i_1318_);
v___x_1326_ = lean_unsigned_to_nat(0u);
v_bs_x27_1327_ = lean_array_uset(v_bs_1319_, v_i_1318_, v___x_1326_);
v___x_1328_ = lean_box_usize(v_i_1318_);
v___x_1329_ = lean_box_usize(v_sz_1317_);
lean_inc(v_f_1316_);
v___f_1330_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1330_, 0, v___x_1328_);
lean_closure_set(v___f_1330_, 1, v_bs_x27_1327_);
lean_closure_set(v___f_1330_, 2, v_inst_1315_);
lean_closure_set(v___f_1330_, 3, v_f_1316_);
lean_closure_set(v___f_1330_, 4, v___x_1329_);
v___x_1331_ = lean_apply_1(v_f_1316_, v_v_1325_);
v___x_1332_ = lean_apply_4(v_toBind_1321_, lean_box(0), lean_box(0), v___x_1331_, v___f_1330_);
return v___x_1332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(size_t v_i_1333_, lean_object* v_bs_x27_1334_, lean_object* v_inst_1335_, lean_object* v_f_1336_, size_t v_sz_1337_, lean_object* v_vNew_1338_){
_start:
{
size_t v___x_1339_; size_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1339_ = ((size_t)1ULL);
v___x_1340_ = lean_usize_add(v_i_1333_, v___x_1339_);
v___x_1341_ = lean_array_uset(v_bs_x27_1334_, v_i_1333_, v_vNew_1338_);
v___x_1342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1335_, v_f_1336_, v_sz_1337_, v___x_1340_, v___x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___boxed(lean_object* v_inst_1343_, lean_object* v_f_1344_, lean_object* v_sz_1345_, lean_object* v_i_1346_, lean_object* v_bs_1347_){
_start:
{
size_t v_sz_boxed_1348_; size_t v_i_boxed_1349_; lean_object* v_res_1350_; 
v_sz_boxed_1348_ = lean_unbox_usize(v_sz_1345_);
lean_dec(v_sz_1345_);
v_i_boxed_1349_ = lean_unbox_usize(v_i_1346_);
lean_dec(v_i_1346_);
v_res_1350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1343_, v_f_1344_, v_sz_boxed_1348_, v_i_boxed_1349_, v_bs_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object* v_00_u03b1_1351_, lean_object* v_00_u03b2_1352_, lean_object* v_m_1353_, lean_object* v_inst_1354_, lean_object* v_f_1355_, size_t v_sz_1356_, size_t v_i_1357_, lean_object* v_bs_1358_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1354_, v_f_1355_, v_sz_1356_, v_i_1357_, v_bs_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___boxed(lean_object* v_00_u03b1_1360_, lean_object* v_00_u03b2_1361_, lean_object* v_m_1362_, lean_object* v_inst_1363_, lean_object* v_f_1364_, lean_object* v_sz_1365_, lean_object* v_i_1366_, lean_object* v_bs_1367_){
_start:
{
size_t v_sz_boxed_1368_; size_t v_i_boxed_1369_; lean_object* v_res_1370_; 
v_sz_boxed_1368_ = lean_unbox_usize(v_sz_1365_);
lean_dec(v_sz_1365_);
v_i_boxed_1369_ = lean_unbox_usize(v_i_1366_);
lean_dec(v_i_1366_);
v_res_1370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(v_00_u03b1_1360_, v_00_u03b2_1361_, v_m_1362_, v_inst_1363_, v_f_1364_, v_sz_boxed_1368_, v_i_boxed_1369_, v_bs_1367_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe___redArg(lean_object* v_inst_1371_, lean_object* v_f_1372_, lean_object* v_as_1373_){
_start:
{
size_t v_sz_1374_; size_t v___x_1375_; lean_object* v___x_1376_; 
v_sz_1374_ = lean_array_size(v_as_1373_);
v___x_1375_ = ((size_t)0ULL);
v___x_1376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1371_, v_f_1372_, v_sz_1374_, v___x_1375_, v_as_1373_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe(lean_object* v_00_u03b1_1377_, lean_object* v_00_u03b2_1378_, lean_object* v_m_1379_, lean_object* v_inst_1380_, lean_object* v_f_1381_, lean_object* v_as_1382_){
_start:
{
size_t v_sz_1383_; size_t v___x_1384_; lean_object* v___x_1385_; 
v_sz_1383_ = lean_array_size(v_as_1382_);
v___x_1384_ = ((size_t)0ULL);
v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1380_, v_f_1381_, v_sz_1383_, v___x_1384_, v_as_1382_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0___boxed(lean_object* v_i_1386_, lean_object* v_bs_1387_, lean_object* v_inst_1388_, lean_object* v_f_1389_, lean_object* v_as_1390_, lean_object* v_____do__lift_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0(v_i_1386_, v_bs_1387_, v_inst_1388_, v_f_1389_, v_as_1390_, v_____do__lift_1391_);
lean_dec(v_i_1386_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(lean_object* v_inst_1393_, lean_object* v_f_1394_, lean_object* v_as_1395_, lean_object* v_i_1396_, lean_object* v_bs_1397_){
_start:
{
lean_object* v_toApplicative_1398_; lean_object* v_toBind_1399_; lean_object* v_toPure_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_toApplicative_1398_ = lean_ctor_get(v_inst_1393_, 0);
v_toBind_1399_ = lean_ctor_get(v_inst_1393_, 1);
lean_inc(v_toBind_1399_);
v_toPure_1400_ = lean_ctor_get(v_toApplicative_1398_, 1);
v___x_1401_ = lean_array_get_size(v_as_1395_);
v___x_1402_ = lean_nat_dec_lt(v_i_1396_, v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; 
lean_inc(v_toPure_1400_);
lean_dec(v_toBind_1399_);
lean_dec(v_i_1396_);
lean_dec_ref(v_as_1395_);
lean_dec(v_f_1394_);
lean_dec_ref(v_inst_1393_);
v___x_1403_ = lean_apply_2(v_toPure_1400_, lean_box(0), v_bs_1397_);
return v___x_1403_;
}
else
{
lean_object* v___f_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_inc_ref(v_as_1395_);
lean_inc(v_f_1394_);
lean_inc(v_i_1396_);
v___f_1404_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1404_, 0, v_i_1396_);
lean_closure_set(v___f_1404_, 1, v_bs_1397_);
lean_closure_set(v___f_1404_, 2, v_inst_1393_);
lean_closure_set(v___f_1404_, 3, v_f_1394_);
lean_closure_set(v___f_1404_, 4, v_as_1395_);
v___x_1405_ = lean_array_fget(v_as_1395_, v_i_1396_);
lean_dec(v_i_1396_);
lean_dec_ref(v_as_1395_);
v___x_1406_ = lean_apply_1(v_f_1394_, v___x_1405_);
v___x_1407_ = lean_apply_4(v_toBind_1399_, lean_box(0), lean_box(0), v___x_1406_, v___f_1404_);
return v___x_1407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0(lean_object* v_i_1408_, lean_object* v_bs_1409_, lean_object* v_inst_1410_, lean_object* v_f_1411_, lean_object* v_as_1412_, lean_object* v_____do__lift_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1414_ = lean_unsigned_to_nat(1u);
v___x_1415_ = lean_nat_add(v_i_1408_, v___x_1414_);
v___x_1416_ = lean_array_push(v_bs_1409_, v_____do__lift_1413_);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(v_inst_1410_, v_f_1411_, v_as_1412_, v___x_1415_, v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map(lean_object* v_00_u03b1_1418_, lean_object* v_00_u03b2_1419_, lean_object* v_m_1420_, lean_object* v_inst_1421_, lean_object* v_f_1422_, lean_object* v_as_1423_, lean_object* v_i_1424_, lean_object* v_bs_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(v_inst_1421_, v_f_1422_, v_as_1423_, v_i_1424_, v_bs_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0___boxed(lean_object* v_i_1427_, lean_object* v_bs_x27_1428_, lean_object* v_inst_1429_, lean_object* v_f_1430_, lean_object* v_sz_1431_, lean_object* v_vNew_1432_){
_start:
{
size_t v_i_boxed_1433_; size_t v_sz_boxed_1434_; lean_object* v_res_1435_; 
v_i_boxed_1433_ = lean_unbox_usize(v_i_1427_);
lean_dec(v_i_1427_);
v_sz_boxed_1434_ = lean_unbox_usize(v_sz_1431_);
lean_dec(v_sz_1431_);
v_res_1435_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0(v_i_boxed_1433_, v_bs_x27_1428_, v_inst_1429_, v_f_1430_, v_sz_boxed_1434_, v_vNew_1432_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(lean_object* v_inst_1436_, lean_object* v_f_1437_, size_t v_sz_1438_, size_t v_i_1439_, lean_object* v_bs_1440_){
_start:
{
lean_object* v_toApplicative_1441_; lean_object* v_toBind_1442_; lean_object* v_toPure_1443_; uint8_t v___x_1444_; 
v_toApplicative_1441_ = lean_ctor_get(v_inst_1436_, 0);
v_toBind_1442_ = lean_ctor_get(v_inst_1436_, 1);
lean_inc(v_toBind_1442_);
v_toPure_1443_ = lean_ctor_get(v_toApplicative_1441_, 1);
v___x_1444_ = lean_usize_dec_lt(v_i_1439_, v_sz_1438_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; 
lean_inc(v_toPure_1443_);
lean_dec(v_toBind_1442_);
lean_dec(v_f_1437_);
lean_dec_ref(v_inst_1436_);
v___x_1445_ = lean_apply_2(v_toPure_1443_, lean_box(0), v_bs_1440_);
return v___x_1445_;
}
else
{
lean_object* v_v_1446_; lean_object* v___x_1447_; lean_object* v_bs_x27_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___f_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v_v_1446_ = lean_array_uget(v_bs_1440_, v_i_1439_);
v___x_1447_ = lean_unsigned_to_nat(0u);
v_bs_x27_1448_ = lean_array_uset(v_bs_1440_, v_i_1439_, v___x_1447_);
v___x_1449_ = lean_box_usize(v_i_1439_);
v___x_1450_ = lean_box_usize(v_sz_1438_);
lean_inc(v_f_1437_);
v___f_1451_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1451_, 0, v___x_1449_);
lean_closure_set(v___f_1451_, 1, v_bs_x27_1448_);
lean_closure_set(v___f_1451_, 2, v_inst_1436_);
lean_closure_set(v___f_1451_, 3, v_f_1437_);
lean_closure_set(v___f_1451_, 4, v___x_1450_);
v___x_1452_ = lean_usize_to_nat(v_i_1439_);
v___x_1453_ = lean_apply_3(v_f_1437_, v___x_1452_, v_v_1446_, lean_box(0));
v___x_1454_ = lean_apply_4(v_toBind_1442_, lean_box(0), lean_box(0), v___x_1453_, v___f_1451_);
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0(size_t v_i_1455_, lean_object* v_bs_x27_1456_, lean_object* v_inst_1457_, lean_object* v_f_1458_, size_t v_sz_1459_, lean_object* v_vNew_1460_){
_start:
{
size_t v___x_1461_; size_t v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1461_ = ((size_t)1ULL);
v___x_1462_ = lean_usize_add(v_i_1455_, v___x_1461_);
v___x_1463_ = lean_array_uset(v_bs_x27_1456_, v_i_1455_, v_vNew_1460_);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1457_, v_f_1458_, v_sz_1459_, v___x_1462_, v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___boxed(lean_object* v_inst_1465_, lean_object* v_f_1466_, lean_object* v_sz_1467_, lean_object* v_i_1468_, lean_object* v_bs_1469_){
_start:
{
size_t v_sz_boxed_1470_; size_t v_i_boxed_1471_; lean_object* v_res_1472_; 
v_sz_boxed_1470_ = lean_unbox_usize(v_sz_1467_);
lean_dec(v_sz_1467_);
v_i_boxed_1471_ = lean_unbox_usize(v_i_1468_);
lean_dec(v_i_1468_);
v_res_1472_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1465_, v_f_1466_, v_sz_boxed_1470_, v_i_boxed_1471_, v_bs_1469_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object* v_00_u03b1_1473_, lean_object* v_00_u03b2_1474_, lean_object* v_m_1475_, lean_object* v_inst_1476_, lean_object* v_as_1477_, lean_object* v_f_1478_, size_t v_sz_1479_, size_t v_i_1480_, lean_object* v_bs_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1476_, v_f_1478_, v_sz_1479_, v_i_1480_, v_bs_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___boxed(lean_object* v_00_u03b1_1483_, lean_object* v_00_u03b2_1484_, lean_object* v_m_1485_, lean_object* v_inst_1486_, lean_object* v_as_1487_, lean_object* v_f_1488_, lean_object* v_sz_1489_, lean_object* v_i_1490_, lean_object* v_bs_1491_){
_start:
{
size_t v_sz_boxed_1492_; size_t v_i_boxed_1493_; lean_object* v_res_1494_; 
v_sz_boxed_1492_ = lean_unbox_usize(v_sz_1489_);
lean_dec(v_sz_1489_);
v_i_boxed_1493_ = lean_unbox_usize(v_i_1490_);
lean_dec(v_i_1490_);
v_res_1494_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(v_00_u03b1_1483_, v_00_u03b2_1484_, v_m_1485_, v_inst_1486_, v_as_1487_, v_f_1488_, v_sz_boxed_1492_, v_i_boxed_1493_, v_bs_1491_);
lean_dec_ref(v_as_1487_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxMUnsafe___redArg(lean_object* v_inst_1495_, lean_object* v_as_1496_, lean_object* v_f_1497_){
_start:
{
size_t v_sz_1498_; size_t v___x_1499_; lean_object* v___x_1500_; 
v_sz_1498_ = lean_array_size(v_as_1496_);
v___x_1499_ = ((size_t)0ULL);
v___x_1500_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1495_, v_f_1497_, v_sz_1498_, v___x_1499_, v_as_1496_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxMUnsafe(lean_object* v_00_u03b1_1501_, lean_object* v_00_u03b2_1502_, lean_object* v_m_1503_, lean_object* v_inst_1504_, lean_object* v_as_1505_, lean_object* v_f_1506_){
_start:
{
size_t v_sz_1507_; size_t v___x_1508_; lean_object* v___x_1509_; 
v_sz_1507_ = lean_array_size(v_as_1505_);
v___x_1508_ = ((size_t)0ULL);
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1504_, v_f_1506_, v_sz_1507_, v___x_1508_, v_as_1505_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1510_, lean_object* v_bs_1511_, lean_object* v_inst_1512_, lean_object* v_as_1513_, lean_object* v_f_1514_, lean_object* v_n_1515_, lean_object* v_____do__lift_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Array_mapFinIdxM_map___redArg___lam__0(v_j_1510_, v_bs_1511_, v_inst_1512_, v_as_1513_, v_f_1514_, v_n_1515_, v_____do__lift_1516_);
lean_dec(v_n_1515_);
lean_dec(v_j_1510_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg(lean_object* v_inst_1518_, lean_object* v_as_1519_, lean_object* v_f_1520_, lean_object* v_i_1521_, lean_object* v_j_1522_, lean_object* v_bs_1523_){
_start:
{
lean_object* v_toApplicative_1524_; lean_object* v_toBind_1525_; lean_object* v_toPure_1526_; lean_object* v_zero_1527_; uint8_t v_isZero_1528_; 
v_toApplicative_1524_ = lean_ctor_get(v_inst_1518_, 0);
v_toBind_1525_ = lean_ctor_get(v_inst_1518_, 1);
lean_inc(v_toBind_1525_);
v_toPure_1526_ = lean_ctor_get(v_toApplicative_1524_, 1);
v_zero_1527_ = lean_unsigned_to_nat(0u);
v_isZero_1528_ = lean_nat_dec_eq(v_i_1521_, v_zero_1527_);
if (v_isZero_1528_ == 1)
{
lean_object* v___x_1529_; 
lean_inc(v_toPure_1526_);
lean_dec(v_toBind_1525_);
lean_dec(v_j_1522_);
lean_dec(v_f_1520_);
lean_dec_ref(v_as_1519_);
lean_dec_ref(v_inst_1518_);
v___x_1529_ = lean_apply_2(v_toPure_1526_, lean_box(0), v_bs_1523_);
return v___x_1529_;
}
else
{
lean_object* v_one_1530_; lean_object* v_n_1531_; lean_object* v___f_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v_one_1530_ = lean_unsigned_to_nat(1u);
v_n_1531_ = lean_nat_sub(v_i_1521_, v_one_1530_);
lean_inc(v_f_1520_);
lean_inc_ref(v_as_1519_);
lean_inc(v_j_1522_);
v___f_1532_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1532_, 0, v_j_1522_);
lean_closure_set(v___f_1532_, 1, v_bs_1523_);
lean_closure_set(v___f_1532_, 2, v_inst_1518_);
lean_closure_set(v___f_1532_, 3, v_as_1519_);
lean_closure_set(v___f_1532_, 4, v_f_1520_);
lean_closure_set(v___f_1532_, 5, v_n_1531_);
v___x_1533_ = lean_array_fget(v_as_1519_, v_j_1522_);
lean_dec_ref(v_as_1519_);
v___x_1534_ = lean_apply_3(v_f_1520_, v_j_1522_, v___x_1533_, lean_box(0));
v___x_1535_ = lean_apply_4(v_toBind_1525_, lean_box(0), lean_box(0), v___x_1534_, v___f_1532_);
return v___x_1535_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1536_, lean_object* v_bs_1537_, lean_object* v_inst_1538_, lean_object* v_as_1539_, lean_object* v_f_1540_, lean_object* v_n_1541_, lean_object* v_____do__lift_1542_){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1543_ = lean_unsigned_to_nat(1u);
v___x_1544_ = lean_nat_add(v_j_1536_, v___x_1543_);
v___x_1545_ = lean_array_push(v_bs_1537_, v_____do__lift_1542_);
v___x_1546_ = l_Array_mapFinIdxM_map___redArg(v_inst_1538_, v_as_1539_, v_f_1540_, v_n_1541_, v___x_1544_, v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1547_, lean_object* v_as_1548_, lean_object* v_f_1549_, lean_object* v_i_1550_, lean_object* v_j_1551_, lean_object* v_bs_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Array_mapFinIdxM_map___redArg(v_inst_1547_, v_as_1548_, v_f_1549_, v_i_1550_, v_j_1551_, v_bs_1552_);
lean_dec(v_i_1550_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map(lean_object* v_00_u03b1_1554_, lean_object* v_00_u03b2_1555_, lean_object* v_m_1556_, lean_object* v_inst_1557_, lean_object* v_as_1558_, lean_object* v_f_1559_, lean_object* v_i_1560_, lean_object* v_j_1561_, lean_object* v_inv_1562_, lean_object* v_bs_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Array_mapFinIdxM_map___redArg(v_inst_1557_, v_as_1558_, v_f_1559_, v_i_1560_, v_j_1561_, v_bs_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___boxed(lean_object* v_00_u03b1_1565_, lean_object* v_00_u03b2_1566_, lean_object* v_m_1567_, lean_object* v_inst_1568_, lean_object* v_as_1569_, lean_object* v_f_1570_, lean_object* v_i_1571_, lean_object* v_j_1572_, lean_object* v_inv_1573_, lean_object* v_bs_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Array_mapFinIdxM_map(v_00_u03b1_1565_, v_00_u03b2_1566_, v_m_1567_, v_inst_1568_, v_as_1569_, v_f_1570_, v_i_1571_, v_j_1572_, v_inv_1573_, v_bs_1574_);
lean_dec(v_i_1571_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg___lam__0(lean_object* v_f_1576_, lean_object* v_i_1577_, lean_object* v_a_1578_, lean_object* v_x_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_apply_2(v_f_1576_, v_i_1577_, v_a_1578_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg(lean_object* v_inst_1581_, lean_object* v_f_1582_, lean_object* v_as_1583_){
_start:
{
lean_object* v___f_1584_; size_t v_sz_1585_; size_t v___x_1586_; lean_object* v___x_1587_; 
v___f_1584_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1584_, 0, v_f_1582_);
v_sz_1585_ = lean_array_size(v_as_1583_);
v___x_1586_ = ((size_t)0ULL);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1581_, v___f_1584_, v_sz_1585_, v___x_1586_, v_as_1583_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM(lean_object* v_00_u03b1_1588_, lean_object* v_00_u03b2_1589_, lean_object* v_m_1590_, lean_object* v_inst_1591_, lean_object* v_f_1592_, lean_object* v_as_1593_){
_start:
{
lean_object* v___f_1594_; size_t v_sz_1595_; size_t v___x_1596_; lean_object* v___x_1597_; 
v___f_1594_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1594_, 0, v_f_1592_);
v_sz_1595_ = lean_array_size(v_as_1593_);
v___x_1596_ = ((size_t)0ULL);
v___x_1597_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1591_, v___f_1594_, v_sz_1595_, v___x_1596_, v_as_1593_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed(lean_object* v_i_1598_, lean_object* v_inst_1599_, lean_object* v_f_1600_, lean_object* v_as_1601_, lean_object* v_x_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(v_i_1598_, v_inst_1599_, v_f_1600_, v_as_1601_, v_x_1602_);
lean_dec(v_i_1598_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(lean_object* v_inst_1604_, lean_object* v_f_1605_, lean_object* v_as_1606_, lean_object* v_i_1607_){
_start:
{
lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = lean_array_get_size(v_as_1606_);
v___x_1609_ = lean_nat_dec_lt(v_i_1607_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v_failure_1610_; lean_object* v___x_1611_; 
lean_dec(v_i_1607_);
lean_dec_ref(v_as_1606_);
lean_dec(v_f_1605_);
v_failure_1610_ = lean_ctor_get(v_inst_1604_, 1);
lean_inc(v_failure_1610_);
lean_dec_ref(v_inst_1604_);
v___x_1611_ = lean_apply_1(v_failure_1610_, lean_box(0));
return v___x_1611_;
}
else
{
lean_object* v_orElse_1612_; lean_object* v___f_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_orElse_1612_ = lean_ctor_get(v_inst_1604_, 2);
lean_inc(v_orElse_1612_);
lean_inc_ref(v_as_1606_);
lean_inc(v_f_1605_);
lean_inc(v_i_1607_);
v___f_1613_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1613_, 0, v_i_1607_);
lean_closure_set(v___f_1613_, 1, v_inst_1604_);
lean_closure_set(v___f_1613_, 2, v_f_1605_);
lean_closure_set(v___f_1613_, 3, v_as_1606_);
v___x_1614_ = lean_array_fget(v_as_1606_, v_i_1607_);
lean_dec(v_i_1607_);
lean_dec_ref(v_as_1606_);
v___x_1615_ = lean_apply_1(v_f_1605_, v___x_1614_);
v___x_1616_ = lean_apply_3(v_orElse_1612_, lean_box(0), v___x_1615_, v___f_1613_);
return v___x_1616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(lean_object* v_i_1617_, lean_object* v_inst_1618_, lean_object* v_f_1619_, lean_object* v_as_1620_, lean_object* v_x_1621_){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1622_ = lean_unsigned_to_nat(1u);
v___x_1623_ = lean_nat_add(v_i_1617_, v___x_1622_);
v___x_1624_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1618_, v_f_1619_, v_as_1620_, v___x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_object* v_00_u03b2_1625_, lean_object* v_00_u03b1_1626_, lean_object* v_m_1627_, lean_object* v_inst_1628_, lean_object* v_f_1629_, lean_object* v_as_1630_, lean_object* v_i_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1628_, v_f_1629_, v_as_1630_, v_i_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM___redArg(lean_object* v_inst_1633_, lean_object* v_f_1634_, lean_object* v_as_1635_){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_unsigned_to_nat(0u);
v___x_1637_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1633_, v_f_1634_, v_as_1635_, v___x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM(lean_object* v_00_u03b2_1638_, lean_object* v_00_u03b1_1639_, lean_object* v_m_1640_, lean_object* v_inst_1641_, lean_object* v_f_1642_, lean_object* v_as_1643_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1641_, v_f_1642_, v_as_1643_, v___x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__0(lean_object* v___x_1646_, lean_object* v_toPure_1647_, lean_object* v___x_1648_, lean_object* v_____do__lift_1649_){
_start:
{
if (lean_obj_tag(v_____do__lift_1649_) == 1)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_dec_ref(v___x_1648_);
v___x_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1650_, 0, v_____do__lift_1649_);
v___x_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v___x_1646_);
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
v___x_1653_ = lean_apply_2(v_toPure_1647_, lean_box(0), v___x_1652_);
return v___x_1653_;
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec(v_____do__lift_1649_);
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1648_);
v___x_1655_ = lean_apply_2(v_toPure_1647_, lean_box(0), v___x_1654_);
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1(lean_object* v_f_1656_, lean_object* v_toBind_1657_, lean_object* v___f_1658_, lean_object* v_a_1659_, lean_object* v_x_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = lean_apply_1(v_f_1656_, v_a_1659_);
v___x_1663_ = lean_apply_4(v_toBind_1657_, lean_box(0), lean_box(0), v___x_1662_, v___f_1658_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1___boxed(lean_object* v_f_1664_, lean_object* v_toBind_1665_, lean_object* v___f_1666_, lean_object* v_a_1667_, lean_object* v_x_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Array_findSomeM_x3f___redArg___lam__1(v_f_1664_, v_toBind_1665_, v___f_1666_, v_a_1667_, v_x_1668_, v___y_1669_);
lean_dec_ref(v___y_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__2(lean_object* v_toPure_1671_, lean_object* v_____s_1672_){
_start:
{
lean_object* v_fst_1673_; 
v_fst_1673_ = lean_ctor_get(v_____s_1672_, 0);
lean_inc(v_fst_1673_);
lean_dec_ref(v_____s_1672_);
if (lean_obj_tag(v_fst_1673_) == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = lean_box(0);
v___x_1675_ = lean_apply_2(v_toPure_1671_, lean_box(0), v___x_1674_);
return v___x_1675_;
}
else
{
lean_object* v_val_1676_; lean_object* v___x_1677_; 
v_val_1676_ = lean_ctor_get(v_fst_1673_, 0);
lean_inc(v_val_1676_);
lean_dec_ref_known(v_fst_1673_, 1);
v___x_1677_ = lean_apply_2(v_toPure_1671_, lean_box(0), v_val_1676_);
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg(lean_object* v_inst_1681_, lean_object* v_f_1682_, lean_object* v_as_1683_){
_start:
{
lean_object* v_toApplicative_1684_; lean_object* v_toBind_1685_; lean_object* v_toPure_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___f_1689_; lean_object* v___f_1690_; lean_object* v___f_1691_; size_t v_sz_1692_; size_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v_toApplicative_1684_ = lean_ctor_get(v_inst_1681_, 0);
v_toBind_1685_ = lean_ctor_get(v_inst_1681_, 1);
lean_inc_n(v_toBind_1685_, 2);
v_toPure_1686_ = lean_ctor_get(v_toApplicative_1684_, 1);
v___x_1687_ = lean_box(0);
v___x_1688_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1686_, 2);
v___f_1689_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1689_, 0, v___x_1687_);
lean_closure_set(v___f_1689_, 1, v_toPure_1686_);
lean_closure_set(v___f_1689_, 2, v___x_1688_);
v___f_1690_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1690_, 0, v_f_1682_);
lean_closure_set(v___f_1690_, 1, v_toBind_1685_);
lean_closure_set(v___f_1690_, 2, v___f_1689_);
v___f_1691_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1691_, 0, v_toPure_1686_);
v_sz_1692_ = lean_array_size(v_as_1683_);
v___x_1693_ = ((size_t)0ULL);
v___x_1694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1681_, v_as_1683_, v___f_1690_, v_sz_1692_, v___x_1693_, v___x_1688_);
v___x_1695_ = lean_apply_4(v_toBind_1685_, lean_box(0), lean_box(0), v___x_1694_, v___f_1691_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f(lean_object* v_00_u03b1_1696_, lean_object* v_00_u03b2_1697_, lean_object* v_m_1698_, lean_object* v_inst_1699_, lean_object* v_f_1700_, lean_object* v_as_1701_){
_start:
{
lean_object* v_toApplicative_1702_; lean_object* v_toBind_1703_; lean_object* v_toPure_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___f_1707_; lean_object* v___f_1708_; lean_object* v___f_1709_; size_t v_sz_1710_; size_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_toApplicative_1702_ = lean_ctor_get(v_inst_1699_, 0);
v_toBind_1703_ = lean_ctor_get(v_inst_1699_, 1);
lean_inc_n(v_toBind_1703_, 2);
v_toPure_1704_ = lean_ctor_get(v_toApplicative_1702_, 1);
v___x_1705_ = lean_box(0);
v___x_1706_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1704_, 2);
v___f_1707_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1707_, 0, v___x_1705_);
lean_closure_set(v___f_1707_, 1, v_toPure_1704_);
lean_closure_set(v___f_1707_, 2, v___x_1706_);
v___f_1708_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1708_, 0, v_f_1700_);
lean_closure_set(v___f_1708_, 1, v_toBind_1703_);
lean_closure_set(v___f_1708_, 2, v___f_1707_);
v___f_1709_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1709_, 0, v_toPure_1704_);
v_sz_1710_ = lean_array_size(v_as_1701_);
v___x_1711_ = ((size_t)0ULL);
v___x_1712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1699_, v_as_1701_, v___f_1708_, v_sz_1710_, v___x_1711_, v___x_1706_);
v___x_1713_ = lean_apply_4(v_toBind_1703_, lean_box(0), lean_box(0), v___x_1712_, v___f_1709_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0(lean_object* v___x_1714_, lean_object* v_toPure_1715_, lean_object* v_a_1716_, lean_object* v___x_1717_, uint8_t v_____do__lift_1718_){
_start:
{
if (v_____do__lift_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_dec(v_a_1716_);
v___x_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1714_);
v___x_1720_ = lean_apply_2(v_toPure_1715_, lean_box(0), v___x_1719_);
return v___x_1720_;
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_dec_ref(v___x_1714_);
v___x_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1721_, 0, v_a_1716_);
v___x_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
lean_ctor_set(v___x_1723_, 1, v___x_1717_);
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
v___x_1725_ = lean_apply_2(v_toPure_1715_, lean_box(0), v___x_1724_);
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0___boxed(lean_object* v___x_1726_, lean_object* v_toPure_1727_, lean_object* v_a_1728_, lean_object* v___x_1729_, lean_object* v_____do__lift_1730_){
_start:
{
uint8_t v_____do__lift_184__boxed_1731_; lean_object* v_res_1732_; 
v_____do__lift_184__boxed_1731_ = lean_unbox(v_____do__lift_1730_);
v_res_1732_ = l_Array_findM_x3f___redArg___lam__0(v___x_1726_, v_toPure_1727_, v_a_1728_, v___x_1729_, v_____do__lift_184__boxed_1731_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1(lean_object* v___x_1733_, lean_object* v_toPure_1734_, lean_object* v___x_1735_, lean_object* v_p_1736_, lean_object* v_toBind_1737_, lean_object* v_a_1738_, lean_object* v_x_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v___f_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_inc(v_a_1738_);
v___f_1741_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1741_, 0, v___x_1733_);
lean_closure_set(v___f_1741_, 1, v_toPure_1734_);
lean_closure_set(v___f_1741_, 2, v_a_1738_);
lean_closure_set(v___f_1741_, 3, v___x_1735_);
v___x_1742_ = lean_apply_1(v_p_1736_, v_a_1738_);
v___x_1743_ = lean_apply_4(v_toBind_1737_, lean_box(0), lean_box(0), v___x_1742_, v___f_1741_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_1744_, lean_object* v_toPure_1745_, lean_object* v___x_1746_, lean_object* v_p_1747_, lean_object* v_toBind_1748_, lean_object* v_a_1749_, lean_object* v_x_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Array_findM_x3f___redArg___lam__1(v___x_1744_, v_toPure_1745_, v___x_1746_, v_p_1747_, v_toBind_1748_, v_a_1749_, v_x_1750_, v___y_1751_);
lean_dec_ref(v___y_1751_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg(lean_object* v_inst_1753_, lean_object* v_p_1754_, lean_object* v_as_1755_){
_start:
{
lean_object* v_toApplicative_1756_; lean_object* v_toBind_1757_; lean_object* v_toPure_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___f_1761_; lean_object* v___f_1762_; size_t v_sz_1763_; size_t v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_toApplicative_1756_ = lean_ctor_get(v_inst_1753_, 0);
v_toBind_1757_ = lean_ctor_get(v_inst_1753_, 1);
lean_inc_n(v_toBind_1757_, 2);
v_toPure_1758_ = lean_ctor_get(v_toApplicative_1756_, 1);
v___x_1759_ = lean_box(0);
v___x_1760_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1758_, 2);
v___f_1761_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1761_, 0, v___x_1760_);
lean_closure_set(v___f_1761_, 1, v_toPure_1758_);
lean_closure_set(v___f_1761_, 2, v___x_1759_);
lean_closure_set(v___f_1761_, 3, v_p_1754_);
lean_closure_set(v___f_1761_, 4, v_toBind_1757_);
v___f_1762_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1762_, 0, v_toPure_1758_);
v_sz_1763_ = lean_array_size(v_as_1755_);
v___x_1764_ = ((size_t)0ULL);
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1753_, v_as_1755_, v___f_1761_, v_sz_1763_, v___x_1764_, v___x_1760_);
v___x_1766_ = lean_apply_4(v_toBind_1757_, lean_box(0), lean_box(0), v___x_1765_, v___f_1762_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f(lean_object* v_m_1767_, lean_object* v_00_u03b1_1768_, lean_object* v_inst_1769_, lean_object* v_p_1770_, lean_object* v_as_1771_){
_start:
{
lean_object* v_toApplicative_1772_; lean_object* v_toBind_1773_; lean_object* v_toPure_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___f_1777_; lean_object* v___f_1778_; size_t v_sz_1779_; size_t v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_toApplicative_1772_ = lean_ctor_get(v_inst_1769_, 0);
v_toBind_1773_ = lean_ctor_get(v_inst_1769_, 1);
lean_inc_n(v_toBind_1773_, 2);
v_toPure_1774_ = lean_ctor_get(v_toApplicative_1772_, 1);
v___x_1775_ = lean_box(0);
v___x_1776_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1774_, 2);
v___f_1777_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1777_, 0, v___x_1776_);
lean_closure_set(v___f_1777_, 1, v_toPure_1774_);
lean_closure_set(v___f_1777_, 2, v___x_1775_);
lean_closure_set(v___f_1777_, 3, v_p_1770_);
lean_closure_set(v___f_1777_, 4, v_toBind_1773_);
v___f_1778_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1778_, 0, v_toPure_1774_);
v_sz_1779_ = lean_array_size(v_as_1771_);
v___x_1780_ = ((size_t)0ULL);
v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1769_, v_as_1771_, v___f_1777_, v_sz_1779_, v___x_1780_, v___x_1776_);
v___x_1782_ = lean_apply_4(v_toBind_1773_, lean_box(0), lean_box(0), v___x_1781_, v___f_1778_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0(lean_object* v_snd_1783_, lean_object* v___x_1784_, lean_object* v_toPure_1785_, uint8_t v_____do__lift_1786_){
_start:
{
if (v_____do__lift_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1787_ = lean_unsigned_to_nat(1u);
v___x_1788_ = lean_nat_add(v_snd_1783_, v___x_1787_);
lean_dec(v_snd_1783_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1784_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
v___x_1791_ = lean_apply_2(v_toPure_1785_, lean_box(0), v___x_1790_);
return v___x_1791_;
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec(v___x_1784_);
lean_inc(v_snd_1783_);
v___x_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1792_, 0, v_snd_1783_);
v___x_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
v___x_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
lean_ctor_set(v___x_1794_, 1, v_snd_1783_);
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
v___x_1796_ = lean_apply_2(v_toPure_1785_, lean_box(0), v___x_1795_);
return v___x_1796_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0___boxed(lean_object* v_snd_1797_, lean_object* v___x_1798_, lean_object* v_toPure_1799_, lean_object* v_____do__lift_1800_){
_start:
{
uint8_t v_____do__lift_213__boxed_1801_; lean_object* v_res_1802_; 
v_____do__lift_213__boxed_1801_ = lean_unbox(v_____do__lift_1800_);
v_res_1802_ = l_Array_findIdxM_x3f___redArg___lam__0(v_snd_1797_, v___x_1798_, v_toPure_1799_, v_____do__lift_213__boxed_1801_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__1(lean_object* v___x_1803_, lean_object* v_toPure_1804_, lean_object* v_p_1805_, lean_object* v_toBind_1806_, lean_object* v_a_1807_, lean_object* v_x_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v_snd_1810_; lean_object* v___f_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v_snd_1810_ = lean_ctor_get(v___y_1809_, 1);
lean_inc(v_snd_1810_);
lean_dec_ref(v___y_1809_);
v___f_1811_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1811_, 0, v_snd_1810_);
lean_closure_set(v___f_1811_, 1, v___x_1803_);
lean_closure_set(v___f_1811_, 2, v_toPure_1804_);
v___x_1812_ = lean_apply_1(v_p_1805_, v_a_1807_);
v___x_1813_ = lean_apply_4(v_toBind_1806_, lean_box(0), lean_box(0), v___x_1812_, v___f_1811_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__2(lean_object* v_toPure_1814_, lean_object* v_____s_1815_){
_start:
{
lean_object* v_fst_1816_; 
v_fst_1816_ = lean_ctor_get(v_____s_1815_, 0);
lean_inc(v_fst_1816_);
lean_dec_ref(v_____s_1815_);
if (lean_obj_tag(v_fst_1816_) == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = lean_box(0);
v___x_1818_ = lean_apply_2(v_toPure_1814_, lean_box(0), v___x_1817_);
return v___x_1818_;
}
else
{
lean_object* v_val_1819_; lean_object* v___x_1820_; 
v_val_1819_ = lean_ctor_get(v_fst_1816_, 0);
lean_inc(v_val_1819_);
lean_dec_ref_known(v_fst_1816_, 1);
v___x_1820_ = lean_apply_2(v_toPure_1814_, lean_box(0), v_val_1819_);
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg(lean_object* v_inst_1824_, lean_object* v_p_1825_, lean_object* v_as_1826_){
_start:
{
lean_object* v_toApplicative_1827_; lean_object* v_toBind_1828_; lean_object* v_toPure_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___f_1832_; lean_object* v___f_1833_; size_t v_sz_1834_; size_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_toApplicative_1827_ = lean_ctor_get(v_inst_1824_, 0);
v_toBind_1828_ = lean_ctor_get(v_inst_1824_, 1);
lean_inc_n(v_toBind_1828_, 2);
v_toPure_1829_ = lean_ctor_get(v_toApplicative_1827_, 1);
v___x_1830_ = lean_box(0);
v___x_1831_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1829_, 2);
v___f_1832_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1832_, 0, v___x_1830_);
lean_closure_set(v___f_1832_, 1, v_toPure_1829_);
lean_closure_set(v___f_1832_, 2, v_p_1825_);
lean_closure_set(v___f_1832_, 3, v_toBind_1828_);
v___f_1833_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1833_, 0, v_toPure_1829_);
v_sz_1834_ = lean_array_size(v_as_1826_);
v___x_1835_ = ((size_t)0ULL);
v___x_1836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1824_, v_as_1826_, v___f_1832_, v_sz_1834_, v___x_1835_, v___x_1831_);
v___x_1837_ = lean_apply_4(v_toBind_1828_, lean_box(0), lean_box(0), v___x_1836_, v___f_1833_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f(lean_object* v_00_u03b1_1838_, lean_object* v_m_1839_, lean_object* v_inst_1840_, lean_object* v_p_1841_, lean_object* v_as_1842_){
_start:
{
lean_object* v_toApplicative_1843_; lean_object* v_toBind_1844_; lean_object* v_toPure_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___f_1848_; lean_object* v___f_1849_; size_t v_sz_1850_; size_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_toApplicative_1843_ = lean_ctor_get(v_inst_1840_, 0);
v_toBind_1844_ = lean_ctor_get(v_inst_1840_, 1);
lean_inc_n(v_toBind_1844_, 2);
v_toPure_1845_ = lean_ctor_get(v_toApplicative_1843_, 1);
v___x_1846_ = lean_box(0);
v___x_1847_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1845_, 2);
v___f_1848_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1848_, 0, v___x_1846_);
lean_closure_set(v___f_1848_, 1, v_toPure_1845_);
lean_closure_set(v___f_1848_, 2, v_p_1841_);
lean_closure_set(v___f_1848_, 3, v_toBind_1844_);
v___f_1849_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1849_, 0, v_toPure_1845_);
v_sz_1850_ = lean_array_size(v_as_1842_);
v___x_1851_ = ((size_t)0ULL);
v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1840_, v_as_1842_, v___f_1848_, v_sz_1850_, v___x_1851_, v___x_1847_);
v___x_1853_ = lean_apply_4(v_toBind_1844_, lean_box(0), lean_box(0), v___x_1852_, v___f_1849_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed(lean_object* v_i_1854_, lean_object* v_inst_1855_, lean_object* v_p_1856_, lean_object* v_as_1857_, lean_object* v_stop_1858_, lean_object* v_toPure_1859_, lean_object* v___x_1860_, lean_object* v_____do__lift_1861_){
_start:
{
size_t v_i_boxed_1862_; size_t v_stop_boxed_1863_; uint8_t v___x_78__boxed_1864_; uint8_t v_____do__lift_79__boxed_1865_; lean_object* v_res_1866_; 
v_i_boxed_1862_ = lean_unbox_usize(v_i_1854_);
lean_dec(v_i_1854_);
v_stop_boxed_1863_ = lean_unbox_usize(v_stop_1858_);
lean_dec(v_stop_1858_);
v___x_78__boxed_1864_ = lean_unbox(v___x_1860_);
v_____do__lift_79__boxed_1865_ = lean_unbox(v_____do__lift_1861_);
v_res_1866_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(v_i_boxed_1862_, v_inst_1855_, v_p_1856_, v_as_1857_, v_stop_boxed_1863_, v_toPure_1859_, v___x_78__boxed_1864_, v_____do__lift_79__boxed_1865_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(lean_object* v_inst_1867_, lean_object* v_p_1868_, lean_object* v_as_1869_, size_t v_i_1870_, size_t v_stop_1871_){
_start:
{
lean_object* v_toApplicative_1872_; lean_object* v_toBind_1873_; lean_object* v_toPure_1874_; uint8_t v___x_1875_; 
v_toApplicative_1872_ = lean_ctor_get(v_inst_1867_, 0);
v_toBind_1873_ = lean_ctor_get(v_inst_1867_, 1);
lean_inc(v_toBind_1873_);
v_toPure_1874_ = lean_ctor_get(v_toApplicative_1872_, 1);
lean_inc(v_toPure_1874_);
v___x_1875_ = lean_usize_dec_eq(v_i_1870_, v_stop_1871_);
if (v___x_1875_ == 0)
{
uint8_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___f_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1876_ = 1;
v___x_1877_ = lean_box_usize(v_i_1870_);
v___x_1878_ = lean_box_usize(v_stop_1871_);
v___x_1879_ = lean_box(v___x_1876_);
lean_inc_ref(v_as_1869_);
lean_inc(v_p_1868_);
v___f_1880_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1880_, 0, v___x_1877_);
lean_closure_set(v___f_1880_, 1, v_inst_1867_);
lean_closure_set(v___f_1880_, 2, v_p_1868_);
lean_closure_set(v___f_1880_, 3, v_as_1869_);
lean_closure_set(v___f_1880_, 4, v___x_1878_);
lean_closure_set(v___f_1880_, 5, v_toPure_1874_);
lean_closure_set(v___f_1880_, 6, v___x_1879_);
v___x_1881_ = lean_array_uget(v_as_1869_, v_i_1870_);
lean_dec_ref(v_as_1869_);
v___x_1882_ = lean_apply_1(v_p_1868_, v___x_1881_);
v___x_1883_ = lean_apply_4(v_toBind_1873_, lean_box(0), lean_box(0), v___x_1882_, v___f_1880_);
return v___x_1883_;
}
else
{
uint8_t v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec(v_toBind_1873_);
lean_dec_ref(v_as_1869_);
lean_dec(v_p_1868_);
lean_dec_ref(v_inst_1867_);
v___x_1884_ = 0;
v___x_1885_ = lean_box(v___x_1884_);
v___x_1886_ = lean_apply_2(v_toPure_1874_, lean_box(0), v___x_1885_);
return v___x_1886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(size_t v_i_1887_, lean_object* v_inst_1888_, lean_object* v_p_1889_, lean_object* v_as_1890_, size_t v_stop_1891_, lean_object* v_toPure_1892_, uint8_t v___x_1893_, uint8_t v_____do__lift_1894_){
_start:
{
if (v_____do__lift_1894_ == 0)
{
size_t v___x_1895_; size_t v___x_1896_; lean_object* v___x_1897_; 
lean_dec(v_toPure_1892_);
v___x_1895_ = ((size_t)1ULL);
v___x_1896_ = lean_usize_add(v_i_1887_, v___x_1895_);
v___x_1897_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1888_, v_p_1889_, v_as_1890_, v___x_1896_, v_stop_1891_);
return v___x_1897_;
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
lean_dec_ref(v_as_1890_);
lean_dec(v_p_1889_);
lean_dec_ref(v_inst_1888_);
v___x_1898_ = lean_box(v___x_1893_);
v___x_1899_ = lean_apply_2(v_toPure_1892_, lean_box(0), v___x_1898_);
return v___x_1899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___boxed(lean_object* v_inst_1900_, lean_object* v_p_1901_, lean_object* v_as_1902_, lean_object* v_i_1903_, lean_object* v_stop_1904_){
_start:
{
size_t v_i_boxed_1905_; size_t v_stop_boxed_1906_; lean_object* v_res_1907_; 
v_i_boxed_1905_ = lean_unbox_usize(v_i_1903_);
lean_dec(v_i_1903_);
v_stop_boxed_1906_ = lean_unbox_usize(v_stop_1904_);
lean_dec(v_stop_1904_);
v_res_1907_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1900_, v_p_1901_, v_as_1902_, v_i_boxed_1905_, v_stop_boxed_1906_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object* v_00_u03b1_1908_, lean_object* v_m_1909_, lean_object* v_inst_1910_, lean_object* v_p_1911_, lean_object* v_as_1912_, size_t v_i_1913_, size_t v_stop_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1910_, v_p_1911_, v_as_1912_, v_i_1913_, v_stop_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___boxed(lean_object* v_00_u03b1_1916_, lean_object* v_m_1917_, lean_object* v_inst_1918_, lean_object* v_p_1919_, lean_object* v_as_1920_, lean_object* v_i_1921_, lean_object* v_stop_1922_){
_start:
{
size_t v_i_boxed_1923_; size_t v_stop_boxed_1924_; lean_object* v_res_1925_; 
v_i_boxed_1923_ = lean_unbox_usize(v_i_1921_);
lean_dec(v_i_1921_);
v_stop_boxed_1924_ = lean_unbox_usize(v_stop_1922_);
lean_dec(v_stop_1922_);
v_res_1925_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(v_00_u03b1_1916_, v_m_1917_, v_inst_1918_, v_p_1919_, v_as_1920_, v_i_boxed_1923_, v_stop_boxed_1924_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg(lean_object* v_inst_1926_, lean_object* v_p_1927_, lean_object* v_as_1928_, lean_object* v_start_1929_, lean_object* v_stop_1930_){
_start:
{
lean_object* v_toApplicative_1931_; lean_object* v_toPure_1932_; lean_object* v___y_1934_; uint8_t v___x_1941_; 
v_toApplicative_1931_ = lean_ctor_get(v_inst_1926_, 0);
v_toPure_1932_ = lean_ctor_get(v_toApplicative_1931_, 1);
v___x_1941_ = lean_nat_dec_lt(v_start_1929_, v_stop_1930_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
lean_inc(v_toPure_1932_);
lean_dec(v_stop_1930_);
lean_dec_ref(v_as_1928_);
lean_dec(v_p_1927_);
lean_dec_ref(v_inst_1926_);
v___x_1942_ = lean_box(v___x_1941_);
v___x_1943_ = lean_apply_2(v_toPure_1932_, lean_box(0), v___x_1942_);
return v___x_1943_;
}
else
{
lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1944_ = lean_array_get_size(v_as_1928_);
v___x_1945_ = lean_nat_dec_le(v_stop_1930_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_dec(v_stop_1930_);
v___y_1934_ = v___x_1944_;
goto v___jp_1933_;
}
else
{
v___y_1934_ = v_stop_1930_;
goto v___jp_1933_;
}
}
v___jp_1933_:
{
uint8_t v___x_1935_; 
v___x_1935_ = lean_nat_dec_lt(v_start_1929_, v___y_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_inc(v_toPure_1932_);
lean_dec(v___y_1934_);
lean_dec_ref(v_as_1928_);
lean_dec(v_p_1927_);
lean_dec_ref(v_inst_1926_);
v___x_1936_ = lean_box(v___x_1935_);
v___x_1937_ = lean_apply_2(v_toPure_1932_, lean_box(0), v___x_1936_);
return v___x_1937_;
}
else
{
size_t v___x_1938_; size_t v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = lean_usize_of_nat(v_start_1929_);
v___x_1939_ = lean_usize_of_nat(v___y_1934_);
lean_dec(v___y_1934_);
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1926_, v_p_1927_, v_as_1928_, v___x_1938_, v___x_1939_);
return v___x_1940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg___boxed(lean_object* v_inst_1946_, lean_object* v_p_1947_, lean_object* v_as_1948_, lean_object* v_start_1949_, lean_object* v_stop_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Array_anyMUnsafe___redArg(v_inst_1946_, v_p_1947_, v_as_1948_, v_start_1949_, v_stop_1950_);
lean_dec(v_start_1949_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe(lean_object* v_00_u03b1_1952_, lean_object* v_m_1953_, lean_object* v_inst_1954_, lean_object* v_p_1955_, lean_object* v_as_1956_, lean_object* v_start_1957_, lean_object* v_stop_1958_){
_start:
{
lean_object* v_toApplicative_1959_; lean_object* v_toPure_1960_; lean_object* v___y_1962_; uint8_t v___x_1969_; 
v_toApplicative_1959_ = lean_ctor_get(v_inst_1954_, 0);
v_toPure_1960_ = lean_ctor_get(v_toApplicative_1959_, 1);
v___x_1969_ = lean_nat_dec_lt(v_start_1957_, v_stop_1958_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_inc(v_toPure_1960_);
lean_dec(v_stop_1958_);
lean_dec_ref(v_as_1956_);
lean_dec(v_p_1955_);
lean_dec_ref(v_inst_1954_);
v___x_1970_ = lean_box(v___x_1969_);
v___x_1971_ = lean_apply_2(v_toPure_1960_, lean_box(0), v___x_1970_);
return v___x_1971_;
}
else
{
lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1972_ = lean_array_get_size(v_as_1956_);
v___x_1973_ = lean_nat_dec_le(v_stop_1958_, v___x_1972_);
if (v___x_1973_ == 0)
{
lean_dec(v_stop_1958_);
v___y_1962_ = v___x_1972_;
goto v___jp_1961_;
}
else
{
v___y_1962_ = v_stop_1958_;
goto v___jp_1961_;
}
}
v___jp_1961_:
{
uint8_t v___x_1963_; 
v___x_1963_ = lean_nat_dec_lt(v_start_1957_, v___y_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_inc(v_toPure_1960_);
lean_dec(v___y_1962_);
lean_dec_ref(v_as_1956_);
lean_dec(v_p_1955_);
lean_dec_ref(v_inst_1954_);
v___x_1964_ = lean_box(v___x_1963_);
v___x_1965_ = lean_apply_2(v_toPure_1960_, lean_box(0), v___x_1964_);
return v___x_1965_;
}
else
{
size_t v___x_1966_; size_t v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = lean_usize_of_nat(v_start_1957_);
v___x_1967_ = lean_usize_of_nat(v___y_1962_);
lean_dec(v___y_1962_);
v___x_1968_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1954_, v_p_1955_, v_as_1956_, v___x_1966_, v___x_1967_);
return v___x_1968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___boxed(lean_object* v_00_u03b1_1974_, lean_object* v_m_1975_, lean_object* v_inst_1976_, lean_object* v_p_1977_, lean_object* v_as_1978_, lean_object* v_start_1979_, lean_object* v_stop_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Array_anyMUnsafe(v_00_u03b1_1974_, v_m_1975_, v_inst_1976_, v_p_1977_, v_as_1978_, v_start_1979_, v_stop_1980_);
lean_dec(v_start_1979_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0___boxed(lean_object* v_j_1982_, lean_object* v_inst_1983_, lean_object* v_p_1984_, lean_object* v_as_1985_, lean_object* v_stop_1986_, lean_object* v_toPure_1987_, lean_object* v___x_1988_, lean_object* v_____do__lift_1989_){
_start:
{
uint8_t v___x_63__boxed_1990_; uint8_t v_____do__lift_64__boxed_1991_; lean_object* v_res_1992_; 
v___x_63__boxed_1990_ = lean_unbox(v___x_1988_);
v_____do__lift_64__boxed_1991_ = lean_unbox(v_____do__lift_1989_);
v_res_1992_ = l_Array_anyM_loop___redArg___lam__0(v_j_1982_, v_inst_1983_, v_p_1984_, v_as_1985_, v_stop_1986_, v_toPure_1987_, v___x_63__boxed_1990_, v_____do__lift_64__boxed_1991_);
lean_dec(v_j_1982_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg(lean_object* v_inst_1993_, lean_object* v_p_1994_, lean_object* v_as_1995_, lean_object* v_stop_1996_, lean_object* v_j_1997_){
_start:
{
lean_object* v_toApplicative_1998_; lean_object* v_toBind_1999_; lean_object* v_toPure_2000_; uint8_t v___x_2001_; 
v_toApplicative_1998_ = lean_ctor_get(v_inst_1993_, 0);
v_toBind_1999_ = lean_ctor_get(v_inst_1993_, 1);
lean_inc(v_toBind_1999_);
v_toPure_2000_ = lean_ctor_get(v_toApplicative_1998_, 1);
lean_inc(v_toPure_2000_);
v___x_2001_ = lean_nat_dec_lt(v_j_1997_, v_stop_1996_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_dec(v_toBind_1999_);
lean_dec(v_j_1997_);
lean_dec(v_stop_1996_);
lean_dec_ref(v_as_1995_);
lean_dec(v_p_1994_);
lean_dec_ref(v_inst_1993_);
v___x_2002_ = lean_box(v___x_2001_);
v___x_2003_ = lean_apply_2(v_toPure_2000_, lean_box(0), v___x_2002_);
return v___x_2003_;
}
else
{
lean_object* v___x_2004_; lean_object* v___f_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2004_ = lean_box(v___x_2001_);
lean_inc_ref(v_as_1995_);
lean_inc(v_p_1994_);
lean_inc(v_j_1997_);
v___f_2005_ = lean_alloc_closure((void*)(l_Array_anyM_loop___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_2005_, 0, v_j_1997_);
lean_closure_set(v___f_2005_, 1, v_inst_1993_);
lean_closure_set(v___f_2005_, 2, v_p_1994_);
lean_closure_set(v___f_2005_, 3, v_as_1995_);
lean_closure_set(v___f_2005_, 4, v_stop_1996_);
lean_closure_set(v___f_2005_, 5, v_toPure_2000_);
lean_closure_set(v___f_2005_, 6, v___x_2004_);
v___x_2006_ = lean_array_fget(v_as_1995_, v_j_1997_);
lean_dec(v_j_1997_);
lean_dec_ref(v_as_1995_);
v___x_2007_ = lean_apply_1(v_p_1994_, v___x_2006_);
v___x_2008_ = lean_apply_4(v_toBind_1999_, lean_box(0), lean_box(0), v___x_2007_, v___f_2005_);
return v___x_2008_;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0(lean_object* v_j_2009_, lean_object* v_inst_2010_, lean_object* v_p_2011_, lean_object* v_as_2012_, lean_object* v_stop_2013_, lean_object* v_toPure_2014_, uint8_t v___x_2015_, uint8_t v_____do__lift_2016_){
_start:
{
if (v_____do__lift_2016_ == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_dec(v_toPure_2014_);
v___x_2017_ = lean_unsigned_to_nat(1u);
v___x_2018_ = lean_nat_add(v_j_2009_, v___x_2017_);
v___x_2019_ = l_Array_anyM_loop___redArg(v_inst_2010_, v_p_2011_, v_as_2012_, v_stop_2013_, v___x_2018_);
return v___x_2019_;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_dec(v_stop_2013_);
lean_dec_ref(v_as_2012_);
lean_dec(v_p_2011_);
lean_dec_ref(v_inst_2010_);
v___x_2020_ = lean_box(v___x_2015_);
v___x_2021_ = lean_apply_2(v_toPure_2014_, lean_box(0), v___x_2020_);
return v___x_2021_;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop(lean_object* v_00_u03b1_2022_, lean_object* v_m_2023_, lean_object* v_inst_2024_, lean_object* v_p_2025_, lean_object* v_as_2026_, lean_object* v_stop_2027_, lean_object* v_h_2028_, lean_object* v_j_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Array_anyM_loop___redArg(v_inst_2024_, v_p_2025_, v_as_2026_, v_stop_2027_, v_j_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0(lean_object* v_toPure_2031_, uint8_t v_____do__lift_2032_){
_start:
{
if (v_____do__lift_2032_ == 0)
{
uint8_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2033_ = 1;
v___x_2034_ = lean_box(v___x_2033_);
v___x_2035_ = lean_apply_2(v_toPure_2031_, lean_box(0), v___x_2034_);
return v___x_2035_;
}
else
{
uint8_t v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = 0;
v___x_2037_ = lean_box(v___x_2036_);
v___x_2038_ = lean_apply_2(v_toPure_2031_, lean_box(0), v___x_2037_);
return v___x_2038_;
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0___boxed(lean_object* v_toPure_2039_, lean_object* v_____do__lift_2040_){
_start:
{
uint8_t v_____do__lift_116__boxed_2041_; lean_object* v_res_2042_; 
v_____do__lift_116__boxed_2041_ = lean_unbox(v_____do__lift_2040_);
v_res_2042_ = l_Array_allM___redArg___lam__0(v_toPure_2039_, v_____do__lift_116__boxed_2041_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1(lean_object* v_toPure_2043_, uint8_t v___x_2044_, uint8_t v_____do__lift_2045_){
_start:
{
if (v_____do__lift_2045_ == 0)
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_box(v___x_2044_);
v___x_2047_ = lean_apply_2(v_toPure_2043_, lean_box(0), v___x_2046_);
return v___x_2047_;
}
else
{
uint8_t v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2048_ = 0;
v___x_2049_ = lean_box(v___x_2048_);
v___x_2050_ = lean_apply_2(v_toPure_2043_, lean_box(0), v___x_2049_);
return v___x_2050_;
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1___boxed(lean_object* v_toPure_2051_, lean_object* v___x_2052_, lean_object* v_____do__lift_2053_){
_start:
{
uint8_t v___x_131__boxed_2054_; uint8_t v_____do__lift_132__boxed_2055_; lean_object* v_res_2056_; 
v___x_131__boxed_2054_ = lean_unbox(v___x_2052_);
v_____do__lift_132__boxed_2055_ = lean_unbox(v_____do__lift_2053_);
v_res_2056_ = l_Array_allM___redArg___lam__1(v_toPure_2051_, v___x_131__boxed_2054_, v_____do__lift_132__boxed_2055_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__2(lean_object* v_p_2057_, lean_object* v_toBind_2058_, lean_object* v___f_2059_, lean_object* v_v_2060_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_apply_1(v_p_2057_, v_v_2060_);
v___x_2062_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___x_2061_, v___f_2059_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg(lean_object* v_inst_2063_, lean_object* v_p_2064_, lean_object* v_as_2065_, lean_object* v_start_2066_, lean_object* v_stop_2067_){
_start:
{
lean_object* v_toApplicative_2068_; lean_object* v_toBind_2069_; lean_object* v_toPure_2070_; lean_object* v___f_2071_; uint8_t v___x_2072_; 
v_toApplicative_2068_ = lean_ctor_get(v_inst_2063_, 0);
v_toBind_2069_ = lean_ctor_get(v_inst_2063_, 1);
lean_inc(v_toBind_2069_);
v_toPure_2070_ = lean_ctor_get(v_toApplicative_2068_, 1);
lean_inc(v_toPure_2070_);
v___f_2071_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2071_, 0, v_toPure_2070_);
v___x_2072_ = lean_nat_dec_lt(v_start_2066_, v_stop_2067_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_inc(v_toPure_2070_);
lean_dec(v_stop_2067_);
lean_dec_ref(v_as_2065_);
lean_dec(v_p_2064_);
lean_dec_ref(v_inst_2063_);
v___x_2073_ = lean_box(v___x_2072_);
v___x_2074_ = lean_apply_2(v_toPure_2070_, lean_box(0), v___x_2073_);
v___x_2075_ = lean_apply_4(v_toBind_2069_, lean_box(0), lean_box(0), v___x_2074_, v___f_2071_);
return v___x_2075_;
}
else
{
lean_object* v___x_2076_; lean_object* v___f_2077_; lean_object* v___f_2078_; lean_object* v___y_2080_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2076_ = lean_box(v___x_2072_);
lean_inc(v_toPure_2070_);
v___f_2077_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2077_, 0, v_toPure_2070_);
lean_closure_set(v___f_2077_, 1, v___x_2076_);
lean_inc(v_toBind_2069_);
v___f_2078_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2078_, 0, v_p_2064_);
lean_closure_set(v___f_2078_, 1, v_toBind_2069_);
lean_closure_set(v___f_2078_, 2, v___f_2077_);
v___x_2089_ = lean_array_get_size(v_as_2065_);
v___x_2090_ = lean_nat_dec_le(v_stop_2067_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_dec(v_stop_2067_);
v___y_2080_ = v___x_2089_;
goto v___jp_2079_;
}
else
{
v___y_2080_ = v_stop_2067_;
goto v___jp_2079_;
}
v___jp_2079_:
{
uint8_t v___x_2081_; 
v___x_2081_ = lean_nat_dec_lt(v_start_2066_, v___y_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_inc(v_toPure_2070_);
lean_dec(v___y_2080_);
lean_dec_ref(v___f_2078_);
lean_dec_ref(v_as_2065_);
lean_dec_ref(v_inst_2063_);
v___x_2082_ = lean_box(v___x_2081_);
v___x_2083_ = lean_apply_2(v_toPure_2070_, lean_box(0), v___x_2082_);
v___x_2084_ = lean_apply_4(v_toBind_2069_, lean_box(0), lean_box(0), v___x_2083_, v___f_2071_);
return v___x_2084_;
}
else
{
size_t v___x_2085_; size_t v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2085_ = lean_usize_of_nat(v_start_2066_);
v___x_2086_ = lean_usize_of_nat(v___y_2080_);
lean_dec(v___y_2080_);
v___x_2087_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2063_, v___f_2078_, v_as_2065_, v___x_2085_, v___x_2086_);
v___x_2088_ = lean_apply_4(v_toBind_2069_, lean_box(0), lean_box(0), v___x_2087_, v___f_2071_);
return v___x_2088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___boxed(lean_object* v_inst_2091_, lean_object* v_p_2092_, lean_object* v_as_2093_, lean_object* v_start_2094_, lean_object* v_stop_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Array_allM___redArg(v_inst_2091_, v_p_2092_, v_as_2093_, v_start_2094_, v_stop_2095_);
lean_dec(v_start_2094_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Array_allM(lean_object* v_00_u03b1_2097_, lean_object* v_m_2098_, lean_object* v_inst_2099_, lean_object* v_p_2100_, lean_object* v_as_2101_, lean_object* v_start_2102_, lean_object* v_stop_2103_){
_start:
{
lean_object* v_toApplicative_2104_; lean_object* v_toBind_2105_; lean_object* v_toPure_2106_; lean_object* v___f_2107_; uint8_t v___x_2108_; 
v_toApplicative_2104_ = lean_ctor_get(v_inst_2099_, 0);
v_toBind_2105_ = lean_ctor_get(v_inst_2099_, 1);
lean_inc(v_toBind_2105_);
v_toPure_2106_ = lean_ctor_get(v_toApplicative_2104_, 1);
lean_inc(v_toPure_2106_);
v___f_2107_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2107_, 0, v_toPure_2106_);
v___x_2108_ = lean_nat_dec_lt(v_start_2102_, v_stop_2103_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
lean_inc(v_toPure_2106_);
lean_dec(v_stop_2103_);
lean_dec_ref(v_as_2101_);
lean_dec(v_p_2100_);
lean_dec_ref(v_inst_2099_);
v___x_2109_ = lean_box(v___x_2108_);
v___x_2110_ = lean_apply_2(v_toPure_2106_, lean_box(0), v___x_2109_);
v___x_2111_ = lean_apply_4(v_toBind_2105_, lean_box(0), lean_box(0), v___x_2110_, v___f_2107_);
return v___x_2111_;
}
else
{
lean_object* v___x_2112_; lean_object* v___f_2113_; lean_object* v___f_2114_; lean_object* v___y_2116_; lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2112_ = lean_box(v___x_2108_);
lean_inc(v_toPure_2106_);
v___f_2113_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2113_, 0, v_toPure_2106_);
lean_closure_set(v___f_2113_, 1, v___x_2112_);
lean_inc(v_toBind_2105_);
v___f_2114_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2114_, 0, v_p_2100_);
lean_closure_set(v___f_2114_, 1, v_toBind_2105_);
lean_closure_set(v___f_2114_, 2, v___f_2113_);
v___x_2125_ = lean_array_get_size(v_as_2101_);
v___x_2126_ = lean_nat_dec_le(v_stop_2103_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_dec(v_stop_2103_);
v___y_2116_ = v___x_2125_;
goto v___jp_2115_;
}
else
{
v___y_2116_ = v_stop_2103_;
goto v___jp_2115_;
}
v___jp_2115_:
{
uint8_t v___x_2117_; 
v___x_2117_ = lean_nat_dec_lt(v_start_2102_, v___y_2116_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_inc(v_toPure_2106_);
lean_dec(v___y_2116_);
lean_dec_ref(v___f_2114_);
lean_dec_ref(v_as_2101_);
lean_dec_ref(v_inst_2099_);
v___x_2118_ = lean_box(v___x_2117_);
v___x_2119_ = lean_apply_2(v_toPure_2106_, lean_box(0), v___x_2118_);
v___x_2120_ = lean_apply_4(v_toBind_2105_, lean_box(0), lean_box(0), v___x_2119_, v___f_2107_);
return v___x_2120_;
}
else
{
size_t v___x_2121_; size_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2121_ = lean_usize_of_nat(v_start_2102_);
v___x_2122_ = lean_usize_of_nat(v___y_2116_);
lean_dec(v___y_2116_);
v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2099_, v___f_2114_, v_as_2101_, v___x_2121_, v___x_2122_);
v___x_2124_ = lean_apply_4(v_toBind_2105_, lean_box(0), lean_box(0), v___x_2123_, v___f_2107_);
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
uint8_t v_____do__lift_59__boxed_2213_; lean_object* v_res_2214_; 
v_____do__lift_59__boxed_2213_ = lean_unbox(v_____do__lift_2212_);
v_res_2214_ = l_Array_findRevM_x3f___redArg___lam__0(v_toPure_2210_, v_a_2211_, v_____do__lift_59__boxed_2213_);
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
lean_object* v_toApplicative_2251_; lean_object* v_toPure_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v_toApplicative_2251_ = lean_ctor_get(v_inst_2246_, 0);
v_toPure_2252_ = lean_ctor_get(v_toApplicative_2251_, 1);
v___x_2253_ = lean_box(0);
v___x_2254_ = lean_nat_dec_lt(v_start_2249_, v_stop_2250_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; 
lean_inc(v_toPure_2252_);
lean_dec_ref(v_as_2248_);
lean_dec(v_f_2247_);
lean_dec_ref(v_inst_2246_);
v___x_2255_ = lean_apply_2(v_toPure_2252_, lean_box(0), v___x_2253_);
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
lean_object* v___x_2260_; 
lean_inc(v_toPure_2252_);
lean_dec_ref(v___f_2256_);
lean_dec_ref(v_as_2248_);
lean_dec_ref(v_inst_2246_);
v___x_2260_ = lean_apply_2(v_toPure_2252_, lean_box(0), v___x_2253_);
return v___x_2260_;
}
else
{
size_t v___x_2261_; size_t v___x_2262_; lean_object* v___x_2263_; 
v___x_2261_ = lean_usize_of_nat(v_start_2249_);
v___x_2262_ = lean_usize_of_nat(v___x_2257_);
v___x_2263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2246_, v___f_2256_, v_as_2248_, v___x_2261_, v___x_2262_, v___x_2253_);
return v___x_2263_;
}
}
else
{
size_t v___x_2264_; size_t v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = lean_usize_of_nat(v_start_2249_);
v___x_2265_ = lean_usize_of_nat(v_stop_2250_);
v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2246_, v___f_2256_, v_as_2248_, v___x_2264_, v___x_2265_, v___x_2253_);
return v___x_2266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___boxed(lean_object* v_inst_2267_, lean_object* v_f_2268_, lean_object* v_as_2269_, lean_object* v_start_2270_, lean_object* v_stop_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Array_forM___redArg(v_inst_2267_, v_f_2268_, v_as_2269_, v_start_2270_, v_stop_2271_);
lean_dec(v_stop_2271_);
lean_dec(v_start_2270_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Array_forM(lean_object* v_00_u03b1_2273_, lean_object* v_m_2274_, lean_object* v_inst_2275_, lean_object* v_f_2276_, lean_object* v_as_2277_, lean_object* v_start_2278_, lean_object* v_stop_2279_){
_start:
{
lean_object* v_toApplicative_2280_; lean_object* v_toPure_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v_toApplicative_2280_ = lean_ctor_get(v_inst_2275_, 0);
v_toPure_2281_ = lean_ctor_get(v_toApplicative_2280_, 1);
v___x_2282_ = lean_box(0);
v___x_2283_ = lean_nat_dec_lt(v_start_2278_, v_stop_2279_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; 
lean_inc(v_toPure_2281_);
lean_dec_ref(v_as_2277_);
lean_dec(v_f_2276_);
lean_dec_ref(v_inst_2275_);
v___x_2284_ = lean_apply_2(v_toPure_2281_, lean_box(0), v___x_2282_);
return v___x_2284_;
}
else
{
lean_object* v___f_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___f_2285_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2285_, 0, v_f_2276_);
v___x_2286_ = lean_array_get_size(v_as_2277_);
v___x_2287_ = lean_nat_dec_le(v_stop_2279_, v___x_2286_);
if (v___x_2287_ == 0)
{
uint8_t v___x_2288_; 
v___x_2288_ = lean_nat_dec_lt(v_start_2278_, v___x_2286_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; 
lean_inc(v_toPure_2281_);
lean_dec_ref(v___f_2285_);
lean_dec_ref(v_as_2277_);
lean_dec_ref(v_inst_2275_);
v___x_2289_ = lean_apply_2(v_toPure_2281_, lean_box(0), v___x_2282_);
return v___x_2289_;
}
else
{
size_t v___x_2290_; size_t v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = lean_usize_of_nat(v_start_2278_);
v___x_2291_ = lean_usize_of_nat(v___x_2286_);
v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2275_, v___f_2285_, v_as_2277_, v___x_2290_, v___x_2291_, v___x_2282_);
return v___x_2292_;
}
}
else
{
size_t v___x_2293_; size_t v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = lean_usize_of_nat(v_start_2278_);
v___x_2294_ = lean_usize_of_nat(v_stop_2279_);
v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2275_, v___f_2285_, v_as_2277_, v___x_2293_, v___x_2294_, v___x_2282_);
return v___x_2295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___boxed(lean_object* v_00_u03b1_2296_, lean_object* v_m_2297_, lean_object* v_inst_2298_, lean_object* v_f_2299_, lean_object* v_as_2300_, lean_object* v_start_2301_, lean_object* v_stop_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Array_forM(v_00_u03b1_2296_, v_m_2297_, v_inst_2298_, v_f_2299_, v_as_2300_, v_start_2301_, v_stop_2302_);
lean_dec(v_stop_2302_);
lean_dec(v_start_2301_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg___lam__1(lean_object* v_inst_2304_, lean_object* v_xs_2305_, lean_object* v_f_2306_){
_start:
{
lean_object* v_toApplicative_2307_; lean_object* v_toPure_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v_toApplicative_2307_ = lean_ctor_get(v_inst_2304_, 0);
v_toPure_2308_ = lean_ctor_get(v_toApplicative_2307_, 1);
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = lean_array_get_size(v_xs_2305_);
v___x_2311_ = lean_box(0);
v___x_2312_ = lean_nat_dec_lt(v___x_2309_, v___x_2310_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; 
lean_inc(v_toPure_2308_);
lean_dec(v_f_2306_);
lean_dec_ref(v_xs_2305_);
lean_dec_ref(v_inst_2304_);
v___x_2313_ = lean_apply_2(v_toPure_2308_, lean_box(0), v___x_2311_);
return v___x_2313_;
}
else
{
lean_object* v___f_2314_; uint8_t v___x_2315_; 
v___f_2314_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2314_, 0, v_f_2306_);
v___x_2315_ = lean_nat_dec_le(v___x_2310_, v___x_2310_);
if (v___x_2315_ == 0)
{
if (v___x_2312_ == 0)
{
lean_object* v___x_2316_; 
lean_inc(v_toPure_2308_);
lean_dec_ref(v___f_2314_);
lean_dec_ref(v_xs_2305_);
lean_dec_ref(v_inst_2304_);
v___x_2316_ = lean_apply_2(v_toPure_2308_, lean_box(0), v___x_2311_);
return v___x_2316_;
}
else
{
size_t v___x_2317_; size_t v___x_2318_; lean_object* v___x_2319_; 
v___x_2317_ = ((size_t)0ULL);
v___x_2318_ = lean_usize_of_nat(v___x_2310_);
v___x_2319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2304_, v___f_2314_, v_xs_2305_, v___x_2317_, v___x_2318_, v___x_2311_);
return v___x_2319_;
}
}
else
{
size_t v___x_2320_; size_t v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = ((size_t)0ULL);
v___x_2321_ = lean_usize_of_nat(v___x_2310_);
v___x_2322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2304_, v___f_2314_, v_xs_2305_, v___x_2320_, v___x_2321_, v___x_2311_);
return v___x_2322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg(lean_object* v_inst_2323_){
_start:
{
lean_object* v___f_2324_; 
v___f_2324_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2324_, 0, v_inst_2323_);
return v___f_2324_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad(lean_object* v_00_u03b1_2325_, lean_object* v_m_2326_, lean_object* v_inst_2327_){
_start:
{
lean_object* v___f_2328_; 
v___f_2328_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2328_, 0, v_inst_2327_);
return v___f_2328_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___lam__0(lean_object* v_f_2329_, lean_object* v_a_2330_, lean_object* v_x_2331_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = lean_apply_1(v_f_2329_, v_a_2330_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg(lean_object* v_inst_2333_, lean_object* v_f_2334_, lean_object* v_as_2335_, lean_object* v_start_2336_, lean_object* v_stop_2337_){
_start:
{
lean_object* v_toApplicative_2338_; lean_object* v_toPure_2339_; lean_object* v___f_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v_toApplicative_2338_ = lean_ctor_get(v_inst_2333_, 0);
v_toPure_2339_ = lean_ctor_get(v_toApplicative_2338_, 1);
v___f_2340_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2340_, 0, v_f_2334_);
v___x_2341_ = lean_box(0);
v___x_2342_ = lean_array_get_size(v_as_2335_);
v___x_2343_ = lean_nat_dec_le(v_start_2336_, v___x_2342_);
if (v___x_2343_ == 0)
{
uint8_t v___x_2344_; 
v___x_2344_ = lean_nat_dec_lt(v_stop_2337_, v___x_2342_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_inc(v_toPure_2339_);
lean_dec_ref(v___f_2340_);
lean_dec_ref(v_as_2335_);
lean_dec_ref(v_inst_2333_);
v___x_2345_ = lean_apply_2(v_toPure_2339_, lean_box(0), v___x_2341_);
return v___x_2345_;
}
else
{
size_t v___x_2346_; size_t v___x_2347_; lean_object* v___x_2348_; 
v___x_2346_ = lean_usize_of_nat(v___x_2342_);
v___x_2347_ = lean_usize_of_nat(v_stop_2337_);
v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2333_, v___f_2340_, v_as_2335_, v___x_2346_, v___x_2347_, v___x_2341_);
return v___x_2348_;
}
}
else
{
uint8_t v___x_2349_; 
v___x_2349_ = lean_nat_dec_lt(v_stop_2337_, v_start_2336_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; 
lean_inc(v_toPure_2339_);
lean_dec_ref(v___f_2340_);
lean_dec_ref(v_as_2335_);
lean_dec_ref(v_inst_2333_);
v___x_2350_ = lean_apply_2(v_toPure_2339_, lean_box(0), v___x_2341_);
return v___x_2350_;
}
else
{
size_t v___x_2351_; size_t v___x_2352_; lean_object* v___x_2353_; 
v___x_2351_ = lean_usize_of_nat(v_start_2336_);
v___x_2352_ = lean_usize_of_nat(v_stop_2337_);
v___x_2353_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2333_, v___f_2340_, v_as_2335_, v___x_2351_, v___x_2352_, v___x_2341_);
return v___x_2353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___boxed(lean_object* v_inst_2354_, lean_object* v_f_2355_, lean_object* v_as_2356_, lean_object* v_start_2357_, lean_object* v_stop_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Array_forRevM___redArg(v_inst_2354_, v_f_2355_, v_as_2356_, v_start_2357_, v_stop_2358_);
lean_dec(v_stop_2358_);
lean_dec(v_start_2357_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM(lean_object* v_00_u03b1_2360_, lean_object* v_m_2361_, lean_object* v_inst_2362_, lean_object* v_f_2363_, lean_object* v_as_2364_, lean_object* v_start_2365_, lean_object* v_stop_2366_){
_start:
{
lean_object* v_toApplicative_2367_; lean_object* v_toPure_2368_; lean_object* v___f_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v_toApplicative_2367_ = lean_ctor_get(v_inst_2362_, 0);
v_toPure_2368_ = lean_ctor_get(v_toApplicative_2367_, 1);
v___f_2369_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2369_, 0, v_f_2363_);
v___x_2370_ = lean_box(0);
v___x_2371_ = lean_array_get_size(v_as_2364_);
v___x_2372_ = lean_nat_dec_le(v_start_2365_, v___x_2371_);
if (v___x_2372_ == 0)
{
uint8_t v___x_2373_; 
v___x_2373_ = lean_nat_dec_lt(v_stop_2366_, v___x_2371_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; 
lean_inc(v_toPure_2368_);
lean_dec_ref(v___f_2369_);
lean_dec_ref(v_as_2364_);
lean_dec_ref(v_inst_2362_);
v___x_2374_ = lean_apply_2(v_toPure_2368_, lean_box(0), v___x_2370_);
return v___x_2374_;
}
else
{
size_t v___x_2375_; size_t v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = lean_usize_of_nat(v___x_2371_);
v___x_2376_ = lean_usize_of_nat(v_stop_2366_);
v___x_2377_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2362_, v___f_2369_, v_as_2364_, v___x_2375_, v___x_2376_, v___x_2370_);
return v___x_2377_;
}
}
else
{
uint8_t v___x_2378_; 
v___x_2378_ = lean_nat_dec_lt(v_stop_2366_, v_start_2365_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; 
lean_inc(v_toPure_2368_);
lean_dec_ref(v___f_2369_);
lean_dec_ref(v_as_2364_);
lean_dec_ref(v_inst_2362_);
v___x_2379_ = lean_apply_2(v_toPure_2368_, lean_box(0), v___x_2370_);
return v___x_2379_;
}
else
{
size_t v___x_2380_; size_t v___x_2381_; lean_object* v___x_2382_; 
v___x_2380_ = lean_usize_of_nat(v_start_2365_);
v___x_2381_ = lean_usize_of_nat(v_stop_2366_);
v___x_2382_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2362_, v___f_2369_, v_as_2364_, v___x_2380_, v___x_2381_, v___x_2370_);
return v___x_2382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___boxed(lean_object* v_00_u03b1_2383_, lean_object* v_m_2384_, lean_object* v_inst_2385_, lean_object* v_f_2386_, lean_object* v_as_2387_, lean_object* v_start_2388_, lean_object* v_stop_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Array_forRevM(v_00_u03b1_2383_, v_m_2384_, v_inst_2385_, v_f_2386_, v_as_2387_, v_start_2388_, v_stop_2389_);
lean_dec(v_stop_2389_);
lean_dec(v_start_2388_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___lam__0(lean_object* v_f_2391_, lean_object* v_x1_2392_, lean_object* v_x2_2393_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = lean_apply_2(v_f_2391_, v_x1_2392_, v_x2_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg(lean_object* v_f_2414_, lean_object* v_init_2415_, lean_object* v_as_2416_, lean_object* v_start_2417_, lean_object* v_stop_2418_){
_start:
{
lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2419_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2420_ = lean_nat_dec_lt(v_start_2417_, v_stop_2418_);
if (v___x_2420_ == 0)
{
lean_dec_ref(v_as_2416_);
lean_dec(v_f_2414_);
return v_init_2415_;
}
else
{
lean_object* v___f_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; 
v___f_2421_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2421_, 0, v_f_2414_);
v___x_2422_ = lean_array_get_size(v_as_2416_);
v___x_2423_ = lean_nat_dec_le(v_stop_2418_, v___x_2422_);
if (v___x_2423_ == 0)
{
uint8_t v___x_2424_; 
v___x_2424_ = lean_nat_dec_lt(v_start_2417_, v___x_2422_);
if (v___x_2424_ == 0)
{
lean_dec_ref(v___f_2421_);
lean_dec_ref(v_as_2416_);
return v_init_2415_;
}
else
{
size_t v___x_2425_; size_t v___x_2426_; lean_object* v___x_2427_; 
v___x_2425_ = lean_usize_of_nat(v_start_2417_);
v___x_2426_ = lean_usize_of_nat(v___x_2422_);
v___x_2427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2419_, v___f_2421_, v_as_2416_, v___x_2425_, v___x_2426_, v_init_2415_);
return v___x_2427_;
}
}
else
{
size_t v___x_2428_; size_t v___x_2429_; lean_object* v___x_2430_; 
v___x_2428_ = lean_usize_of_nat(v_start_2417_);
v___x_2429_ = lean_usize_of_nat(v_stop_2418_);
v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2419_, v___f_2421_, v_as_2416_, v___x_2428_, v___x_2429_, v_init_2415_);
return v___x_2430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___boxed(lean_object* v_f_2431_, lean_object* v_init_2432_, lean_object* v_as_2433_, lean_object* v_start_2434_, lean_object* v_stop_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Array_foldl___redArg(v_f_2431_, v_init_2432_, v_as_2433_, v_start_2434_, v_stop_2435_);
lean_dec(v_stop_2435_);
lean_dec(v_start_2434_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl(lean_object* v_00_u03b1_2437_, lean_object* v_00_u03b2_2438_, lean_object* v_f_2439_, lean_object* v_init_2440_, lean_object* v_as_2441_, lean_object* v_start_2442_, lean_object* v_stop_2443_){
_start:
{
lean_object* v___x_2444_; uint8_t v___x_2445_; 
v___x_2444_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2445_ = lean_nat_dec_lt(v_start_2442_, v_stop_2443_);
if (v___x_2445_ == 0)
{
lean_dec_ref(v_as_2441_);
lean_dec(v_f_2439_);
return v_init_2440_;
}
else
{
lean_object* v___f_2446_; lean_object* v___x_2447_; uint8_t v___x_2448_; 
v___f_2446_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2446_, 0, v_f_2439_);
v___x_2447_ = lean_array_get_size(v_as_2441_);
v___x_2448_ = lean_nat_dec_le(v_stop_2443_, v___x_2447_);
if (v___x_2448_ == 0)
{
uint8_t v___x_2449_; 
v___x_2449_ = lean_nat_dec_lt(v_start_2442_, v___x_2447_);
if (v___x_2449_ == 0)
{
lean_dec_ref(v___f_2446_);
lean_dec_ref(v_as_2441_);
return v_init_2440_;
}
else
{
size_t v___x_2450_; size_t v___x_2451_; lean_object* v___x_2452_; 
v___x_2450_ = lean_usize_of_nat(v_start_2442_);
v___x_2451_ = lean_usize_of_nat(v___x_2447_);
v___x_2452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2444_, v___f_2446_, v_as_2441_, v___x_2450_, v___x_2451_, v_init_2440_);
return v___x_2452_;
}
}
else
{
size_t v___x_2453_; size_t v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = lean_usize_of_nat(v_start_2442_);
v___x_2454_ = lean_usize_of_nat(v_stop_2443_);
v___x_2455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2444_, v___f_2446_, v_as_2441_, v___x_2453_, v___x_2454_, v_init_2440_);
return v___x_2455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___boxed(lean_object* v_00_u03b1_2456_, lean_object* v_00_u03b2_2457_, lean_object* v_f_2458_, lean_object* v_init_2459_, lean_object* v_as_2460_, lean_object* v_start_2461_, lean_object* v_stop_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Array_foldl(v_00_u03b1_2456_, v_00_u03b2_2457_, v_f_2458_, v_init_2459_, v_as_2460_, v_start_2461_, v_stop_2462_);
lean_dec(v_stop_2462_);
lean_dec(v_start_2461_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg(lean_object* v_f_2464_, lean_object* v_init_2465_, lean_object* v_as_2466_, lean_object* v_start_2467_, lean_object* v_stop_2468_){
_start:
{
lean_object* v___f_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___f_2469_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2469_, 0, v_f_2464_);
v___x_2470_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2471_ = lean_array_get_size(v_as_2466_);
v___x_2472_ = lean_nat_dec_le(v_start_2467_, v___x_2471_);
if (v___x_2472_ == 0)
{
uint8_t v___x_2473_; 
v___x_2473_ = lean_nat_dec_lt(v_stop_2468_, v___x_2471_);
if (v___x_2473_ == 0)
{
lean_dec_ref(v___f_2469_);
lean_dec_ref(v_as_2466_);
return v_init_2465_;
}
else
{
size_t v___x_2474_; size_t v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = lean_usize_of_nat(v___x_2471_);
v___x_2475_ = lean_usize_of_nat(v_stop_2468_);
v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2470_, v___f_2469_, v_as_2466_, v___x_2474_, v___x_2475_, v_init_2465_);
return v___x_2476_;
}
}
else
{
uint8_t v___x_2477_; 
v___x_2477_ = lean_nat_dec_lt(v_stop_2468_, v_start_2467_);
if (v___x_2477_ == 0)
{
lean_dec_ref(v___f_2469_);
lean_dec_ref(v_as_2466_);
return v_init_2465_;
}
else
{
size_t v___x_2478_; size_t v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = lean_usize_of_nat(v_start_2467_);
v___x_2479_ = lean_usize_of_nat(v_stop_2468_);
v___x_2480_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2470_, v___f_2469_, v_as_2466_, v___x_2478_, v___x_2479_, v_init_2465_);
return v___x_2480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg___boxed(lean_object* v_f_2481_, lean_object* v_init_2482_, lean_object* v_as_2483_, lean_object* v_start_2484_, lean_object* v_stop_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Array_foldr___redArg(v_f_2481_, v_init_2482_, v_as_2483_, v_start_2484_, v_stop_2485_);
lean_dec(v_stop_2485_);
lean_dec(v_start_2484_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr(lean_object* v_00_u03b1_2487_, lean_object* v_00_u03b2_2488_, lean_object* v_f_2489_, lean_object* v_init_2490_, lean_object* v_as_2491_, lean_object* v_start_2492_, lean_object* v_stop_2493_){
_start:
{
lean_object* v___f_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___f_2494_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2494_, 0, v_f_2489_);
v___x_2495_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2496_ = lean_array_get_size(v_as_2491_);
v___x_2497_ = lean_nat_dec_le(v_start_2492_, v___x_2496_);
if (v___x_2497_ == 0)
{
uint8_t v___x_2498_; 
v___x_2498_ = lean_nat_dec_lt(v_stop_2493_, v___x_2496_);
if (v___x_2498_ == 0)
{
lean_dec_ref(v___f_2494_);
lean_dec_ref(v_as_2491_);
return v_init_2490_;
}
else
{
size_t v___x_2499_; size_t v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = lean_usize_of_nat(v___x_2496_);
v___x_2500_ = lean_usize_of_nat(v_stop_2493_);
v___x_2501_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2495_, v___f_2494_, v_as_2491_, v___x_2499_, v___x_2500_, v_init_2490_);
return v___x_2501_;
}
}
else
{
uint8_t v___x_2502_; 
v___x_2502_ = lean_nat_dec_lt(v_stop_2493_, v_start_2492_);
if (v___x_2502_ == 0)
{
lean_dec_ref(v___f_2494_);
lean_dec_ref(v_as_2491_);
return v_init_2490_;
}
else
{
size_t v___x_2503_; size_t v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = lean_usize_of_nat(v_start_2492_);
v___x_2504_ = lean_usize_of_nat(v_stop_2493_);
v___x_2505_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2495_, v___f_2494_, v_as_2491_, v___x_2503_, v___x_2504_, v_init_2490_);
return v___x_2505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___boxed(lean_object* v_00_u03b1_2506_, lean_object* v_00_u03b2_2507_, lean_object* v_f_2508_, lean_object* v_init_2509_, lean_object* v_as_2510_, lean_object* v_start_2511_, lean_object* v_stop_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Array_foldr(v_00_u03b1_2506_, v_00_u03b2_2507_, v_f_2508_, v_init_2509_, v_as_2510_, v_start_2511_, v_stop_2512_);
lean_dec(v_stop_2512_);
lean_dec(v_start_2511_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg___lam__0(lean_object* v_inst_2514_, lean_object* v_x1_2515_, lean_object* v_x2_2516_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = lean_apply_2(v_inst_2514_, v_x1_2515_, v_x2_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg(lean_object* v_inst_2518_, lean_object* v_inst_2519_, lean_object* v_as_2520_){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2521_ = lean_array_get_size(v_as_2520_);
v___x_2522_ = lean_unsigned_to_nat(0u);
v___x_2523_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2524_ = lean_nat_dec_lt(v___x_2522_, v___x_2521_);
if (v___x_2524_ == 0)
{
lean_dec_ref(v_as_2520_);
lean_dec(v_inst_2518_);
return v_inst_2519_;
}
else
{
lean_object* v___f_2525_; size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___f_2525_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2525_, 0, v_inst_2518_);
v___x_2526_ = lean_usize_of_nat(v___x_2521_);
v___x_2527_ = ((size_t)0ULL);
v___x_2528_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2523_, v___f_2525_, v_as_2520_, v___x_2526_, v___x_2527_, v_inst_2519_);
return v___x_2528_;
}
}
}
LEAN_EXPORT lean_object* l_Array_sum(lean_object* v_00_u03b1_2529_, lean_object* v_inst_2530_, lean_object* v_inst_2531_, lean_object* v_as_2532_){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2533_ = lean_array_get_size(v_as_2532_);
v___x_2534_ = lean_unsigned_to_nat(0u);
v___x_2535_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2536_ = lean_nat_dec_lt(v___x_2534_, v___x_2533_);
if (v___x_2536_ == 0)
{
lean_dec_ref(v_as_2532_);
lean_dec(v_inst_2530_);
return v_inst_2531_;
}
else
{
lean_object* v___f_2537_; size_t v___x_2538_; size_t v___x_2539_; lean_object* v___x_2540_; 
v___f_2537_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2537_, 0, v_inst_2530_);
v___x_2538_ = lean_usize_of_nat(v___x_2533_);
v___x_2539_ = ((size_t)0ULL);
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2535_, v___f_2537_, v_as_2532_, v___x_2538_, v___x_2539_, v_inst_2531_);
return v___x_2540_;
}
}
}
LEAN_EXPORT lean_object* l_Array_prod___redArg(lean_object* v_inst_2541_, lean_object* v_inst_2542_, lean_object* v_as_2543_){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2544_ = lean_array_get_size(v_as_2543_);
v___x_2545_ = lean_unsigned_to_nat(0u);
v___x_2546_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2547_ = lean_nat_dec_lt(v___x_2545_, v___x_2544_);
if (v___x_2547_ == 0)
{
lean_dec_ref(v_as_2543_);
lean_dec(v_inst_2541_);
return v_inst_2542_;
}
else
{
lean_object* v___f_2548_; size_t v___x_2549_; size_t v___x_2550_; lean_object* v___x_2551_; 
v___f_2548_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2548_, 0, v_inst_2541_);
v___x_2549_ = lean_usize_of_nat(v___x_2544_);
v___x_2550_ = ((size_t)0ULL);
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2546_, v___f_2548_, v_as_2543_, v___x_2549_, v___x_2550_, v_inst_2542_);
return v___x_2551_;
}
}
}
LEAN_EXPORT lean_object* l_Array_prod(lean_object* v_00_u03b1_2552_, lean_object* v_inst_2553_, lean_object* v_inst_2554_, lean_object* v_as_2555_){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2556_ = lean_array_get_size(v_as_2555_);
v___x_2557_ = lean_unsigned_to_nat(0u);
v___x_2558_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2559_ = lean_nat_dec_lt(v___x_2557_, v___x_2556_);
if (v___x_2559_ == 0)
{
lean_dec_ref(v_as_2555_);
lean_dec(v_inst_2553_);
return v_inst_2554_;
}
else
{
lean_object* v___f_2560_; size_t v___x_2561_; size_t v___x_2562_; lean_object* v___x_2563_; 
v___f_2560_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2560_, 0, v_inst_2553_);
v___x_2561_ = lean_usize_of_nat(v___x_2556_);
v___x_2562_ = ((size_t)0ULL);
v___x_2563_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2558_, v___f_2560_, v_as_2555_, v___x_2561_, v___x_2562_, v_inst_2554_);
return v___x_2563_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0(lean_object* v_p_2564_, lean_object* v_x1_2565_, lean_object* v_x2_2566_){
_start:
{
lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2567_ = lean_apply_1(v_p_2564_, v_x1_2565_);
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
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0___boxed(lean_object* v_p_2571_, lean_object* v_x1_2572_, lean_object* v_x2_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Array_countP___redArg___lam__0(v_p_2571_, v_x1_2572_, v_x2_2573_);
lean_dec(v_x2_2573_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg(lean_object* v_p_2575_, lean_object* v_as_2576_){
_start:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; 
v___x_2577_ = lean_unsigned_to_nat(0u);
v___x_2578_ = lean_array_get_size(v_as_2576_);
v___x_2579_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2580_ = lean_nat_dec_lt(v___x_2577_, v___x_2578_);
if (v___x_2580_ == 0)
{
lean_dec_ref(v_as_2576_);
lean_dec_ref(v_p_2575_);
return v___x_2577_;
}
else
{
lean_object* v___f_2581_; size_t v___x_2582_; size_t v___x_2583_; lean_object* v___x_2584_; 
v___f_2581_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2581_, 0, v_p_2575_);
v___x_2582_ = lean_usize_of_nat(v___x_2578_);
v___x_2583_ = ((size_t)0ULL);
v___x_2584_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2579_, v___f_2581_, v_as_2576_, v___x_2582_, v___x_2583_, v___x_2577_);
return v___x_2584_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP(lean_object* v_00_u03b1_2585_, lean_object* v_p_2586_, lean_object* v_as_2587_){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; 
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = lean_array_get_size(v_as_2587_);
v___x_2590_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2591_ = lean_nat_dec_lt(v___x_2588_, v___x_2589_);
if (v___x_2591_ == 0)
{
lean_dec_ref(v_as_2587_);
lean_dec_ref(v_p_2586_);
return v___x_2588_;
}
else
{
lean_object* v___f_2592_; size_t v___x_2593_; size_t v___x_2594_; lean_object* v___x_2595_; 
v___f_2592_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2592_, 0, v_p_2586_);
v___x_2593_ = lean_usize_of_nat(v___x_2589_);
v___x_2594_ = ((size_t)0ULL);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2590_, v___f_2592_, v_as_2587_, v___x_2593_, v___x_2594_, v___x_2588_);
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0(lean_object* v_inst_2596_, lean_object* v_a_2597_, lean_object* v_x1_2598_, lean_object* v_x2_2599_){
_start:
{
lean_object* v___x_2600_; uint8_t v___x_2601_; 
v___x_2600_ = lean_apply_2(v_inst_2596_, v_x1_2598_, v_a_2597_);
v___x_2601_ = lean_unbox(v___x_2600_);
if (v___x_2601_ == 0)
{
lean_inc(v_x2_2599_);
return v_x2_2599_;
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = lean_unsigned_to_nat(1u);
v___x_2603_ = lean_nat_add(v_x2_2599_, v___x_2602_);
return v___x_2603_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0___boxed(lean_object* v_inst_2604_, lean_object* v_a_2605_, lean_object* v_x1_2606_, lean_object* v_x2_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Array_count___redArg___lam__0(v_inst_2604_, v_a_2605_, v_x1_2606_, v_x2_2607_);
lean_dec(v_x2_2607_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg(lean_object* v_inst_2609_, lean_object* v_a_2610_, lean_object* v_as_2611_){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2612_ = lean_unsigned_to_nat(0u);
v___x_2613_ = lean_array_get_size(v_as_2611_);
v___x_2614_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2615_ = lean_nat_dec_lt(v___x_2612_, v___x_2613_);
if (v___x_2615_ == 0)
{
lean_dec_ref(v_as_2611_);
lean_dec(v_a_2610_);
lean_dec_ref(v_inst_2609_);
return v___x_2612_;
}
else
{
lean_object* v___f_2616_; size_t v___x_2617_; size_t v___x_2618_; lean_object* v___x_2619_; 
v___f_2616_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2616_, 0, v_inst_2609_);
lean_closure_set(v___f_2616_, 1, v_a_2610_);
v___x_2617_ = lean_usize_of_nat(v___x_2613_);
v___x_2618_ = ((size_t)0ULL);
v___x_2619_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2614_, v___f_2616_, v_as_2611_, v___x_2617_, v___x_2618_, v___x_2612_);
return v___x_2619_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count(lean_object* v_00_u03b1_2620_, lean_object* v_inst_2621_, lean_object* v_a_2622_, lean_object* v_as_2623_){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2624_ = lean_unsigned_to_nat(0u);
v___x_2625_ = lean_array_get_size(v_as_2623_);
v___x_2626_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2627_ = lean_nat_dec_lt(v___x_2624_, v___x_2625_);
if (v___x_2627_ == 0)
{
lean_dec_ref(v_as_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_inst_2621_);
return v___x_2624_;
}
else
{
lean_object* v___f_2628_; size_t v___x_2629_; size_t v___x_2630_; lean_object* v___x_2631_; 
v___f_2628_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2628_, 0, v_inst_2621_);
lean_closure_set(v___f_2628_, 1, v_a_2622_);
v___x_2629_ = lean_usize_of_nat(v___x_2625_);
v___x_2630_ = ((size_t)0ULL);
v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2626_, v___f_2628_, v_as_2623_, v___x_2629_, v___x_2630_, v___x_2624_);
return v___x_2631_;
}
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg___lam__0(lean_object* v_f_2632_, lean_object* v_x_2633_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = lean_apply_1(v_f_2632_, v_x_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg(lean_object* v_f_2635_, lean_object* v_as_2636_){
_start:
{
lean_object* v___f_2637_; lean_object* v___x_2638_; size_t v_sz_2639_; size_t v___x_2640_; lean_object* v___x_2641_; 
v___f_2637_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2637_, 0, v_f_2635_);
v___x_2638_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2639_ = lean_array_size(v_as_2636_);
v___x_2640_ = ((size_t)0ULL);
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2638_, v___f_2637_, v_sz_2639_, v___x_2640_, v_as_2636_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Array_map(lean_object* v_00_u03b1_2642_, lean_object* v_00_u03b2_2643_, lean_object* v_f_2644_, lean_object* v_as_2645_){
_start:
{
lean_object* v___f_2646_; lean_object* v___x_2647_; size_t v_sz_2648_; size_t v___x_2649_; lean_object* v___x_2650_; 
v___f_2646_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2646_, 0, v_f_2644_);
v___x_2647_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2648_ = lean_array_size(v_as_2645_);
v___x_2649_ = ((size_t)0ULL);
v___x_2650_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2647_, v___f_2646_, v_sz_2648_, v___x_2649_, v_as_2645_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0(lean_object* v___y_2651_, lean_object* v_x_2652_){
_start:
{
lean_inc(v___y_2651_);
return v___y_2651_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0___boxed(lean_object* v___y_2653_, lean_object* v_x_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Array_instFunctor___lam__0(v___y_2653_, v_x_2654_);
lean_dec(v_x_2654_);
lean_dec(v___y_2653_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__1(lean_object* v_00_u03b1_2656_, lean_object* v_00_u03b2_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___f_2660_; lean_object* v___x_2661_; size_t v_sz_2662_; size_t v___x_2663_; lean_object* v___x_2664_; 
v___f_2660_ = lean_alloc_closure((void*)(l_Array_instFunctor___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2660_, 0, v___y_2658_);
v___x_2661_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2662_ = lean_array_size(v___y_2659_);
v___x_2663_ = ((size_t)0ULL);
v___x_2664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2661_, v___f_2660_, v_sz_2662_, v___x_2663_, v___y_2659_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg___lam__0(lean_object* v_f_2671_, lean_object* v_x1_2672_, lean_object* v_x2_2673_, lean_object* v_x3_2674_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = lean_apply_3(v_f_2671_, v_x1_2672_, v_x2_2673_, lean_box(0));
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg(lean_object* v_as_2676_, lean_object* v_f_2677_){
_start:
{
lean_object* v___f_2678_; lean_object* v___x_2679_; size_t v_sz_2680_; size_t v___x_2681_; lean_object* v___x_2682_; 
v___f_2678_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2678_, 0, v_f_2677_);
v___x_2679_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2680_ = lean_array_size(v_as_2676_);
v___x_2681_ = ((size_t)0ULL);
v___x_2682_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2679_, v___f_2678_, v_sz_2680_, v___x_2681_, v_as_2676_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx(lean_object* v_00_u03b1_2683_, lean_object* v_00_u03b2_2684_, lean_object* v_as_2685_, lean_object* v_f_2686_){
_start:
{
lean_object* v___f_2687_; lean_object* v___x_2688_; size_t v_sz_2689_; size_t v___x_2690_; lean_object* v___x_2691_; 
v___f_2687_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2687_, 0, v_f_2686_);
v___x_2688_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2689_ = lean_array_size(v_as_2685_);
v___x_2690_ = ((size_t)0ULL);
v___x_2691_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2688_, v___f_2687_, v_sz_2689_, v___x_2690_, v_as_2685_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx___redArg(lean_object* v_f_2692_, lean_object* v_as_2693_){
_start:
{
lean_object* v___f_2694_; lean_object* v___x_2695_; size_t v_sz_2696_; size_t v___x_2697_; lean_object* v___x_2698_; 
v___f_2694_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2694_, 0, v_f_2692_);
v___x_2695_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2696_ = lean_array_size(v_as_2693_);
v___x_2697_ = ((size_t)0ULL);
v___x_2698_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2695_, v___f_2694_, v_sz_2696_, v___x_2697_, v_as_2693_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx(lean_object* v_00_u03b1_2699_, lean_object* v_00_u03b2_2700_, lean_object* v_f_2701_, lean_object* v_as_2702_){
_start:
{
lean_object* v___f_2703_; lean_object* v___x_2704_; size_t v_sz_2705_; size_t v___x_2706_; lean_object* v___x_2707_; 
v___f_2703_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2703_, 0, v_f_2701_);
v___x_2704_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2705_ = lean_array_size(v_as_2702_);
v___x_2706_ = ((size_t)0ULL);
v___x_2707_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2704_, v___f_2703_, v_sz_2705_, v___x_2706_, v_as_2702_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(lean_object* v_start_2708_, size_t v_sz_2709_, size_t v_i_2710_, lean_object* v_bs_2711_){
_start:
{
uint8_t v___x_2712_; 
v___x_2712_ = lean_usize_dec_lt(v_i_2710_, v_sz_2709_);
if (v___x_2712_ == 0)
{
return v_bs_2711_;
}
else
{
lean_object* v_v_2713_; lean_object* v___x_2714_; lean_object* v_bs_x27_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; size_t v___x_2719_; size_t v___x_2720_; lean_object* v___x_2721_; 
v_v_2713_ = lean_array_uget(v_bs_2711_, v_i_2710_);
v___x_2714_ = lean_unsigned_to_nat(0u);
v_bs_x27_2715_ = lean_array_uset(v_bs_2711_, v_i_2710_, v___x_2714_);
v___x_2716_ = lean_usize_to_nat(v_i_2710_);
v___x_2717_ = lean_nat_add(v_start_2708_, v___x_2716_);
lean_dec(v___x_2716_);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v_v_2713_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___x_2719_ = ((size_t)1ULL);
v___x_2720_ = lean_usize_add(v_i_2710_, v___x_2719_);
v___x_2721_ = lean_array_uset(v_bs_x27_2715_, v_i_2710_, v___x_2718_);
v_i_2710_ = v___x_2720_;
v_bs_2711_ = v___x_2721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg___boxed(lean_object* v_start_2723_, lean_object* v_sz_2724_, lean_object* v_i_2725_, lean_object* v_bs_2726_){
_start:
{
size_t v_sz_boxed_2727_; size_t v_i_boxed_2728_; lean_object* v_res_2729_; 
v_sz_boxed_2727_ = lean_unbox_usize(v_sz_2724_);
lean_dec(v_sz_2724_);
v_i_boxed_2728_ = lean_unbox_usize(v_i_2725_);
lean_dec(v_i_2725_);
v_res_2729_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2723_, v_sz_boxed_2727_, v_i_boxed_2728_, v_bs_2726_);
lean_dec(v_start_2723_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg(lean_object* v_xs_2730_, lean_object* v_start_2731_){
_start:
{
size_t v_sz_2732_; size_t v___x_2733_; lean_object* v___x_2734_; 
v_sz_2732_ = lean_array_size(v_xs_2730_);
v___x_2733_ = ((size_t)0ULL);
v___x_2734_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2731_, v_sz_2732_, v___x_2733_, v_xs_2730_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg___boxed(lean_object* v_xs_2735_, lean_object* v_start_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Array_zipIdx___redArg(v_xs_2735_, v_start_2736_);
lean_dec(v_start_2736_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx(lean_object* v_00_u03b1_2738_, lean_object* v_xs_2739_, lean_object* v_start_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Array_zipIdx___redArg(v_xs_2739_, v_start_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___boxed(lean_object* v_00_u03b1_2742_, lean_object* v_xs_2743_, lean_object* v_start_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Array_zipIdx(v_00_u03b1_2742_, v_xs_2743_, v_start_2744_);
lean_dec(v_start_2744_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(lean_object* v_00_u03b1_2746_, lean_object* v_start_2747_, lean_object* v_as_2748_, size_t v_sz_2749_, size_t v_i_2750_, lean_object* v_bs_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2747_, v_sz_2749_, v_i_2750_, v_bs_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___boxed(lean_object* v_00_u03b1_2753_, lean_object* v_start_2754_, lean_object* v_as_2755_, lean_object* v_sz_2756_, lean_object* v_i_2757_, lean_object* v_bs_2758_){
_start:
{
size_t v_sz_boxed_2759_; size_t v_i_boxed_2760_; lean_object* v_res_2761_; 
v_sz_boxed_2759_ = lean_unbox_usize(v_sz_2756_);
lean_dec(v_sz_2756_);
v_i_boxed_2760_ = lean_unbox_usize(v_i_2757_);
lean_dec(v_i_2757_);
v_res_2761_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(v_00_u03b1_2753_, v_start_2754_, v_as_2755_, v_sz_boxed_2759_, v_i_boxed_2760_, v_bs_2758_);
lean_dec_ref(v_as_2755_);
lean_dec(v_start_2754_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0(lean_object* v_p_2762_, lean_object* v___x_2763_, lean_object* v___x_2764_, lean_object* v_a_2765_, lean_object* v_x_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v___x_2768_; uint8_t v___x_2769_; 
lean_inc(v_a_2765_);
v___x_2768_ = lean_apply_1(v_p_2762_, v_a_2765_);
v___x_2769_ = lean_unbox(v___x_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; 
lean_dec(v_a_2765_);
v___x_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2763_);
return v___x_2770_;
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
lean_dec_ref(v___x_2763_);
v___x_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2771_, 0, v_a_2765_);
v___x_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
lean_ctor_set(v___x_2773_, 1, v___x_2764_);
v___x_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
return v___x_2774_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0___boxed(lean_object* v_p_2775_, lean_object* v___x_2776_, lean_object* v___x_2777_, lean_object* v_a_2778_, lean_object* v_x_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Array_find_x3f___redArg___lam__0(v_p_2775_, v___x_2776_, v___x_2777_, v_a_2778_, v_x_2779_, v___y_2780_);
lean_dec_ref(v___y_2780_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg(lean_object* v_p_2782_, lean_object* v_as_2783_){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___f_2788_; size_t v_sz_2789_; size_t v___x_2790_; lean_object* v___x_2791_; lean_object* v_fst_2792_; 
v___x_2784_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2785_ = lean_box(0);
v___x_2786_ = lean_box(0);
v___x_2787_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2788_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2788_, 0, v_p_2782_);
lean_closure_set(v___f_2788_, 1, v___x_2787_);
lean_closure_set(v___f_2788_, 2, v___x_2786_);
v_sz_2789_ = lean_array_size(v_as_2783_);
v___x_2790_ = ((size_t)0ULL);
v___x_2791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2784_, v_as_2783_, v___f_2788_, v_sz_2789_, v___x_2790_, v___x_2787_);
v_fst_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_fst_2792_);
lean_dec(v___x_2791_);
if (lean_obj_tag(v_fst_2792_) == 0)
{
return v___x_2785_;
}
else
{
lean_object* v_val_2793_; 
v_val_2793_ = lean_ctor_get(v_fst_2792_, 0);
lean_inc(v_val_2793_);
lean_dec_ref_known(v_fst_2792_, 1);
return v_val_2793_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f(lean_object* v_00_u03b1_2794_, lean_object* v_p_2795_, lean_object* v_as_2796_){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___f_2801_; size_t v_sz_2802_; size_t v___x_2803_; lean_object* v___x_2804_; lean_object* v_fst_2805_; 
v___x_2797_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2798_ = lean_box(0);
v___x_2799_ = lean_box(0);
v___x_2800_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2801_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2801_, 0, v_p_2795_);
lean_closure_set(v___f_2801_, 1, v___x_2800_);
lean_closure_set(v___f_2801_, 2, v___x_2799_);
v_sz_2802_ = lean_array_size(v_as_2796_);
v___x_2803_ = ((size_t)0ULL);
v___x_2804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2797_, v_as_2796_, v___f_2801_, v_sz_2802_, v___x_2803_, v___x_2800_);
v_fst_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_fst_2805_);
lean_dec(v___x_2804_);
if (lean_obj_tag(v_fst_2805_) == 0)
{
return v___x_2798_;
}
else
{
lean_object* v_val_2806_; 
v_val_2806_ = lean_ctor_get(v_fst_2805_, 0);
lean_inc(v_val_2806_);
lean_dec_ref_known(v_fst_2805_, 1);
return v_val_2806_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0(lean_object* v_f_2807_, lean_object* v___x_2808_, lean_object* v___x_2809_, lean_object* v_a_2810_, lean_object* v_x_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_apply_1(v_f_2807_, v_a_2810_);
if (lean_obj_tag(v___x_2813_) == 1)
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
lean_dec_ref(v___x_2809_);
v___x_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v___x_2808_);
v___x_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
return v___x_2816_;
}
else
{
lean_object* v___x_2817_; 
lean_dec(v___x_2813_);
v___x_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2809_);
return v___x_2817_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2818_, lean_object* v___x_2819_, lean_object* v___x_2820_, lean_object* v_a_2821_, lean_object* v_x_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Array_findSome_x3f___redArg___lam__0(v_f_2818_, v___x_2819_, v___x_2820_, v_a_2821_, v_x_2822_, v___y_2823_);
lean_dec_ref(v___y_2823_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg(lean_object* v_f_2825_, lean_object* v_as_2826_){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___f_2831_; size_t v_sz_2832_; size_t v___x_2833_; lean_object* v___x_2834_; lean_object* v_fst_2835_; 
v___x_2827_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2828_ = lean_box(0);
v___x_2829_ = lean_box(0);
v___x_2830_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2831_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2831_, 0, v_f_2825_);
lean_closure_set(v___f_2831_, 1, v___x_2829_);
lean_closure_set(v___f_2831_, 2, v___x_2830_);
v_sz_2832_ = lean_array_size(v_as_2826_);
v___x_2833_ = ((size_t)0ULL);
v___x_2834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2827_, v_as_2826_, v___f_2831_, v_sz_2832_, v___x_2833_, v___x_2830_);
v_fst_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_fst_2835_);
lean_dec(v___x_2834_);
if (lean_obj_tag(v_fst_2835_) == 0)
{
return v___x_2828_;
}
else
{
lean_object* v_val_2836_; 
v_val_2836_ = lean_ctor_get(v_fst_2835_, 0);
lean_inc(v_val_2836_);
lean_dec_ref_known(v_fst_2835_, 1);
return v_val_2836_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f(lean_object* v_00_u03b1_2837_, lean_object* v_00_u03b2_2838_, lean_object* v_f_2839_, lean_object* v_as_2840_){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___f_2845_; size_t v_sz_2846_; size_t v___x_2847_; lean_object* v___x_2848_; lean_object* v_fst_2849_; 
v___x_2841_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2842_ = lean_box(0);
v___x_2843_ = lean_box(0);
v___x_2844_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2845_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2845_, 0, v_f_2839_);
lean_closure_set(v___f_2845_, 1, v___x_2843_);
lean_closure_set(v___f_2845_, 2, v___x_2844_);
v_sz_2846_ = lean_array_size(v_as_2840_);
v___x_2847_ = ((size_t)0ULL);
v___x_2848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2841_, v_as_2840_, v___f_2845_, v_sz_2846_, v___x_2847_, v___x_2844_);
v_fst_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_fst_2849_);
lean_dec(v___x_2848_);
if (lean_obj_tag(v_fst_2849_) == 0)
{
return v___x_2842_;
}
else
{
lean_object* v_val_2850_; 
v_val_2850_ = lean_ctor_get(v_fst_2849_, 0);
lean_inc(v_val_2850_);
lean_dec_ref_known(v_fst_2849_, 1);
return v_val_2850_;
}
}
}
static lean_object* _init_l_Array_findSome_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2853_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__1));
v___x_2854_ = lean_unsigned_to_nat(14u);
v___x_2855_ = lean_unsigned_to_nat(1254u);
v___x_2856_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__0));
v___x_2857_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_2858_ = l_mkPanicMessageWithDecl(v___x_2857_, v___x_2856_, v___x_2855_, v___x_2854_, v___x_2853_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg(lean_object* v_inst_2859_, lean_object* v_f_2860_, lean_object* v_xs_2861_){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___f_2868_; size_t v_sz_2869_; size_t v___x_2870_; lean_object* v___x_2871_; lean_object* v_fst_2872_; 
v___x_2865_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2866_ = lean_box(0);
v___x_2867_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2868_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2868_, 0, v_f_2860_);
lean_closure_set(v___f_2868_, 1, v___x_2866_);
lean_closure_set(v___f_2868_, 2, v___x_2867_);
v_sz_2869_ = lean_array_size(v_xs_2861_);
v___x_2870_ = ((size_t)0ULL);
v___x_2871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2865_, v_xs_2861_, v___f_2868_, v_sz_2869_, v___x_2870_, v___x_2867_);
v_fst_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_fst_2872_);
lean_dec(v___x_2871_);
if (lean_obj_tag(v_fst_2872_) == 0)
{
goto v___jp_2862_;
}
else
{
lean_object* v_val_2873_; 
v_val_2873_ = lean_ctor_get(v_fst_2872_, 0);
lean_inc(v_val_2873_);
lean_dec_ref_known(v_fst_2872_, 1);
if (lean_obj_tag(v_val_2873_) == 0)
{
goto v___jp_2862_;
}
else
{
lean_object* v_val_2874_; 
v_val_2874_ = lean_ctor_get(v_val_2873_, 0);
lean_inc(v_val_2874_);
lean_dec_ref_known(v_val_2873_, 1);
return v_val_2874_;
}
}
v___jp_2862_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2864_ = l_panic___redArg(v_inst_2859_, v___x_2863_);
return v___x_2864_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg___boxed(lean_object* v_inst_2875_, lean_object* v_f_2876_, lean_object* v_xs_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Array_findSome_x21___redArg(v_inst_2875_, v_f_2876_, v_xs_2877_);
lean_dec(v_inst_2875_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21(lean_object* v_00_u03b1_2879_, lean_object* v_00_u03b2_2880_, lean_object* v_inst_2881_, lean_object* v_f_2882_, lean_object* v_xs_2883_){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___f_2890_; size_t v_sz_2891_; size_t v___x_2892_; lean_object* v___x_2893_; lean_object* v_fst_2894_; 
v___x_2887_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2888_ = lean_box(0);
v___x_2889_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2890_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2890_, 0, v_f_2882_);
lean_closure_set(v___f_2890_, 1, v___x_2888_);
lean_closure_set(v___f_2890_, 2, v___x_2889_);
v_sz_2891_ = lean_array_size(v_xs_2883_);
v___x_2892_ = ((size_t)0ULL);
v___x_2893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2887_, v_xs_2883_, v___f_2890_, v_sz_2891_, v___x_2892_, v___x_2889_);
v_fst_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_fst_2894_);
lean_dec(v___x_2893_);
if (lean_obj_tag(v_fst_2894_) == 0)
{
goto v___jp_2884_;
}
else
{
lean_object* v_val_2895_; 
v_val_2895_ = lean_ctor_get(v_fst_2894_, 0);
lean_inc(v_val_2895_);
lean_dec_ref_known(v_fst_2894_, 1);
if (lean_obj_tag(v_val_2895_) == 0)
{
goto v___jp_2884_;
}
else
{
lean_object* v_val_2896_; 
v_val_2896_ = lean_ctor_get(v_val_2895_, 0);
lean_inc(v_val_2896_);
lean_dec_ref_known(v_val_2895_, 1);
return v_val_2896_;
}
}
v___jp_2884_:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2886_ = l_panic___redArg(v_inst_2881_, v___x_2885_);
return v___x_2886_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___boxed(lean_object* v_00_u03b1_2897_, lean_object* v_00_u03b2_2898_, lean_object* v_inst_2899_, lean_object* v_f_2900_, lean_object* v_xs_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Array_findSome_x21(v_00_u03b1_2897_, v_00_u03b2_2898_, v_inst_2899_, v_f_2900_, v_xs_2901_);
lean_dec(v_inst_2899_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2903_, lean_object* v_x_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = lean_apply_1(v_f_2903_, v_x_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg(lean_object* v_f_2906_, lean_object* v_as_2907_){
_start:
{
lean_object* v___f_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___f_2908_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2908_, 0, v_f_2906_);
v___x_2909_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2910_ = lean_array_get_size(v_as_2907_);
v___x_2911_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2909_, v___f_2908_, v_as_2907_, v___x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f(lean_object* v_00_u03b1_2912_, lean_object* v_00_u03b2_2913_, lean_object* v_f_2914_, lean_object* v_as_2915_){
_start:
{
lean_object* v___f_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___f_2916_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2916_, 0, v_f_2914_);
v___x_2917_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2918_ = lean_array_get_size(v_as_2915_);
v___x_2919_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2917_, v___f_2916_, v_as_2915_, v___x_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg___lam__0(lean_object* v_p_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v___x_2922_; uint8_t v___x_2923_; 
lean_inc(v_a_2921_);
v___x_2922_ = lean_apply_1(v_p_2920_, v_a_2921_);
v___x_2923_ = lean_unbox(v___x_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; 
lean_dec(v_a_2921_);
v___x_2924_ = lean_box(0);
return v___x_2924_;
}
else
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2925_, 0, v_a_2921_);
return v___x_2925_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg(lean_object* v_p_2926_, lean_object* v_as_2927_){
_start:
{
lean_object* v___f_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___f_2928_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2928_, 0, v_p_2926_);
v___x_2929_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2930_ = lean_array_get_size(v_as_2927_);
v___x_2931_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2929_, v___f_2928_, v_as_2927_, v___x_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f(lean_object* v_00_u03b1_2932_, lean_object* v_p_2933_, lean_object* v_as_2934_){
_start:
{
lean_object* v___f_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___f_2935_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2935_, 0, v_p_2933_);
v___x_2936_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2937_ = lean_array_get_size(v_as_2934_);
v___x_2938_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2936_, v___f_2935_, v_as_2934_, v___x_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object* v_p_2939_, lean_object* v_as_2940_, lean_object* v_j_2941_){
_start:
{
lean_object* v___x_2942_; uint8_t v___x_2943_; 
v___x_2942_ = lean_array_get_size(v_as_2940_);
v___x_2943_ = lean_nat_dec_lt(v_j_2941_, v___x_2942_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; 
lean_dec(v_j_2941_);
lean_dec_ref(v_p_2939_);
v___x_2944_ = lean_box(0);
return v___x_2944_;
}
else
{
lean_object* v___x_2945_; lean_object* v___x_2946_; uint8_t v___x_2947_; 
v___x_2945_ = lean_array_fget_borrowed(v_as_2940_, v_j_2941_);
lean_inc_ref(v_p_2939_);
lean_inc(v___x_2945_);
v___x_2946_ = lean_apply_1(v_p_2939_, v___x_2945_);
v___x_2947_ = lean_unbox(v___x_2946_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = lean_unsigned_to_nat(1u);
v___x_2949_ = lean_nat_add(v_j_2941_, v___x_2948_);
lean_dec(v_j_2941_);
v_j_2941_ = v___x_2949_;
goto _start;
}
else
{
lean_object* v___x_2951_; 
lean_dec_ref(v_p_2939_);
v___x_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2951_, 0, v_j_2941_);
return v___x_2951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg___boxed(lean_object* v_p_2952_, lean_object* v_as_2953_, lean_object* v_j_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Array_findIdx_x3f_loop___redArg(v_p_2952_, v_as_2953_, v_j_2954_);
lean_dec_ref(v_as_2953_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop(lean_object* v_00_u03b1_2956_, lean_object* v_p_2957_, lean_object* v_as_2958_, lean_object* v_j_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Array_findIdx_x3f_loop___redArg(v_p_2957_, v_as_2958_, v_j_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___boxed(lean_object* v_00_u03b1_2961_, lean_object* v_p_2962_, lean_object* v_as_2963_, lean_object* v_j_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Array_findIdx_x3f_loop(v_00_u03b1_2961_, v_p_2962_, v_as_2963_, v_j_2964_);
lean_dec_ref(v_as_2963_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg(lean_object* v_p_2966_, lean_object* v_as_2967_){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = lean_unsigned_to_nat(0u);
v___x_2969_ = l_Array_findIdx_x3f_loop___redArg(v_p_2966_, v_as_2967_, v___x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg___boxed(lean_object* v_p_2970_, lean_object* v_as_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Array_findIdx_x3f___redArg(v_p_2970_, v_as_2971_);
lean_dec_ref(v_as_2971_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f(lean_object* v_00_u03b1_2973_, lean_object* v_p_2974_, lean_object* v_as_2975_){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = lean_unsigned_to_nat(0u);
v___x_2977_ = l_Array_findIdx_x3f_loop___redArg(v_p_2974_, v_as_2975_, v___x_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___boxed(lean_object* v_00_u03b1_2978_, lean_object* v_p_2979_, lean_object* v_as_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Array_findIdx_x3f(v_00_u03b1_2978_, v_p_2979_, v_as_2980_);
lean_dec_ref(v_as_2980_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(lean_object* v_p_2982_, lean_object* v_as_2983_, lean_object* v_j_2984_){
_start:
{
lean_object* v___x_2985_; uint8_t v___x_2986_; 
v___x_2985_ = lean_array_get_size(v_as_2983_);
v___x_2986_ = lean_nat_dec_lt(v_j_2984_, v___x_2985_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; 
lean_dec(v_j_2984_);
lean_dec_ref(v_p_2982_);
v___x_2987_ = lean_box(0);
return v___x_2987_;
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2988_ = lean_array_fget_borrowed(v_as_2983_, v_j_2984_);
lean_inc_ref(v_p_2982_);
lean_inc(v___x_2988_);
v___x_2989_ = lean_apply_1(v_p_2982_, v___x_2988_);
v___x_2990_ = lean_unbox(v___x_2989_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = lean_unsigned_to_nat(1u);
v___x_2992_ = lean_nat_add(v_j_2984_, v___x_2991_);
lean_dec(v_j_2984_);
v_j_2984_ = v___x_2992_;
goto _start;
}
else
{
lean_object* v___x_2994_; 
lean_dec_ref(v_p_2982_);
v___x_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2994_, 0, v_j_2984_);
return v___x_2994_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg___boxed(lean_object* v_p_2995_, lean_object* v_as_2996_, lean_object* v_j_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2995_, v_as_2996_, v_j_2997_);
lean_dec_ref(v_as_2996_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object* v_00_u03b1_2999_, lean_object* v_p_3000_, lean_object* v_as_3001_, lean_object* v_j_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3000_, v_as_3001_, v_j_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___boxed(lean_object* v_00_u03b1_3004_, lean_object* v_p_3005_, lean_object* v_as_3006_, lean_object* v_j_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(v_00_u03b1_3004_, v_p_3005_, v_as_3006_, v_j_3007_);
lean_dec_ref(v_as_3006_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg(lean_object* v_p_3009_, lean_object* v_as_3010_){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = lean_unsigned_to_nat(0u);
v___x_3012_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3009_, v_as_3010_, v___x_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg___boxed(lean_object* v_p_3013_, lean_object* v_as_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l_Array_findFinIdx_x3f___redArg(v_p_3013_, v_as_3014_);
lean_dec_ref(v_as_3014_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f(lean_object* v_00_u03b1_3016_, lean_object* v_p_3017_, lean_object* v_as_3018_){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = lean_unsigned_to_nat(0u);
v___x_3020_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3017_, v_as_3018_, v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_3021_, lean_object* v_p_3022_, lean_object* v_as_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Array_findFinIdx_x3f(v_00_u03b1_3021_, v_p_3022_, v_as_3023_);
lean_dec_ref(v_as_3023_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg(lean_object* v_p_3025_, lean_object* v_as_3026_){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = lean_unsigned_to_nat(0u);
v___x_3028_ = l_Array_findIdx_x3f_loop___redArg(v_p_3025_, v_as_3026_, v___x_3027_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_array_get_size(v_as_3026_);
return v___x_3029_;
}
else
{
lean_object* v_val_3030_; 
v_val_3030_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_val_3030_);
lean_dec_ref_known(v___x_3028_, 1);
return v_val_3030_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg___boxed(lean_object* v_p_3031_, lean_object* v_as_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Array_findIdx___redArg(v_p_3031_, v_as_3032_);
lean_dec_ref(v_as_3032_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx(lean_object* v_00_u03b1_3034_, lean_object* v_p_3035_, lean_object* v_as_3036_){
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
LEAN_EXPORT lean_object* l_Array_findIdx___boxed(lean_object* v_00_u03b1_3041_, lean_object* v_p_3042_, lean_object* v_as_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Array_findIdx(v_00_u03b1_3041_, v_p_3042_, v_as_3043_);
lean_dec_ref(v_as_3043_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg(lean_object* v_inst_3045_, lean_object* v_xs_3046_, lean_object* v_v_3047_, lean_object* v_i_3048_){
_start:
{
lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3049_ = lean_array_get_size(v_xs_3046_);
v___x_3050_ = lean_nat_dec_lt(v_i_3048_, v___x_3049_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; 
lean_dec(v_i_3048_);
lean_dec(v_v_3047_);
lean_dec_ref(v_inst_3045_);
v___x_3051_ = lean_box(0);
return v___x_3051_;
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; 
v___x_3052_ = lean_array_fget_borrowed(v_xs_3046_, v_i_3048_);
lean_inc_ref(v_inst_3045_);
lean_inc(v_v_3047_);
lean_inc(v___x_3052_);
v___x_3053_ = lean_apply_2(v_inst_3045_, v___x_3052_, v_v_3047_);
v___x_3054_ = lean_unbox(v___x_3053_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = lean_unsigned_to_nat(1u);
v___x_3056_ = lean_nat_add(v_i_3048_, v___x_3055_);
lean_dec(v_i_3048_);
v_i_3048_ = v___x_3056_;
goto _start;
}
else
{
lean_object* v___x_3058_; 
lean_dec(v_v_3047_);
lean_dec_ref(v_inst_3045_);
v___x_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3058_, 0, v_i_3048_);
return v___x_3058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg___boxed(lean_object* v_inst_3059_, lean_object* v_xs_3060_, lean_object* v_v_3061_, lean_object* v_i_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_Array_idxOfAux___redArg(v_inst_3059_, v_xs_3060_, v_v_3061_, v_i_3062_);
lean_dec_ref(v_xs_3060_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux(lean_object* v_00_u03b1_3064_, lean_object* v_inst_3065_, lean_object* v_xs_3066_, lean_object* v_v_3067_, lean_object* v_i_3068_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Array_idxOfAux___redArg(v_inst_3065_, v_xs_3066_, v_v_3067_, v_i_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___boxed(lean_object* v_00_u03b1_3070_, lean_object* v_inst_3071_, lean_object* v_xs_3072_, lean_object* v_v_3073_, lean_object* v_i_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Array_idxOfAux(v_00_u03b1_3070_, v_inst_3071_, v_xs_3072_, v_v_3073_, v_i_3074_);
lean_dec_ref(v_xs_3072_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg(lean_object* v_inst_3076_, lean_object* v_xs_3077_, lean_object* v_v_3078_){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_unsigned_to_nat(0u);
v___x_3080_ = l_Array_idxOfAux___redArg(v_inst_3076_, v_xs_3077_, v_v_3078_, v___x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_3081_, lean_object* v_xs_3082_, lean_object* v_v_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Array_finIdxOf_x3f___redArg(v_inst_3081_, v_xs_3082_, v_v_3083_);
lean_dec_ref(v_xs_3082_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f(lean_object* v_00_u03b1_3085_, lean_object* v_inst_3086_, lean_object* v_xs_3087_, lean_object* v_v_3088_){
_start:
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Array_finIdxOf_x3f___redArg(v_inst_3086_, v_xs_3087_, v_v_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_3090_, lean_object* v_inst_3091_, lean_object* v_xs_3092_, lean_object* v_v_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Array_finIdxOf_x3f(v_00_u03b1_3090_, v_inst_3091_, v_xs_3092_, v_v_3093_);
lean_dec_ref(v_xs_3092_);
return v_res_3094_;
}
}
LEAN_EXPORT uint8_t l_Array_idxOf___redArg___lam__0(lean_object* v_inst_3095_, lean_object* v_a_3096_, lean_object* v_x_3097_){
_start:
{
lean_object* v___x_3098_; uint8_t v___x_3099_; 
v___x_3098_ = lean_apply_2(v_inst_3095_, v_x_3097_, v_a_3096_);
v___x_3099_ = lean_unbox(v___x_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___lam__0___boxed(lean_object* v_inst_3100_, lean_object* v_a_3101_, lean_object* v_x_3102_){
_start:
{
uint8_t v_res_3103_; lean_object* v_r_3104_; 
v_res_3103_ = l_Array_idxOf___redArg___lam__0(v_inst_3100_, v_a_3101_, v_x_3102_);
v_r_3104_ = lean_box(v_res_3103_);
return v_r_3104_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg(lean_object* v_inst_3105_, lean_object* v_a_3106_, lean_object* v_as_3107_){
_start:
{
lean_object* v___f_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___f_3108_ = lean_alloc_closure((void*)(l_Array_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3108_, 0, v_inst_3105_);
lean_closure_set(v___f_3108_, 1, v_a_3106_);
v___x_3109_ = lean_unsigned_to_nat(0u);
v___x_3110_ = l_Array_findIdx_x3f_loop___redArg(v___f_3108_, v_as_3107_, v___x_3109_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v___x_3111_; 
v___x_3111_ = lean_array_get_size(v_as_3107_);
return v___x_3111_;
}
else
{
lean_object* v_val_3112_; 
v_val_3112_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_val_3112_);
lean_dec_ref_known(v___x_3110_, 1);
return v_val_3112_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___boxed(lean_object* v_inst_3113_, lean_object* v_a_3114_, lean_object* v_as_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Array_idxOf___redArg(v_inst_3113_, v_a_3114_, v_as_3115_);
lean_dec_ref(v_as_3115_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf(lean_object* v_00_u03b1_3117_, lean_object* v_inst_3118_, lean_object* v_a_3119_, lean_object* v_as_3120_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Array_idxOf___redArg(v_inst_3118_, v_a_3119_, v_as_3120_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___boxed(lean_object* v_00_u03b1_3122_, lean_object* v_inst_3123_, lean_object* v_a_3124_, lean_object* v_as_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Array_idxOf(v_00_u03b1_3122_, v_inst_3123_, v_a_3124_, v_as_3125_);
lean_dec_ref(v_as_3125_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg(lean_object* v_inst_3127_, lean_object* v_xs_3128_, lean_object* v_v_3129_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l_Array_finIdxOf_x3f___redArg(v_inst_3127_, v_xs_3128_, v_v_3129_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v___x_3131_; 
v___x_3131_ = lean_box(0);
return v___x_3131_;
}
else
{
lean_object* v_val_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
v_val_3132_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3130_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_val_3132_);
lean_dec(v___x_3130_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_val_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg___boxed(lean_object* v_inst_3140_, lean_object* v_xs_3141_, lean_object* v_v_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Array_idxOf_x3f___redArg(v_inst_3140_, v_xs_3141_, v_v_3142_);
lean_dec_ref(v_xs_3141_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f(lean_object* v_00_u03b1_3144_, lean_object* v_inst_3145_, lean_object* v_xs_3146_, lean_object* v_v_3147_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Array_idxOf_x3f___redArg(v_inst_3145_, v_xs_3146_, v_v_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___boxed(lean_object* v_00_u03b1_3149_, lean_object* v_inst_3150_, lean_object* v_xs_3151_, lean_object* v_v_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Array_idxOf_x3f(v_00_u03b1_3149_, v_inst_3150_, v_xs_3151_, v_v_3152_);
lean_dec_ref(v_xs_3151_);
return v_res_3153_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg___lam__0(lean_object* v_p_3154_, lean_object* v_x_3155_){
_start:
{
lean_object* v___x_3156_; uint8_t v___x_3157_; 
v___x_3156_ = lean_apply_1(v_p_3154_, v_x_3155_);
v___x_3157_ = lean_unbox(v___x_3156_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___lam__0___boxed(lean_object* v_p_3158_, lean_object* v_x_3159_){
_start:
{
uint8_t v_res_3160_; lean_object* v_r_3161_; 
v_res_3160_ = l_Array_any___redArg___lam__0(v_p_3158_, v_x_3159_);
v_r_3161_ = lean_box(v_res_3160_);
return v_r_3161_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg(lean_object* v_as_3162_, lean_object* v_p_3163_, lean_object* v_start_3164_, lean_object* v_stop_3165_){
_start:
{
lean_object* v___x_3166_; uint8_t v___x_3167_; 
v___x_3166_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3167_ = lean_nat_dec_lt(v_start_3164_, v_stop_3165_);
if (v___x_3167_ == 0)
{
lean_dec(v_stop_3165_);
lean_dec_ref(v_p_3163_);
lean_dec_ref(v_as_3162_);
return v___x_3167_;
}
else
{
lean_object* v___f_3168_; lean_object* v___y_3170_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___f_3168_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3168_, 0, v_p_3163_);
v___x_3176_ = lean_array_get_size(v_as_3162_);
v___x_3177_ = lean_nat_dec_le(v_stop_3165_, v___x_3176_);
if (v___x_3177_ == 0)
{
lean_dec(v_stop_3165_);
v___y_3170_ = v___x_3176_;
goto v___jp_3169_;
}
else
{
v___y_3170_ = v_stop_3165_;
goto v___jp_3169_;
}
v___jp_3169_:
{
uint8_t v___x_3171_; 
v___x_3171_ = lean_nat_dec_lt(v_start_3164_, v___y_3170_);
if (v___x_3171_ == 0)
{
lean_dec(v___y_3170_);
lean_dec_ref(v___f_3168_);
lean_dec_ref(v_as_3162_);
return v___x_3171_;
}
else
{
size_t v___x_3172_; size_t v___x_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; 
v___x_3172_ = lean_usize_of_nat(v_start_3164_);
v___x_3173_ = lean_usize_of_nat(v___y_3170_);
lean_dec(v___y_3170_);
v___x_3174_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3166_, v___f_3168_, v_as_3162_, v___x_3172_, v___x_3173_);
v___x_3175_ = lean_unbox(v___x_3174_);
lean_dec(v___x_3174_);
return v___x_3175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___boxed(lean_object* v_as_3178_, lean_object* v_p_3179_, lean_object* v_start_3180_, lean_object* v_stop_3181_){
_start:
{
uint8_t v_res_3182_; lean_object* v_r_3183_; 
v_res_3182_ = l_Array_any___redArg(v_as_3178_, v_p_3179_, v_start_3180_, v_stop_3181_);
lean_dec(v_start_3180_);
v_r_3183_ = lean_box(v_res_3182_);
return v_r_3183_;
}
}
LEAN_EXPORT uint8_t l_Array_any(lean_object* v_00_u03b1_3184_, lean_object* v_as_3185_, lean_object* v_p_3186_, lean_object* v_start_3187_, lean_object* v_stop_3188_){
_start:
{
lean_object* v___x_3189_; uint8_t v___x_3190_; 
v___x_3189_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3190_ = lean_nat_dec_lt(v_start_3187_, v_stop_3188_);
if (v___x_3190_ == 0)
{
lean_dec(v_stop_3188_);
lean_dec_ref(v_p_3186_);
lean_dec_ref(v_as_3185_);
return v___x_3190_;
}
else
{
lean_object* v___f_3191_; lean_object* v___y_3193_; lean_object* v___x_3199_; uint8_t v___x_3200_; 
v___f_3191_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3191_, 0, v_p_3186_);
v___x_3199_ = lean_array_get_size(v_as_3185_);
v___x_3200_ = lean_nat_dec_le(v_stop_3188_, v___x_3199_);
if (v___x_3200_ == 0)
{
lean_dec(v_stop_3188_);
v___y_3193_ = v___x_3199_;
goto v___jp_3192_;
}
else
{
v___y_3193_ = v_stop_3188_;
goto v___jp_3192_;
}
v___jp_3192_:
{
uint8_t v___x_3194_; 
v___x_3194_ = lean_nat_dec_lt(v_start_3187_, v___y_3193_);
if (v___x_3194_ == 0)
{
lean_dec(v___y_3193_);
lean_dec_ref(v___f_3191_);
lean_dec_ref(v_as_3185_);
return v___x_3194_;
}
else
{
size_t v___x_3195_; size_t v___x_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
v___x_3195_ = lean_usize_of_nat(v_start_3187_);
v___x_3196_ = lean_usize_of_nat(v___y_3193_);
lean_dec(v___y_3193_);
v___x_3197_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3189_, v___f_3191_, v_as_3185_, v___x_3195_, v___x_3196_);
v___x_3198_ = lean_unbox(v___x_3197_);
lean_dec(v___x_3197_);
return v___x_3198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___boxed(lean_object* v_00_u03b1_3201_, lean_object* v_as_3202_, lean_object* v_p_3203_, lean_object* v_start_3204_, lean_object* v_stop_3205_){
_start:
{
uint8_t v_res_3206_; lean_object* v_r_3207_; 
v_res_3206_ = l_Array_any(v_00_u03b1_3201_, v_as_3202_, v_p_3203_, v_start_3204_, v_stop_3205_);
lean_dec(v_start_3204_);
v_r_3207_ = lean_box(v_res_3206_);
return v_r_3207_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg___lam__0(lean_object* v_p_3208_, uint8_t v___x_3209_, lean_object* v_v_3210_){
_start:
{
lean_object* v___x_3211_; uint8_t v___x_3212_; 
v___x_3211_ = lean_apply_1(v_p_3208_, v_v_3210_);
v___x_3212_ = lean_unbox(v___x_3211_);
if (v___x_3212_ == 0)
{
return v___x_3209_;
}
else
{
uint8_t v___x_3213_; 
v___x_3213_ = 0;
return v___x_3213_;
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___lam__0___boxed(lean_object* v_p_3214_, lean_object* v___x_3215_, lean_object* v_v_3216_){
_start:
{
uint8_t v___x_334__boxed_3217_; uint8_t v_res_3218_; lean_object* v_r_3219_; 
v___x_334__boxed_3217_ = lean_unbox(v___x_3215_);
v_res_3218_ = l_Array_all___redArg___lam__0(v_p_3214_, v___x_334__boxed_3217_, v_v_3216_);
v_r_3219_ = lean_box(v_res_3218_);
return v_r_3219_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg(lean_object* v_as_3220_, lean_object* v_p_3221_, lean_object* v_start_3222_, lean_object* v_stop_3223_){
_start:
{
lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3224_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3225_ = lean_nat_dec_lt(v_start_3222_, v_stop_3223_);
if (v___x_3225_ == 0)
{
uint8_t v___x_3226_; 
lean_dec(v_stop_3223_);
lean_dec_ref(v_p_3221_);
lean_dec_ref(v_as_3220_);
v___x_3226_ = 1;
return v___x_3226_;
}
else
{
lean_object* v___x_3227_; lean_object* v___f_3228_; lean_object* v___y_3230_; lean_object* v___x_3237_; uint8_t v___x_3238_; 
v___x_3227_ = lean_box(v___x_3225_);
v___f_3228_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3228_, 0, v_p_3221_);
lean_closure_set(v___f_3228_, 1, v___x_3227_);
v___x_3237_ = lean_array_get_size(v_as_3220_);
v___x_3238_ = lean_nat_dec_le(v_stop_3223_, v___x_3237_);
if (v___x_3238_ == 0)
{
lean_dec(v_stop_3223_);
v___y_3230_ = v___x_3237_;
goto v___jp_3229_;
}
else
{
v___y_3230_ = v_stop_3223_;
goto v___jp_3229_;
}
v___jp_3229_:
{
uint8_t v___x_3231_; 
v___x_3231_ = lean_nat_dec_lt(v_start_3222_, v___y_3230_);
if (v___x_3231_ == 0)
{
lean_dec(v___y_3230_);
lean_dec_ref(v___f_3228_);
lean_dec_ref(v_as_3220_);
return v___x_3225_;
}
else
{
size_t v___x_3232_; size_t v___x_3233_; lean_object* v___x_3234_; uint8_t v___x_3235_; 
v___x_3232_ = lean_usize_of_nat(v_start_3222_);
v___x_3233_ = lean_usize_of_nat(v___y_3230_);
lean_dec(v___y_3230_);
v___x_3234_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3224_, v___f_3228_, v_as_3220_, v___x_3232_, v___x_3233_);
v___x_3235_ = lean_unbox(v___x_3234_);
lean_dec(v___x_3234_);
if (v___x_3235_ == 0)
{
return v___x_3231_;
}
else
{
uint8_t v___x_3236_; 
v___x_3236_ = 0;
return v___x_3236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___boxed(lean_object* v_as_3239_, lean_object* v_p_3240_, lean_object* v_start_3241_, lean_object* v_stop_3242_){
_start:
{
uint8_t v_res_3243_; lean_object* v_r_3244_; 
v_res_3243_ = l_Array_all___redArg(v_as_3239_, v_p_3240_, v_start_3241_, v_stop_3242_);
lean_dec(v_start_3241_);
v_r_3244_ = lean_box(v_res_3243_);
return v_r_3244_;
}
}
LEAN_EXPORT uint8_t l_Array_all(lean_object* v_00_u03b1_3245_, lean_object* v_as_3246_, lean_object* v_p_3247_, lean_object* v_start_3248_, lean_object* v_stop_3249_){
_start:
{
lean_object* v___x_3250_; uint8_t v___x_3251_; 
v___x_3250_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3251_ = lean_nat_dec_lt(v_start_3248_, v_stop_3249_);
if (v___x_3251_ == 0)
{
uint8_t v___x_3252_; 
lean_dec(v_stop_3249_);
lean_dec_ref(v_p_3247_);
lean_dec_ref(v_as_3246_);
v___x_3252_ = 1;
return v___x_3252_;
}
else
{
lean_object* v___x_3253_; lean_object* v___f_3254_; lean_object* v___y_3256_; lean_object* v___x_3263_; uint8_t v___x_3264_; 
v___x_3253_ = lean_box(v___x_3251_);
v___f_3254_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3254_, 0, v_p_3247_);
lean_closure_set(v___f_3254_, 1, v___x_3253_);
v___x_3263_ = lean_array_get_size(v_as_3246_);
v___x_3264_ = lean_nat_dec_le(v_stop_3249_, v___x_3263_);
if (v___x_3264_ == 0)
{
lean_dec(v_stop_3249_);
v___y_3256_ = v___x_3263_;
goto v___jp_3255_;
}
else
{
v___y_3256_ = v_stop_3249_;
goto v___jp_3255_;
}
v___jp_3255_:
{
uint8_t v___x_3257_; 
v___x_3257_ = lean_nat_dec_lt(v_start_3248_, v___y_3256_);
if (v___x_3257_ == 0)
{
lean_dec(v___y_3256_);
lean_dec_ref(v___f_3254_);
lean_dec_ref(v_as_3246_);
return v___x_3251_;
}
else
{
size_t v___x_3258_; size_t v___x_3259_; lean_object* v___x_3260_; uint8_t v___x_3261_; 
v___x_3258_ = lean_usize_of_nat(v_start_3248_);
v___x_3259_ = lean_usize_of_nat(v___y_3256_);
lean_dec(v___y_3256_);
v___x_3260_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3250_, v___f_3254_, v_as_3246_, v___x_3258_, v___x_3259_);
v___x_3261_ = lean_unbox(v___x_3260_);
lean_dec(v___x_3260_);
if (v___x_3261_ == 0)
{
return v___x_3257_;
}
else
{
uint8_t v___x_3262_; 
v___x_3262_ = 0;
return v___x_3262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___boxed(lean_object* v_00_u03b1_3265_, lean_object* v_as_3266_, lean_object* v_p_3267_, lean_object* v_start_3268_, lean_object* v_stop_3269_){
_start:
{
uint8_t v_res_3270_; lean_object* v_r_3271_; 
v_res_3270_ = l_Array_all(v_00_u03b1_3265_, v_as_3266_, v_p_3267_, v_start_3268_, v_stop_3269_);
lean_dec(v_start_3268_);
v_r_3271_ = lean_box(v_res_3270_);
return v_r_3271_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg___lam__0(lean_object* v_inst_3272_, lean_object* v_a_3273_, lean_object* v_x_3274_){
_start:
{
lean_object* v___x_3275_; uint8_t v___x_3276_; 
v___x_3275_ = lean_apply_2(v_inst_3272_, v_a_3273_, v_x_3274_);
v___x_3276_ = lean_unbox(v___x_3275_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___lam__0___boxed(lean_object* v_inst_3277_, lean_object* v_a_3278_, lean_object* v_x_3279_){
_start:
{
uint8_t v_res_3280_; lean_object* v_r_3281_; 
v_res_3280_ = l_Array_contains___redArg___lam__0(v_inst_3277_, v_a_3278_, v_x_3279_);
v_r_3281_ = lean_box(v_res_3280_);
return v_r_3281_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg(lean_object* v_inst_3282_, lean_object* v_as_3283_, lean_object* v_a_3284_){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; uint8_t v___x_3288_; 
v___x_3285_ = lean_unsigned_to_nat(0u);
v___x_3286_ = lean_array_get_size(v_as_3283_);
v___x_3287_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3288_ = lean_nat_dec_lt(v___x_3285_, v___x_3286_);
if (v___x_3288_ == 0)
{
lean_dec(v_a_3284_);
lean_dec_ref(v_as_3283_);
lean_dec_ref(v_inst_3282_);
return v___x_3288_;
}
else
{
if (v___x_3288_ == 0)
{
lean_dec(v_a_3284_);
lean_dec_ref(v_as_3283_);
lean_dec_ref(v_inst_3282_);
return v___x_3288_;
}
else
{
lean_object* v___f_3289_; size_t v___x_3290_; size_t v___x_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; 
v___f_3289_ = lean_alloc_closure((void*)(l_Array_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3289_, 0, v_inst_3282_);
lean_closure_set(v___f_3289_, 1, v_a_3284_);
v___x_3290_ = ((size_t)0ULL);
v___x_3291_ = lean_usize_of_nat(v___x_3286_);
v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3287_, v___f_3289_, v_as_3283_, v___x_3290_, v___x_3291_);
v___x_3293_ = lean_unbox(v___x_3292_);
lean_dec(v___x_3292_);
return v___x_3293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___boxed(lean_object* v_inst_3294_, lean_object* v_as_3295_, lean_object* v_a_3296_){
_start:
{
uint8_t v_res_3297_; lean_object* v_r_3298_; 
v_res_3297_ = l_Array_contains___redArg(v_inst_3294_, v_as_3295_, v_a_3296_);
v_r_3298_ = lean_box(v_res_3297_);
return v_r_3298_;
}
}
LEAN_EXPORT uint8_t l_Array_contains(lean_object* v_00_u03b1_3299_, lean_object* v_inst_3300_, lean_object* v_as_3301_, lean_object* v_a_3302_){
_start:
{
uint8_t v___x_3303_; 
v___x_3303_ = l_Array_contains___redArg(v_inst_3300_, v_as_3301_, v_a_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___boxed(lean_object* v_00_u03b1_3304_, lean_object* v_inst_3305_, lean_object* v_as_3306_, lean_object* v_a_3307_){
_start:
{
uint8_t v_res_3308_; lean_object* v_r_3309_; 
v_res_3308_ = l_Array_contains(v_00_u03b1_3304_, v_inst_3305_, v_as_3306_, v_a_3307_);
v_r_3309_ = lean_box(v_res_3308_);
return v_r_3309_;
}
}
LEAN_EXPORT uint8_t l_Array_elem___redArg(lean_object* v_inst_3310_, lean_object* v_a_3311_, lean_object* v_as_3312_){
_start:
{
uint8_t v___x_3313_; 
v___x_3313_ = l_Array_contains___redArg(v_inst_3310_, v_as_3312_, v_a_3311_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___redArg___boxed(lean_object* v_inst_3314_, lean_object* v_a_3315_, lean_object* v_as_3316_){
_start:
{
uint8_t v_res_3317_; lean_object* v_r_3318_; 
v_res_3317_ = l_Array_elem___redArg(v_inst_3314_, v_a_3315_, v_as_3316_);
v_r_3318_ = lean_box(v_res_3317_);
return v_r_3318_;
}
}
LEAN_EXPORT uint8_t l_Array_elem(lean_object* v_00_u03b1_3319_, lean_object* v_inst_3320_, lean_object* v_a_3321_, lean_object* v_as_3322_){
_start:
{
uint8_t v___x_3323_; 
v___x_3323_ = l_Array_contains___redArg(v_inst_3320_, v_as_3322_, v_a_3321_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___boxed(lean_object* v_00_u03b1_3324_, lean_object* v_inst_3325_, lean_object* v_a_3326_, lean_object* v_as_3327_){
_start:
{
uint8_t v_res_3328_; lean_object* v_r_3329_; 
v_res_3328_ = l_Array_elem(v_00_u03b1_3324_, v_inst_3325_, v_a_3326_, v_as_3327_);
v_r_3329_ = lean_box(v_res_3328_);
return v_r_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(lean_object* v_as_3330_, size_t v_i_3331_, size_t v_stop_3332_, lean_object* v_b_3333_){
_start:
{
uint8_t v___x_3334_; 
v___x_3334_ = lean_usize_dec_eq(v_i_3331_, v_stop_3332_);
if (v___x_3334_ == 0)
{
size_t v___x_3335_; size_t v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3335_ = ((size_t)1ULL);
v___x_3336_ = lean_usize_sub(v_i_3331_, v___x_3335_);
v___x_3337_ = lean_array_uget_borrowed(v_as_3330_, v___x_3336_);
lean_inc(v___x_3337_);
v___x_3338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
lean_ctor_set(v___x_3338_, 1, v_b_3333_);
v_i_3331_ = v___x_3336_;
v_b_3333_ = v___x_3338_;
goto _start;
}
else
{
return v_b_3333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg___boxed(lean_object* v_as_3340_, lean_object* v_i_3341_, lean_object* v_stop_3342_, lean_object* v_b_3343_){
_start:
{
size_t v_i_boxed_3344_; size_t v_stop_boxed_3345_; lean_object* v_res_3346_; 
v_i_boxed_3344_ = lean_unbox_usize(v_i_3341_);
lean_dec(v_i_3341_);
v_stop_boxed_3345_ = lean_unbox_usize(v_stop_3342_);
lean_dec(v_stop_3342_);
v_res_3346_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3340_, v_i_boxed_3344_, v_stop_boxed_3345_, v_b_3343_);
lean_dec_ref(v_as_3340_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg(lean_object* v_as_3347_){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v___x_3348_ = lean_box(0);
v___x_3349_ = lean_array_get_size(v_as_3347_);
v___x_3350_ = lean_unsigned_to_nat(0u);
v___x_3351_ = lean_nat_dec_lt(v___x_3350_, v___x_3349_);
if (v___x_3351_ == 0)
{
return v___x_3348_;
}
else
{
size_t v___x_3352_; size_t v___x_3353_; lean_object* v___x_3354_; 
v___x_3352_ = lean_usize_of_nat(v___x_3349_);
v___x_3353_ = ((size_t)0ULL);
v___x_3354_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3347_, v___x_3352_, v___x_3353_, v___x_3348_);
return v___x_3354_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg___boxed(lean_object* v_as_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Array_toListImpl___redArg(v_as_3355_);
lean_dec_ref(v_as_3355_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* lean_array_to_list_impl(lean_object* v_00_u03b1_3357_, lean_object* v_as_3358_){
_start:
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Array_toListImpl___redArg(v_as_3358_);
lean_dec_ref(v_as_3358_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(lean_object* v_00_u03b1_3360_, lean_object* v_as_3361_, size_t v_i_3362_, size_t v_stop_3363_, lean_object* v_b_3364_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3361_, v_i_3362_, v_stop_3363_, v_b_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___boxed(lean_object* v_00_u03b1_3366_, lean_object* v_as_3367_, lean_object* v_i_3368_, lean_object* v_stop_3369_, lean_object* v_b_3370_){
_start:
{
size_t v_i_boxed_3371_; size_t v_stop_boxed_3372_; lean_object* v_res_3373_; 
v_i_boxed_3371_ = lean_unbox_usize(v_i_3368_);
lean_dec(v_i_3368_);
v_stop_boxed_3372_ = lean_unbox_usize(v_stop_3369_);
lean_dec(v_stop_3369_);
v_res_3373_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(v_00_u03b1_3366_, v_as_3367_, v_i_boxed_3371_, v_stop_boxed_3372_, v_b_3370_);
lean_dec_ref(v_as_3367_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg___lam__0(lean_object* v_x1_3374_, lean_object* v_x2_3375_){
_start:
{
lean_object* v___x_3376_; 
v___x_3376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3376_, 0, v_x1_3374_);
lean_ctor_set(v___x_3376_, 1, v_x2_3375_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg(lean_object* v_as_3378_, lean_object* v_l_3379_){
_start:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v___x_3380_ = lean_array_get_size(v_as_3378_);
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3383_ = lean_nat_dec_lt(v___x_3381_, v___x_3380_);
if (v___x_3383_ == 0)
{
lean_dec_ref(v_as_3378_);
return v_l_3379_;
}
else
{
lean_object* v___f_3384_; size_t v___x_3385_; size_t v___x_3386_; lean_object* v___x_3387_; 
v___f_3384_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3385_ = lean_usize_of_nat(v___x_3380_);
v___x_3386_ = ((size_t)0ULL);
v___x_3387_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3382_, v___f_3384_, v_as_3378_, v___x_3385_, v___x_3386_, v_l_3379_);
return v___x_3387_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend(lean_object* v_00_u03b1_3388_, lean_object* v_as_3389_, lean_object* v_l_3390_){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; uint8_t v___x_3394_; 
v___x_3391_ = lean_array_get_size(v_as_3389_);
v___x_3392_ = lean_unsigned_to_nat(0u);
v___x_3393_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3394_ = lean_nat_dec_lt(v___x_3392_, v___x_3391_);
if (v___x_3394_ == 0)
{
lean_dec_ref(v_as_3389_);
return v_l_3390_;
}
else
{
lean_object* v___f_3395_; size_t v___x_3396_; size_t v___x_3397_; lean_object* v___x_3398_; 
v___f_3395_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3396_ = lean_usize_of_nat(v___x_3391_);
v___x_3397_ = ((size_t)0ULL);
v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3393_, v___f_3395_, v_as_3389_, v___x_3396_, v___x_3397_, v_l_3390_);
return v___x_3398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(lean_object* v_as_3399_, size_t v_i_3400_, size_t v_stop_3401_, lean_object* v_b_3402_){
_start:
{
uint8_t v___x_3403_; 
v___x_3403_ = lean_usize_dec_eq(v_i_3400_, v_stop_3401_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; lean_object* v___x_3405_; size_t v___x_3406_; size_t v___x_3407_; 
v___x_3404_ = lean_array_uget_borrowed(v_as_3399_, v_i_3400_);
lean_inc(v___x_3404_);
v___x_3405_ = lean_array_push(v_b_3402_, v___x_3404_);
v___x_3406_ = ((size_t)1ULL);
v___x_3407_ = lean_usize_add(v_i_3400_, v___x_3406_);
v_i_3400_ = v___x_3407_;
v_b_3402_ = v___x_3405_;
goto _start;
}
else
{
return v_b_3402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg___boxed(lean_object* v_as_3409_, lean_object* v_i_3410_, lean_object* v_stop_3411_, lean_object* v_b_3412_){
_start:
{
size_t v_i_boxed_3413_; size_t v_stop_boxed_3414_; lean_object* v_res_3415_; 
v_i_boxed_3413_ = lean_unbox_usize(v_i_3410_);
lean_dec(v_i_3410_);
v_stop_boxed_3414_ = lean_unbox_usize(v_stop_3411_);
lean_dec(v_stop_3411_);
v_res_3415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3409_, v_i_boxed_3413_, v_stop_boxed_3414_, v_b_3412_);
lean_dec_ref(v_as_3409_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg(lean_object* v_as_3416_, lean_object* v_bs_3417_){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; 
v___x_3418_ = lean_unsigned_to_nat(0u);
v___x_3419_ = lean_array_get_size(v_bs_3417_);
v___x_3420_ = lean_nat_dec_lt(v___x_3418_, v___x_3419_);
if (v___x_3420_ == 0)
{
return v_as_3416_;
}
else
{
uint8_t v___x_3421_; 
v___x_3421_ = lean_nat_dec_le(v___x_3419_, v___x_3419_);
if (v___x_3421_ == 0)
{
if (v___x_3420_ == 0)
{
return v_as_3416_;
}
else
{
size_t v___x_3422_; size_t v___x_3423_; lean_object* v___x_3424_; 
v___x_3422_ = ((size_t)0ULL);
v___x_3423_ = lean_usize_of_nat(v___x_3419_);
v___x_3424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3417_, v___x_3422_, v___x_3423_, v_as_3416_);
return v___x_3424_;
}
}
else
{
size_t v___x_3425_; size_t v___x_3426_; lean_object* v___x_3427_; 
v___x_3425_ = ((size_t)0ULL);
v___x_3426_ = lean_usize_of_nat(v___x_3419_);
v___x_3427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3417_, v___x_3425_, v___x_3426_, v_as_3416_);
return v___x_3427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg___boxed(lean_object* v_as_3428_, lean_object* v_bs_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Array_append___redArg(v_as_3428_, v_bs_3429_);
lean_dec_ref(v_bs_3429_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Array_append(lean_object* v_00_u03b1_3431_, lean_object* v_as_3432_, lean_object* v_bs_3433_){
_start:
{
lean_object* v___x_3434_; 
v___x_3434_ = l_Array_append___redArg(v_as_3432_, v_bs_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Array_append___boxed(lean_object* v_00_u03b1_3435_, lean_object* v_as_3436_, lean_object* v_bs_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Array_append(v_00_u03b1_3435_, v_as_3436_, v_bs_3437_);
lean_dec_ref(v_bs_3437_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(lean_object* v_00_u03b1_3439_, lean_object* v_as_3440_, size_t v_i_3441_, size_t v_stop_3442_, lean_object* v_b_3443_){
_start:
{
lean_object* v___x_3444_; 
v___x_3444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3440_, v_i_3441_, v_stop_3442_, v_b_3443_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___boxed(lean_object* v_00_u03b1_3445_, lean_object* v_as_3446_, lean_object* v_i_3447_, lean_object* v_stop_3448_, lean_object* v_b_3449_){
_start:
{
size_t v_i_boxed_3450_; size_t v_stop_boxed_3451_; lean_object* v_res_3452_; 
v_i_boxed_3450_ = lean_unbox_usize(v_i_3447_);
lean_dec(v_i_3447_);
v_stop_boxed_3451_ = lean_unbox_usize(v_stop_3448_);
lean_dec(v_stop_3448_);
v_res_3452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(v_00_u03b1_3445_, v_as_3446_, v_i_boxed_3450_, v_stop_boxed_3451_, v_b_3449_);
lean_dec_ref(v_as_3446_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend(lean_object* v_00_u03b1_3454_){
_start:
{
lean_object* v___x_3455_; 
v___x_3455_ = ((lean_object*)(l_Array_instAppend___closed__0));
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object* v_x_3456_, lean_object* v_x_3457_){
_start:
{
if (lean_obj_tag(v_x_3457_) == 0)
{
return v_x_3456_;
}
else
{
lean_object* v_head_3458_; lean_object* v_tail_3459_; lean_object* v___x_3460_; 
v_head_3458_ = lean_ctor_get(v_x_3457_, 0);
lean_inc(v_head_3458_);
v_tail_3459_ = lean_ctor_get(v_x_3457_, 1);
lean_inc(v_tail_3459_);
lean_dec_ref_known(v_x_3457_, 2);
v___x_3460_ = lean_array_push(v_x_3456_, v_head_3458_);
v_x_3456_ = v___x_3460_;
v_x_3457_ = v_tail_3459_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_appendList___redArg(lean_object* v_as_3462_, lean_object* v_bs_3463_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3462_, v_bs_3463_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l_Array_appendList(lean_object* v_00_u03b1_3465_, lean_object* v_as_3466_, lean_object* v_bs_3467_){
_start:
{
lean_object* v___x_3468_; 
v___x_3468_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3466_, v_bs_3467_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0(lean_object* v_00_u03b1_3469_, lean_object* v_x_3470_, lean_object* v_x_3471_){
_start:
{
lean_object* v___x_3472_; 
v___x_3472_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_3470_, v_x_3471_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList(lean_object* v_00_u03b1_3474_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = ((lean_object*)(l_Array_instHAppendList___closed__0));
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0(lean_object* v_bs_3476_, lean_object* v_toPure_3477_, lean_object* v_____do__lift_3478_){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3479_ = l_Array_append___redArg(v_bs_3476_, v_____do__lift_3478_);
v___x_3480_ = lean_apply_2(v_toPure_3477_, lean_box(0), v___x_3479_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0___boxed(lean_object* v_bs_3481_, lean_object* v_toPure_3482_, lean_object* v_____do__lift_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Array_flatMapM___redArg___lam__0(v_bs_3481_, v_toPure_3482_, v_____do__lift_3483_);
lean_dec_ref(v_____do__lift_3483_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__1(lean_object* v_toPure_3485_, lean_object* v_f_3486_, lean_object* v_toBind_3487_, lean_object* v_bs_3488_, lean_object* v_a_3489_){
_start:
{
lean_object* v___f_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___f_3490_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3490_, 0, v_bs_3488_);
lean_closure_set(v___f_3490_, 1, v_toPure_3485_);
v___x_3491_ = lean_apply_1(v_f_3486_, v_a_3489_);
v___x_3492_ = lean_apply_4(v_toBind_3487_, lean_box(0), lean_box(0), v___x_3491_, v___f_3490_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg(lean_object* v_inst_3493_, lean_object* v_f_3494_, lean_object* v_as_3495_){
_start:
{
lean_object* v_toApplicative_3496_; lean_object* v_toBind_3497_; lean_object* v_toPure_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; 
v_toApplicative_3496_ = lean_ctor_get(v_inst_3493_, 0);
v_toBind_3497_ = lean_ctor_get(v_inst_3493_, 1);
v_toPure_3498_ = lean_ctor_get(v_toApplicative_3496_, 1);
v___x_3499_ = lean_unsigned_to_nat(0u);
v___x_3500_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3501_ = lean_array_get_size(v_as_3495_);
v___x_3502_ = lean_nat_dec_lt(v___x_3499_, v___x_3501_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; 
lean_inc(v_toPure_3498_);
lean_dec_ref(v_as_3495_);
lean_dec(v_f_3494_);
lean_dec_ref(v_inst_3493_);
v___x_3503_ = lean_apply_2(v_toPure_3498_, lean_box(0), v___x_3500_);
return v___x_3503_;
}
else
{
lean_object* v___f_3504_; uint8_t v___x_3505_; 
lean_inc(v_toBind_3497_);
lean_inc(v_toPure_3498_);
v___f_3504_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3504_, 0, v_toPure_3498_);
lean_closure_set(v___f_3504_, 1, v_f_3494_);
lean_closure_set(v___f_3504_, 2, v_toBind_3497_);
v___x_3505_ = lean_nat_dec_le(v___x_3501_, v___x_3501_);
if (v___x_3505_ == 0)
{
if (v___x_3502_ == 0)
{
lean_object* v___x_3506_; 
lean_inc(v_toPure_3498_);
lean_dec_ref(v___f_3504_);
lean_dec_ref(v_as_3495_);
lean_dec_ref(v_inst_3493_);
v___x_3506_ = lean_apply_2(v_toPure_3498_, lean_box(0), v___x_3500_);
return v___x_3506_;
}
else
{
size_t v___x_3507_; size_t v___x_3508_; lean_object* v___x_3509_; 
v___x_3507_ = ((size_t)0ULL);
v___x_3508_ = lean_usize_of_nat(v___x_3501_);
v___x_3509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3493_, v___f_3504_, v_as_3495_, v___x_3507_, v___x_3508_, v___x_3500_);
return v___x_3509_;
}
}
else
{
size_t v___x_3510_; size_t v___x_3511_; lean_object* v___x_3512_; 
v___x_3510_ = ((size_t)0ULL);
v___x_3511_ = lean_usize_of_nat(v___x_3501_);
v___x_3512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3493_, v___f_3504_, v_as_3495_, v___x_3510_, v___x_3511_, v___x_3500_);
return v___x_3512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM(lean_object* v_00_u03b1_3513_, lean_object* v_m_3514_, lean_object* v_00_u03b2_3515_, lean_object* v_inst_3516_, lean_object* v_f_3517_, lean_object* v_as_3518_){
_start:
{
lean_object* v_toApplicative_3519_; lean_object* v_toBind_3520_; lean_object* v_toPure_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; uint8_t v___x_3525_; 
v_toApplicative_3519_ = lean_ctor_get(v_inst_3516_, 0);
v_toBind_3520_ = lean_ctor_get(v_inst_3516_, 1);
v_toPure_3521_ = lean_ctor_get(v_toApplicative_3519_, 1);
v___x_3522_ = lean_unsigned_to_nat(0u);
v___x_3523_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3524_ = lean_array_get_size(v_as_3518_);
v___x_3525_ = lean_nat_dec_lt(v___x_3522_, v___x_3524_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; 
lean_inc(v_toPure_3521_);
lean_dec_ref(v_as_3518_);
lean_dec(v_f_3517_);
lean_dec_ref(v_inst_3516_);
v___x_3526_ = lean_apply_2(v_toPure_3521_, lean_box(0), v___x_3523_);
return v___x_3526_;
}
else
{
lean_object* v___f_3527_; uint8_t v___x_3528_; 
lean_inc(v_toBind_3520_);
lean_inc(v_toPure_3521_);
v___f_3527_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3527_, 0, v_toPure_3521_);
lean_closure_set(v___f_3527_, 1, v_f_3517_);
lean_closure_set(v___f_3527_, 2, v_toBind_3520_);
v___x_3528_ = lean_nat_dec_le(v___x_3524_, v___x_3524_);
if (v___x_3528_ == 0)
{
if (v___x_3525_ == 0)
{
lean_object* v___x_3529_; 
lean_inc(v_toPure_3521_);
lean_dec_ref(v___f_3527_);
lean_dec_ref(v_as_3518_);
lean_dec_ref(v_inst_3516_);
v___x_3529_ = lean_apply_2(v_toPure_3521_, lean_box(0), v___x_3523_);
return v___x_3529_;
}
else
{
size_t v___x_3530_; size_t v___x_3531_; lean_object* v___x_3532_; 
v___x_3530_ = ((size_t)0ULL);
v___x_3531_ = lean_usize_of_nat(v___x_3524_);
v___x_3532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3516_, v___f_3527_, v_as_3518_, v___x_3530_, v___x_3531_, v___x_3523_);
return v___x_3532_;
}
}
else
{
size_t v___x_3533_; size_t v___x_3534_; lean_object* v___x_3535_; 
v___x_3533_ = ((size_t)0ULL);
v___x_3534_ = lean_usize_of_nat(v___x_3524_);
v___x_3535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3516_, v___f_3527_, v_as_3518_, v___x_3533_, v___x_3534_, v___x_3523_);
return v___x_3535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg___lam__0(lean_object* v_f_3536_, lean_object* v_x1_3537_, lean_object* v_x2_3538_){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = lean_apply_1(v_f_3536_, v_x2_3538_);
v___x_3540_ = l_Array_append___redArg(v_x1_3537_, v___x_3539_);
lean_dec_ref(v___x_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg(lean_object* v_f_3541_, lean_object* v_as_3542_){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
v___x_3543_ = lean_unsigned_to_nat(0u);
v___x_3544_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3545_ = lean_array_get_size(v_as_3542_);
v___x_3546_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3547_ = lean_nat_dec_lt(v___x_3543_, v___x_3545_);
if (v___x_3547_ == 0)
{
lean_dec_ref(v_as_3542_);
lean_dec_ref(v_f_3541_);
return v___x_3544_;
}
else
{
lean_object* v___f_3548_; uint8_t v___x_3549_; 
v___f_3548_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3548_, 0, v_f_3541_);
v___x_3549_ = lean_nat_dec_le(v___x_3545_, v___x_3545_);
if (v___x_3549_ == 0)
{
if (v___x_3547_ == 0)
{
lean_dec_ref(v___f_3548_);
lean_dec_ref(v_as_3542_);
return v___x_3544_;
}
else
{
size_t v___x_3550_; size_t v___x_3551_; lean_object* v___x_3552_; 
v___x_3550_ = ((size_t)0ULL);
v___x_3551_ = lean_usize_of_nat(v___x_3545_);
v___x_3552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3546_, v___f_3548_, v_as_3542_, v___x_3550_, v___x_3551_, v___x_3544_);
return v___x_3552_;
}
}
else
{
size_t v___x_3553_; size_t v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = ((size_t)0ULL);
v___x_3554_ = lean_usize_of_nat(v___x_3545_);
v___x_3555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3546_, v___f_3548_, v_as_3542_, v___x_3553_, v___x_3554_, v___x_3544_);
return v___x_3555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap(lean_object* v_00_u03b1_3556_, lean_object* v_00_u03b2_3557_, lean_object* v_f_3558_, lean_object* v_as_3559_){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v___x_3560_ = lean_unsigned_to_nat(0u);
v___x_3561_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3562_ = lean_array_get_size(v_as_3559_);
v___x_3563_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3564_ = lean_nat_dec_lt(v___x_3560_, v___x_3562_);
if (v___x_3564_ == 0)
{
lean_dec_ref(v_as_3559_);
lean_dec_ref(v_f_3558_);
return v___x_3561_;
}
else
{
lean_object* v___f_3565_; uint8_t v___x_3566_; 
v___f_3565_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3565_, 0, v_f_3558_);
v___x_3566_ = lean_nat_dec_le(v___x_3562_, v___x_3562_);
if (v___x_3566_ == 0)
{
if (v___x_3564_ == 0)
{
lean_dec_ref(v___f_3565_);
lean_dec_ref(v_as_3559_);
return v___x_3561_;
}
else
{
size_t v___x_3567_; size_t v___x_3568_; lean_object* v___x_3569_; 
v___x_3567_ = ((size_t)0ULL);
v___x_3568_ = lean_usize_of_nat(v___x_3562_);
v___x_3569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3563_, v___f_3565_, v_as_3559_, v___x_3567_, v___x_3568_, v___x_3561_);
return v___x_3569_;
}
}
else
{
size_t v___x_3570_; size_t v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = ((size_t)0ULL);
v___x_3571_ = lean_usize_of_nat(v___x_3562_);
v___x_3572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3563_, v___f_3565_, v_as_3559_, v___x_3570_, v___x_3571_, v___x_3561_);
return v___x_3572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten___redArg(lean_object* v_xss_3574_){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; 
v___x_3575_ = lean_unsigned_to_nat(0u);
v___x_3576_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3577_ = lean_array_get_size(v_xss_3574_);
v___x_3578_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3579_ = lean_nat_dec_lt(v___x_3575_, v___x_3577_);
if (v___x_3579_ == 0)
{
lean_dec_ref(v_xss_3574_);
return v___x_3576_;
}
else
{
lean_object* v___f_3580_; uint8_t v___x_3581_; 
v___f_3580_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3581_ = lean_nat_dec_le(v___x_3577_, v___x_3577_);
if (v___x_3581_ == 0)
{
if (v___x_3579_ == 0)
{
lean_dec_ref(v_xss_3574_);
return v___x_3576_;
}
else
{
size_t v___x_3582_; size_t v___x_3583_; lean_object* v___x_3584_; 
v___x_3582_ = ((size_t)0ULL);
v___x_3583_ = lean_usize_of_nat(v___x_3577_);
v___x_3584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3578_, v___f_3580_, v_xss_3574_, v___x_3582_, v___x_3583_, v___x_3576_);
return v___x_3584_;
}
}
else
{
size_t v___x_3585_; size_t v___x_3586_; lean_object* v___x_3587_; 
v___x_3585_ = ((size_t)0ULL);
v___x_3586_ = lean_usize_of_nat(v___x_3577_);
v___x_3587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3578_, v___f_3580_, v_xss_3574_, v___x_3585_, v___x_3586_, v___x_3576_);
return v___x_3587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten(lean_object* v_00_u03b1_3588_, lean_object* v_xss_3589_){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; uint8_t v___x_3594_; 
v___x_3590_ = lean_unsigned_to_nat(0u);
v___x_3591_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3592_ = lean_array_get_size(v_xss_3589_);
v___x_3593_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3594_ = lean_nat_dec_lt(v___x_3590_, v___x_3592_);
if (v___x_3594_ == 0)
{
lean_dec_ref(v_xss_3589_);
return v___x_3591_;
}
else
{
lean_object* v___f_3595_; uint8_t v___x_3596_; 
v___f_3595_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3596_ = lean_nat_dec_le(v___x_3592_, v___x_3592_);
if (v___x_3596_ == 0)
{
if (v___x_3594_ == 0)
{
lean_dec_ref(v_xss_3589_);
return v___x_3591_;
}
else
{
size_t v___x_3597_; size_t v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = ((size_t)0ULL);
v___x_3598_ = lean_usize_of_nat(v___x_3592_);
v___x_3599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3593_, v___f_3595_, v_xss_3589_, v___x_3597_, v___x_3598_, v___x_3591_);
return v___x_3599_;
}
}
else
{
size_t v___x_3600_; size_t v___x_3601_; lean_object* v___x_3602_; 
v___x_3600_ = ((size_t)0ULL);
v___x_3601_ = lean_usize_of_nat(v___x_3592_);
v___x_3602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3593_, v___f_3595_, v_xss_3589_, v___x_3600_, v___x_3601_, v___x_3591_);
return v___x_3602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop___redArg(lean_object* v_as_3603_, lean_object* v_i_3604_, lean_object* v_j_3605_){
_start:
{
uint8_t v___x_3606_; 
v___x_3606_ = lean_nat_dec_lt(v_i_3604_, v_j_3605_);
if (v___x_3606_ == 0)
{
lean_dec(v_j_3605_);
lean_dec(v_i_3604_);
return v_as_3603_;
}
else
{
lean_object* v_as_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v_as_3607_ = lean_array_fswap(v_as_3603_, v_i_3604_, v_j_3605_);
v___x_3608_ = lean_unsigned_to_nat(1u);
v___x_3609_ = lean_nat_add(v_i_3604_, v___x_3608_);
lean_dec(v_i_3604_);
v___x_3610_ = lean_nat_sub(v_j_3605_, v___x_3608_);
lean_dec(v_j_3605_);
v_as_3603_ = v_as_3607_;
v_i_3604_ = v___x_3609_;
v_j_3605_ = v___x_3610_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop(lean_object* v_00_u03b1_3612_, lean_object* v_as_3613_, lean_object* v_i_3614_, lean_object* v_j_3615_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l_Array_reverse_loop___redArg(v_as_3613_, v_i_3614_, v_j_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Array_reverse___redArg(lean_object* v_as_3617_){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; uint8_t v___x_3620_; 
v___x_3618_ = lean_array_get_size(v_as_3617_);
v___x_3619_ = lean_unsigned_to_nat(1u);
v___x_3620_ = lean_nat_dec_le(v___x_3618_, v___x_3619_);
if (v___x_3620_ == 0)
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3621_ = lean_unsigned_to_nat(0u);
v___x_3622_ = lean_nat_sub(v___x_3618_, v___x_3619_);
v___x_3623_ = l_Array_reverse_loop___redArg(v_as_3617_, v___x_3621_, v___x_3622_);
return v___x_3623_;
}
else
{
return v_as_3617_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse(lean_object* v_00_u03b1_3624_, lean_object* v_as_3625_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Array_reverse___redArg(v_as_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___lam__0(lean_object* v_p_3627_, lean_object* v_x1_3628_, lean_object* v_x2_3629_){
_start:
{
lean_object* v___x_3630_; uint8_t v___x_3631_; 
lean_inc(v_x2_3629_);
v___x_3630_ = lean_apply_1(v_p_3627_, v_x2_3629_);
v___x_3631_ = lean_unbox(v___x_3630_);
if (v___x_3631_ == 0)
{
lean_dec(v_x2_3629_);
return v_x1_3628_;
}
else
{
lean_object* v___x_3632_; 
v___x_3632_ = lean_array_push(v_x1_3628_, v_x2_3629_);
return v___x_3632_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg(lean_object* v_p_3635_, lean_object* v_as_3636_, lean_object* v_start_3637_, lean_object* v_stop_3638_){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; uint8_t v___x_3641_; 
v___x_3639_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3640_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3641_ = lean_nat_dec_lt(v_start_3637_, v_stop_3638_);
if (v___x_3641_ == 0)
{
lean_dec_ref(v_as_3636_);
lean_dec_ref(v_p_3635_);
return v___x_3639_;
}
else
{
lean_object* v___f_3642_; lean_object* v___x_3643_; uint8_t v___x_3644_; 
v___f_3642_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3642_, 0, v_p_3635_);
v___x_3643_ = lean_array_get_size(v_as_3636_);
v___x_3644_ = lean_nat_dec_le(v_stop_3638_, v___x_3643_);
if (v___x_3644_ == 0)
{
uint8_t v___x_3645_; 
v___x_3645_ = lean_nat_dec_lt(v_start_3637_, v___x_3643_);
if (v___x_3645_ == 0)
{
lean_dec_ref(v___f_3642_);
lean_dec_ref(v_as_3636_);
return v___x_3639_;
}
else
{
size_t v___x_3646_; size_t v___x_3647_; lean_object* v___x_3648_; 
v___x_3646_ = lean_usize_of_nat(v_start_3637_);
v___x_3647_ = lean_usize_of_nat(v___x_3643_);
v___x_3648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3640_, v___f_3642_, v_as_3636_, v___x_3646_, v___x_3647_, v___x_3639_);
return v___x_3648_;
}
}
else
{
size_t v___x_3649_; size_t v___x_3650_; lean_object* v___x_3651_; 
v___x_3649_ = lean_usize_of_nat(v_start_3637_);
v___x_3650_ = lean_usize_of_nat(v_stop_3638_);
v___x_3651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3640_, v___f_3642_, v_as_3636_, v___x_3649_, v___x_3650_, v___x_3639_);
return v___x_3651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___boxed(lean_object* v_p_3652_, lean_object* v_as_3653_, lean_object* v_start_3654_, lean_object* v_stop_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Array_filter___redArg(v_p_3652_, v_as_3653_, v_start_3654_, v_stop_3655_);
lean_dec(v_stop_3655_);
lean_dec(v_start_3654_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Array_filter(lean_object* v_00_u03b1_3657_, lean_object* v_p_3658_, lean_object* v_as_3659_, lean_object* v_start_3660_, lean_object* v_stop_3661_){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; uint8_t v___x_3664_; 
v___x_3662_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3663_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3664_ = lean_nat_dec_lt(v_start_3660_, v_stop_3661_);
if (v___x_3664_ == 0)
{
lean_dec_ref(v_as_3659_);
lean_dec_ref(v_p_3658_);
return v___x_3662_;
}
else
{
lean_object* v___f_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; 
v___f_3665_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3665_, 0, v_p_3658_);
v___x_3666_ = lean_array_get_size(v_as_3659_);
v___x_3667_ = lean_nat_dec_le(v_stop_3661_, v___x_3666_);
if (v___x_3667_ == 0)
{
uint8_t v___x_3668_; 
v___x_3668_ = lean_nat_dec_lt(v_start_3660_, v___x_3666_);
if (v___x_3668_ == 0)
{
lean_dec_ref(v___f_3665_);
lean_dec_ref(v_as_3659_);
return v___x_3662_;
}
else
{
size_t v___x_3669_; size_t v___x_3670_; lean_object* v___x_3671_; 
v___x_3669_ = lean_usize_of_nat(v_start_3660_);
v___x_3670_ = lean_usize_of_nat(v___x_3666_);
v___x_3671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3663_, v___f_3665_, v_as_3659_, v___x_3669_, v___x_3670_, v___x_3662_);
return v___x_3671_;
}
}
else
{
size_t v___x_3672_; size_t v___x_3673_; lean_object* v___x_3674_; 
v___x_3672_ = lean_usize_of_nat(v_start_3660_);
v___x_3673_ = lean_usize_of_nat(v_stop_3661_);
v___x_3674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3663_, v___f_3665_, v_as_3659_, v___x_3672_, v___x_3673_, v___x_3662_);
return v___x_3674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___boxed(lean_object* v_00_u03b1_3675_, lean_object* v_p_3676_, lean_object* v_as_3677_, lean_object* v_start_3678_, lean_object* v_stop_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Array_filter(v_00_u03b1_3675_, v_p_3676_, v_as_3677_, v_start_3678_, v_stop_3679_);
lean_dec(v_stop_3679_);
lean_dec(v_start_3678_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0(lean_object* v_toPure_3681_, lean_object* v_acc_3682_, lean_object* v_a_3683_, uint8_t v_____do__lift_3684_){
_start:
{
if (v_____do__lift_3684_ == 0)
{
lean_object* v___x_3685_; 
lean_dec(v_a_3683_);
v___x_3685_ = lean_apply_2(v_toPure_3681_, lean_box(0), v_acc_3682_);
return v___x_3685_;
}
else
{
lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3686_ = lean_array_push(v_acc_3682_, v_a_3683_);
v___x_3687_ = lean_apply_2(v_toPure_3681_, lean_box(0), v___x_3686_);
return v___x_3687_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0___boxed(lean_object* v_toPure_3688_, lean_object* v_acc_3689_, lean_object* v_a_3690_, lean_object* v_____do__lift_3691_){
_start:
{
uint8_t v_____do__lift_89__boxed_3692_; lean_object* v_res_3693_; 
v_____do__lift_89__boxed_3692_ = lean_unbox(v_____do__lift_3691_);
v_res_3693_ = l_Array_filterM___redArg___lam__0(v_toPure_3688_, v_acc_3689_, v_a_3690_, v_____do__lift_89__boxed_3692_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__1(lean_object* v_toPure_3694_, lean_object* v_p_3695_, lean_object* v_toBind_3696_, lean_object* v_acc_3697_, lean_object* v_a_3698_){
_start:
{
lean_object* v___f_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
lean_inc(v_a_3698_);
v___f_3699_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3699_, 0, v_toPure_3694_);
lean_closure_set(v___f_3699_, 1, v_acc_3697_);
lean_closure_set(v___f_3699_, 2, v_a_3698_);
v___x_3700_ = lean_apply_1(v_p_3695_, v_a_3698_);
v___x_3701_ = lean_apply_4(v_toBind_3696_, lean_box(0), lean_box(0), v___x_3700_, v___f_3699_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg(lean_object* v_inst_3702_, lean_object* v_p_3703_, lean_object* v_as_3704_, lean_object* v_start_3705_, lean_object* v_stop_3706_){
_start:
{
lean_object* v_toApplicative_3707_; lean_object* v_toBind_3708_; lean_object* v_toPure_3709_; lean_object* v___x_3710_; uint8_t v___x_3711_; 
v_toApplicative_3707_ = lean_ctor_get(v_inst_3702_, 0);
v_toBind_3708_ = lean_ctor_get(v_inst_3702_, 1);
v_toPure_3709_ = lean_ctor_get(v_toApplicative_3707_, 1);
v___x_3710_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3711_ = lean_nat_dec_lt(v_start_3705_, v_stop_3706_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3712_; 
lean_inc(v_toPure_3709_);
lean_dec_ref(v_as_3704_);
lean_dec(v_p_3703_);
lean_dec_ref(v_inst_3702_);
v___x_3712_ = lean_apply_2(v_toPure_3709_, lean_box(0), v___x_3710_);
return v___x_3712_;
}
else
{
lean_object* v___f_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; 
lean_inc(v_toBind_3708_);
lean_inc(v_toPure_3709_);
v___f_3713_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3713_, 0, v_toPure_3709_);
lean_closure_set(v___f_3713_, 1, v_p_3703_);
lean_closure_set(v___f_3713_, 2, v_toBind_3708_);
v___x_3714_ = lean_array_get_size(v_as_3704_);
v___x_3715_ = lean_nat_dec_le(v_stop_3706_, v___x_3714_);
if (v___x_3715_ == 0)
{
uint8_t v___x_3716_; 
v___x_3716_ = lean_nat_dec_lt(v_start_3705_, v___x_3714_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; 
lean_inc(v_toPure_3709_);
lean_dec_ref(v___f_3713_);
lean_dec_ref(v_as_3704_);
lean_dec_ref(v_inst_3702_);
v___x_3717_ = lean_apply_2(v_toPure_3709_, lean_box(0), v___x_3710_);
return v___x_3717_;
}
else
{
size_t v___x_3718_; size_t v___x_3719_; lean_object* v___x_3720_; 
v___x_3718_ = lean_usize_of_nat(v_start_3705_);
v___x_3719_ = lean_usize_of_nat(v___x_3714_);
v___x_3720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3702_, v___f_3713_, v_as_3704_, v___x_3718_, v___x_3719_, v___x_3710_);
return v___x_3720_;
}
}
else
{
size_t v___x_3721_; size_t v___x_3722_; lean_object* v___x_3723_; 
v___x_3721_ = lean_usize_of_nat(v_start_3705_);
v___x_3722_ = lean_usize_of_nat(v_stop_3706_);
v___x_3723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3702_, v___f_3713_, v_as_3704_, v___x_3721_, v___x_3722_, v___x_3710_);
return v___x_3723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___boxed(lean_object* v_inst_3724_, lean_object* v_p_3725_, lean_object* v_as_3726_, lean_object* v_start_3727_, lean_object* v_stop_3728_){
_start:
{
lean_object* v_res_3729_; 
v_res_3729_ = l_Array_filterM___redArg(v_inst_3724_, v_p_3725_, v_as_3726_, v_start_3727_, v_stop_3728_);
lean_dec(v_stop_3728_);
lean_dec(v_start_3727_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM(lean_object* v_m_3730_, lean_object* v_00_u03b1_3731_, lean_object* v_inst_3732_, lean_object* v_p_3733_, lean_object* v_as_3734_, lean_object* v_start_3735_, lean_object* v_stop_3736_){
_start:
{
lean_object* v_toApplicative_3737_; lean_object* v_toBind_3738_; lean_object* v_toPure_3739_; lean_object* v___x_3740_; uint8_t v___x_3741_; 
v_toApplicative_3737_ = lean_ctor_get(v_inst_3732_, 0);
v_toBind_3738_ = lean_ctor_get(v_inst_3732_, 1);
v_toPure_3739_ = lean_ctor_get(v_toApplicative_3737_, 1);
v___x_3740_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3741_ = lean_nat_dec_lt(v_start_3735_, v_stop_3736_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3742_; 
lean_inc(v_toPure_3739_);
lean_dec_ref(v_as_3734_);
lean_dec(v_p_3733_);
lean_dec_ref(v_inst_3732_);
v___x_3742_ = lean_apply_2(v_toPure_3739_, lean_box(0), v___x_3740_);
return v___x_3742_;
}
else
{
lean_object* v___f_3743_; lean_object* v___x_3744_; uint8_t v___x_3745_; 
lean_inc(v_toBind_3738_);
lean_inc(v_toPure_3739_);
v___f_3743_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3743_, 0, v_toPure_3739_);
lean_closure_set(v___f_3743_, 1, v_p_3733_);
lean_closure_set(v___f_3743_, 2, v_toBind_3738_);
v___x_3744_ = lean_array_get_size(v_as_3734_);
v___x_3745_ = lean_nat_dec_le(v_stop_3736_, v___x_3744_);
if (v___x_3745_ == 0)
{
uint8_t v___x_3746_; 
v___x_3746_ = lean_nat_dec_lt(v_start_3735_, v___x_3744_);
if (v___x_3746_ == 0)
{
lean_object* v___x_3747_; 
lean_inc(v_toPure_3739_);
lean_dec_ref(v___f_3743_);
lean_dec_ref(v_as_3734_);
lean_dec_ref(v_inst_3732_);
v___x_3747_ = lean_apply_2(v_toPure_3739_, lean_box(0), v___x_3740_);
return v___x_3747_;
}
else
{
size_t v___x_3748_; size_t v___x_3749_; lean_object* v___x_3750_; 
v___x_3748_ = lean_usize_of_nat(v_start_3735_);
v___x_3749_ = lean_usize_of_nat(v___x_3744_);
v___x_3750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3732_, v___f_3743_, v_as_3734_, v___x_3748_, v___x_3749_, v___x_3740_);
return v___x_3750_;
}
}
else
{
size_t v___x_3751_; size_t v___x_3752_; lean_object* v___x_3753_; 
v___x_3751_ = lean_usize_of_nat(v_start_3735_);
v___x_3752_ = lean_usize_of_nat(v_stop_3736_);
v___x_3753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3732_, v___f_3743_, v_as_3734_, v___x_3751_, v___x_3752_, v___x_3740_);
return v___x_3753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___boxed(lean_object* v_m_3754_, lean_object* v_00_u03b1_3755_, lean_object* v_inst_3756_, lean_object* v_p_3757_, lean_object* v_as_3758_, lean_object* v_start_3759_, lean_object* v_stop_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_Array_filterM(v_m_3754_, v_00_u03b1_3755_, v_inst_3756_, v_p_3757_, v_as_3758_, v_start_3759_, v_stop_3760_);
lean_dec(v_stop_3760_);
lean_dec(v_start_3759_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__1(lean_object* v_toPure_3762_, lean_object* v_p_3763_, lean_object* v_toBind_3764_, lean_object* v_a_3765_, lean_object* v_acc_3766_){
_start:
{
lean_object* v___f_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
lean_inc(v_a_3765_);
v___f_3767_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3767_, 0, v_toPure_3762_);
lean_closure_set(v___f_3767_, 1, v_acc_3766_);
lean_closure_set(v___f_3767_, 2, v_a_3765_);
v___x_3768_ = lean_apply_1(v_p_3763_, v_a_3765_);
v___x_3769_ = lean_apply_4(v_toBind_3764_, lean_box(0), lean_box(0), v___x_3768_, v___f_3767_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg(lean_object* v_inst_3771_, lean_object* v_p_3772_, lean_object* v_as_3773_, lean_object* v_start_3774_, lean_object* v_stop_3775_){
_start:
{
lean_object* v_toApplicative_3776_; lean_object* v_toFunctor_3777_; lean_object* v_toBind_3778_; lean_object* v_toPure_3779_; lean_object* v_map_3780_; lean_object* v___f_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; uint8_t v___x_3785_; 
v_toApplicative_3776_ = lean_ctor_get(v_inst_3771_, 0);
v_toFunctor_3777_ = lean_ctor_get(v_toApplicative_3776_, 0);
v_toBind_3778_ = lean_ctor_get(v_inst_3771_, 1);
v_toPure_3779_ = lean_ctor_get(v_toApplicative_3776_, 1);
v_map_3780_ = lean_ctor_get(v_toFunctor_3777_, 0);
lean_inc(v_map_3780_);
lean_inc(v_toBind_3778_);
lean_inc(v_toPure_3779_);
v___f_3781_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3781_, 0, v_toPure_3779_);
lean_closure_set(v___f_3781_, 1, v_p_3772_);
lean_closure_set(v___f_3781_, 2, v_toBind_3778_);
v___x_3782_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3783_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3784_ = lean_array_get_size(v_as_3773_);
v___x_3785_ = lean_nat_dec_le(v_start_3774_, v___x_3784_);
if (v___x_3785_ == 0)
{
uint8_t v___x_3786_; 
v___x_3786_ = lean_nat_dec_lt(v_stop_3775_, v___x_3784_);
if (v___x_3786_ == 0)
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
lean_inc(v_toPure_3779_);
lean_dec_ref(v___f_3781_);
lean_dec_ref(v_as_3773_);
lean_dec_ref(v_inst_3771_);
v___x_3787_ = lean_apply_2(v_toPure_3779_, lean_box(0), v___x_3783_);
v___x_3788_ = lean_apply_4(v_map_3780_, lean_box(0), lean_box(0), v___x_3782_, v___x_3787_);
return v___x_3788_;
}
else
{
size_t v___x_3789_; size_t v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3789_ = lean_usize_of_nat(v___x_3784_);
v___x_3790_ = lean_usize_of_nat(v_stop_3775_);
v___x_3791_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3771_, v___f_3781_, v_as_3773_, v___x_3789_, v___x_3790_, v___x_3783_);
v___x_3792_ = lean_apply_4(v_map_3780_, lean_box(0), lean_box(0), v___x_3782_, v___x_3791_);
return v___x_3792_;
}
}
else
{
uint8_t v___x_3793_; 
v___x_3793_ = lean_nat_dec_lt(v_stop_3775_, v_start_3774_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
lean_inc(v_toPure_3779_);
lean_dec_ref(v___f_3781_);
lean_dec_ref(v_as_3773_);
lean_dec_ref(v_inst_3771_);
v___x_3794_ = lean_apply_2(v_toPure_3779_, lean_box(0), v___x_3783_);
v___x_3795_ = lean_apply_4(v_map_3780_, lean_box(0), lean_box(0), v___x_3782_, v___x_3794_);
return v___x_3795_;
}
else
{
size_t v___x_3796_; size_t v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3796_ = lean_usize_of_nat(v_start_3774_);
v___x_3797_ = lean_usize_of_nat(v_stop_3775_);
v___x_3798_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3771_, v___f_3781_, v_as_3773_, v___x_3796_, v___x_3797_, v___x_3783_);
v___x_3799_ = lean_apply_4(v_map_3780_, lean_box(0), lean_box(0), v___x_3782_, v___x_3798_);
return v___x_3799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___boxed(lean_object* v_inst_3800_, lean_object* v_p_3801_, lean_object* v_as_3802_, lean_object* v_start_3803_, lean_object* v_stop_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_Array_filterRevM___redArg(v_inst_3800_, v_p_3801_, v_as_3802_, v_start_3803_, v_stop_3804_);
lean_dec(v_stop_3804_);
lean_dec(v_start_3803_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM(lean_object* v_m_3806_, lean_object* v_00_u03b1_3807_, lean_object* v_inst_3808_, lean_object* v_p_3809_, lean_object* v_as_3810_, lean_object* v_start_3811_, lean_object* v_stop_3812_){
_start:
{
lean_object* v_toApplicative_3813_; lean_object* v_toFunctor_3814_; lean_object* v_toBind_3815_; lean_object* v_toPure_3816_; lean_object* v_map_3817_; lean_object* v___f_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
v_toApplicative_3813_ = lean_ctor_get(v_inst_3808_, 0);
v_toFunctor_3814_ = lean_ctor_get(v_toApplicative_3813_, 0);
v_toBind_3815_ = lean_ctor_get(v_inst_3808_, 1);
v_toPure_3816_ = lean_ctor_get(v_toApplicative_3813_, 1);
v_map_3817_ = lean_ctor_get(v_toFunctor_3814_, 0);
lean_inc(v_map_3817_);
lean_inc(v_toBind_3815_);
lean_inc(v_toPure_3816_);
v___f_3818_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3818_, 0, v_toPure_3816_);
lean_closure_set(v___f_3818_, 1, v_p_3809_);
lean_closure_set(v___f_3818_, 2, v_toBind_3815_);
v___x_3819_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3820_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3821_ = lean_array_get_size(v_as_3810_);
v___x_3822_ = lean_nat_dec_le(v_start_3811_, v___x_3821_);
if (v___x_3822_ == 0)
{
uint8_t v___x_3823_; 
v___x_3823_ = lean_nat_dec_lt(v_stop_3812_, v___x_3821_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; lean_object* v___x_3825_; 
lean_inc(v_toPure_3816_);
lean_dec_ref(v___f_3818_);
lean_dec_ref(v_as_3810_);
lean_dec_ref(v_inst_3808_);
v___x_3824_ = lean_apply_2(v_toPure_3816_, lean_box(0), v___x_3820_);
v___x_3825_ = lean_apply_4(v_map_3817_, lean_box(0), lean_box(0), v___x_3819_, v___x_3824_);
return v___x_3825_;
}
else
{
size_t v___x_3826_; size_t v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3826_ = lean_usize_of_nat(v___x_3821_);
v___x_3827_ = lean_usize_of_nat(v_stop_3812_);
v___x_3828_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3808_, v___f_3818_, v_as_3810_, v___x_3826_, v___x_3827_, v___x_3820_);
v___x_3829_ = lean_apply_4(v_map_3817_, lean_box(0), lean_box(0), v___x_3819_, v___x_3828_);
return v___x_3829_;
}
}
else
{
uint8_t v___x_3830_; 
v___x_3830_ = lean_nat_dec_lt(v_stop_3812_, v_start_3811_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
lean_inc(v_toPure_3816_);
lean_dec_ref(v___f_3818_);
lean_dec_ref(v_as_3810_);
lean_dec_ref(v_inst_3808_);
v___x_3831_ = lean_apply_2(v_toPure_3816_, lean_box(0), v___x_3820_);
v___x_3832_ = lean_apply_4(v_map_3817_, lean_box(0), lean_box(0), v___x_3819_, v___x_3831_);
return v___x_3832_;
}
else
{
size_t v___x_3833_; size_t v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3833_ = lean_usize_of_nat(v_start_3811_);
v___x_3834_ = lean_usize_of_nat(v_stop_3812_);
v___x_3835_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3808_, v___f_3818_, v_as_3810_, v___x_3833_, v___x_3834_, v___x_3820_);
v___x_3836_ = lean_apply_4(v_map_3817_, lean_box(0), lean_box(0), v___x_3819_, v___x_3835_);
return v___x_3836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___boxed(lean_object* v_m_3837_, lean_object* v_00_u03b1_3838_, lean_object* v_inst_3839_, lean_object* v_p_3840_, lean_object* v_as_3841_, lean_object* v_start_3842_, lean_object* v_stop_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Array_filterRevM(v_m_3837_, v_00_u03b1_3838_, v_inst_3839_, v_p_3840_, v_as_3841_, v_start_3842_, v_stop_3843_);
lean_dec(v_stop_3843_);
lean_dec(v_start_3842_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__0(lean_object* v_toPure_3845_, lean_object* v_bs_3846_, lean_object* v_____do__lift_3847_){
_start:
{
if (lean_obj_tag(v_____do__lift_3847_) == 0)
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_apply_2(v_toPure_3845_, lean_box(0), v_bs_3846_);
return v___x_3848_;
}
else
{
lean_object* v_val_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v_val_3849_ = lean_ctor_get(v_____do__lift_3847_, 0);
lean_inc(v_val_3849_);
lean_dec_ref_known(v_____do__lift_3847_, 1);
v___x_3850_ = lean_array_push(v_bs_3846_, v_val_3849_);
v___x_3851_ = lean_apply_2(v_toPure_3845_, lean_box(0), v___x_3850_);
return v___x_3851_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__1(lean_object* v_toPure_3852_, lean_object* v_f_3853_, lean_object* v_toBind_3854_, lean_object* v_bs_3855_, lean_object* v_a_3856_){
_start:
{
lean_object* v___f_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___f_3857_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3857_, 0, v_toPure_3852_);
lean_closure_set(v___f_3857_, 1, v_bs_3855_);
v___x_3858_ = lean_apply_1(v_f_3853_, v_a_3856_);
v___x_3859_ = lean_apply_4(v_toBind_3854_, lean_box(0), lean_box(0), v___x_3858_, v___f_3857_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg(lean_object* v_inst_3860_, lean_object* v_f_3861_, lean_object* v_as_3862_, lean_object* v_start_3863_, lean_object* v_stop_3864_){
_start:
{
lean_object* v_toApplicative_3865_; lean_object* v_toBind_3866_; lean_object* v_toPure_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; 
v_toApplicative_3865_ = lean_ctor_get(v_inst_3860_, 0);
v_toBind_3866_ = lean_ctor_get(v_inst_3860_, 1);
v_toPure_3867_ = lean_ctor_get(v_toApplicative_3865_, 1);
v___x_3868_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3869_ = lean_nat_dec_lt(v_start_3863_, v_stop_3864_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; 
lean_inc(v_toPure_3867_);
lean_dec_ref(v_as_3862_);
lean_dec(v_f_3861_);
lean_dec_ref(v_inst_3860_);
v___x_3870_ = lean_apply_2(v_toPure_3867_, lean_box(0), v___x_3868_);
return v___x_3870_;
}
else
{
lean_object* v___f_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; 
lean_inc(v_toBind_3866_);
lean_inc(v_toPure_3867_);
v___f_3871_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3871_, 0, v_toPure_3867_);
lean_closure_set(v___f_3871_, 1, v_f_3861_);
lean_closure_set(v___f_3871_, 2, v_toBind_3866_);
v___x_3872_ = lean_array_get_size(v_as_3862_);
v___x_3873_ = lean_nat_dec_le(v_stop_3864_, v___x_3872_);
if (v___x_3873_ == 0)
{
uint8_t v___x_3874_; 
v___x_3874_ = lean_nat_dec_lt(v_start_3863_, v___x_3872_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3875_; 
lean_inc(v_toPure_3867_);
lean_dec_ref(v___f_3871_);
lean_dec_ref(v_as_3862_);
lean_dec_ref(v_inst_3860_);
v___x_3875_ = lean_apply_2(v_toPure_3867_, lean_box(0), v___x_3868_);
return v___x_3875_;
}
else
{
size_t v___x_3876_; size_t v___x_3877_; lean_object* v___x_3878_; 
v___x_3876_ = lean_usize_of_nat(v_start_3863_);
v___x_3877_ = lean_usize_of_nat(v___x_3872_);
v___x_3878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3860_, v___f_3871_, v_as_3862_, v___x_3876_, v___x_3877_, v___x_3868_);
return v___x_3878_;
}
}
else
{
size_t v___x_3879_; size_t v___x_3880_; lean_object* v___x_3881_; 
v___x_3879_ = lean_usize_of_nat(v_start_3863_);
v___x_3880_ = lean_usize_of_nat(v_stop_3864_);
v___x_3881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3860_, v___f_3871_, v_as_3862_, v___x_3879_, v___x_3880_, v___x_3868_);
return v___x_3881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___boxed(lean_object* v_inst_3882_, lean_object* v_f_3883_, lean_object* v_as_3884_, lean_object* v_start_3885_, lean_object* v_stop_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Array_filterMapM___redArg(v_inst_3882_, v_f_3883_, v_as_3884_, v_start_3885_, v_stop_3886_);
lean_dec(v_stop_3886_);
lean_dec(v_start_3885_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM(lean_object* v_00_u03b1_3888_, lean_object* v_m_3889_, lean_object* v_00_u03b2_3890_, lean_object* v_inst_3891_, lean_object* v_f_3892_, lean_object* v_as_3893_, lean_object* v_start_3894_, lean_object* v_stop_3895_){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Array_filterMapM___redArg(v_inst_3891_, v_f_3892_, v_as_3893_, v_start_3894_, v_stop_3895_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___boxed(lean_object* v_00_u03b1_3897_, lean_object* v_m_3898_, lean_object* v_00_u03b2_3899_, lean_object* v_inst_3900_, lean_object* v_f_3901_, lean_object* v_as_3902_, lean_object* v_start_3903_, lean_object* v_stop_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Array_filterMapM(v_00_u03b1_3897_, v_m_3898_, v_00_u03b2_3899_, v_inst_3900_, v_f_3901_, v_as_3902_, v_start_3903_, v_stop_3904_);
lean_dec(v_stop_3904_);
lean_dec(v_start_3903_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg(lean_object* v_f_3906_, lean_object* v_as_3907_, lean_object* v_start_3908_, lean_object* v_stop_3909_){
_start:
{
lean_object* v___f_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___f_3910_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3910_, 0, v_f_3906_);
v___x_3911_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3912_ = l_Array_filterMapM___redArg(v___x_3911_, v___f_3910_, v_as_3907_, v_start_3908_, v_stop_3909_);
return v___x_3912_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg___boxed(lean_object* v_f_3913_, lean_object* v_as_3914_, lean_object* v_start_3915_, lean_object* v_stop_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l_Array_filterMap___redArg(v_f_3913_, v_as_3914_, v_start_3915_, v_stop_3916_);
lean_dec(v_stop_3916_);
lean_dec(v_start_3915_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap(lean_object* v_00_u03b1_3918_, lean_object* v_00_u03b2_3919_, lean_object* v_f_3920_, lean_object* v_as_3921_, lean_object* v_start_3922_, lean_object* v_stop_3923_){
_start:
{
lean_object* v___f_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___f_3924_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3924_, 0, v_f_3920_);
v___x_3925_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3926_ = l_Array_filterMapM___redArg(v___x_3925_, v___f_3924_, v_as_3921_, v_start_3922_, v_stop_3923_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___boxed(lean_object* v_00_u03b1_3927_, lean_object* v_00_u03b2_3928_, lean_object* v_f_3929_, lean_object* v_as_3930_, lean_object* v_start_3931_, lean_object* v_stop_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l_Array_filterMap(v_00_u03b1_3927_, v_00_u03b2_3928_, v_f_3929_, v_as_3930_, v_start_3931_, v_stop_3932_);
lean_dec(v_stop_3932_);
lean_dec(v_start_3931_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg___lam__0(lean_object* v_lt_3934_, lean_object* v_x1_3935_, lean_object* v_x2_3936_){
_start:
{
lean_object* v___x_3937_; uint8_t v___x_3938_; 
lean_inc(v_x2_3936_);
lean_inc(v_x1_3935_);
v___x_3937_ = lean_apply_2(v_lt_3934_, v_x1_3935_, v_x2_3936_);
v___x_3938_ = lean_unbox(v___x_3937_);
if (v___x_3938_ == 0)
{
lean_dec(v_x2_3936_);
return v_x1_3935_;
}
else
{
lean_dec(v_x1_3935_);
return v_x2_3936_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg(lean_object* v_as_3939_, lean_object* v_lt_3940_){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; uint8_t v___x_3943_; 
v___x_3941_ = lean_unsigned_to_nat(0u);
v___x_3942_ = lean_array_get_size(v_as_3939_);
v___x_3943_ = lean_nat_dec_lt(v___x_3941_, v___x_3942_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; 
lean_dec_ref(v_lt_3940_);
lean_dec_ref(v_as_3939_);
v___x_3944_ = lean_box(0);
return v___x_3944_;
}
else
{
lean_object* v_a0_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; uint8_t v___x_3948_; 
v_a0_3945_ = lean_array_fget(v_as_3939_, v___x_3941_);
v___x_3946_ = lean_unsigned_to_nat(1u);
v___x_3947_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3948_ = lean_nat_dec_lt(v___x_3946_, v___x_3942_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; 
lean_dec_ref(v_lt_3940_);
lean_dec_ref(v_as_3939_);
v___x_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3949_, 0, v_a0_3945_);
return v___x_3949_;
}
else
{
lean_object* v___f_3950_; uint8_t v___x_3951_; 
v___f_3950_ = lean_alloc_closure((void*)(l_Array_getMax_x3f___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3950_, 0, v_lt_3940_);
v___x_3951_ = lean_nat_dec_le(v___x_3942_, v___x_3942_);
if (v___x_3951_ == 0)
{
if (v___x_3948_ == 0)
{
lean_object* v___x_3952_; 
lean_dec_ref(v___f_3950_);
lean_dec_ref(v_as_3939_);
v___x_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3952_, 0, v_a0_3945_);
return v___x_3952_;
}
else
{
size_t v___x_3953_; size_t v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3953_ = ((size_t)1ULL);
v___x_3954_ = lean_usize_of_nat(v___x_3942_);
v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3947_, v___f_3950_, v_as_3939_, v___x_3953_, v___x_3954_, v_a0_3945_);
v___x_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3955_);
return v___x_3956_;
}
}
else
{
size_t v___x_3957_; size_t v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3957_ = ((size_t)1ULL);
v___x_3958_ = lean_usize_of_nat(v___x_3942_);
v___x_3959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3947_, v___f_3950_, v_as_3939_, v___x_3957_, v___x_3958_, v_a0_3945_);
v___x_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3959_);
return v___x_3960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f(lean_object* v_00_u03b1_3961_, lean_object* v_as_3962_, lean_object* v_lt_3963_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_Array_getMax_x3f___redArg(v_as_3962_, v_lt_3963_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg___lam__0(lean_object* v_p_3965_, lean_object* v_a_3966_, lean_object* v_x_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v_fst_3969_; lean_object* v_snd_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3986_; 
v_fst_3969_ = lean_ctor_get(v___y_3968_, 0);
v_snd_3970_ = lean_ctor_get(v___y_3968_, 1);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___y_3968_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3972_ = v___y_3968_;
v_isShared_3973_ = v_isSharedCheck_3986_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_snd_3970_);
lean_inc(v_fst_3969_);
lean_dec(v___y_3968_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3986_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; uint8_t v___x_3975_; 
lean_inc(v_a_3966_);
v___x_3974_ = lean_apply_1(v_p_3965_, v_a_3966_);
v___x_3975_ = lean_unbox(v___x_3974_);
if (v___x_3975_ == 0)
{
lean_object* v___x_3976_; lean_object* v___x_3978_; 
v___x_3976_ = lean_array_push(v_snd_3970_, v_a_3966_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 1, v___x_3976_);
v___x_3978_ = v___x_3972_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_fst_3969_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
lean_object* v___x_3979_; 
v___x_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
return v___x_3979_;
}
}
else
{
lean_object* v___x_3981_; lean_object* v___x_3983_; 
v___x_3981_ = lean_array_push(v_fst_3969_, v_a_3966_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v___x_3981_);
v___x_3983_ = v___x_3972_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3981_);
lean_ctor_set(v_reuseFailAlloc_3985_, 1, v_snd_3970_);
v___x_3983_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
lean_object* v___x_3984_; 
v___x_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3983_);
return v___x_3984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg(lean_object* v_p_3989_, lean_object* v_as_3990_){
_start:
{
lean_object* v___f_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; size_t v_sz_3994_; size_t v___x_3995_; lean_object* v___x_3996_; lean_object* v_fst_3997_; lean_object* v_snd_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
v___f_3991_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3991_, 0, v_p_3989_);
v___x_3992_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3993_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_3994_ = lean_array_size(v_as_3990_);
v___x_3995_ = ((size_t)0ULL);
v___x_3996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_3992_, v_as_3990_, v___f_3991_, v_sz_3994_, v___x_3995_, v___x_3993_);
v_fst_3997_ = lean_ctor_get(v___x_3996_, 0);
v_snd_3998_ = lean_ctor_get(v___x_3996_, 1);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3996_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_snd_3998_);
lean_inc(v_fst_3997_);
lean_dec(v___x_3996_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_fst_3997_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_snd_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition(lean_object* v_00_u03b1_4006_, lean_object* v_p_4007_, lean_object* v_as_4008_){
_start:
{
lean_object* v___f_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; size_t v_sz_4012_; size_t v___x_4013_; lean_object* v___x_4014_; lean_object* v_fst_4015_; lean_object* v_snd_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
v___f_4009_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4009_, 0, v_p_4007_);
v___x_4010_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4011_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_4012_ = lean_array_size(v_as_4008_);
v___x_4013_ = ((size_t)0ULL);
v___x_4014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_4010_, v_as_4008_, v___f_4009_, v_sz_4012_, v___x_4013_, v___x_4011_);
v_fst_4015_ = lean_ctor_get(v___x_4014_, 0);
v_snd_4016_ = lean_ctor_get(v___x_4014_, 1);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_4014_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_snd_4016_);
lean_inc(v_fst_4015_);
lean_dec(v___x_4014_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_fst_4015_);
lean_ctor_set(v_reuseFailAlloc_4022_, 1, v_snd_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile___redArg(lean_object* v_p_4024_, lean_object* v_as_4025_){
_start:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; uint8_t v___x_4028_; 
v___x_4026_ = lean_unsigned_to_nat(0u);
v___x_4027_ = lean_array_get_size(v_as_4025_);
v___x_4028_ = lean_nat_dec_lt(v___x_4026_, v___x_4027_);
if (v___x_4028_ == 0)
{
lean_dec_ref(v_p_4024_);
return v_as_4025_;
}
else
{
lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; uint8_t v___x_4033_; 
v___x_4029_ = lean_unsigned_to_nat(1u);
v___x_4030_ = lean_nat_sub(v___x_4027_, v___x_4029_);
v___x_4031_ = lean_array_fget_borrowed(v_as_4025_, v___x_4030_);
lean_dec(v___x_4030_);
lean_inc_ref(v_p_4024_);
lean_inc(v___x_4031_);
v___x_4032_ = lean_apply_1(v_p_4024_, v___x_4031_);
v___x_4033_ = lean_unbox(v___x_4032_);
if (v___x_4033_ == 0)
{
lean_dec_ref(v_p_4024_);
return v_as_4025_;
}
else
{
lean_object* v___x_4034_; 
v___x_4034_ = lean_array_pop(v_as_4025_);
v_as_4025_ = v___x_4034_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile(lean_object* v_00_u03b1_4036_, lean_object* v_p_4037_, lean_object* v_as_4038_){
_start:
{
lean_object* v___x_4039_; 
v___x_4039_ = l_Array_popWhile___redArg(v_p_4037_, v_as_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(lean_object* v_p_4040_, lean_object* v_as_4041_, lean_object* v_i_4042_, lean_object* v_acc_4043_){
_start:
{
lean_object* v___x_4044_; uint8_t v___x_4045_; 
v___x_4044_ = lean_array_get_size(v_as_4041_);
v___x_4045_ = lean_nat_dec_lt(v_i_4042_, v___x_4044_);
if (v___x_4045_ == 0)
{
lean_dec(v_i_4042_);
lean_dec_ref(v_p_4040_);
return v_acc_4043_;
}
else
{
lean_object* v_a_4046_; lean_object* v___x_4047_; uint8_t v___x_4048_; 
v_a_4046_ = lean_array_fget_borrowed(v_as_4041_, v_i_4042_);
lean_inc_ref(v_p_4040_);
lean_inc(v_a_4046_);
v___x_4047_ = lean_apply_1(v_p_4040_, v_a_4046_);
v___x_4048_ = lean_unbox(v___x_4047_);
if (v___x_4048_ == 0)
{
lean_dec(v_i_4042_);
lean_dec_ref(v_p_4040_);
return v_acc_4043_;
}
else
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4049_ = lean_unsigned_to_nat(1u);
v___x_4050_ = lean_nat_add(v_i_4042_, v___x_4049_);
lean_dec(v_i_4042_);
lean_inc(v_a_4046_);
v___x_4051_ = lean_array_push(v_acc_4043_, v_a_4046_);
v_i_4042_ = v___x_4050_;
v_acc_4043_ = v___x_4051_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg___boxed(lean_object* v_p_4053_, lean_object* v_as_4054_, lean_object* v_i_4055_, lean_object* v_acc_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4053_, v_as_4054_, v_i_4055_, v_acc_4056_);
lean_dec_ref(v_as_4054_);
return v_res_4057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(lean_object* v_00_u03b1_4058_, lean_object* v_p_4059_, lean_object* v_as_4060_, lean_object* v_i_4061_, lean_object* v_acc_4062_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4059_, v_as_4060_, v_i_4061_, v_acc_4062_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___boxed(lean_object* v_00_u03b1_4064_, lean_object* v_p_4065_, lean_object* v_as_4066_, lean_object* v_i_4067_, lean_object* v_acc_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(v_00_u03b1_4064_, v_p_4065_, v_as_4066_, v_i_4067_, v_acc_4068_);
lean_dec_ref(v_as_4066_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg(lean_object* v_p_4070_, lean_object* v_as_4071_){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4072_ = lean_unsigned_to_nat(0u);
v___x_4073_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4074_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4070_, v_as_4071_, v___x_4072_, v___x_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg___boxed(lean_object* v_p_4075_, lean_object* v_as_4076_){
_start:
{
lean_object* v_res_4077_; 
v_res_4077_ = l_Array_takeWhile___redArg(v_p_4075_, v_as_4076_);
lean_dec_ref(v_as_4076_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile(lean_object* v_00_u03b1_4078_, lean_object* v_p_4079_, lean_object* v_as_4080_){
_start:
{
lean_object* v___x_4081_; 
v___x_4081_ = l_Array_takeWhile___redArg(v_p_4079_, v_as_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___boxed(lean_object* v_00_u03b1_4082_, lean_object* v_p_4083_, lean_object* v_as_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l_Array_takeWhile(v_00_u03b1_4082_, v_p_4083_, v_as_4084_);
lean_dec_ref(v_as_4084_);
return v_res_4085_;
}
}
static lean_object* _init_l_Array_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx___redArg(lean_object* v_xs_4087_, lean_object* v_i_4088_){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; uint8_t v___x_4092_; 
v___x_4089_ = lean_unsigned_to_nat(1u);
v___x_4090_ = lean_nat_add(v_i_4088_, v___x_4089_);
v___x_4091_ = lean_array_get_size(v_xs_4087_);
v___x_4092_ = lean_nat_dec_lt(v___x_4090_, v___x_4091_);
if (v___x_4092_ == 0)
{
lean_object* v___x_4093_; 
lean_dec(v___x_4090_);
lean_dec(v_i_4088_);
v___x_4093_ = lean_array_pop(v_xs_4087_);
return v___x_4093_;
}
else
{
lean_object* v_xs_x27_4094_; 
v_xs_x27_4094_ = lean_array_fswap(v_xs_4087_, v___x_4090_, v_i_4088_);
lean_dec(v_i_4088_);
v_xs_4087_ = v_xs_x27_4094_;
v_i_4088_ = v___x_4090_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx(lean_object* v_00_u03b1_4096_, lean_object* v_xs_4097_, lean_object* v_i_4098_, lean_object* v_h_4099_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Array_eraseIdx___redArg(v_xs_4097_, v_i_4098_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds___redArg(lean_object* v_xs_4101_, lean_object* v_i_4102_){
_start:
{
lean_object* v___x_4103_; uint8_t v___x_4104_; 
v___x_4103_ = lean_array_get_size(v_xs_4101_);
v___x_4104_ = lean_nat_dec_lt(v_i_4102_, v___x_4103_);
if (v___x_4104_ == 0)
{
lean_dec(v_i_4102_);
return v_xs_4101_;
}
else
{
lean_object* v___x_4105_; 
v___x_4105_ = l_Array_eraseIdx___redArg(v_xs_4101_, v_i_4102_);
return v___x_4105_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds(lean_object* v_00_u03b1_4106_, lean_object* v_xs_4107_, lean_object* v_i_4108_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l_Array_eraseIdxIfInBounds___redArg(v_xs_4107_, v_i_4108_);
return v___x_4109_;
}
}
static lean_object* _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4110_; 
v___x_4110_ = l_Array_instInhabited(lean_box(0));
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(lean_object* v_msg_4111_){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = lean_obj_once(&l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0, &l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0_once, _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0);
v___x_4113_ = lean_panic_fn_borrowed(v___x_4112_, v_msg_4111_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0(lean_object* v_00_u03b1_4114_, lean_object* v_msg_4115_){
_start:
{
lean_object* v___x_4116_; 
v___x_4116_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v_msg_4115_);
return v___x_4116_;
}
}
static lean_object* _init_l_Array_eraseIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4119_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4120_ = lean_unsigned_to_nat(47u);
v___x_4121_ = lean_unsigned_to_nat(1842u);
v___x_4122_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__0));
v___x_4123_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4124_ = l_mkPanicMessageWithDecl(v___x_4123_, v___x_4122_, v___x_4121_, v___x_4120_, v___x_4119_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21___redArg(lean_object* v_xs_4125_, lean_object* v_i_4126_){
_start:
{
lean_object* v___x_4127_; uint8_t v___x_4128_; 
v___x_4127_ = lean_array_get_size(v_xs_4125_);
v___x_4128_ = lean_nat_dec_lt(v_i_4126_, v___x_4127_);
if (v___x_4128_ == 0)
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
lean_dec(v_i_4126_);
lean_dec_ref(v_xs_4125_);
v___x_4129_ = lean_obj_once(&l_Array_eraseIdx_x21___redArg___closed__2, &l_Array_eraseIdx_x21___redArg___closed__2_once, _init_l_Array_eraseIdx_x21___redArg___closed__2);
v___x_4130_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4129_);
return v___x_4130_;
}
else
{
lean_object* v___x_4131_; 
v___x_4131_ = l_Array_eraseIdx___redArg(v_xs_4125_, v_i_4126_);
return v___x_4131_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21(lean_object* v_00_u03b1_4132_, lean_object* v_xs_4133_, lean_object* v_i_4134_){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = l_Array_eraseIdx_x21___redArg(v_xs_4133_, v_i_4134_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_Array_erase___redArg(lean_object* v_inst_4136_, lean_object* v_as_4137_, lean_object* v_a_4138_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = l_Array_finIdxOf_x3f___redArg(v_inst_4136_, v_as_4137_, v_a_4138_);
if (lean_obj_tag(v___x_4139_) == 0)
{
return v_as_4137_;
}
else
{
lean_object* v_val_4140_; lean_object* v___x_4141_; 
v_val_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_val_4140_);
lean_dec_ref_known(v___x_4139_, 1);
v___x_4141_ = l_Array_eraseIdx___redArg(v_as_4137_, v_val_4140_);
return v___x_4141_;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase(lean_object* v_00_u03b1_4142_, lean_object* v_inst_4143_, lean_object* v_as_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v___x_4146_; 
v___x_4146_ = l_Array_erase___redArg(v_inst_4143_, v_as_4144_, v_a_4145_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseP___redArg(lean_object* v_as_4147_, lean_object* v_p_4148_){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4149_ = lean_unsigned_to_nat(0u);
v___x_4150_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_4148_, v_as_4147_, v___x_4149_);
if (lean_obj_tag(v___x_4150_) == 0)
{
return v_as_4147_;
}
else
{
lean_object* v_val_4151_; lean_object* v___x_4152_; 
v_val_4151_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_val_4151_);
lean_dec_ref_known(v___x_4150_, 1);
v___x_4152_ = l_Array_eraseIdx___redArg(v_as_4147_, v_val_4151_);
return v___x_4152_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseP(lean_object* v_00_u03b1_4153_, lean_object* v_as_4154_, lean_object* v_p_4155_){
_start:
{
lean_object* v___x_4156_; 
v___x_4156_ = l_Array_eraseP___redArg(v_as_4154_, v_p_4155_);
return v___x_4156_;
}
}
static lean_object* _init_l_Array_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_4157_; 
v___x_4157_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(lean_object* v_i_4158_, lean_object* v_as_4159_, lean_object* v_j_4160_){
_start:
{
uint8_t v___x_4161_; 
v___x_4161_ = lean_nat_dec_lt(v_i_4158_, v_j_4160_);
if (v___x_4161_ == 0)
{
lean_dec(v_j_4160_);
return v_as_4159_;
}
else
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v_as_4164_; 
v___x_4162_ = lean_unsigned_to_nat(1u);
v___x_4163_ = lean_nat_sub(v_j_4160_, v___x_4162_);
v_as_4164_ = lean_array_fswap(v_as_4159_, v___x_4163_, v_j_4160_);
lean_dec(v_j_4160_);
v_as_4159_ = v_as_4164_;
v_j_4160_ = v___x_4163_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg___boxed(lean_object* v_i_4166_, lean_object* v_as_4167_, lean_object* v_j_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4166_, v_as_4167_, v_j_4168_);
lean_dec(v_i_4166_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object* v_00_u03b1_4170_, lean_object* v_i_4171_, lean_object* v_as_4172_, lean_object* v_j_4173_){
_start:
{
lean_object* v___x_4174_; 
v___x_4174_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4171_, v_as_4172_, v_j_4173_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___boxed(lean_object* v_00_u03b1_4175_, lean_object* v_i_4176_, lean_object* v_as_4177_, lean_object* v_j_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(v_00_u03b1_4175_, v_i_4176_, v_as_4177_, v_j_4178_);
lean_dec(v_i_4176_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg(lean_object* v_as_4180_, lean_object* v_i_4181_, lean_object* v_a_4182_){
_start:
{
lean_object* v_j_4183_; lean_object* v_as_4184_; lean_object* v___x_4185_; 
v_j_4183_ = lean_array_get_size(v_as_4180_);
v_as_4184_ = lean_array_push(v_as_4180_, v_a_4182_);
v___x_4185_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4181_, v_as_4184_, v_j_4183_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg___boxed(lean_object* v_as_4186_, lean_object* v_i_4187_, lean_object* v_a_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Array_insertIdx___redArg(v_as_4186_, v_i_4187_, v_a_4188_);
lean_dec(v_i_4187_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx(lean_object* v_00_u03b1_4190_, lean_object* v_as_4191_, lean_object* v_i_4192_, lean_object* v_a_4193_, lean_object* v_x_4194_){
_start:
{
lean_object* v_j_4195_; lean_object* v_as_4196_; lean_object* v___x_4197_; 
v_j_4195_ = lean_array_get_size(v_as_4191_);
v_as_4196_ = lean_array_push(v_as_4191_, v_a_4193_);
v___x_4197_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4192_, v_as_4196_, v_j_4195_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___boxed(lean_object* v_00_u03b1_4198_, lean_object* v_as_4199_, lean_object* v_i_4200_, lean_object* v_a_4201_, lean_object* v_x_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l_Array_insertIdx(v_00_u03b1_4198_, v_as_4199_, v_i_4200_, v_a_4201_, v_x_4202_);
lean_dec(v_i_4200_);
return v_res_4203_;
}
}
static lean_object* _init_l_Array_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4205_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4206_ = lean_unsigned_to_nat(7u);
v___x_4207_ = lean_unsigned_to_nat(1924u);
v___x_4208_ = ((lean_object*)(l_Array_insertIdx_x21___redArg___closed__0));
v___x_4209_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4210_ = l_mkPanicMessageWithDecl(v___x_4209_, v___x_4208_, v___x_4207_, v___x_4206_, v___x_4205_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg(lean_object* v_as_4211_, lean_object* v_i_4212_, lean_object* v_a_4213_){
_start:
{
lean_object* v___x_4214_; uint8_t v___x_4215_; 
v___x_4214_ = lean_array_get_size(v_as_4211_);
v___x_4215_ = lean_nat_dec_le(v_i_4212_, v___x_4214_);
if (v___x_4215_ == 0)
{
lean_object* v___x_4216_; lean_object* v___x_4217_; 
lean_dec(v_a_4213_);
lean_dec_ref(v_as_4211_);
v___x_4216_ = lean_obj_once(&l_Array_insertIdx_x21___redArg___closed__1, &l_Array_insertIdx_x21___redArg___closed__1_once, _init_l_Array_insertIdx_x21___redArg___closed__1);
v___x_4217_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4216_);
return v___x_4217_;
}
else
{
lean_object* v_as_4218_; lean_object* v___x_4219_; 
v_as_4218_ = lean_array_push(v_as_4211_, v_a_4213_);
v___x_4219_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4212_, v_as_4218_, v___x_4214_);
return v___x_4219_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg___boxed(lean_object* v_as_4220_, lean_object* v_i_4221_, lean_object* v_a_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l_Array_insertIdx_x21___redArg(v_as_4220_, v_i_4221_, v_a_4222_);
lean_dec(v_i_4221_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21(lean_object* v_00_u03b1_4224_, lean_object* v_as_4225_, lean_object* v_i_4226_, lean_object* v_a_4227_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l_Array_insertIdx_x21___redArg(v_as_4225_, v_i_4226_, v_a_4227_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___boxed(lean_object* v_00_u03b1_4229_, lean_object* v_as_4230_, lean_object* v_i_4231_, lean_object* v_a_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_Array_insertIdx_x21(v_00_u03b1_4229_, v_as_4230_, v_i_4231_, v_a_4232_);
lean_dec(v_i_4231_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg(lean_object* v_as_4234_, lean_object* v_i_4235_, lean_object* v_a_4236_){
_start:
{
lean_object* v___x_4237_; uint8_t v___x_4238_; 
v___x_4237_ = lean_array_get_size(v_as_4234_);
v___x_4238_ = lean_nat_dec_le(v_i_4235_, v___x_4237_);
if (v___x_4238_ == 0)
{
lean_dec(v_a_4236_);
return v_as_4234_;
}
else
{
lean_object* v_as_4239_; lean_object* v___x_4240_; 
v_as_4239_ = lean_array_push(v_as_4234_, v_a_4236_);
v___x_4240_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4235_, v_as_4239_, v___x_4237_);
return v___x_4240_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg___boxed(lean_object* v_as_4241_, lean_object* v_i_4242_, lean_object* v_a_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Array_insertIdxIfInBounds___redArg(v_as_4241_, v_i_4242_, v_a_4243_);
lean_dec(v_i_4242_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds(lean_object* v_00_u03b1_4245_, lean_object* v_as_4246_, lean_object* v_i_4247_, lean_object* v_a_4248_){
_start:
{
lean_object* v___x_4249_; 
v___x_4249_ = l_Array_insertIdxIfInBounds___redArg(v_as_4246_, v_i_4247_, v_a_4248_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___boxed(lean_object* v_00_u03b1_4250_, lean_object* v_as_4251_, lean_object* v_i_4252_, lean_object* v_a_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Array_insertIdxIfInBounds(v_00_u03b1_4250_, v_as_4251_, v_i_4252_, v_a_4253_);
lean_dec(v_i_4252_);
return v_res_4254_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux___redArg(lean_object* v_inst_4255_, lean_object* v_as_4256_, lean_object* v_bs_4257_, lean_object* v_i_4258_){
_start:
{
lean_object* v___x_4259_; uint8_t v___x_4260_; 
v___x_4259_ = lean_array_get_size(v_as_4256_);
v___x_4260_ = lean_nat_dec_lt(v_i_4258_, v___x_4259_);
if (v___x_4260_ == 0)
{
uint8_t v___x_4261_; 
lean_dec(v_i_4258_);
lean_dec_ref(v_inst_4255_);
v___x_4261_ = 1;
return v___x_4261_;
}
else
{
lean_object* v_a_4262_; lean_object* v_b_4263_; lean_object* v___x_4264_; uint8_t v___x_4265_; 
v_a_4262_ = lean_array_fget_borrowed(v_as_4256_, v_i_4258_);
v_b_4263_ = lean_array_fget_borrowed(v_bs_4257_, v_i_4258_);
lean_inc_ref(v_inst_4255_);
lean_inc(v_b_4263_);
lean_inc(v_a_4262_);
v___x_4264_ = lean_apply_2(v_inst_4255_, v_a_4262_, v_b_4263_);
v___x_4265_ = lean_unbox(v___x_4264_);
if (v___x_4265_ == 0)
{
uint8_t v___x_4266_; 
lean_dec(v_i_4258_);
lean_dec_ref(v_inst_4255_);
v___x_4266_ = lean_unbox(v___x_4264_);
return v___x_4266_;
}
else
{
lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4267_ = lean_unsigned_to_nat(1u);
v___x_4268_ = lean_nat_add(v_i_4258_, v___x_4267_);
lean_dec(v_i_4258_);
v_i_4258_ = v___x_4268_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___redArg___boxed(lean_object* v_inst_4270_, lean_object* v_as_4271_, lean_object* v_bs_4272_, lean_object* v_i_4273_){
_start:
{
uint8_t v_res_4274_; lean_object* v_r_4275_; 
v_res_4274_ = l_Array_isPrefixOfAux___redArg(v_inst_4270_, v_as_4271_, v_bs_4272_, v_i_4273_);
lean_dec_ref(v_bs_4272_);
lean_dec_ref(v_as_4271_);
v_r_4275_ = lean_box(v_res_4274_);
return v_r_4275_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux(lean_object* v_00_u03b1_4276_, lean_object* v_inst_4277_, lean_object* v_as_4278_, lean_object* v_bs_4279_, lean_object* v_hle_4280_, lean_object* v_i_4281_){
_start:
{
uint8_t v___x_4282_; 
v___x_4282_ = l_Array_isPrefixOfAux___redArg(v_inst_4277_, v_as_4278_, v_bs_4279_, v_i_4281_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___boxed(lean_object* v_00_u03b1_4283_, lean_object* v_inst_4284_, lean_object* v_as_4285_, lean_object* v_bs_4286_, lean_object* v_hle_4287_, lean_object* v_i_4288_){
_start:
{
uint8_t v_res_4289_; lean_object* v_r_4290_; 
v_res_4289_ = l_Array_isPrefixOfAux(v_00_u03b1_4283_, v_inst_4284_, v_as_4285_, v_bs_4286_, v_hle_4287_, v_i_4288_);
lean_dec_ref(v_bs_4286_);
lean_dec_ref(v_as_4285_);
v_r_4290_ = lean_box(v_res_4289_);
return v_r_4290_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf___redArg(lean_object* v_inst_4291_, lean_object* v_as_4292_, lean_object* v_bs_4293_){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; uint8_t v___x_4296_; 
v___x_4294_ = lean_array_get_size(v_as_4292_);
v___x_4295_ = lean_array_get_size(v_bs_4293_);
v___x_4296_ = lean_nat_dec_le(v___x_4294_, v___x_4295_);
if (v___x_4296_ == 0)
{
lean_dec_ref(v_inst_4291_);
return v___x_4296_;
}
else
{
lean_object* v___x_4297_; uint8_t v___x_4298_; 
v___x_4297_ = lean_unsigned_to_nat(0u);
v___x_4298_ = l_Array_isPrefixOfAux___redArg(v_inst_4291_, v_as_4292_, v_bs_4293_, v___x_4297_);
return v___x_4298_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___redArg___boxed(lean_object* v_inst_4299_, lean_object* v_as_4300_, lean_object* v_bs_4301_){
_start:
{
uint8_t v_res_4302_; lean_object* v_r_4303_; 
v_res_4302_ = l_Array_isPrefixOf___redArg(v_inst_4299_, v_as_4300_, v_bs_4301_);
lean_dec_ref(v_bs_4301_);
lean_dec_ref(v_as_4300_);
v_r_4303_ = lean_box(v_res_4302_);
return v_r_4303_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf(lean_object* v_00_u03b1_4304_, lean_object* v_inst_4305_, lean_object* v_as_4306_, lean_object* v_bs_4307_){
_start:
{
uint8_t v___x_4308_; 
v___x_4308_ = l_Array_isPrefixOf___redArg(v_inst_4305_, v_as_4306_, v_bs_4307_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___boxed(lean_object* v_00_u03b1_4309_, lean_object* v_inst_4310_, lean_object* v_as_4311_, lean_object* v_bs_4312_){
_start:
{
uint8_t v_res_4313_; lean_object* v_r_4314_; 
v_res_4313_ = l_Array_isPrefixOf(v_00_u03b1_4309_, v_inst_4310_, v_as_4311_, v_bs_4312_);
lean_dec_ref(v_bs_4312_);
lean_dec_ref(v_as_4311_);
v_r_4314_ = lean_box(v_res_4313_);
return v_r_4314_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0___boxed(lean_object* v_i_4315_, lean_object* v_cs_4316_, lean_object* v_inst_4317_, lean_object* v_as_4318_, lean_object* v_bs_4319_, lean_object* v_f_4320_, lean_object* v_____do__lift_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l_Array_zipWithMAux___redArg___lam__0(v_i_4315_, v_cs_4316_, v_inst_4317_, v_as_4318_, v_bs_4319_, v_f_4320_, v_____do__lift_4321_);
lean_dec(v_i_4315_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg(lean_object* v_inst_4323_, lean_object* v_as_4324_, lean_object* v_bs_4325_, lean_object* v_f_4326_, lean_object* v_i_4327_, lean_object* v_cs_4328_){
_start:
{
lean_object* v_toApplicative_4329_; lean_object* v_toBind_4330_; lean_object* v_toPure_4331_; lean_object* v___x_4332_; uint8_t v___x_4333_; 
v_toApplicative_4329_ = lean_ctor_get(v_inst_4323_, 0);
v_toBind_4330_ = lean_ctor_get(v_inst_4323_, 1);
lean_inc(v_toBind_4330_);
v_toPure_4331_ = lean_ctor_get(v_toApplicative_4329_, 1);
v___x_4332_ = lean_array_get_size(v_as_4324_);
v___x_4333_ = lean_nat_dec_lt(v_i_4327_, v___x_4332_);
if (v___x_4333_ == 0)
{
lean_object* v___x_4334_; 
lean_inc(v_toPure_4331_);
lean_dec(v_toBind_4330_);
lean_dec(v_i_4327_);
lean_dec(v_f_4326_);
lean_dec_ref(v_bs_4325_);
lean_dec_ref(v_as_4324_);
lean_dec_ref(v_inst_4323_);
v___x_4334_ = lean_apply_2(v_toPure_4331_, lean_box(0), v_cs_4328_);
return v___x_4334_;
}
else
{
lean_object* v___x_4335_; uint8_t v___x_4336_; 
v___x_4335_ = lean_array_get_size(v_bs_4325_);
v___x_4336_ = lean_nat_dec_lt(v_i_4327_, v___x_4335_);
if (v___x_4336_ == 0)
{
lean_object* v___x_4337_; 
lean_inc(v_toPure_4331_);
lean_dec(v_toBind_4330_);
lean_dec(v_i_4327_);
lean_dec(v_f_4326_);
lean_dec_ref(v_bs_4325_);
lean_dec_ref(v_as_4324_);
lean_dec_ref(v_inst_4323_);
v___x_4337_ = lean_apply_2(v_toPure_4331_, lean_box(0), v_cs_4328_);
return v___x_4337_;
}
else
{
lean_object* v___f_4338_; lean_object* v_a_4339_; lean_object* v_b_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
lean_inc(v_f_4326_);
lean_inc_ref(v_bs_4325_);
lean_inc_ref(v_as_4324_);
lean_inc(v_i_4327_);
v___f_4338_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4338_, 0, v_i_4327_);
lean_closure_set(v___f_4338_, 1, v_cs_4328_);
lean_closure_set(v___f_4338_, 2, v_inst_4323_);
lean_closure_set(v___f_4338_, 3, v_as_4324_);
lean_closure_set(v___f_4338_, 4, v_bs_4325_);
lean_closure_set(v___f_4338_, 5, v_f_4326_);
v_a_4339_ = lean_array_fget(v_as_4324_, v_i_4327_);
lean_dec_ref(v_as_4324_);
v_b_4340_ = lean_array_fget(v_bs_4325_, v_i_4327_);
lean_dec(v_i_4327_);
lean_dec_ref(v_bs_4325_);
v___x_4341_ = lean_apply_2(v_f_4326_, v_a_4339_, v_b_4340_);
v___x_4342_ = lean_apply_4(v_toBind_4330_, lean_box(0), lean_box(0), v___x_4341_, v___f_4338_);
return v___x_4342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0(lean_object* v_i_4343_, lean_object* v_cs_4344_, lean_object* v_inst_4345_, lean_object* v_as_4346_, lean_object* v_bs_4347_, lean_object* v_f_4348_, lean_object* v_____do__lift_4349_){
_start:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4350_ = lean_unsigned_to_nat(1u);
v___x_4351_ = lean_nat_add(v_i_4343_, v___x_4350_);
v___x_4352_ = lean_array_push(v_cs_4344_, v_____do__lift_4349_);
v___x_4353_ = l_Array_zipWithMAux___redArg(v_inst_4345_, v_as_4346_, v_bs_4347_, v_f_4348_, v___x_4351_, v___x_4352_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux(lean_object* v_00_u03b1_4354_, lean_object* v_00_u03b2_4355_, lean_object* v_00_u03b3_4356_, lean_object* v_m_4357_, lean_object* v_inst_4358_, lean_object* v_as_4359_, lean_object* v_bs_4360_, lean_object* v_f_4361_, lean_object* v_i_4362_, lean_object* v_cs_4363_){
_start:
{
lean_object* v___x_4364_; 
v___x_4364_ = l_Array_zipWithMAux___redArg(v_inst_4358_, v_as_4359_, v_bs_4360_, v_f_4361_, v_i_4362_, v_cs_4363_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith___redArg(lean_object* v_f_4365_, lean_object* v_as_4366_, lean_object* v_bs_4367_){
_start:
{
lean_object* v___f_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___f_4368_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4368_, 0, v_f_4365_);
v___x_4369_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4370_ = lean_unsigned_to_nat(0u);
v___x_4371_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4372_ = l_Array_zipWithMAux___redArg(v___x_4369_, v_as_4366_, v_bs_4367_, v___f_4368_, v___x_4370_, v___x_4371_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith(lean_object* v_00_u03b1_4373_, lean_object* v_00_u03b2_4374_, lean_object* v_00_u03b3_4375_, lean_object* v_f_4376_, lean_object* v_as_4377_, lean_object* v_bs_4378_){
_start:
{
lean_object* v___f_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___f_4379_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4379_, 0, v_f_4376_);
v___x_4380_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4381_ = lean_unsigned_to_nat(0u);
v___x_4382_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4383_ = l_Array_zipWithMAux___redArg(v___x_4380_, v_as_4377_, v_bs_4378_, v___f_4379_, v___x_4381_, v___x_4382_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(lean_object* v_as_4384_, lean_object* v_bs_4385_, lean_object* v_i_4386_, lean_object* v_cs_4387_){
_start:
{
lean_object* v___x_4388_; uint8_t v___x_4389_; 
v___x_4388_ = lean_array_get_size(v_as_4384_);
v___x_4389_ = lean_nat_dec_lt(v_i_4386_, v___x_4388_);
if (v___x_4389_ == 0)
{
lean_dec(v_i_4386_);
return v_cs_4387_;
}
else
{
lean_object* v___x_4390_; uint8_t v___x_4391_; 
v___x_4390_ = lean_array_get_size(v_bs_4385_);
v___x_4391_ = lean_nat_dec_lt(v_i_4386_, v___x_4390_);
if (v___x_4391_ == 0)
{
lean_dec(v_i_4386_);
return v_cs_4387_;
}
else
{
lean_object* v_a_4392_; lean_object* v_b_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v_a_4392_ = lean_array_fget_borrowed(v_as_4384_, v_i_4386_);
v_b_4393_ = lean_array_fget_borrowed(v_bs_4385_, v_i_4386_);
lean_inc(v_b_4393_);
lean_inc(v_a_4392_);
v___x_4394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4394_, 0, v_a_4392_);
lean_ctor_set(v___x_4394_, 1, v_b_4393_);
v___x_4395_ = lean_unsigned_to_nat(1u);
v___x_4396_ = lean_nat_add(v_i_4386_, v___x_4395_);
lean_dec(v_i_4386_);
v___x_4397_ = lean_array_push(v_cs_4387_, v___x_4394_);
v_i_4386_ = v___x_4396_;
v_cs_4387_ = v___x_4397_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg___boxed(lean_object* v_as_4399_, lean_object* v_bs_4400_, lean_object* v_i_4401_, lean_object* v_cs_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4399_, v_bs_4400_, v_i_4401_, v_cs_4402_);
lean_dec_ref(v_bs_4400_);
lean_dec_ref(v_as_4399_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg(lean_object* v_as_4406_, lean_object* v_bs_4407_){
_start:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4408_ = lean_unsigned_to_nat(0u);
v___x_4409_ = ((lean_object*)(l_Array_zip___redArg___closed__0));
v___x_4410_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4406_, v_bs_4407_, v___x_4408_, v___x_4409_);
return v___x_4410_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg___boxed(lean_object* v_as_4411_, lean_object* v_bs_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l_Array_zip___redArg(v_as_4411_, v_bs_4412_);
lean_dec_ref(v_bs_4412_);
lean_dec_ref(v_as_4411_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_Array_zip(lean_object* v_00_u03b1_4414_, lean_object* v_00_u03b2_4415_, lean_object* v_as_4416_, lean_object* v_bs_4417_){
_start:
{
lean_object* v___x_4418_; 
v___x_4418_ = l_Array_zip___redArg(v_as_4416_, v_bs_4417_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___boxed(lean_object* v_00_u03b1_4419_, lean_object* v_00_u03b2_4420_, lean_object* v_as_4421_, lean_object* v_bs_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l_Array_zip(v_00_u03b1_4419_, v_00_u03b2_4420_, v_as_4421_, v_bs_4422_);
lean_dec_ref(v_bs_4422_);
lean_dec_ref(v_as_4421_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0(lean_object* v_00_u03b1_4424_, lean_object* v_00_u03b2_4425_, lean_object* v_as_4426_, lean_object* v_bs_4427_, lean_object* v_i_4428_, lean_object* v_cs_4429_){
_start:
{
lean_object* v___x_4430_; 
v___x_4430_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4426_, v_bs_4427_, v_i_4428_, v_cs_4429_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___boxed(lean_object* v_00_u03b1_4431_, lean_object* v_00_u03b2_4432_, lean_object* v_as_4433_, lean_object* v_bs_4434_, lean_object* v_i_4435_, lean_object* v_cs_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_Array_zipWithMAux___at___00Array_zip_spec__0(v_00_u03b1_4431_, v_00_u03b2_4432_, v_as_4433_, v_bs_4434_, v_i_4435_, v_cs_4436_);
lean_dec_ref(v_bs_4434_);
lean_dec_ref(v_as_4433_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(lean_object* v_f_4438_, lean_object* v_as_4439_, lean_object* v_bs_4440_, lean_object* v_i_4441_, lean_object* v_cs_4442_){
_start:
{
lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4452_; lean_object* v___y_4459_; lean_object* v___x_4466_; lean_object* v___x_4467_; uint8_t v___x_4468_; 
v___x_4466_ = lean_array_get_size(v_as_4439_);
v___x_4467_ = lean_array_get_size(v_bs_4440_);
v___x_4468_ = lean_nat_dec_le(v___x_4466_, v___x_4467_);
if (v___x_4468_ == 0)
{
v___y_4459_ = v___x_4466_;
goto v___jp_4458_;
}
else
{
v___y_4459_ = v___x_4467_;
goto v___jp_4458_;
}
v___jp_4443_:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4446_ = lean_unsigned_to_nat(1u);
v___x_4447_ = lean_nat_add(v_i_4441_, v___x_4446_);
lean_dec(v_i_4441_);
lean_inc(v_f_4438_);
v___x_4448_ = lean_apply_2(v_f_4438_, v___y_4444_, v___y_4445_);
v___x_4449_ = lean_array_push(v_cs_4442_, v___x_4448_);
v_i_4441_ = v___x_4447_;
v_cs_4442_ = v___x_4449_;
goto _start;
}
v___jp_4451_:
{
lean_object* v___x_4453_; uint8_t v___x_4454_; 
v___x_4453_ = lean_array_get_size(v_bs_4440_);
v___x_4454_ = lean_nat_dec_lt(v_i_4441_, v___x_4453_);
if (v___x_4454_ == 0)
{
lean_object* v___x_4455_; 
v___x_4455_ = lean_box(0);
v___y_4444_ = v___y_4452_;
v___y_4445_ = v___x_4455_;
goto v___jp_4443_;
}
else
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = lean_array_fget_borrowed(v_bs_4440_, v_i_4441_);
lean_inc(v___x_4456_);
v___x_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4456_);
v___y_4444_ = v___y_4452_;
v___y_4445_ = v___x_4457_;
goto v___jp_4443_;
}
}
v___jp_4458_:
{
uint8_t v___x_4460_; 
v___x_4460_ = lean_nat_dec_lt(v_i_4441_, v___y_4459_);
lean_dec(v___y_4459_);
if (v___x_4460_ == 0)
{
lean_dec(v_i_4441_);
lean_dec(v_f_4438_);
return v_cs_4442_;
}
else
{
lean_object* v___x_4461_; uint8_t v___x_4462_; 
v___x_4461_ = lean_array_get_size(v_as_4439_);
v___x_4462_ = lean_nat_dec_lt(v_i_4441_, v___x_4461_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4463_; 
v___x_4463_ = lean_box(0);
v___y_4452_ = v___x_4463_;
goto v___jp_4451_;
}
else
{
lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___x_4464_ = lean_array_fget_borrowed(v_as_4439_, v_i_4441_);
lean_inc(v___x_4464_);
v___x_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4464_);
v___y_4452_ = v___x_4465_;
goto v___jp_4451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg___boxed(lean_object* v_f_4469_, lean_object* v_as_4470_, lean_object* v_bs_4471_, lean_object* v_i_4472_, lean_object* v_cs_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4469_, v_as_4470_, v_bs_4471_, v_i_4472_, v_cs_4473_);
lean_dec_ref(v_bs_4471_);
lean_dec_ref(v_as_4470_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(lean_object* v_00_u03b1_4475_, lean_object* v_00_u03b2_4476_, lean_object* v_00_u03b3_4477_, lean_object* v_f_4478_, lean_object* v_as_4479_, lean_object* v_bs_4480_, lean_object* v_i_4481_, lean_object* v_cs_4482_){
_start:
{
lean_object* v___x_4483_; 
v___x_4483_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4478_, v_as_4479_, v_bs_4480_, v_i_4481_, v_cs_4482_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___boxed(lean_object* v_00_u03b1_4484_, lean_object* v_00_u03b2_4485_, lean_object* v_00_u03b3_4486_, lean_object* v_f_4487_, lean_object* v_as_4488_, lean_object* v_bs_4489_, lean_object* v_i_4490_, lean_object* v_cs_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(v_00_u03b1_4484_, v_00_u03b2_4485_, v_00_u03b3_4486_, v_f_4487_, v_as_4488_, v_bs_4489_, v_i_4490_, v_cs_4491_);
lean_dec_ref(v_bs_4489_);
lean_dec_ref(v_as_4488_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg(lean_object* v_f_4493_, lean_object* v_as_4494_, lean_object* v_bs_4495_){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4496_ = lean_unsigned_to_nat(0u);
v___x_4497_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4498_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4493_, v_as_4494_, v_bs_4495_, v___x_4496_, v___x_4497_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg___boxed(lean_object* v_f_4499_, lean_object* v_as_4500_, lean_object* v_bs_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l_Array_zipWithAll___redArg(v_f_4499_, v_as_4500_, v_bs_4501_);
lean_dec_ref(v_bs_4501_);
lean_dec_ref(v_as_4500_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll(lean_object* v_00_u03b1_4503_, lean_object* v_00_u03b2_4504_, lean_object* v_00_u03b3_4505_, lean_object* v_f_4506_, lean_object* v_as_4507_, lean_object* v_bs_4508_){
_start:
{
lean_object* v___x_4509_; 
v___x_4509_ = l_Array_zipWithAll___redArg(v_f_4506_, v_as_4507_, v_bs_4508_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___boxed(lean_object* v_00_u03b1_4510_, lean_object* v_00_u03b2_4511_, lean_object* v_00_u03b3_4512_, lean_object* v_f_4513_, lean_object* v_as_4514_, lean_object* v_bs_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l_Array_zipWithAll(v_00_u03b1_4510_, v_00_u03b2_4511_, v_00_u03b3_4512_, v_f_4513_, v_as_4514_, v_bs_4515_);
lean_dec_ref(v_bs_4515_);
lean_dec_ref(v_as_4514_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM___redArg(lean_object* v_inst_4517_, lean_object* v_f_4518_, lean_object* v_as_4519_, lean_object* v_bs_4520_){
_start:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4521_ = lean_unsigned_to_nat(0u);
v___x_4522_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4523_ = l_Array_zipWithMAux___redArg(v_inst_4517_, v_as_4519_, v_bs_4520_, v_f_4518_, v___x_4521_, v___x_4522_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM(lean_object* v_00_u03b1_4524_, lean_object* v_00_u03b2_4525_, lean_object* v_00_u03b3_4526_, lean_object* v_m_4527_, lean_object* v_inst_4528_, lean_object* v_f_4529_, lean_object* v_as_4530_, lean_object* v_bs_4531_){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4532_ = lean_unsigned_to_nat(0u);
v___x_4533_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4534_ = l_Array_zipWithMAux___redArg(v_inst_4528_, v_as_4530_, v_bs_4531_, v_f_4529_, v___x_4532_, v___x_4533_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(lean_object* v_as_4535_, size_t v_i_4536_, size_t v_stop_4537_, lean_object* v_b_4538_){
_start:
{
uint8_t v___x_4539_; 
v___x_4539_ = lean_usize_dec_eq(v_i_4536_, v_stop_4537_);
if (v___x_4539_ == 0)
{
lean_object* v_fst_4540_; lean_object* v_snd_4541_; lean_object* v___x_4542_; lean_object* v_fst_4543_; lean_object* v_snd_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4556_; 
v_fst_4540_ = lean_ctor_get(v_b_4538_, 0);
lean_inc(v_fst_4540_);
v_snd_4541_ = lean_ctor_get(v_b_4538_, 1);
lean_inc(v_snd_4541_);
lean_dec_ref(v_b_4538_);
v___x_4542_ = lean_array_uget(v_as_4535_, v_i_4536_);
v_fst_4543_ = lean_ctor_get(v___x_4542_, 0);
v_snd_4544_ = lean_ctor_get(v___x_4542_, 1);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4546_ = v___x_4542_;
v_isShared_4547_ = v_isSharedCheck_4556_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_snd_4544_);
lean_inc(v_fst_4543_);
lean_dec(v___x_4542_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4556_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4551_; 
v___x_4548_ = lean_array_push(v_fst_4540_, v_fst_4543_);
v___x_4549_ = lean_array_push(v_snd_4541_, v_snd_4544_);
if (v_isShared_4547_ == 0)
{
lean_ctor_set(v___x_4546_, 1, v___x_4549_);
lean_ctor_set(v___x_4546_, 0, v___x_4548_);
v___x_4551_ = v___x_4546_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v___x_4548_);
lean_ctor_set(v_reuseFailAlloc_4555_, 1, v___x_4549_);
v___x_4551_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
size_t v___x_4552_; size_t v___x_4553_; 
v___x_4552_ = ((size_t)1ULL);
v___x_4553_ = lean_usize_add(v_i_4536_, v___x_4552_);
v_i_4536_ = v___x_4553_;
v_b_4538_ = v___x_4551_;
goto _start;
}
}
}
else
{
return v_b_4538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg___boxed(lean_object* v_as_4557_, lean_object* v_i_4558_, lean_object* v_stop_4559_, lean_object* v_b_4560_){
_start:
{
size_t v_i_boxed_4561_; size_t v_stop_boxed_4562_; lean_object* v_res_4563_; 
v_i_boxed_4561_ = lean_unbox_usize(v_i_4558_);
lean_dec(v_i_4558_);
v_stop_boxed_4562_ = lean_unbox_usize(v_stop_4559_);
lean_dec(v_stop_4559_);
v_res_4563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4557_, v_i_boxed_4561_, v_stop_boxed_4562_, v_b_4560_);
lean_dec_ref(v_as_4557_);
return v_res_4563_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg(lean_object* v_as_4564_){
_start:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; uint8_t v___x_4568_; 
v___x_4565_ = lean_unsigned_to_nat(0u);
v___x_4566_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v___x_4567_ = lean_array_get_size(v_as_4564_);
v___x_4568_ = lean_nat_dec_lt(v___x_4565_, v___x_4567_);
if (v___x_4568_ == 0)
{
return v___x_4566_;
}
else
{
uint8_t v___x_4569_; 
v___x_4569_ = lean_nat_dec_le(v___x_4567_, v___x_4567_);
if (v___x_4569_ == 0)
{
if (v___x_4568_ == 0)
{
return v___x_4566_;
}
else
{
size_t v___x_4570_; size_t v___x_4571_; lean_object* v___x_4572_; 
v___x_4570_ = ((size_t)0ULL);
v___x_4571_ = lean_usize_of_nat(v___x_4567_);
v___x_4572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4564_, v___x_4570_, v___x_4571_, v___x_4566_);
return v___x_4572_;
}
}
else
{
size_t v___x_4573_; size_t v___x_4574_; lean_object* v___x_4575_; 
v___x_4573_ = ((size_t)0ULL);
v___x_4574_ = lean_usize_of_nat(v___x_4567_);
v___x_4575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4564_, v___x_4573_, v___x_4574_, v___x_4566_);
return v___x_4575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg___boxed(lean_object* v_as_4576_){
_start:
{
lean_object* v_res_4577_; 
v_res_4577_ = l_Array_unzip___redArg(v_as_4576_);
lean_dec_ref(v_as_4576_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip(lean_object* v_00_u03b1_4578_, lean_object* v_00_u03b2_4579_, lean_object* v_as_4580_){
_start:
{
lean_object* v___x_4581_; 
v___x_4581_ = l_Array_unzip___redArg(v_as_4580_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___boxed(lean_object* v_00_u03b1_4582_, lean_object* v_00_u03b2_4583_, lean_object* v_as_4584_){
_start:
{
lean_object* v_res_4585_; 
v_res_4585_ = l_Array_unzip(v_00_u03b1_4582_, v_00_u03b2_4583_, v_as_4584_);
lean_dec_ref(v_as_4584_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(lean_object* v_00_u03b1_4586_, lean_object* v_00_u03b2_4587_, lean_object* v_as_4588_, size_t v_i_4589_, size_t v_stop_4590_, lean_object* v_b_4591_){
_start:
{
lean_object* v___x_4592_; 
v___x_4592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4588_, v_i_4589_, v_stop_4590_, v_b_4591_);
return v___x_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___boxed(lean_object* v_00_u03b1_4593_, lean_object* v_00_u03b2_4594_, lean_object* v_as_4595_, lean_object* v_i_4596_, lean_object* v_stop_4597_, lean_object* v_b_4598_){
_start:
{
size_t v_i_boxed_4599_; size_t v_stop_boxed_4600_; lean_object* v_res_4601_; 
v_i_boxed_4599_ = lean_unbox_usize(v_i_4596_);
lean_dec(v_i_4596_);
v_stop_boxed_4600_ = lean_unbox_usize(v_stop_4597_);
lean_dec(v_stop_4597_);
v_res_4601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(v_00_u03b1_4593_, v_00_u03b2_4594_, v_as_4595_, v_i_boxed_4599_, v_stop_boxed_4600_, v_b_4598_);
lean_dec_ref(v_as_4595_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l_Array_replace___redArg(lean_object* v_inst_4602_, lean_object* v_xs_4603_, lean_object* v_a_4604_, lean_object* v_b_4605_){
_start:
{
lean_object* v___x_4606_; 
v___x_4606_ = l_Array_finIdxOf_x3f___redArg(v_inst_4602_, v_xs_4603_, v_a_4604_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_dec(v_b_4605_);
return v_xs_4603_;
}
else
{
lean_object* v_val_4607_; lean_object* v___x_4608_; 
v_val_4607_ = lean_ctor_get(v___x_4606_, 0);
lean_inc(v_val_4607_);
lean_dec_ref_known(v___x_4606_, 1);
v___x_4608_ = lean_array_fset(v_xs_4603_, v_val_4607_, v_b_4605_);
lean_dec(v_val_4607_);
return v___x_4608_;
}
}
}
LEAN_EXPORT lean_object* l_Array_replace(lean_object* v_00_u03b1_4609_, lean_object* v_inst_4610_, lean_object* v_xs_4611_, lean_object* v_a_4612_, lean_object* v_b_4613_){
_start:
{
lean_object* v___x_4614_; 
v___x_4614_ = l_Array_replace___redArg(v_inst_4610_, v_xs_4611_, v_a_4612_, v_b_4613_);
return v___x_4614_;
}
}
LEAN_EXPORT lean_object* l_Array_instLT(lean_object* v_00_u03b1_4615_, lean_object* v_inst_4616_){
_start:
{
lean_object* v___x_4617_; 
v___x_4617_ = lean_box(0);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l_Array_instLE(lean_object* v_00_u03b1_4618_, lean_object* v_inst_4619_){
_start:
{
lean_object* v___x_4620_; 
v___x_4620_ = lean_box(0);
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg(lean_object* v_n_4621_, lean_object* v_a_4622_, lean_object* v_xs_4623_){
_start:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; 
v___x_4624_ = lean_array_get_size(v_xs_4623_);
v___x_4625_ = lean_nat_sub(v_n_4621_, v___x_4624_);
v___x_4626_ = lean_mk_array(v___x_4625_, v_a_4622_);
v___x_4627_ = l_Array_append___redArg(v___x_4626_, v_xs_4623_);
return v___x_4627_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg___boxed(lean_object* v_n_4628_, lean_object* v_a_4629_, lean_object* v_xs_4630_){
_start:
{
lean_object* v_res_4631_; 
v_res_4631_ = l_Array_leftpad___redArg(v_n_4628_, v_a_4629_, v_xs_4630_);
lean_dec_ref(v_xs_4630_);
lean_dec(v_n_4628_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad(lean_object* v_00_u03b1_4632_, lean_object* v_n_4633_, lean_object* v_a_4634_, lean_object* v_xs_4635_){
_start:
{
lean_object* v___x_4636_; 
v___x_4636_ = l_Array_leftpad___redArg(v_n_4633_, v_a_4634_, v_xs_4635_);
return v___x_4636_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___boxed(lean_object* v_00_u03b1_4637_, lean_object* v_n_4638_, lean_object* v_a_4639_, lean_object* v_xs_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l_Array_leftpad(v_00_u03b1_4637_, v_n_4638_, v_a_4639_, v_xs_4640_);
lean_dec_ref(v_xs_4640_);
lean_dec(v_n_4638_);
return v_res_4641_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg(lean_object* v_n_4642_, lean_object* v_a_4643_, lean_object* v_xs_4644_){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4645_ = lean_array_get_size(v_xs_4644_);
v___x_4646_ = lean_nat_sub(v_n_4642_, v___x_4645_);
v___x_4647_ = lean_mk_array(v___x_4646_, v_a_4643_);
v___x_4648_ = l_Array_append___redArg(v_xs_4644_, v___x_4647_);
lean_dec_ref(v___x_4647_);
return v___x_4648_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg___boxed(lean_object* v_n_4649_, lean_object* v_a_4650_, lean_object* v_xs_4651_){
_start:
{
lean_object* v_res_4652_; 
v_res_4652_ = l_Array_rightpad___redArg(v_n_4649_, v_a_4650_, v_xs_4651_);
lean_dec(v_n_4649_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad(lean_object* v_00_u03b1_4653_, lean_object* v_n_4654_, lean_object* v_a_4655_, lean_object* v_xs_4656_){
_start:
{
lean_object* v___x_4657_; 
v___x_4657_ = l_Array_rightpad___redArg(v_n_4654_, v_a_4655_, v_xs_4656_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___boxed(lean_object* v_00_u03b1_4658_, lean_object* v_n_4659_, lean_object* v_a_4660_, lean_object* v_xs_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l_Array_rightpad(v_00_u03b1_4658_, v_n_4659_, v_a_4660_, v_xs_4661_);
lean_dec(v_n_4659_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0(lean_object* v_x_4663_){
_start:
{
lean_inc(v_x_4663_);
return v_x_4663_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0___boxed(lean_object* v_x_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Array_reduceOption___redArg___lam__0(v_x_4664_);
lean_dec(v_x_4664_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg(lean_object* v_as_4667_){
_start:
{
lean_object* v___f_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___f_4668_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4669_ = lean_unsigned_to_nat(0u);
v___x_4670_ = lean_array_get_size(v_as_4667_);
v___x_4671_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4672_ = l_Array_filterMapM___redArg(v___x_4671_, v___f_4668_, v_as_4667_, v___x_4669_, v___x_4670_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption(lean_object* v_00_u03b1_4673_, lean_object* v_as_4674_){
_start:
{
lean_object* v___f_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___f_4675_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4676_ = lean_unsigned_to_nat(0u);
v___x_4677_ = lean_array_get_size(v_as_4674_);
v___x_4678_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4679_ = l_Array_filterMapM___redArg(v___x_4678_, v___f_4675_, v_as_4674_, v___x_4676_, v___x_4677_);
return v___x_4679_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg___lam__0(lean_object* v_inst_4680_, lean_object* v_x1_4681_, lean_object* v_x2_4682_){
_start:
{
lean_object* v_fst_4683_; lean_object* v_snd_4684_; lean_object* v___x_4685_; uint8_t v___x_4686_; 
v_fst_4683_ = lean_ctor_get(v_x1_4681_, 0);
v_snd_4684_ = lean_ctor_get(v_x1_4681_, 1);
lean_inc(v_fst_4683_);
lean_inc(v_x2_4682_);
v___x_4685_ = lean_apply_2(v_inst_4680_, v_x2_4682_, v_fst_4683_);
v___x_4686_ = lean_unbox(v___x_4685_);
if (v___x_4686_ == 0)
{
lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4694_; 
lean_inc(v_snd_4684_);
lean_inc(v_fst_4683_);
v_isSharedCheck_4694_ = !lean_is_exclusive(v_x1_4681_);
if (v_isSharedCheck_4694_ == 0)
{
lean_object* v_unused_4695_; lean_object* v_unused_4696_; 
v_unused_4695_ = lean_ctor_get(v_x1_4681_, 1);
lean_dec(v_unused_4695_);
v_unused_4696_ = lean_ctor_get(v_x1_4681_, 0);
lean_dec(v_unused_4696_);
v___x_4688_ = v_x1_4681_;
v_isShared_4689_ = v_isSharedCheck_4694_;
goto v_resetjp_4687_;
}
else
{
lean_dec(v_x1_4681_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4694_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4690_; lean_object* v___x_4692_; 
v___x_4690_ = lean_array_push(v_snd_4684_, v_fst_4683_);
if (v_isShared_4689_ == 0)
{
lean_ctor_set(v___x_4688_, 1, v___x_4690_);
lean_ctor_set(v___x_4688_, 0, v_x2_4682_);
v___x_4692_ = v___x_4688_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_x2_4682_);
lean_ctor_set(v_reuseFailAlloc_4693_, 1, v___x_4690_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
else
{
lean_dec(v_x2_4682_);
return v_x1_4681_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg(lean_object* v_inst_4697_, lean_object* v_as_4698_){
_start:
{
lean_object* v___y_4700_; lean_object* v___x_4704_; lean_object* v___x_4705_; uint8_t v___x_4706_; 
v___x_4704_ = lean_unsigned_to_nat(0u);
v___x_4705_ = lean_array_get_size(v_as_4698_);
v___x_4706_ = lean_nat_dec_lt(v___x_4704_, v___x_4705_);
if (v___x_4706_ == 0)
{
lean_object* v___x_4707_; 
lean_dec_ref(v_as_4698_);
lean_dec_ref(v_inst_4697_);
v___x_4707_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
return v___x_4707_;
}
else
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4708_ = lean_array_fget_borrowed(v_as_4698_, v___x_4704_);
v___x_4709_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4710_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
if (v___x_4706_ == 0)
{
lean_object* v___x_4711_; 
lean_inc(v___x_4708_);
lean_dec_ref(v_as_4698_);
lean_dec_ref(v_inst_4697_);
v___x_4711_ = lean_array_push(v___x_4709_, v___x_4708_);
return v___x_4711_;
}
else
{
lean_object* v___f_4712_; lean_object* v___x_4713_; uint8_t v___x_4714_; 
v___f_4712_ = lean_alloc_closure((void*)(l_Array_eraseReps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4712_, 0, v_inst_4697_);
lean_inc(v___x_4708_);
v___x_4713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4708_);
lean_ctor_set(v___x_4713_, 1, v___x_4709_);
v___x_4714_ = lean_nat_dec_le(v___x_4705_, v___x_4705_);
if (v___x_4714_ == 0)
{
if (v___x_4706_ == 0)
{
lean_object* v___x_4715_; 
lean_inc(v___x_4708_);
lean_dec_ref_known(v___x_4713_, 2);
lean_dec_ref(v___f_4712_);
lean_dec_ref(v_as_4698_);
v___x_4715_ = lean_array_push(v___x_4709_, v___x_4708_);
return v___x_4715_;
}
else
{
size_t v___x_4716_; size_t v___x_4717_; lean_object* v___x_4718_; 
v___x_4716_ = ((size_t)0ULL);
v___x_4717_ = lean_usize_of_nat(v___x_4705_);
v___x_4718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4710_, v___f_4712_, v_as_4698_, v___x_4716_, v___x_4717_, v___x_4713_);
v___y_4700_ = v___x_4718_;
goto v___jp_4699_;
}
}
else
{
size_t v___x_4719_; size_t v___x_4720_; lean_object* v___x_4721_; 
v___x_4719_ = ((size_t)0ULL);
v___x_4720_ = lean_usize_of_nat(v___x_4705_);
v___x_4721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4710_, v___f_4712_, v_as_4698_, v___x_4719_, v___x_4720_, v___x_4713_);
v___y_4700_ = v___x_4721_;
goto v___jp_4699_;
}
}
}
v___jp_4699_:
{
lean_object* v_fst_4701_; lean_object* v_snd_4702_; lean_object* v___x_4703_; 
v_fst_4701_ = lean_ctor_get(v___y_4700_, 0);
lean_inc(v_fst_4701_);
v_snd_4702_ = lean_ctor_get(v___y_4700_, 1);
lean_inc(v_snd_4702_);
lean_dec_ref(v___y_4700_);
v___x_4703_ = lean_array_push(v_snd_4702_, v_fst_4701_);
return v___x_4703_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps(lean_object* v_00_u03b1_4722_, lean_object* v_inst_4723_, lean_object* v_as_4724_){
_start:
{
lean_object* v___x_4725_; 
v___x_4725_ = l_Array_eraseReps___redArg(v_inst_4723_, v_as_4724_);
return v___x_4725_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(lean_object* v_inst_4726_, lean_object* v_as_4727_, lean_object* v_a_4728_, lean_object* v_x_4729_){
_start:
{
lean_object* v_zero_4730_; uint8_t v_isZero_4731_; 
v_zero_4730_ = lean_unsigned_to_nat(0u);
v_isZero_4731_ = lean_nat_dec_eq(v_x_4729_, v_zero_4730_);
if (v_isZero_4731_ == 1)
{
lean_dec(v_x_4729_);
lean_dec(v_a_4728_);
lean_dec_ref(v_inst_4726_);
return v_isZero_4731_;
}
else
{
lean_object* v_one_4732_; lean_object* v_n_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; uint8_t v___x_4736_; 
v_one_4732_ = lean_unsigned_to_nat(1u);
v_n_4733_ = lean_nat_sub(v_x_4729_, v_one_4732_);
lean_dec(v_x_4729_);
v___x_4734_ = lean_array_fget_borrowed(v_as_4727_, v_n_4733_);
lean_inc_ref(v_inst_4726_);
lean_inc(v___x_4734_);
lean_inc(v_a_4728_);
v___x_4735_ = lean_apply_2(v_inst_4726_, v_a_4728_, v___x_4734_);
v___x_4736_ = lean_unbox(v___x_4735_);
if (v___x_4736_ == 0)
{
v_x_4729_ = v_n_4733_;
goto _start;
}
else
{
lean_dec(v_n_4733_);
lean_dec(v_a_4728_);
lean_dec_ref(v_inst_4726_);
return v_isZero_4731_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg___boxed(lean_object* v_inst_4738_, lean_object* v_as_4739_, lean_object* v_a_4740_, lean_object* v_x_4741_){
_start:
{
uint8_t v_res_4742_; lean_object* v_r_4743_; 
v_res_4742_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4738_, v_as_4739_, v_a_4740_, v_x_4741_);
lean_dec_ref(v_as_4739_);
v_r_4743_ = lean_box(v_res_4742_);
return v_r_4743_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(lean_object* v_00_u03b1_4744_, lean_object* v_inst_4745_, lean_object* v_as_4746_, lean_object* v_a_4747_, lean_object* v_x_4748_, lean_object* v_x_4749_){
_start:
{
uint8_t v___x_4750_; 
v___x_4750_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4745_, v_as_4746_, v_a_4747_, v_x_4748_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___boxed(lean_object* v_00_u03b1_4751_, lean_object* v_inst_4752_, lean_object* v_as_4753_, lean_object* v_a_4754_, lean_object* v_x_4755_, lean_object* v_x_4756_){
_start:
{
uint8_t v_res_4757_; lean_object* v_r_4758_; 
v_res_4757_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(v_00_u03b1_4751_, v_inst_4752_, v_as_4753_, v_a_4754_, v_x_4755_, v_x_4756_);
lean_dec_ref(v_as_4753_);
v_r_4758_ = lean_box(v_res_4757_);
return v_r_4758_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(lean_object* v_inst_4759_, lean_object* v_as_4760_, lean_object* v_i_4761_){
_start:
{
lean_object* v___x_4762_; uint8_t v___x_4763_; 
v___x_4762_ = lean_array_get_size(v_as_4760_);
v___x_4763_ = lean_nat_dec_lt(v_i_4761_, v___x_4762_);
if (v___x_4763_ == 0)
{
uint8_t v___x_4764_; 
lean_dec(v_i_4761_);
lean_dec_ref(v_inst_4759_);
v___x_4764_ = 1;
return v___x_4764_;
}
else
{
lean_object* v___x_4765_; uint8_t v___x_4766_; 
v___x_4765_ = lean_array_fget_borrowed(v_as_4760_, v_i_4761_);
lean_inc(v_i_4761_);
lean_inc(v___x_4765_);
lean_inc_ref(v_inst_4759_);
v___x_4766_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4759_, v_as_4760_, v___x_4765_, v_i_4761_);
if (v___x_4766_ == 0)
{
lean_dec(v_i_4761_);
lean_dec_ref(v_inst_4759_);
return v___x_4766_;
}
else
{
lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4767_ = lean_unsigned_to_nat(1u);
v___x_4768_ = lean_nat_add(v_i_4761_, v___x_4767_);
lean_dec(v_i_4761_);
v_i_4761_ = v___x_4768_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg___boxed(lean_object* v_inst_4770_, lean_object* v_as_4771_, lean_object* v_i_4772_){
_start:
{
uint8_t v_res_4773_; lean_object* v_r_4774_; 
v_res_4773_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4770_, v_as_4771_, v_i_4772_);
lean_dec_ref(v_as_4771_);
v_r_4774_ = lean_box(v_res_4773_);
return v_r_4774_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux(lean_object* v_00_u03b1_4775_, lean_object* v_inst_4776_, lean_object* v_as_4777_, lean_object* v_i_4778_){
_start:
{
uint8_t v___x_4779_; 
v___x_4779_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4776_, v_as_4777_, v_i_4778_);
return v___x_4779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___boxed(lean_object* v_00_u03b1_4780_, lean_object* v_inst_4781_, lean_object* v_as_4782_, lean_object* v_i_4783_){
_start:
{
uint8_t v_res_4784_; lean_object* v_r_4785_; 
v_res_4784_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux(v_00_u03b1_4780_, v_inst_4781_, v_as_4782_, v_i_4783_);
lean_dec_ref(v_as_4782_);
v_r_4785_ = lean_box(v_res_4784_);
return v_r_4785_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___redArg(lean_object* v_inst_4786_, lean_object* v_as_4787_){
_start:
{
lean_object* v___x_4788_; uint8_t v___x_4789_; 
v___x_4788_ = lean_unsigned_to_nat(0u);
v___x_4789_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4786_, v_as_4787_, v___x_4788_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___redArg___boxed(lean_object* v_inst_4790_, lean_object* v_as_4791_){
_start:
{
uint8_t v_res_4792_; lean_object* v_r_4793_; 
v_res_4792_ = l_Array_allDiff___redArg(v_inst_4790_, v_as_4791_);
lean_dec_ref(v_as_4791_);
v_r_4793_ = lean_box(v_res_4792_);
return v_r_4793_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff(lean_object* v_00_u03b1_4794_, lean_object* v_inst_4795_, lean_object* v_as_4796_){
_start:
{
uint8_t v___x_4797_; 
v___x_4797_ = l_Array_allDiff___redArg(v_inst_4795_, v_as_4796_);
return v___x_4797_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___boxed(lean_object* v_00_u03b1_4798_, lean_object* v_inst_4799_, lean_object* v_as_4800_){
_start:
{
uint8_t v_res_4801_; lean_object* v_r_4802_; 
v_res_4801_ = l_Array_allDiff(v_00_u03b1_4798_, v_inst_4799_, v_as_4800_);
lean_dec_ref(v_as_4800_);
v_r_4802_ = lean_box(v_res_4801_);
return v_r_4802_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0(uint8_t v___x_4803_, lean_object* v_x1_4804_, lean_object* v_x2_4805_){
_start:
{
lean_object* v_fst_4806_; uint8_t v___x_4807_; 
v_fst_4806_ = lean_ctor_get(v_x1_4804_, 0);
v___x_4807_ = lean_unbox(v_fst_4806_);
if (v___x_4807_ == 0)
{
lean_object* v_snd_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4816_; 
lean_dec(v_x2_4805_);
v_snd_4808_ = lean_ctor_get(v_x1_4804_, 1);
v_isSharedCheck_4816_ = !lean_is_exclusive(v_x1_4804_);
if (v_isSharedCheck_4816_ == 0)
{
lean_object* v_unused_4817_; 
v_unused_4817_ = lean_ctor_get(v_x1_4804_, 0);
lean_dec(v_unused_4817_);
v___x_4810_ = v_x1_4804_;
v_isShared_4811_ = v_isSharedCheck_4816_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_snd_4808_);
lean_dec(v_x1_4804_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4816_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4812_; lean_object* v___x_4814_; 
v___x_4812_ = lean_box(v___x_4803_);
if (v_isShared_4811_ == 0)
{
lean_ctor_set(v___x_4810_, 0, v___x_4812_);
v___x_4814_ = v___x_4810_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v___x_4812_);
lean_ctor_set(v_reuseFailAlloc_4815_, 1, v_snd_4808_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
}
else
{
lean_object* v_snd_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4828_; 
v_snd_4818_ = lean_ctor_get(v_x1_4804_, 1);
v_isSharedCheck_4828_ = !lean_is_exclusive(v_x1_4804_);
if (v_isSharedCheck_4828_ == 0)
{
lean_object* v_unused_4829_; 
v_unused_4829_ = lean_ctor_get(v_x1_4804_, 0);
lean_dec(v_unused_4829_);
v___x_4820_ = v_x1_4804_;
v_isShared_4821_ = v_isSharedCheck_4828_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_snd_4818_);
lean_dec(v_x1_4804_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4828_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
uint8_t v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4826_; 
v___x_4822_ = 0;
v___x_4823_ = lean_array_push(v_snd_4818_, v_x2_4805_);
v___x_4824_ = lean_box(v___x_4822_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 1, v___x_4823_);
lean_ctor_set(v___x_4820_, 0, v___x_4824_);
v___x_4826_ = v___x_4820_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v___x_4824_);
lean_ctor_set(v_reuseFailAlloc_4827_, 1, v___x_4823_);
v___x_4826_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
return v___x_4826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0___boxed(lean_object* v___x_4830_, lean_object* v_x1_4831_, lean_object* v_x2_4832_){
_start:
{
uint8_t v___x_139__boxed_4833_; lean_object* v_res_4834_; 
v___x_139__boxed_4833_ = lean_unbox(v___x_4830_);
v_res_4834_ = l_Array_getEvenElems___redArg___lam__0(v___x_139__boxed_4833_, v_x1_4831_, v_x2_4832_);
return v_res_4834_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg(lean_object* v_as_4835_){
_start:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; uint8_t v___x_4840_; 
v___x_4836_ = lean_unsigned_to_nat(0u);
v___x_4837_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_4838_ = lean_array_get_size(v_as_4835_);
v___x_4839_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4840_ = lean_nat_dec_lt(v___x_4836_, v___x_4838_);
if (v___x_4840_ == 0)
{
lean_dec_ref(v_as_4835_);
return v___x_4837_;
}
else
{
lean_object* v___x_4841_; lean_object* v___f_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; uint8_t v___x_4845_; 
v___x_4841_ = lean_box(v___x_4840_);
v___f_4842_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4842_, 0, v___x_4841_);
v___x_4843_ = lean_box(v___x_4840_);
v___x_4844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4843_);
lean_ctor_set(v___x_4844_, 1, v___x_4837_);
v___x_4845_ = lean_nat_dec_le(v___x_4838_, v___x_4838_);
if (v___x_4845_ == 0)
{
if (v___x_4840_ == 0)
{
lean_dec_ref_known(v___x_4844_, 2);
lean_dec_ref(v___f_4842_);
lean_dec_ref(v_as_4835_);
return v___x_4837_;
}
else
{
size_t v___x_4846_; size_t v___x_4847_; lean_object* v___x_4848_; lean_object* v_snd_4849_; 
v___x_4846_ = ((size_t)0ULL);
v___x_4847_ = lean_usize_of_nat(v___x_4838_);
v___x_4848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4839_, v___f_4842_, v_as_4835_, v___x_4846_, v___x_4847_, v___x_4844_);
v_snd_4849_ = lean_ctor_get(v___x_4848_, 1);
lean_inc(v_snd_4849_);
lean_dec(v___x_4848_);
return v_snd_4849_;
}
}
else
{
size_t v___x_4850_; size_t v___x_4851_; lean_object* v___x_4852_; lean_object* v_snd_4853_; 
v___x_4850_ = ((size_t)0ULL);
v___x_4851_ = lean_usize_of_nat(v___x_4838_);
v___x_4852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4839_, v___f_4842_, v_as_4835_, v___x_4850_, v___x_4851_, v___x_4844_);
v_snd_4853_ = lean_ctor_get(v___x_4852_, 1);
lean_inc(v_snd_4853_);
lean_dec(v___x_4852_);
return v_snd_4853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems(lean_object* v_00_u03b1_4854_, lean_object* v_as_4855_){
_start:
{
lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; uint8_t v___x_4860_; 
v___x_4856_ = lean_unsigned_to_nat(0u);
v___x_4857_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_4858_ = lean_array_get_size(v_as_4855_);
v___x_4859_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4860_ = lean_nat_dec_lt(v___x_4856_, v___x_4858_);
if (v___x_4860_ == 0)
{
lean_dec_ref(v_as_4855_);
return v___x_4857_;
}
else
{
lean_object* v___x_4861_; lean_object* v___f_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; uint8_t v___x_4865_; 
v___x_4861_ = lean_box(v___x_4860_);
v___f_4862_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4862_, 0, v___x_4861_);
v___x_4863_ = lean_box(v___x_4860_);
v___x_4864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4863_);
lean_ctor_set(v___x_4864_, 1, v___x_4857_);
v___x_4865_ = lean_nat_dec_le(v___x_4858_, v___x_4858_);
if (v___x_4865_ == 0)
{
if (v___x_4860_ == 0)
{
lean_dec_ref_known(v___x_4864_, 2);
lean_dec_ref(v___f_4862_);
lean_dec_ref(v_as_4855_);
return v___x_4857_;
}
else
{
size_t v___x_4866_; size_t v___x_4867_; lean_object* v___x_4868_; lean_object* v_snd_4869_; 
v___x_4866_ = ((size_t)0ULL);
v___x_4867_ = lean_usize_of_nat(v___x_4858_);
v___x_4868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4859_, v___f_4862_, v_as_4855_, v___x_4866_, v___x_4867_, v___x_4864_);
v_snd_4869_ = lean_ctor_get(v___x_4868_, 1);
lean_inc(v_snd_4869_);
lean_dec(v___x_4868_);
return v_snd_4869_;
}
}
else
{
size_t v___x_4870_; size_t v___x_4871_; lean_object* v___x_4872_; lean_object* v_snd_4873_; 
v___x_4870_ = ((size_t)0ULL);
v___x_4871_ = lean_usize_of_nat(v___x_4858_);
v___x_4872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4859_, v___f_4862_, v_as_4855_, v___x_4870_, v___x_4871_, v___x_4864_);
v_snd_4873_ = lean_ctor_get(v___x_4872_, 1);
lean_inc(v_snd_4873_);
lean_dec(v___x_4872_);
return v_snd_4873_;
}
}
}
}
static lean_object* _init_l_Array_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4879_ = ((lean_object*)(l_term_x23_x5b___x2c_x5d___closed__4));
v___x_4880_ = lean_string_length(v___x_4879_);
return v___x_4880_;
}
}
static lean_object* _init_l_Array_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4881_ = lean_obj_once(&l_Array_repr___redArg___closed__2, &l_Array_repr___redArg___closed__2_once, _init_l_Array_repr___redArg___closed__2);
v___x_4882_ = lean_nat_to_int(v___x_4881_);
return v___x_4882_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___redArg(lean_object* v_inst_4890_, lean_object* v_xs_4891_){
_start:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; uint8_t v___x_4894_; 
v___x_4892_ = lean_array_get_size(v_xs_4891_);
v___x_4893_ = lean_unsigned_to_nat(0u);
v___x_4894_ = lean_nat_dec_eq(v___x_4892_, v___x_4893_);
if (v___x_4894_ == 0)
{
lean_object* v_x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; 
v_x_4895_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_4895_, 0, lean_box(0));
lean_closure_set(v_x_4895_, 1, v_inst_4890_);
v___x_4896_ = lean_array_to_list(v_xs_4891_);
v___x_4897_ = ((lean_object*)(l_Array_repr___redArg___closed__1));
v___x_4898_ = l_Std_Format_joinSep___redArg(v_x_4895_, v___x_4896_, v___x_4897_);
v___x_4899_ = lean_obj_once(&l_Array_repr___redArg___closed__3, &l_Array_repr___redArg___closed__3_once, _init_l_Array_repr___redArg___closed__3);
v___x_4900_ = ((lean_object*)(l_Array_repr___redArg___closed__4));
v___x_4901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4901_, 0, v___x_4900_);
lean_ctor_set(v___x_4901_, 1, v___x_4898_);
v___x_4902_ = ((lean_object*)(l_Array_repr___redArg___closed__5));
v___x_4903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4903_, 0, v___x_4901_);
lean_ctor_set(v___x_4903_, 1, v___x_4902_);
v___x_4904_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4899_);
lean_ctor_set(v___x_4904_, 1, v___x_4903_);
v___x_4905_ = l_Std_Format_fill(v___x_4904_);
return v___x_4905_;
}
else
{
lean_object* v___x_4906_; 
lean_dec_ref(v_xs_4891_);
lean_dec_ref(v_inst_4890_);
v___x_4906_ = ((lean_object*)(l_Array_repr___redArg___closed__7));
return v___x_4906_;
}
}
}
LEAN_EXPORT lean_object* l_Array_repr(lean_object* v_00_u03b1_4907_, lean_object* v_inst_4908_, lean_object* v_xs_4909_){
_start:
{
lean_object* v___x_4910_; 
v___x_4910_ = l_Array_repr___redArg(v_inst_4908_, v_xs_4909_);
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0(lean_object* v_inst_4911_, lean_object* v_xs_4912_, lean_object* v_x_4913_){
_start:
{
lean_object* v___x_4914_; 
v___x_4914_ = l_Array_repr___redArg(v_inst_4911_, v_xs_4912_);
return v___x_4914_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object* v_inst_4915_, lean_object* v_xs_4916_, lean_object* v_x_4917_){
_start:
{
lean_object* v_res_4918_; 
v_res_4918_ = l_Array_instRepr___redArg___lam__0(v_inst_4915_, v_xs_4916_, v_x_4917_);
lean_dec(v_x_4917_);
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg(lean_object* v_inst_4919_){
_start:
{
lean_object* v___f_4920_; 
v___f_4920_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4920_, 0, v_inst_4919_);
return v___f_4920_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr(lean_object* v_00_u03b1_4921_, lean_object* v_inst_4922_){
_start:
{
lean_object* v___f_4923_; 
v___f_4923_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4923_, 0, v_inst_4922_);
return v___f_4923_;
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
