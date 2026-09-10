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
LEAN_EXPORT lean_object* l_Array_markLinear___boxed(lean_object* v_00_u03b1_197_, lean_object* v_xs_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = lean_array_mark_linear(v_xs_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Array_propagateMark___boxed(lean_object* v_00_u03b1_204_, lean_object* v_00_u03b2_205_, lean_object* v_xs_206_, lean_object* v_ys_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = lean_array_propagate_mark(v_xs_206_, v_ys_207_);
lean_dec_ref(v_xs_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Array_replicate___boxed(lean_object* v_00_u03b1_212_, lean_object* v_n_213_, lean_object* v_v_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = lean_mk_array(v_n_213_, v_v_214_);
return v_res_215_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__9(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l_Array_swap___auto__1___closed__8));
v___x_236_ = l_Lean_mkAtom(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__10(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_obj_once(&l_Array_swap___auto__1___closed__9, &l_Array_swap___auto__1___closed__9_once, _init_l_Array_swap___auto__1___closed__9);
v___x_238_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_239_ = lean_array_push(v___x_238_, v___x_237_);
return v___x_239_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__11(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_240_ = lean_obj_once(&l_Array_swap___auto__1___closed__10, &l_Array_swap___auto__1___closed__10_once, _init_l_Array_swap___auto__1___closed__10);
v___x_241_ = ((lean_object*)(l_Array_swap___auto__1___closed__7));
v___x_242_ = lean_box(2);
v___x_243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
lean_ctor_set(v___x_243_, 2, v___x_240_);
return v___x_243_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__12(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_Array_swap___auto__1___closed__11, &l_Array_swap___auto__1___closed__11_once, _init_l_Array_swap___auto__1___closed__11);
v___x_245_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_246_ = lean_array_push(v___x_245_, v___x_244_);
return v___x_246_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__13(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_247_ = lean_obj_once(&l_Array_swap___auto__1___closed__12, &l_Array_swap___auto__1___closed__12_once, _init_l_Array_swap___auto__1___closed__12);
v___x_248_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13));
v___x_249_ = lean_box(2);
v___x_250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_248_);
lean_ctor_set(v___x_250_, 2, v___x_247_);
return v___x_250_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__14(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_obj_once(&l_Array_swap___auto__1___closed__13, &l_Array_swap___auto__1___closed__13_once, _init_l_Array_swap___auto__1___closed__13);
v___x_252_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_253_ = lean_array_push(v___x_252_, v___x_251_);
return v___x_253_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__15(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_254_ = lean_obj_once(&l_Array_swap___auto__1___closed__14, &l_Array_swap___auto__1___closed__14_once, _init_l_Array_swap___auto__1___closed__14);
v___x_255_ = ((lean_object*)(l_Array_swap___auto__1___closed__5));
v___x_256_ = lean_box(2);
v___x_257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
lean_ctor_set(v___x_257_, 2, v___x_254_);
return v___x_257_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__16(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_obj_once(&l_Array_swap___auto__1___closed__15, &l_Array_swap___auto__1___closed__15_once, _init_l_Array_swap___auto__1___closed__15);
v___x_259_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_260_ = lean_array_push(v___x_259_, v___x_258_);
return v___x_260_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__17(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = lean_obj_once(&l_Array_swap___auto__1___closed__16, &l_Array_swap___auto__1___closed__16_once, _init_l_Array_swap___auto__1___closed__16);
v___x_262_ = ((lean_object*)(l_Array_swap___auto__1___closed__2));
v___x_263_ = lean_box(2);
v___x_264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
lean_ctor_set(v___x_264_, 2, v___x_261_);
return v___x_264_;
}
}
static lean_object* _init_l_Array_swap___auto__1(void){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_265_;
}
}
static lean_object* _init_l_Array_swap___auto__3(void){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Array_swap___boxed(lean_object* v_00_u03b1_273_, lean_object* v_xs_274_, lean_object* v_i_275_, lean_object* v_j_276_, lean_object* v_hi_277_, lean_object* v_hj_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = lean_array_fswap(v_xs_274_, v_i_275_, v_j_276_);
lean_dec(v_j_276_);
lean_dec(v_i_275_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Array_swapIfInBounds___boxed(lean_object* v_00_u03b1_284_, lean_object* v_xs_285_, lean_object* v_i_286_, lean_object* v_j_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = lean_array_swap(v_xs_285_, v_i_286_, v_j_287_);
lean_dec(v_j_287_);
lean_dec(v_i_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___lam__0(lean_object* v_xs_289_, size_t v_i_290_, lean_object* v_h_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = lean_array_uget_borrowed(v_xs_289_, v_i_290_);
lean_inc(v___x_292_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___lam__0___boxed(lean_object* v_xs_293_, lean_object* v_i_294_, lean_object* v_h_295_){
_start:
{
size_t v_i_boxed_296_; lean_object* v_res_297_; 
v_i_boxed_296_ = lean_unbox_usize(v_i_294_);
lean_dec(v_i_294_);
v_res_297_ = l_Array_instGetElemUSizeLtNatToNatSize___lam__0(v_xs_293_, v_i_boxed_296_, v_h_295_);
lean_dec_ref(v_xs_293_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize(lean_object* v_00_u03b1_299_){
_start:
{
lean_object* v___f_300_; 
v___f_300_ = ((lean_object*)(l_Array_instGetElemUSizeLtNatToNatSize___closed__0));
return v___f_300_;
}
}
LEAN_EXPORT lean_object* l_Array_instEmptyCollection(lean_object* v_00_u03b1_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Array_instInhabited(lean_object* v_00_u03b1_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
return v___x_306_;
}
}
LEAN_EXPORT uint8_t l_Array_isEmpty___redArg(lean_object* v_xs_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_308_ = lean_array_get_size(v_xs_307_);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_nat_dec_eq(v___x_308_, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Array_isEmpty___redArg___boxed(lean_object* v_xs_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_Array_isEmpty___redArg(v_xs_311_);
lean_dec_ref(v_xs_311_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT uint8_t l_Array_isEmpty(lean_object* v_00_u03b1_314_, lean_object* v_xs_315_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_316_ = lean_array_get_size(v_xs_315_);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = lean_nat_dec_eq(v___x_316_, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Array_isEmpty___boxed(lean_object* v_00_u03b1_319_, lean_object* v_xs_320_){
_start:
{
uint8_t v_res_321_; lean_object* v_r_322_; 
v_res_321_ = l_Array_isEmpty(v_00_u03b1_319_, v_xs_320_);
lean_dec_ref(v_xs_320_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___redArg(lean_object* v_xs_323_, lean_object* v_ys_324_, lean_object* v_p_325_, lean_object* v_x_326_){
_start:
{
lean_object* v_zero_327_; uint8_t v_isZero_328_; 
v_zero_327_ = lean_unsigned_to_nat(0u);
v_isZero_328_ = lean_nat_dec_eq(v_x_326_, v_zero_327_);
if (v_isZero_328_ == 1)
{
lean_dec(v_x_326_);
lean_dec_ref(v_p_325_);
return v_isZero_328_;
}
else
{
lean_object* v_one_329_; lean_object* v_n_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v_one_329_ = lean_unsigned_to_nat(1u);
v_n_330_ = lean_nat_sub(v_x_326_, v_one_329_);
lean_dec(v_x_326_);
v___x_331_ = lean_array_fget_borrowed(v_xs_323_, v_n_330_);
v___x_332_ = lean_array_fget_borrowed(v_ys_324_, v_n_330_);
lean_inc_ref(v_p_325_);
lean_inc(v___x_332_);
lean_inc(v___x_331_);
v___x_333_ = lean_apply_2(v_p_325_, v___x_331_, v___x_332_);
v___x_334_ = lean_unbox(v___x_333_);
if (v___x_334_ == 0)
{
uint8_t v___x_335_; 
lean_dec(v_n_330_);
lean_dec_ref(v_p_325_);
v___x_335_ = lean_unbox(v___x_333_);
return v___x_335_;
}
else
{
v_x_326_ = v_n_330_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___redArg___boxed(lean_object* v_xs_337_, lean_object* v_ys_338_, lean_object* v_p_339_, lean_object* v_x_340_){
_start:
{
uint8_t v_res_341_; lean_object* v_r_342_; 
v_res_341_ = l_Array_isEqvAux___redArg(v_xs_337_, v_ys_338_, v_p_339_, v_x_340_);
lean_dec_ref(v_ys_338_);
lean_dec_ref(v_xs_337_);
v_r_342_ = lean_box(v_res_341_);
return v_r_342_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux(lean_object* v_00_u03b1_343_, lean_object* v_xs_344_, lean_object* v_ys_345_, lean_object* v_hsz_346_, lean_object* v_p_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
uint8_t v___x_350_; 
v___x_350_ = l_Array_isEqvAux___redArg(v_xs_344_, v_ys_345_, v_p_347_, v_x_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___boxed(lean_object* v_00_u03b1_351_, lean_object* v_xs_352_, lean_object* v_ys_353_, lean_object* v_hsz_354_, lean_object* v_p_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = l_Array_isEqvAux(v_00_u03b1_351_, v_xs_352_, v_ys_353_, v_hsz_354_, v_p_355_, v_x_356_, v_x_357_);
lean_dec_ref(v_ys_353_);
lean_dec_ref(v_xs_352_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqv___redArg(lean_object* v_xs_360_, lean_object* v_ys_361_, lean_object* v_p_362_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_363_ = lean_array_get_size(v_xs_360_);
v___x_364_ = lean_array_get_size(v_ys_361_);
v___x_365_ = lean_nat_dec_eq(v___x_363_, v___x_364_);
if (v___x_365_ == 0)
{
lean_dec_ref(v_p_362_);
return v___x_365_;
}
else
{
uint8_t v___x_366_; 
v___x_366_ = l_Array_isEqvAux___redArg(v_xs_360_, v_ys_361_, v_p_362_, v___x_363_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqv___redArg___boxed(lean_object* v_xs_367_, lean_object* v_ys_368_, lean_object* v_p_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l_Array_isEqv___redArg(v_xs_367_, v_ys_368_, v_p_369_);
lean_dec_ref(v_ys_368_);
lean_dec_ref(v_xs_367_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqv(lean_object* v_00_u03b1_372_, lean_object* v_xs_373_, lean_object* v_ys_374_, lean_object* v_p_375_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_376_ = lean_array_get_size(v_xs_373_);
v___x_377_ = lean_array_get_size(v_ys_374_);
v___x_378_ = lean_nat_dec_eq(v___x_376_, v___x_377_);
if (v___x_378_ == 0)
{
lean_dec_ref(v_p_375_);
return v___x_378_;
}
else
{
uint8_t v___x_379_; 
v___x_379_ = l_Array_isEqvAux___redArg(v_xs_373_, v_ys_374_, v_p_375_, v___x_376_);
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqv___boxed(lean_object* v_00_u03b1_380_, lean_object* v_xs_381_, lean_object* v_ys_382_, lean_object* v_p_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = l_Array_isEqv(v_00_u03b1_380_, v_xs_381_, v_ys_382_, v_p_383_);
lean_dec_ref(v_ys_382_);
lean_dec_ref(v_xs_381_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT uint8_t l_Array_instBEq___redArg___lam__0(lean_object* v_inst_386_, lean_object* v_xs_387_, lean_object* v_ys_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_389_ = lean_array_get_size(v_xs_387_);
v___x_390_ = lean_array_get_size(v_ys_388_);
v___x_391_ = lean_nat_dec_eq(v___x_389_, v___x_390_);
if (v___x_391_ == 0)
{
lean_dec_ref(v_inst_386_);
return v___x_391_;
}
else
{
uint8_t v___x_392_; 
v___x_392_ = l_Array_isEqvAux___redArg(v_xs_387_, v_ys_388_, v_inst_386_, v___x_389_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instBEq___redArg___lam__0___boxed(lean_object* v_inst_393_, lean_object* v_xs_394_, lean_object* v_ys_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_Array_instBEq___redArg___lam__0(v_inst_393_, v_xs_394_, v_ys_395_);
lean_dec_ref(v_ys_395_);
lean_dec_ref(v_xs_394_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT lean_object* l_Array_instBEq___redArg(lean_object* v_inst_398_){
_start:
{
lean_object* v___f_399_; 
v___f_399_ = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_399_, 0, v_inst_398_);
return v___f_399_;
}
}
LEAN_EXPORT lean_object* l_Array_instBEq(lean_object* v_00_u03b1_400_, lean_object* v_inst_401_){
_start:
{
lean_object* v___f_402_; 
v___f_402_ = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_402_, 0, v_inst_401_);
return v___f_402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(lean_object* v_n_403_, lean_object* v_f_404_, lean_object* v_acc_405_, lean_object* v_i_406_){
_start:
{
lean_object* v_zero_407_; uint8_t v_isZero_408_; 
v_zero_407_ = lean_unsigned_to_nat(0u);
v_isZero_408_ = lean_nat_dec_eq(v_i_406_, v_zero_407_);
if (v_isZero_408_ == 1)
{
lean_dec(v_i_406_);
lean_dec(v_f_404_);
return v_acc_405_;
}
else
{
lean_object* v_one_409_; lean_object* v_n_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_one_409_ = lean_unsigned_to_nat(1u);
v_n_410_ = lean_nat_sub(v_i_406_, v_one_409_);
lean_dec(v_i_406_);
v___x_411_ = lean_nat_sub(v_n_403_, v_n_410_);
v___x_412_ = lean_nat_sub(v___x_411_, v_one_409_);
lean_dec(v___x_411_);
lean_inc(v_f_404_);
v___x_413_ = lean_apply_1(v_f_404_, v___x_412_);
v___x_414_ = lean_array_push(v_acc_405_, v___x_413_);
v_acc_405_ = v___x_414_;
v_i_406_ = v_n_410_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg___boxed(lean_object* v_n_416_, lean_object* v_f_417_, lean_object* v_acc_418_, lean_object* v_i_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(v_n_416_, v_f_417_, v_acc_418_, v_i_419_);
lean_dec(v_n_416_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go(lean_object* v_00_u03b1_421_, lean_object* v_n_422_, lean_object* v_f_423_, lean_object* v_acc_424_, lean_object* v_i_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(v_n_422_, v_f_423_, v_acc_424_, v_i_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go___boxed(lean_object* v_00_u03b1_428_, lean_object* v_n_429_, lean_object* v_f_430_, lean_object* v_acc_431_, lean_object* v_i_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go(v_00_u03b1_428_, v_n_429_, v_f_430_, v_acc_431_, v_i_432_, v_a_433_);
lean_dec(v_n_429_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn___redArg(lean_object* v_n_435_, lean_object* v_f_436_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_mk_empty_array_with_capacity(v_n_435_);
lean_inc(v_n_435_);
v___x_438_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(v_n_435_, v_f_436_, v___x_437_, v_n_435_);
lean_dec(v_n_435_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn(lean_object* v_00_u03b1_439_, lean_object* v_n_440_, lean_object* v_f_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Array_ofFn___redArg(v_n_440_, v_f_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Array_range___lam__0(lean_object* v_i_443_){
_start:
{
lean_inc(v_i_443_);
return v_i_443_;
}
}
LEAN_EXPORT lean_object* l_Array_range___lam__0___boxed(lean_object* v_i_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Array_range___lam__0(v_i_444_);
lean_dec(v_i_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Array_range(lean_object* v_n_447_){
_start:
{
lean_object* v___f_448_; lean_object* v___x_449_; 
v___f_448_ = ((lean_object*)(l_Array_range___closed__0));
v___x_449_ = l_Array_ofFn___redArg(v_n_447_, v___f_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27___lam__0(lean_object* v_step_450_, lean_object* v_start_451_, lean_object* v_i_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_nat_mul(v_step_450_, v_i_452_);
v___x_454_ = lean_nat_add(v_start_451_, v___x_453_);
lean_dec(v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27___lam__0___boxed(lean_object* v_step_455_, lean_object* v_start_456_, lean_object* v_i_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Array_range_x27___lam__0(v_step_455_, v_start_456_, v_i_457_);
lean_dec(v_i_457_);
lean_dec(v_start_456_);
lean_dec(v_step_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27(lean_object* v_start_459_, lean_object* v_size_460_, lean_object* v_step_461_){
_start:
{
lean_object* v___f_462_; lean_object* v___x_463_; 
v___f_462_ = lean_alloc_closure((void*)(l_Array_range_x27___lam__0___boxed), 3, 2);
lean_closure_set(v___f_462_, 0, v_step_461_);
lean_closure_set(v___f_462_, 1, v_start_459_);
v___x_463_ = l_Array_ofFn___redArg(v_size_460_, v___f_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Array_singleton___redArg(lean_object* v_v_464_){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = lean_mk_empty_array_with_capacity(v___x_465_);
v___x_467_ = lean_array_push(v___x_466_, v_v_464_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Array_singleton(lean_object* v_00_u03b1_468_, lean_object* v_v_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = lean_mk_empty_array_with_capacity(v___x_470_);
v___x_472_ = lean_array_push(v___x_471_, v_v_469_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___redArg(lean_object* v_inst_473_, lean_object* v_xs_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_475_ = lean_array_get_size(v_xs_474_);
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_sub(v___x_475_, v___x_476_);
v___x_478_ = lean_array_get_borrowed(v_inst_473_, v_xs_474_, v___x_477_);
lean_dec(v___x_477_);
lean_inc(v___x_478_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___redArg___boxed(lean_object* v_inst_479_, lean_object* v_xs_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Array_back_x21___redArg(v_inst_479_, v_xs_480_);
lean_dec_ref(v_xs_480_);
lean_dec(v_inst_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21(lean_object* v_00_u03b1_482_, lean_object* v_inst_483_, lean_object* v_xs_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_485_ = lean_array_get_size(v_xs_484_);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_sub(v___x_485_, v___x_486_);
v___x_488_ = lean_array_get_borrowed(v_inst_483_, v_xs_484_, v___x_487_);
lean_dec(v___x_487_);
lean_inc(v___x_488_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___boxed(lean_object* v_00_u03b1_489_, lean_object* v_inst_490_, lean_object* v_xs_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Array_back_x21(v_00_u03b1_489_, v_inst_490_, v_xs_491_);
lean_dec_ref(v_xs_491_);
lean_dec(v_inst_490_);
return v_res_492_;
}
}
static lean_object* _init_l_Array_back___auto__1(void){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Array_back___redArg(lean_object* v_xs_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_495_ = lean_array_get_size(v_xs_494_);
v___x_496_ = lean_unsigned_to_nat(1u);
v___x_497_ = lean_nat_sub(v___x_495_, v___x_496_);
v___x_498_ = lean_array_fget_borrowed(v_xs_494_, v___x_497_);
lean_dec(v___x_497_);
lean_inc(v___x_498_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Array_back___redArg___boxed(lean_object* v_xs_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Array_back___redArg(v_xs_499_);
lean_dec_ref(v_xs_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Array_back(lean_object* v_00_u03b1_501_, lean_object* v_xs_502_, lean_object* v_h_503_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_504_ = lean_array_get_size(v_xs_502_);
v___x_505_ = lean_unsigned_to_nat(1u);
v___x_506_ = lean_nat_sub(v___x_504_, v___x_505_);
v___x_507_ = lean_array_fget_borrowed(v_xs_502_, v___x_506_);
lean_dec(v___x_506_);
lean_inc(v___x_507_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Array_back___boxed(lean_object* v_00_u03b1_508_, lean_object* v_xs_509_, lean_object* v_h_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Array_back(v_00_u03b1_508_, v_xs_509_, v_h_510_);
lean_dec_ref(v_xs_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___redArg(lean_object* v_xs_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_513_ = lean_array_get_size(v_xs_512_);
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_sub(v___x_513_, v___x_514_);
v___x_516_ = lean_nat_dec_lt(v___x_515_, v___x_513_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
lean_dec(v___x_515_);
v___x_517_ = lean_box(0);
return v___x_517_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_array_fget_borrowed(v_xs_512_, v___x_515_);
lean_dec(v___x_515_);
lean_inc(v___x_518_);
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___redArg___boxed(lean_object* v_xs_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Array_back_x3f___redArg(v_xs_520_);
lean_dec_ref(v_xs_520_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f(lean_object* v_00_u03b1_522_, lean_object* v_xs_523_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_524_ = lean_array_get_size(v_xs_523_);
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_sub(v___x_524_, v___x_525_);
v___x_527_ = lean_nat_dec_lt(v___x_526_, v___x_524_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
lean_dec(v___x_526_);
v___x_528_ = lean_box(0);
return v___x_528_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_array_fget_borrowed(v_xs_523_, v___x_526_);
lean_dec(v___x_526_);
lean_inc(v___x_529_);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___boxed(lean_object* v_00_u03b1_531_, lean_object* v_xs_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Array_back_x3f(v_00_u03b1_531_, v_xs_532_);
lean_dec_ref(v_xs_532_);
return v_res_533_;
}
}
static lean_object* _init_l_Array_swapAt___auto__1(void){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___redArg(lean_object* v_xs_535_, lean_object* v_i_536_, lean_object* v_v_537_){
_start:
{
lean_object* v_e_538_; lean_object* v_xs_x27_539_; lean_object* v___x_540_; 
v_e_538_ = lean_array_fget(v_xs_535_, v_i_536_);
v_xs_x27_539_ = lean_array_fset(v_xs_535_, v_i_536_, v_v_537_);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v_e_538_);
lean_ctor_set(v___x_540_, 1, v_xs_x27_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___redArg___boxed(lean_object* v_xs_541_, lean_object* v_i_542_, lean_object* v_v_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Array_swapAt___redArg(v_xs_541_, v_i_542_, v_v_543_);
lean_dec(v_i_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt(lean_object* v_00_u03b1_545_, lean_object* v_xs_546_, lean_object* v_i_547_, lean_object* v_v_548_, lean_object* v_hi_549_){
_start:
{
lean_object* v_e_550_; lean_object* v_xs_x27_551_; lean_object* v___x_552_; 
v_e_550_ = lean_array_fget(v_xs_546_, v_i_547_);
v_xs_x27_551_ = lean_array_fset(v_xs_546_, v_i_547_, v_v_548_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v_e_550_);
lean_ctor_set(v___x_552_, 1, v_xs_x27_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___boxed(lean_object* v_00_u03b1_553_, lean_object* v_xs_554_, lean_object* v_i_555_, lean_object* v_v_556_, lean_object* v_hi_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Array_swapAt(v_00_u03b1_553_, v_xs_554_, v_i_555_, v_v_556_, v_hi_557_);
lean_dec(v_i_555_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt_x21___redArg(lean_object* v_xs_563_, lean_object* v_i_564_, lean_object* v_v_565_){
_start:
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = lean_array_get_size(v_xs_563_);
v___x_567_ = lean_nat_dec_lt(v_i_564_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v_this_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_this_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_568_, 0, v_v_565_);
lean_ctor_set(v_this_568_, 1, v_xs_563_);
v___x_569_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_570_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__1));
v___x_571_ = lean_unsigned_to_nat(463u);
v___x_572_ = lean_unsigned_to_nat(4u);
v___x_573_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__2));
v___x_574_ = l_Nat_reprFast(v_i_564_);
v___x_575_ = lean_string_append(v___x_573_, v___x_574_);
lean_dec_ref(v___x_574_);
v___x_576_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__3));
v___x_577_ = lean_string_append(v___x_575_, v___x_576_);
v___x_578_ = l_mkPanicMessageWithDecl(v___x_569_, v___x_570_, v___x_571_, v___x_572_, v___x_577_);
lean_dec_ref(v___x_577_);
v___x_579_ = l_panic___redArg(v_this_568_, v___x_578_);
lean_dec_ref_known(v_this_568_, 2);
return v___x_579_;
}
else
{
lean_object* v_e_580_; lean_object* v_xs_x27_581_; lean_object* v___x_582_; 
v_e_580_ = lean_array_fget(v_xs_563_, v_i_564_);
v_xs_x27_581_ = lean_array_fset(v_xs_563_, v_i_564_, v_v_565_);
lean_dec(v_i_564_);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v_e_580_);
lean_ctor_set(v___x_582_, 1, v_xs_x27_581_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l_Array_swapAt_x21(lean_object* v_00_u03b1_583_, lean_object* v_xs_584_, lean_object* v_i_585_, lean_object* v_v_586_){
_start:
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = lean_array_get_size(v_xs_584_);
v___x_588_ = lean_nat_dec_lt(v_i_585_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v_this_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v_this_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_589_, 0, v_v_586_);
lean_ctor_set(v_this_589_, 1, v_xs_584_);
v___x_590_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_591_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__1));
v___x_592_ = lean_unsigned_to_nat(463u);
v___x_593_ = lean_unsigned_to_nat(4u);
v___x_594_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__2));
v___x_595_ = l_Nat_reprFast(v_i_585_);
v___x_596_ = lean_string_append(v___x_594_, v___x_595_);
lean_dec_ref(v___x_595_);
v___x_597_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__3));
v___x_598_ = lean_string_append(v___x_596_, v___x_597_);
v___x_599_ = l_mkPanicMessageWithDecl(v___x_590_, v___x_591_, v___x_592_, v___x_593_, v___x_598_);
lean_dec_ref(v___x_598_);
v___x_600_ = l_panic___redArg(v_this_589_, v___x_599_);
lean_dec_ref_known(v_this_589_, 2);
return v___x_600_;
}
else
{
lean_object* v_e_601_; lean_object* v_xs_x27_602_; lean_object* v___x_603_; 
v_e_601_ = lean_array_fget(v_xs_584_, v_i_585_);
v_xs_x27_602_ = lean_array_fset(v_xs_584_, v_i_585_, v_v_586_);
lean_dec(v_i_585_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v_e_601_);
lean_ctor_set(v___x_603_, 1, v_xs_x27_602_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
lean_object* v_zero_606_; uint8_t v_isZero_607_; 
v_zero_606_ = lean_unsigned_to_nat(0u);
v_isZero_607_ = lean_nat_dec_eq(v_x_604_, v_zero_606_);
if (v_isZero_607_ == 1)
{
lean_dec(v_x_604_);
return v_x_605_;
}
else
{
lean_object* v_one_608_; lean_object* v_n_609_; lean_object* v___x_610_; 
v_one_608_ = lean_unsigned_to_nat(1u);
v_n_609_ = lean_nat_sub(v_x_604_, v_one_608_);
lean_dec(v_x_604_);
v___x_610_ = lean_array_pop(v_x_605_);
v_x_604_ = v_n_609_;
v_x_605_ = v___x_610_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_shrink_loop(lean_object* v_00_u03b1_612_, lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(v_x_613_, v_x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___redArg(lean_object* v_xs_616_, lean_object* v_n_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = lean_array_get_size(v_xs_616_);
v___x_619_ = lean_nat_sub(v___x_618_, v_n_617_);
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(v___x_619_, v_xs_616_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___redArg___boxed(lean_object* v_xs_621_, lean_object* v_n_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Array_shrink___redArg(v_xs_621_, v_n_622_);
lean_dec(v_n_622_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink(lean_object* v_00_u03b1_624_, lean_object* v_xs_625_, lean_object* v_n_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Array_shrink___redArg(v_xs_625_, v_n_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___boxed(lean_object* v_00_u03b1_628_, lean_object* v_xs_629_, lean_object* v_n_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Array_shrink(v_00_u03b1_628_, v_xs_629_, v_n_630_);
lean_dec(v_n_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Array_take___redArg(lean_object* v_xs_632_, lean_object* v_i_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = l_Array_extract___redArg(v_xs_632_, v___x_634_, v_i_633_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Array_take___redArg___boxed(lean_object* v_xs_636_, lean_object* v_i_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Array_take___redArg(v_xs_636_, v_i_637_);
lean_dec_ref(v_xs_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Array_take(lean_object* v_00_u03b1_639_, lean_object* v_xs_640_, lean_object* v_i_641_){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = l_Array_extract___redArg(v_xs_640_, v___x_642_, v_i_641_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Array_take___boxed(lean_object* v_00_u03b1_644_, lean_object* v_xs_645_, lean_object* v_i_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Array_take(v_00_u03b1_644_, v_xs_645_, v_i_646_);
lean_dec_ref(v_xs_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___redArg(lean_object* v_xs_648_, lean_object* v_i_649_){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_array_get_size(v_xs_648_);
v___x_651_ = l_Array_extract___redArg(v_xs_648_, v_i_649_, v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___redArg___boxed(lean_object* v_xs_652_, lean_object* v_i_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Array_drop___redArg(v_xs_652_, v_i_653_);
lean_dec_ref(v_xs_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Array_drop(lean_object* v_00_u03b1_655_, lean_object* v_xs_656_, lean_object* v_i_657_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_array_get_size(v_xs_656_);
v___x_659_ = l_Array_extract___redArg(v_xs_656_, v_i_657_, v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___boxed(lean_object* v_00_u03b1_660_, lean_object* v_xs_661_, lean_object* v_i_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Array_drop(v_00_u03b1_660_, v_xs_661_, v_i_662_);
lean_dec_ref(v_xs_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0(lean_object* v_xs_x27_664_, lean_object* v_i_665_, lean_object* v_toPure_666_, lean_object* v_v_667_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_array_fset(v_xs_x27_664_, v_i_665_, v_v_667_);
v___x_669_ = lean_apply_2(v_toPure_666_, lean_box(0), v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0___boxed(lean_object* v_xs_x27_670_, lean_object* v_i_671_, lean_object* v_toPure_672_, lean_object* v_v_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Array_modifyMUnsafe___redArg___lam__0(v_xs_x27_670_, v_i_671_, v_toPure_672_, v_v_673_);
lean_dec(v_i_671_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg(lean_object* v_inst_675_, lean_object* v_xs_676_, lean_object* v_i_677_, lean_object* v_f_678_){
_start:
{
lean_object* v_toApplicative_679_; lean_object* v_toBind_680_; lean_object* v_toPure_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v_toApplicative_679_ = lean_ctor_get(v_inst_675_, 0);
lean_inc_ref(v_toApplicative_679_);
v_toBind_680_ = lean_ctor_get(v_inst_675_, 1);
lean_inc(v_toBind_680_);
lean_dec_ref(v_inst_675_);
v_toPure_681_ = lean_ctor_get(v_toApplicative_679_, 1);
lean_inc(v_toPure_681_);
lean_dec_ref(v_toApplicative_679_);
v___x_682_ = lean_array_get_size(v_xs_676_);
v___x_683_ = lean_nat_dec_lt(v_i_677_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
lean_dec(v_toBind_680_);
lean_dec(v_f_678_);
lean_dec(v_i_677_);
v___x_684_ = lean_apply_2(v_toPure_681_, lean_box(0), v_xs_676_);
return v___x_684_;
}
else
{
lean_object* v_v_685_; lean_object* v___x_686_; lean_object* v_xs_x27_687_; lean_object* v___f_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_v_685_ = lean_array_fget(v_xs_676_, v_i_677_);
v___x_686_ = lean_box(0);
v_xs_x27_687_ = lean_array_fset(v_xs_676_, v_i_677_, v___x_686_);
v___f_688_ = lean_alloc_closure((void*)(l_Array_modifyMUnsafe___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_688_, 0, v_xs_x27_687_);
lean_closure_set(v___f_688_, 1, v_i_677_);
lean_closure_set(v___f_688_, 2, v_toPure_681_);
v___x_689_ = lean_apply_1(v_f_678_, v_v_685_);
v___x_690_ = lean_apply_4(v_toBind_680_, lean_box(0), lean_box(0), v___x_689_, v___f_688_);
return v___x_690_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe(lean_object* v_00_u03b1_691_, lean_object* v_m_692_, lean_object* v_inst_693_, lean_object* v_xs_694_, lean_object* v_i_695_, lean_object* v_f_696_){
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
LEAN_EXPORT lean_object* l_Array_modify___redArg(lean_object* v_xs_709_, lean_object* v_i_710_, lean_object* v_f_711_){
_start:
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_array_get_size(v_xs_709_);
v___x_713_ = lean_nat_dec_lt(v_i_710_, v___x_712_);
if (v___x_713_ == 0)
{
lean_dec(v_f_711_);
return v_xs_709_;
}
else
{
lean_object* v_v_714_; lean_object* v___x_715_; lean_object* v_xs_x27_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_v_714_ = lean_array_fget(v_xs_709_, v_i_710_);
v___x_715_ = lean_box(0);
v_xs_x27_716_ = lean_array_fset(v_xs_709_, v_i_710_, v___x_715_);
v___x_717_ = lean_apply_1(v_f_711_, v_v_714_);
v___x_718_ = lean_array_fset(v_xs_x27_716_, v_i_710_, v___x_717_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___redArg___boxed(lean_object* v_xs_719_, lean_object* v_i_720_, lean_object* v_f_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Array_modify___redArg(v_xs_719_, v_i_720_, v_f_721_);
lean_dec(v_i_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Array_modify(lean_object* v_00_u03b1_723_, lean_object* v_xs_724_, lean_object* v_i_725_, lean_object* v_f_726_){
_start:
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = lean_array_get_size(v_xs_724_);
v___x_728_ = lean_nat_dec_lt(v_i_725_, v___x_727_);
if (v___x_728_ == 0)
{
lean_dec(v_f_726_);
return v_xs_724_;
}
else
{
lean_object* v_v_729_; lean_object* v___x_730_; lean_object* v_xs_x27_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_v_729_ = lean_array_fget(v_xs_724_, v_i_725_);
v___x_730_ = lean_box(0);
v_xs_x27_731_ = lean_array_fset(v_xs_724_, v_i_725_, v___x_730_);
v___x_732_ = lean_apply_1(v_f_726_, v_v_729_);
v___x_733_ = lean_array_fset(v_xs_x27_731_, v_i_725_, v___x_732_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___boxed(lean_object* v_00_u03b1_734_, lean_object* v_xs_735_, lean_object* v_i_736_, lean_object* v_f_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Array_modify(v_00_u03b1_734_, v_xs_735_, v_i_736_, v_f_737_);
lean_dec(v_i_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg(lean_object* v_xs_739_, lean_object* v_idx_740_, lean_object* v_f_741_){
_start:
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = lean_array_get_size(v_xs_739_);
v___x_743_ = lean_nat_dec_lt(v_idx_740_, v___x_742_);
if (v___x_743_ == 0)
{
lean_dec(v_f_741_);
return v_xs_739_;
}
else
{
lean_object* v_v_744_; lean_object* v___x_745_; lean_object* v_xs_x27_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_v_744_ = lean_array_fget(v_xs_739_, v_idx_740_);
v___x_745_ = lean_box(0);
v_xs_x27_746_ = lean_array_fset(v_xs_739_, v_idx_740_, v___x_745_);
v___x_747_ = lean_apply_1(v_f_741_, v_v_744_);
v___x_748_ = lean_array_fset(v_xs_x27_746_, v_idx_740_, v___x_747_);
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg___boxed(lean_object* v_xs_749_, lean_object* v_idx_750_, lean_object* v_f_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Array_modifyOp___redArg(v_xs_749_, v_idx_750_, v_f_751_);
lean_dec(v_idx_750_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp(lean_object* v_00_u03b1_753_, lean_object* v_xs_754_, lean_object* v_idx_755_, lean_object* v_f_756_){
_start:
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_array_get_size(v_xs_754_);
v___x_758_ = lean_nat_dec_lt(v_idx_755_, v___x_757_);
if (v___x_758_ == 0)
{
lean_dec(v_f_756_);
return v_xs_754_;
}
else
{
lean_object* v_v_759_; lean_object* v___x_760_; lean_object* v_xs_x27_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_v_759_ = lean_array_fget(v_xs_754_, v_idx_755_);
v___x_760_ = lean_box(0);
v_xs_x27_761_ = lean_array_fset(v_xs_754_, v_idx_755_, v___x_760_);
v___x_762_ = lean_apply_1(v_f_756_, v_v_759_);
v___x_763_ = lean_array_fset(v_xs_x27_761_, v_idx_755_, v___x_762_);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___boxed(lean_object* v_00_u03b1_764_, lean_object* v_xs_765_, lean_object* v_idx_766_, lean_object* v_f_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Array_modifyOp(v_00_u03b1_764_, v_xs_765_, v_idx_766_, v_f_767_);
lean_dec(v_idx_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed(lean_object* v_toPure_769_, lean_object* v_i_770_, lean_object* v_inst_771_, lean_object* v_as_772_, lean_object* v_f_773_, lean_object* v_sz_774_, lean_object* v_____do__lift_775_){
_start:
{
size_t v_i_boxed_776_; size_t v_sz_boxed_777_; lean_object* v_res_778_; 
v_i_boxed_776_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_sz_boxed_777_ = lean_unbox_usize(v_sz_774_);
lean_dec(v_sz_774_);
v_res_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(v_toPure_769_, v_i_boxed_776_, v_inst_771_, v_as_772_, v_f_773_, v_sz_boxed_777_, v_____do__lift_775_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(lean_object* v_inst_779_, lean_object* v_as_780_, lean_object* v_f_781_, size_t v_sz_782_, size_t v_i_783_, lean_object* v_b_784_){
_start:
{
lean_object* v_toApplicative_785_; lean_object* v_toBind_786_; lean_object* v_toPure_787_; uint8_t v___x_788_; 
v_toApplicative_785_ = lean_ctor_get(v_inst_779_, 0);
v_toBind_786_ = lean_ctor_get(v_inst_779_, 1);
lean_inc(v_toBind_786_);
v_toPure_787_ = lean_ctor_get(v_toApplicative_785_, 1);
lean_inc(v_toPure_787_);
v___x_788_ = lean_usize_dec_lt(v_i_783_, v_sz_782_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
lean_dec(v_toBind_786_);
lean_dec(v_f_781_);
lean_dec_ref(v_as_780_);
lean_dec_ref(v_inst_779_);
v___x_789_ = lean_apply_2(v_toPure_787_, lean_box(0), v_b_784_);
return v___x_789_;
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___f_792_; lean_object* v_a_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_790_ = lean_box_usize(v_i_783_);
v___x_791_ = lean_box_usize(v_sz_782_);
lean_inc(v_f_781_);
lean_inc_ref(v_as_780_);
v___f_792_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_792_, 0, v_toPure_787_);
lean_closure_set(v___f_792_, 1, v___x_790_);
lean_closure_set(v___f_792_, 2, v_inst_779_);
lean_closure_set(v___f_792_, 3, v_as_780_);
lean_closure_set(v___f_792_, 4, v_f_781_);
lean_closure_set(v___f_792_, 5, v___x_791_);
v_a_793_ = lean_array_uget(v_as_780_, v_i_783_);
lean_dec_ref(v_as_780_);
v___x_794_ = lean_apply_3(v_f_781_, v_a_793_, lean_box(0), v_b_784_);
v___x_795_ = lean_apply_4(v_toBind_786_, lean_box(0), lean_box(0), v___x_794_, v___f_792_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(lean_object* v_toPure_796_, size_t v_i_797_, lean_object* v_inst_798_, lean_object* v_as_799_, lean_object* v_f_800_, size_t v_sz_801_, lean_object* v_____do__lift_802_){
_start:
{
if (lean_obj_tag(v_____do__lift_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_804_; 
lean_dec(v_f_800_);
lean_dec_ref(v_as_799_);
lean_dec_ref(v_inst_798_);
v_a_803_ = lean_ctor_get(v_____do__lift_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v_____do__lift_802_, 1);
v___x_804_ = lean_apply_2(v_toPure_796_, lean_box(0), v_a_803_);
return v___x_804_;
}
else
{
lean_object* v_a_805_; size_t v___x_806_; size_t v___x_807_; lean_object* v___x_808_; 
lean_dec(v_toPure_796_);
v_a_805_ = lean_ctor_get(v_____do__lift_802_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v_____do__lift_802_, 1);
v___x_806_ = ((size_t)1ULL);
v___x_807_ = lean_usize_add(v_i_797_, v___x_806_);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_798_, v_as_799_, v_f_800_, v_sz_801_, v___x_807_, v_a_805_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___boxed(lean_object* v_inst_809_, lean_object* v_as_810_, lean_object* v_f_811_, lean_object* v_sz_812_, lean_object* v_i_813_, lean_object* v_b_814_){
_start:
{
size_t v_sz_boxed_815_; size_t v_i_boxed_816_; lean_object* v_res_817_; 
v_sz_boxed_815_ = lean_unbox_usize(v_sz_812_);
lean_dec(v_sz_812_);
v_i_boxed_816_ = lean_unbox_usize(v_i_813_);
lean_dec(v_i_813_);
v_res_817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_809_, v_as_810_, v_f_811_, v_sz_boxed_815_, v_i_boxed_816_, v_b_814_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object* v_00_u03b1_818_, lean_object* v_00_u03b2_819_, lean_object* v_m_820_, lean_object* v_inst_821_, lean_object* v_as_822_, lean_object* v_f_823_, size_t v_sz_824_, size_t v_i_825_, lean_object* v_b_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_821_, v_as_822_, v_f_823_, v_sz_824_, v_i_825_, v_b_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___boxed(lean_object* v_00_u03b1_828_, lean_object* v_00_u03b2_829_, lean_object* v_m_830_, lean_object* v_inst_831_, lean_object* v_as_832_, lean_object* v_f_833_, lean_object* v_sz_834_, lean_object* v_i_835_, lean_object* v_b_836_){
_start:
{
size_t v_sz_boxed_837_; size_t v_i_boxed_838_; lean_object* v_res_839_; 
v_sz_boxed_837_ = lean_unbox_usize(v_sz_834_);
lean_dec(v_sz_834_);
v_i_boxed_838_ = lean_unbox_usize(v_i_835_);
lean_dec(v_i_835_);
v_res_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(v_00_u03b1_828_, v_00_u03b2_829_, v_m_830_, v_inst_831_, v_as_832_, v_f_833_, v_sz_boxed_837_, v_i_boxed_838_, v_b_836_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe___redArg(lean_object* v_inst_840_, lean_object* v_as_841_, lean_object* v_b_842_, lean_object* v_f_843_){
_start:
{
size_t v_sz_844_; size_t v___x_845_; lean_object* v___x_846_; 
v_sz_844_ = lean_array_size(v_as_841_);
v___x_845_ = ((size_t)0ULL);
v___x_846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_840_, v_as_841_, v_f_843_, v_sz_844_, v___x_845_, v_b_842_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe(lean_object* v_00_u03b1_847_, lean_object* v_00_u03b2_848_, lean_object* v_m_849_, lean_object* v_inst_850_, lean_object* v_as_851_, lean_object* v_b_852_, lean_object* v_f_853_){
_start:
{
size_t v_sz_854_; size_t v___x_855_; lean_object* v___x_856_; 
v_sz_854_ = lean_array_size(v_as_851_);
v___x_855_ = ((size_t)0ULL);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_850_, v_as_851_, v_f_853_, v_sz_854_, v___x_855_, v_b_852_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0___boxed(lean_object* v_toPure_857_, lean_object* v_inst_858_, lean_object* v_as_859_, lean_object* v_f_860_, lean_object* v_n_861_, lean_object* v_____do__lift_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Array_forIn_x27_loop___redArg___lam__0(v_toPure_857_, v_inst_858_, v_as_859_, v_f_860_, v_n_861_, v_____do__lift_862_);
lean_dec(v_n_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg(lean_object* v_inst_864_, lean_object* v_as_865_, lean_object* v_f_866_, lean_object* v_i_867_, lean_object* v_b_868_){
_start:
{
lean_object* v_toApplicative_869_; lean_object* v_toBind_870_; lean_object* v_toPure_871_; lean_object* v_zero_872_; uint8_t v_isZero_873_; 
v_toApplicative_869_ = lean_ctor_get(v_inst_864_, 0);
v_toBind_870_ = lean_ctor_get(v_inst_864_, 1);
lean_inc(v_toBind_870_);
v_toPure_871_ = lean_ctor_get(v_toApplicative_869_, 1);
lean_inc(v_toPure_871_);
v_zero_872_ = lean_unsigned_to_nat(0u);
v_isZero_873_ = lean_nat_dec_eq(v_i_867_, v_zero_872_);
if (v_isZero_873_ == 1)
{
lean_object* v___x_874_; 
lean_dec(v_toBind_870_);
lean_dec(v_f_866_);
lean_dec_ref(v_as_865_);
lean_dec_ref(v_inst_864_);
v___x_874_ = lean_apply_2(v_toPure_871_, lean_box(0), v_b_868_);
return v___x_874_;
}
else
{
lean_object* v_one_875_; lean_object* v_n_876_; lean_object* v___f_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_one_875_ = lean_unsigned_to_nat(1u);
v_n_876_ = lean_nat_sub(v_i_867_, v_one_875_);
lean_inc(v_n_876_);
lean_inc(v_f_866_);
lean_inc_ref(v_as_865_);
v___f_877_ = lean_alloc_closure((void*)(l_Array_forIn_x27_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_877_, 0, v_toPure_871_);
lean_closure_set(v___f_877_, 1, v_inst_864_);
lean_closure_set(v___f_877_, 2, v_as_865_);
lean_closure_set(v___f_877_, 3, v_f_866_);
lean_closure_set(v___f_877_, 4, v_n_876_);
v___x_878_ = lean_array_get_size(v_as_865_);
v___x_879_ = lean_nat_sub(v___x_878_, v_one_875_);
v___x_880_ = lean_nat_sub(v___x_879_, v_n_876_);
lean_dec(v_n_876_);
lean_dec(v___x_879_);
v___x_881_ = lean_array_fget(v_as_865_, v___x_880_);
lean_dec(v___x_880_);
lean_dec_ref(v_as_865_);
v___x_882_ = lean_apply_3(v_f_866_, v___x_881_, lean_box(0), v_b_868_);
v___x_883_ = lean_apply_4(v_toBind_870_, lean_box(0), lean_box(0), v___x_882_, v___f_877_);
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0(lean_object* v_toPure_884_, lean_object* v_inst_885_, lean_object* v_as_886_, lean_object* v_f_887_, lean_object* v_n_888_, lean_object* v_____do__lift_889_){
_start:
{
if (lean_obj_tag(v_____do__lift_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_891_; 
lean_dec(v_f_887_);
lean_dec_ref(v_as_886_);
lean_dec_ref(v_inst_885_);
v_a_890_ = lean_ctor_get(v_____do__lift_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v_____do__lift_889_, 1);
v___x_891_ = lean_apply_2(v_toPure_884_, lean_box(0), v_a_890_);
return v___x_891_;
}
else
{
lean_object* v_a_892_; lean_object* v___x_893_; 
lean_dec(v_toPure_884_);
v_a_892_ = lean_ctor_get(v_____do__lift_889_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v_____do__lift_889_, 1);
v___x_893_ = l_Array_forIn_x27_loop___redArg(v_inst_885_, v_as_886_, v_f_887_, v_n_888_, v_a_892_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___boxed(lean_object* v_inst_894_, lean_object* v_as_895_, lean_object* v_f_896_, lean_object* v_i_897_, lean_object* v_b_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Array_forIn_x27_loop___redArg(v_inst_894_, v_as_895_, v_f_896_, v_i_897_, v_b_898_);
lean_dec(v_i_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop(lean_object* v_00_u03b1_900_, lean_object* v_00_u03b2_901_, lean_object* v_m_902_, lean_object* v_inst_903_, lean_object* v_as_904_, lean_object* v_f_905_, lean_object* v_i_906_, lean_object* v_h_907_, lean_object* v_b_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Array_forIn_x27_loop___redArg(v_inst_903_, v_as_904_, v_f_905_, v_i_906_, v_b_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___boxed(lean_object* v_00_u03b1_910_, lean_object* v_00_u03b2_911_, lean_object* v_m_912_, lean_object* v_inst_913_, lean_object* v_as_914_, lean_object* v_f_915_, lean_object* v_i_916_, lean_object* v_h_917_, lean_object* v_b_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Array_forIn_x27_loop(v_00_u03b1_910_, v_00_u03b2_911_, v_m_912_, v_inst_913_, v_as_914_, v_f_915_, v_i_916_, v_h_917_, v_b_918_);
lean_dec(v_i_916_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_inst_920_, lean_object* v_00_u03b2_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
size_t v_sz_925_; size_t v___x_926_; lean_object* v___x_927_; 
v_sz_925_ = lean_array_size(v___y_922_);
v___x_926_ = ((size_t)0ULL);
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_920_, v___y_922_, v___y_924_, v_sz_925_, v___x_926_, v___y_923_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_928_){
_start:
{
lean_object* v___f_929_; 
v___f_929_ = lean_alloc_closure((void*)(l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_929_, 0, v_inst_928_);
return v___f_929_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_00_u03b1_930_, lean_object* v_m_931_, lean_object* v_inst_932_){
_start:
{
lean_object* v___f_933_; 
v___f_933_ = lean_alloc_closure((void*)(l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_933_, 0, v_inst_932_);
return v___f_933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_934_, lean_object* v_inst_935_, lean_object* v_f_936_, lean_object* v_as_937_, lean_object* v_stop_938_, lean_object* v_____do__lift_939_){
_start:
{
size_t v_i_boxed_940_; size_t v_stop_boxed_941_; lean_object* v_res_942_; 
v_i_boxed_940_ = lean_unbox_usize(v_i_934_);
lean_dec(v_i_934_);
v_stop_boxed_941_ = lean_unbox_usize(v_stop_938_);
lean_dec(v_stop_938_);
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_940_, v_inst_935_, v_f_936_, v_as_937_, v_stop_boxed_941_, v_____do__lift_939_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(lean_object* v_inst_943_, lean_object* v_f_944_, lean_object* v_as_945_, size_t v_i_946_, size_t v_stop_947_, lean_object* v_b_948_){
_start:
{
lean_object* v_toApplicative_949_; lean_object* v_toBind_950_; lean_object* v_toPure_951_; uint8_t v___x_952_; 
v_toApplicative_949_ = lean_ctor_get(v_inst_943_, 0);
v_toBind_950_ = lean_ctor_get(v_inst_943_, 1);
lean_inc(v_toBind_950_);
v_toPure_951_ = lean_ctor_get(v_toApplicative_949_, 1);
v___x_952_ = lean_usize_dec_eq(v_i_946_, v_stop_947_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___f_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_953_ = lean_box_usize(v_i_946_);
v___x_954_ = lean_box_usize(v_stop_947_);
lean_inc_ref(v_as_945_);
lean_inc(v_f_944_);
v___f_955_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_955_, 0, v___x_953_);
lean_closure_set(v___f_955_, 1, v_inst_943_);
lean_closure_set(v___f_955_, 2, v_f_944_);
lean_closure_set(v___f_955_, 3, v_as_945_);
lean_closure_set(v___f_955_, 4, v___x_954_);
v___x_956_ = lean_array_uget(v_as_945_, v_i_946_);
lean_dec_ref(v_as_945_);
v___x_957_ = lean_apply_2(v_f_944_, v_b_948_, v___x_956_);
v___x_958_ = lean_apply_4(v_toBind_950_, lean_box(0), lean_box(0), v___x_957_, v___f_955_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; 
lean_inc(v_toPure_951_);
lean_dec(v_toBind_950_);
lean_dec_ref(v_as_945_);
lean_dec(v_f_944_);
lean_dec_ref(v_inst_943_);
v___x_959_ = lean_apply_2(v_toPure_951_, lean_box(0), v_b_948_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_960_, lean_object* v_inst_961_, lean_object* v_f_962_, lean_object* v_as_963_, size_t v_stop_964_, lean_object* v_____do__lift_965_){
_start:
{
size_t v___x_966_; size_t v___x_967_; lean_object* v___x_968_; 
v___x_966_ = ((size_t)1ULL);
v___x_967_ = lean_usize_add(v_i_960_, v___x_966_);
v___x_968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_961_, v_f_962_, v_as_963_, v___x_967_, v_stop_964_, v_____do__lift_965_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_969_, lean_object* v_f_970_, lean_object* v_as_971_, lean_object* v_i_972_, lean_object* v_stop_973_, lean_object* v_b_974_){
_start:
{
size_t v_i_boxed_975_; size_t v_stop_boxed_976_; lean_object* v_res_977_; 
v_i_boxed_975_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_stop_boxed_976_ = lean_unbox_usize(v_stop_973_);
lean_dec(v_stop_973_);
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_969_, v_f_970_, v_as_971_, v_i_boxed_975_, v_stop_boxed_976_, v_b_974_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object* v_00_u03b1_978_, lean_object* v_00_u03b2_979_, lean_object* v_m_980_, lean_object* v_inst_981_, lean_object* v_f_982_, lean_object* v_as_983_, size_t v_i_984_, size_t v_stop_985_, lean_object* v_b_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_981_, v_f_982_, v_as_983_, v_i_984_, v_stop_985_, v_b_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b1_988_, lean_object* v_00_u03b2_989_, lean_object* v_m_990_, lean_object* v_inst_991_, lean_object* v_f_992_, lean_object* v_as_993_, lean_object* v_i_994_, lean_object* v_stop_995_, lean_object* v_b_996_){
_start:
{
size_t v_i_boxed_997_; size_t v_stop_boxed_998_; lean_object* v_res_999_; 
v_i_boxed_997_ = lean_unbox_usize(v_i_994_);
lean_dec(v_i_994_);
v_stop_boxed_998_ = lean_unbox_usize(v_stop_995_);
lean_dec(v_stop_995_);
v_res_999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(v_00_u03b1_988_, v_00_u03b2_989_, v_m_990_, v_inst_991_, v_f_992_, v_as_993_, v_i_boxed_997_, v_stop_boxed_998_, v_b_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg(lean_object* v_inst_1000_, lean_object* v_f_1001_, lean_object* v_init_1002_, lean_object* v_as_1003_, lean_object* v_start_1004_, lean_object* v_stop_1005_){
_start:
{
lean_object* v_toApplicative_1006_; lean_object* v_toPure_1007_; uint8_t v___x_1008_; 
v_toApplicative_1006_ = lean_ctor_get(v_inst_1000_, 0);
v_toPure_1007_ = lean_ctor_get(v_toApplicative_1006_, 1);
v___x_1008_ = lean_nat_dec_lt(v_start_1004_, v_stop_1005_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
lean_inc(v_toPure_1007_);
lean_dec_ref(v_as_1003_);
lean_dec(v_f_1001_);
lean_dec_ref(v_inst_1000_);
v___x_1009_ = lean_apply_2(v_toPure_1007_, lean_box(0), v_init_1002_);
return v___x_1009_;
}
else
{
lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = lean_array_get_size(v_as_1003_);
v___x_1011_ = lean_nat_dec_le(v_stop_1005_, v___x_1010_);
if (v___x_1011_ == 0)
{
uint8_t v___x_1012_; 
v___x_1012_ = lean_nat_dec_lt(v_start_1004_, v___x_1010_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; 
lean_inc(v_toPure_1007_);
lean_dec_ref(v_as_1003_);
lean_dec(v_f_1001_);
lean_dec_ref(v_inst_1000_);
v___x_1013_ = lean_apply_2(v_toPure_1007_, lean_box(0), v_init_1002_);
return v___x_1013_;
}
else
{
size_t v___x_1014_; size_t v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = lean_usize_of_nat(v_start_1004_);
v___x_1015_ = lean_usize_of_nat(v___x_1010_);
v___x_1016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1000_, v_f_1001_, v_as_1003_, v___x_1014_, v___x_1015_, v_init_1002_);
return v___x_1016_;
}
}
else
{
size_t v___x_1017_; size_t v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = lean_usize_of_nat(v_start_1004_);
v___x_1018_ = lean_usize_of_nat(v_stop_1005_);
v___x_1019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1000_, v_f_1001_, v_as_1003_, v___x_1017_, v___x_1018_, v_init_1002_);
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg___boxed(lean_object* v_inst_1020_, lean_object* v_f_1021_, lean_object* v_init_1022_, lean_object* v_as_1023_, lean_object* v_start_1024_, lean_object* v_stop_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Array_foldlMUnsafe___redArg(v_inst_1020_, v_f_1021_, v_init_1022_, v_as_1023_, v_start_1024_, v_stop_1025_);
lean_dec(v_stop_1025_);
lean_dec(v_start_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe(lean_object* v_00_u03b1_1027_, lean_object* v_00_u03b2_1028_, lean_object* v_m_1029_, lean_object* v_inst_1030_, lean_object* v_f_1031_, lean_object* v_init_1032_, lean_object* v_as_1033_, lean_object* v_start_1034_, lean_object* v_stop_1035_){
_start:
{
lean_object* v_toApplicative_1036_; lean_object* v_toPure_1037_; uint8_t v___x_1038_; 
v_toApplicative_1036_ = lean_ctor_get(v_inst_1030_, 0);
v_toPure_1037_ = lean_ctor_get(v_toApplicative_1036_, 1);
v___x_1038_ = lean_nat_dec_lt(v_start_1034_, v_stop_1035_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; 
lean_inc(v_toPure_1037_);
lean_dec_ref(v_as_1033_);
lean_dec(v_f_1031_);
lean_dec_ref(v_inst_1030_);
v___x_1039_ = lean_apply_2(v_toPure_1037_, lean_box(0), v_init_1032_);
return v___x_1039_;
}
else
{
lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = lean_array_get_size(v_as_1033_);
v___x_1041_ = lean_nat_dec_le(v_stop_1035_, v___x_1040_);
if (v___x_1041_ == 0)
{
uint8_t v___x_1042_; 
v___x_1042_ = lean_nat_dec_lt(v_start_1034_, v___x_1040_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; 
lean_inc(v_toPure_1037_);
lean_dec_ref(v_as_1033_);
lean_dec(v_f_1031_);
lean_dec_ref(v_inst_1030_);
v___x_1043_ = lean_apply_2(v_toPure_1037_, lean_box(0), v_init_1032_);
return v___x_1043_;
}
else
{
size_t v___x_1044_; size_t v___x_1045_; lean_object* v___x_1046_; 
v___x_1044_ = lean_usize_of_nat(v_start_1034_);
v___x_1045_ = lean_usize_of_nat(v___x_1040_);
v___x_1046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1030_, v_f_1031_, v_as_1033_, v___x_1044_, v___x_1045_, v_init_1032_);
return v___x_1046_;
}
}
else
{
size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = lean_usize_of_nat(v_start_1034_);
v___x_1048_ = lean_usize_of_nat(v_stop_1035_);
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1030_, v_f_1031_, v_as_1033_, v___x_1047_, v___x_1048_, v_init_1032_);
return v___x_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___boxed(lean_object* v_00_u03b1_1050_, lean_object* v_00_u03b2_1051_, lean_object* v_m_1052_, lean_object* v_inst_1053_, lean_object* v_f_1054_, lean_object* v_init_1055_, lean_object* v_as_1056_, lean_object* v_start_1057_, lean_object* v_stop_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Array_foldlMUnsafe(v_00_u03b1_1050_, v_00_u03b2_1051_, v_m_1052_, v_inst_1053_, v_f_1054_, v_init_1055_, v_as_1056_, v_start_1057_, v_stop_1058_);
lean_dec(v_stop_1058_);
lean_dec(v_start_1057_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_1060_, lean_object* v_inst_1061_, lean_object* v_f_1062_, lean_object* v_as_1063_, lean_object* v_stop_1064_, lean_object* v_n_1065_, lean_object* v_____do__lift_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Array_foldlM_loop___redArg___lam__0(v_j_1060_, v_inst_1061_, v_f_1062_, v_as_1063_, v_stop_1064_, v_n_1065_, v_____do__lift_1066_);
lean_dec(v_n_1065_);
lean_dec(v_j_1060_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg(lean_object* v_inst_1068_, lean_object* v_f_1069_, lean_object* v_as_1070_, lean_object* v_stop_1071_, lean_object* v_i_1072_, lean_object* v_j_1073_, lean_object* v_b_1074_){
_start:
{
lean_object* v_toApplicative_1075_; lean_object* v_toBind_1076_; lean_object* v_toPure_1077_; uint8_t v___x_1078_; 
v_toApplicative_1075_ = lean_ctor_get(v_inst_1068_, 0);
v_toBind_1076_ = lean_ctor_get(v_inst_1068_, 1);
lean_inc(v_toBind_1076_);
v_toPure_1077_ = lean_ctor_get(v_toApplicative_1075_, 1);
v___x_1078_ = lean_nat_dec_lt(v_j_1073_, v_stop_1071_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
lean_inc(v_toPure_1077_);
lean_dec(v_toBind_1076_);
lean_dec(v_j_1073_);
lean_dec(v_stop_1071_);
lean_dec_ref(v_as_1070_);
lean_dec(v_f_1069_);
lean_dec_ref(v_inst_1068_);
v___x_1079_ = lean_apply_2(v_toPure_1077_, lean_box(0), v_b_1074_);
return v___x_1079_;
}
else
{
lean_object* v_zero_1080_; uint8_t v_isZero_1081_; 
v_zero_1080_ = lean_unsigned_to_nat(0u);
v_isZero_1081_ = lean_nat_dec_eq(v_i_1072_, v_zero_1080_);
if (v_isZero_1081_ == 1)
{
lean_object* v___x_1082_; 
lean_inc(v_toPure_1077_);
lean_dec(v_toBind_1076_);
lean_dec(v_j_1073_);
lean_dec(v_stop_1071_);
lean_dec_ref(v_as_1070_);
lean_dec(v_f_1069_);
lean_dec_ref(v_inst_1068_);
v___x_1082_ = lean_apply_2(v_toPure_1077_, lean_box(0), v_b_1074_);
return v___x_1082_;
}
else
{
lean_object* v_one_1083_; lean_object* v_n_1084_; lean_object* v___f_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v_one_1083_ = lean_unsigned_to_nat(1u);
v_n_1084_ = lean_nat_sub(v_i_1072_, v_one_1083_);
lean_inc_ref(v_as_1070_);
lean_inc(v_f_1069_);
lean_inc(v_j_1073_);
v___f_1085_ = lean_alloc_closure((void*)(l_Array_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1085_, 0, v_j_1073_);
lean_closure_set(v___f_1085_, 1, v_inst_1068_);
lean_closure_set(v___f_1085_, 2, v_f_1069_);
lean_closure_set(v___f_1085_, 3, v_as_1070_);
lean_closure_set(v___f_1085_, 4, v_stop_1071_);
lean_closure_set(v___f_1085_, 5, v_n_1084_);
v___x_1086_ = lean_array_fget(v_as_1070_, v_j_1073_);
lean_dec(v_j_1073_);
lean_dec_ref(v_as_1070_);
v___x_1087_ = lean_apply_2(v_f_1069_, v_b_1074_, v___x_1086_);
v___x_1088_ = lean_apply_4(v_toBind_1076_, lean_box(0), lean_box(0), v___x_1087_, v___f_1085_);
return v___x_1088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0(lean_object* v_j_1089_, lean_object* v_inst_1090_, lean_object* v_f_1091_, lean_object* v_as_1092_, lean_object* v_stop_1093_, lean_object* v_n_1094_, lean_object* v_____do__lift_1095_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = lean_unsigned_to_nat(1u);
v___x_1097_ = lean_nat_add(v_j_1089_, v___x_1096_);
v___x_1098_ = l_Array_foldlM_loop___redArg(v_inst_1090_, v_f_1091_, v_as_1092_, v_stop_1093_, v_n_1094_, v___x_1097_, v_____do__lift_1095_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___boxed(lean_object* v_inst_1099_, lean_object* v_f_1100_, lean_object* v_as_1101_, lean_object* v_stop_1102_, lean_object* v_i_1103_, lean_object* v_j_1104_, lean_object* v_b_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Array_foldlM_loop___redArg(v_inst_1099_, v_f_1100_, v_as_1101_, v_stop_1102_, v_i_1103_, v_j_1104_, v_b_1105_);
lean_dec(v_i_1103_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop(lean_object* v_00_u03b1_1107_, lean_object* v_00_u03b2_1108_, lean_object* v_m_1109_, lean_object* v_inst_1110_, lean_object* v_f_1111_, lean_object* v_as_1112_, lean_object* v_stop_1113_, lean_object* v_h_1114_, lean_object* v_i_1115_, lean_object* v_j_1116_, lean_object* v_b_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Array_foldlM_loop___redArg(v_inst_1110_, v_f_1111_, v_as_1112_, v_stop_1113_, v_i_1115_, v_j_1116_, v_b_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___boxed(lean_object* v_00_u03b1_1119_, lean_object* v_00_u03b2_1120_, lean_object* v_m_1121_, lean_object* v_inst_1122_, lean_object* v_f_1123_, lean_object* v_as_1124_, lean_object* v_stop_1125_, lean_object* v_h_1126_, lean_object* v_i_1127_, lean_object* v_j_1128_, lean_object* v_b_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Array_foldlM_loop(v_00_u03b1_1119_, v_00_u03b2_1120_, v_m_1121_, v_inst_1122_, v_f_1123_, v_as_1124_, v_stop_1125_, v_h_1126_, v_i_1127_, v_j_1128_, v_b_1129_);
lean_dec(v_i_1127_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_inst_1131_, lean_object* v_f_1132_, lean_object* v_as_1133_, lean_object* v___x_1134_, lean_object* v_stop_1135_, lean_object* v_____do__lift_1136_){
_start:
{
size_t v___x_63__boxed_1137_; size_t v_stop_boxed_1138_; lean_object* v_res_1139_; 
v___x_63__boxed_1137_ = lean_unbox_usize(v___x_1134_);
lean_dec(v___x_1134_);
v_stop_boxed_1138_ = lean_unbox_usize(v_stop_1135_);
lean_dec(v_stop_1135_);
v_res_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(v_inst_1131_, v_f_1132_, v_as_1133_, v___x_63__boxed_1137_, v_stop_boxed_1138_, v_____do__lift_1136_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(lean_object* v_inst_1140_, lean_object* v_f_1141_, lean_object* v_as_1142_, size_t v_i_1143_, size_t v_stop_1144_, lean_object* v_b_1145_){
_start:
{
lean_object* v_toApplicative_1146_; lean_object* v_toBind_1147_; lean_object* v_toPure_1148_; uint8_t v___x_1149_; 
v_toApplicative_1146_ = lean_ctor_get(v_inst_1140_, 0);
v_toBind_1147_ = lean_ctor_get(v_inst_1140_, 1);
lean_inc(v_toBind_1147_);
v_toPure_1148_ = lean_ctor_get(v_toApplicative_1146_, 1);
v___x_1149_ = lean_usize_dec_eq(v_i_1143_, v_stop_1144_);
if (v___x_1149_ == 0)
{
size_t v___x_1150_; size_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___f_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1150_ = ((size_t)1ULL);
v___x_1151_ = lean_usize_sub(v_i_1143_, v___x_1150_);
v___x_1152_ = lean_box_usize(v___x_1151_);
v___x_1153_ = lean_box_usize(v_stop_1144_);
lean_inc_ref(v_as_1142_);
lean_inc(v_f_1141_);
v___f_1154_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1154_, 0, v_inst_1140_);
lean_closure_set(v___f_1154_, 1, v_f_1141_);
lean_closure_set(v___f_1154_, 2, v_as_1142_);
lean_closure_set(v___f_1154_, 3, v___x_1152_);
lean_closure_set(v___f_1154_, 4, v___x_1153_);
v___x_1155_ = lean_array_uget(v_as_1142_, v___x_1151_);
lean_dec_ref(v_as_1142_);
v___x_1156_ = lean_apply_2(v_f_1141_, v___x_1155_, v_b_1145_);
v___x_1157_ = lean_apply_4(v_toBind_1147_, lean_box(0), lean_box(0), v___x_1156_, v___f_1154_);
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; 
lean_inc(v_toPure_1148_);
lean_dec(v_toBind_1147_);
lean_dec_ref(v_as_1142_);
lean_dec(v_f_1141_);
lean_dec_ref(v_inst_1140_);
v___x_1158_ = lean_apply_2(v_toPure_1148_, lean_box(0), v_b_1145_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(lean_object* v_inst_1159_, lean_object* v_f_1160_, lean_object* v_as_1161_, size_t v___x_1162_, size_t v_stop_1163_, lean_object* v_____do__lift_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1159_, v_f_1160_, v_as_1161_, v___x_1162_, v_stop_1163_, v_____do__lift_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___boxed(lean_object* v_inst_1166_, lean_object* v_f_1167_, lean_object* v_as_1168_, lean_object* v_i_1169_, lean_object* v_stop_1170_, lean_object* v_b_1171_){
_start:
{
size_t v_i_boxed_1172_; size_t v_stop_boxed_1173_; lean_object* v_res_1174_; 
v_i_boxed_1172_ = lean_unbox_usize(v_i_1169_);
lean_dec(v_i_1169_);
v_stop_boxed_1173_ = lean_unbox_usize(v_stop_1170_);
lean_dec(v_stop_1170_);
v_res_1174_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1166_, v_f_1167_, v_as_1168_, v_i_boxed_1172_, v_stop_boxed_1173_, v_b_1171_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object* v_00_u03b1_1175_, lean_object* v_00_u03b2_1176_, lean_object* v_m_1177_, lean_object* v_inst_1178_, lean_object* v_f_1179_, lean_object* v_as_1180_, size_t v_i_1181_, size_t v_stop_1182_, lean_object* v_b_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1178_, v_f_1179_, v_as_1180_, v_i_1181_, v_stop_1182_, v_b_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___boxed(lean_object* v_00_u03b1_1185_, lean_object* v_00_u03b2_1186_, lean_object* v_m_1187_, lean_object* v_inst_1188_, lean_object* v_f_1189_, lean_object* v_as_1190_, lean_object* v_i_1191_, lean_object* v_stop_1192_, lean_object* v_b_1193_){
_start:
{
size_t v_i_boxed_1194_; size_t v_stop_boxed_1195_; lean_object* v_res_1196_; 
v_i_boxed_1194_ = lean_unbox_usize(v_i_1191_);
lean_dec(v_i_1191_);
v_stop_boxed_1195_ = lean_unbox_usize(v_stop_1192_);
lean_dec(v_stop_1192_);
v_res_1196_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(v_00_u03b1_1185_, v_00_u03b2_1186_, v_m_1187_, v_inst_1188_, v_f_1189_, v_as_1190_, v_i_boxed_1194_, v_stop_boxed_1195_, v_b_1193_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg(lean_object* v_inst_1197_, lean_object* v_f_1198_, lean_object* v_init_1199_, lean_object* v_as_1200_, lean_object* v_start_1201_, lean_object* v_stop_1202_){
_start:
{
lean_object* v_toApplicative_1203_; lean_object* v_toPure_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v_toApplicative_1203_ = lean_ctor_get(v_inst_1197_, 0);
v_toPure_1204_ = lean_ctor_get(v_toApplicative_1203_, 1);
v___x_1205_ = lean_array_get_size(v_as_1200_);
v___x_1206_ = lean_nat_dec_le(v_start_1201_, v___x_1205_);
if (v___x_1206_ == 0)
{
uint8_t v___x_1207_; 
v___x_1207_ = lean_nat_dec_lt(v_stop_1202_, v___x_1205_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; 
lean_inc(v_toPure_1204_);
lean_dec_ref(v_as_1200_);
lean_dec(v_f_1198_);
lean_dec_ref(v_inst_1197_);
v___x_1208_ = lean_apply_2(v_toPure_1204_, lean_box(0), v_init_1199_);
return v___x_1208_;
}
else
{
size_t v___x_1209_; size_t v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_usize_of_nat(v___x_1205_);
v___x_1210_ = lean_usize_of_nat(v_stop_1202_);
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1197_, v_f_1198_, v_as_1200_, v___x_1209_, v___x_1210_, v_init_1199_);
return v___x_1211_;
}
}
else
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_nat_dec_lt(v_stop_1202_, v_start_1201_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_inc(v_toPure_1204_);
lean_dec_ref(v_as_1200_);
lean_dec(v_f_1198_);
lean_dec_ref(v_inst_1197_);
v___x_1213_ = lean_apply_2(v_toPure_1204_, lean_box(0), v_init_1199_);
return v___x_1213_;
}
else
{
size_t v___x_1214_; size_t v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = lean_usize_of_nat(v_start_1201_);
v___x_1215_ = lean_usize_of_nat(v_stop_1202_);
v___x_1216_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1197_, v_f_1198_, v_as_1200_, v___x_1214_, v___x_1215_, v_init_1199_);
return v___x_1216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg___boxed(lean_object* v_inst_1217_, lean_object* v_f_1218_, lean_object* v_init_1219_, lean_object* v_as_1220_, lean_object* v_start_1221_, lean_object* v_stop_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Array_foldrMUnsafe___redArg(v_inst_1217_, v_f_1218_, v_init_1219_, v_as_1220_, v_start_1221_, v_stop_1222_);
lean_dec(v_stop_1222_);
lean_dec(v_start_1221_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe(lean_object* v_00_u03b1_1224_, lean_object* v_00_u03b2_1225_, lean_object* v_m_1226_, lean_object* v_inst_1227_, lean_object* v_f_1228_, lean_object* v_init_1229_, lean_object* v_as_1230_, lean_object* v_start_1231_, lean_object* v_stop_1232_){
_start:
{
lean_object* v_toApplicative_1233_; lean_object* v_toPure_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v_toApplicative_1233_ = lean_ctor_get(v_inst_1227_, 0);
v_toPure_1234_ = lean_ctor_get(v_toApplicative_1233_, 1);
v___x_1235_ = lean_array_get_size(v_as_1230_);
v___x_1236_ = lean_nat_dec_le(v_start_1231_, v___x_1235_);
if (v___x_1236_ == 0)
{
uint8_t v___x_1237_; 
v___x_1237_ = lean_nat_dec_lt(v_stop_1232_, v___x_1235_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
lean_inc(v_toPure_1234_);
lean_dec_ref(v_as_1230_);
lean_dec(v_f_1228_);
lean_dec_ref(v_inst_1227_);
v___x_1238_ = lean_apply_2(v_toPure_1234_, lean_box(0), v_init_1229_);
return v___x_1238_;
}
else
{
size_t v___x_1239_; size_t v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = lean_usize_of_nat(v___x_1235_);
v___x_1240_ = lean_usize_of_nat(v_stop_1232_);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1227_, v_f_1228_, v_as_1230_, v___x_1239_, v___x_1240_, v_init_1229_);
return v___x_1241_;
}
}
else
{
uint8_t v___x_1242_; 
v___x_1242_ = lean_nat_dec_lt(v_stop_1232_, v_start_1231_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
lean_inc(v_toPure_1234_);
lean_dec_ref(v_as_1230_);
lean_dec(v_f_1228_);
lean_dec_ref(v_inst_1227_);
v___x_1243_ = lean_apply_2(v_toPure_1234_, lean_box(0), v_init_1229_);
return v___x_1243_;
}
else
{
size_t v___x_1244_; size_t v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = lean_usize_of_nat(v_start_1231_);
v___x_1245_ = lean_usize_of_nat(v_stop_1232_);
v___x_1246_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1227_, v_f_1228_, v_as_1230_, v___x_1244_, v___x_1245_, v_init_1229_);
return v___x_1246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___boxed(lean_object* v_00_u03b1_1247_, lean_object* v_00_u03b2_1248_, lean_object* v_m_1249_, lean_object* v_inst_1250_, lean_object* v_f_1251_, lean_object* v_init_1252_, lean_object* v_as_1253_, lean_object* v_start_1254_, lean_object* v_stop_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Array_foldrMUnsafe(v_00_u03b1_1247_, v_00_u03b2_1248_, v_m_1249_, v_inst_1250_, v_f_1251_, v_init_1252_, v_as_1253_, v_start_1254_, v_stop_1255_);
lean_dec(v_stop_1255_);
lean_dec(v_start_1254_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0___boxed(lean_object* v_inst_1257_, lean_object* v_f_1258_, lean_object* v_as_1259_, lean_object* v_stop_1260_, lean_object* v_n_1261_, lean_object* v_____do__lift_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Array_foldrM_fold___redArg___lam__0(v_inst_1257_, v_f_1258_, v_as_1259_, v_stop_1260_, v_n_1261_, v_____do__lift_1262_);
lean_dec(v_n_1261_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg(lean_object* v_inst_1264_, lean_object* v_f_1265_, lean_object* v_as_1266_, lean_object* v_stop_1267_, lean_object* v_i_1268_, lean_object* v_b_1269_){
_start:
{
lean_object* v_toApplicative_1270_; lean_object* v_toBind_1271_; lean_object* v_toPure_1272_; uint8_t v___x_1273_; 
v_toApplicative_1270_ = lean_ctor_get(v_inst_1264_, 0);
v_toBind_1271_ = lean_ctor_get(v_inst_1264_, 1);
lean_inc(v_toBind_1271_);
v_toPure_1272_ = lean_ctor_get(v_toApplicative_1270_, 1);
v___x_1273_ = lean_nat_dec_eq(v_i_1268_, v_stop_1267_);
if (v___x_1273_ == 0)
{
lean_object* v_zero_1274_; uint8_t v_isZero_1275_; 
v_zero_1274_ = lean_unsigned_to_nat(0u);
v_isZero_1275_ = lean_nat_dec_eq(v_i_1268_, v_zero_1274_);
if (v_isZero_1275_ == 1)
{
lean_object* v___x_1276_; 
lean_inc(v_toPure_1272_);
lean_dec(v_toBind_1271_);
lean_dec(v_stop_1267_);
lean_dec_ref(v_as_1266_);
lean_dec(v_f_1265_);
lean_dec_ref(v_inst_1264_);
v___x_1276_ = lean_apply_2(v_toPure_1272_, lean_box(0), v_b_1269_);
return v___x_1276_;
}
else
{
lean_object* v_one_1277_; lean_object* v_n_1278_; lean_object* v___f_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_one_1277_ = lean_unsigned_to_nat(1u);
v_n_1278_ = lean_nat_sub(v_i_1268_, v_one_1277_);
lean_inc(v_n_1278_);
lean_inc_ref(v_as_1266_);
lean_inc(v_f_1265_);
v___f_1279_ = lean_alloc_closure((void*)(l_Array_foldrM_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1279_, 0, v_inst_1264_);
lean_closure_set(v___f_1279_, 1, v_f_1265_);
lean_closure_set(v___f_1279_, 2, v_as_1266_);
lean_closure_set(v___f_1279_, 3, v_stop_1267_);
lean_closure_set(v___f_1279_, 4, v_n_1278_);
v___x_1280_ = lean_array_fget(v_as_1266_, v_n_1278_);
lean_dec(v_n_1278_);
lean_dec_ref(v_as_1266_);
v___x_1281_ = lean_apply_2(v_f_1265_, v___x_1280_, v_b_1269_);
v___x_1282_ = lean_apply_4(v_toBind_1271_, lean_box(0), lean_box(0), v___x_1281_, v___f_1279_);
return v___x_1282_;
}
}
else
{
lean_object* v___x_1283_; 
lean_inc(v_toPure_1272_);
lean_dec(v_toBind_1271_);
lean_dec(v_stop_1267_);
lean_dec_ref(v_as_1266_);
lean_dec(v_f_1265_);
lean_dec_ref(v_inst_1264_);
v___x_1283_ = lean_apply_2(v_toPure_1272_, lean_box(0), v_b_1269_);
return v___x_1283_;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0(lean_object* v_inst_1284_, lean_object* v_f_1285_, lean_object* v_as_1286_, lean_object* v_stop_1287_, lean_object* v_n_1288_, lean_object* v_____do__lift_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Array_foldrM_fold___redArg(v_inst_1284_, v_f_1285_, v_as_1286_, v_stop_1287_, v_n_1288_, v_____do__lift_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___boxed(lean_object* v_inst_1291_, lean_object* v_f_1292_, lean_object* v_as_1293_, lean_object* v_stop_1294_, lean_object* v_i_1295_, lean_object* v_b_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Array_foldrM_fold___redArg(v_inst_1291_, v_f_1292_, v_as_1293_, v_stop_1294_, v_i_1295_, v_b_1296_);
lean_dec(v_i_1295_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold(lean_object* v_00_u03b1_1298_, lean_object* v_00_u03b2_1299_, lean_object* v_m_1300_, lean_object* v_inst_1301_, lean_object* v_f_1302_, lean_object* v_as_1303_, lean_object* v_stop_1304_, lean_object* v_i_1305_, lean_object* v_h_1306_, lean_object* v_b_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Array_foldrM_fold___redArg(v_inst_1301_, v_f_1302_, v_as_1303_, v_stop_1304_, v_i_1305_, v_b_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___boxed(lean_object* v_00_u03b1_1309_, lean_object* v_00_u03b2_1310_, lean_object* v_m_1311_, lean_object* v_inst_1312_, lean_object* v_f_1313_, lean_object* v_as_1314_, lean_object* v_stop_1315_, lean_object* v_i_1316_, lean_object* v_h_1317_, lean_object* v_b_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Array_foldrM_fold(v_00_u03b1_1309_, v_00_u03b2_1310_, v_m_1311_, v_inst_1312_, v_f_1313_, v_as_1314_, v_stop_1315_, v_i_1316_, v_h_1317_, v_b_1318_);
lean_dec(v_i_1316_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed(lean_object* v_i_1320_, lean_object* v_bs_x27_1321_, lean_object* v_inst_1322_, lean_object* v_f_1323_, lean_object* v_sz_1324_, lean_object* v_vNew_1325_){
_start:
{
size_t v_i_boxed_1326_; size_t v_sz_boxed_1327_; lean_object* v_res_1328_; 
v_i_boxed_1326_ = lean_unbox_usize(v_i_1320_);
lean_dec(v_i_1320_);
v_sz_boxed_1327_ = lean_unbox_usize(v_sz_1324_);
lean_dec(v_sz_1324_);
v_res_1328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(v_i_boxed_1326_, v_bs_x27_1321_, v_inst_1322_, v_f_1323_, v_sz_boxed_1327_, v_vNew_1325_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(lean_object* v_inst_1329_, lean_object* v_f_1330_, size_t v_sz_1331_, size_t v_i_1332_, lean_object* v_bs_1333_){
_start:
{
lean_object* v_toApplicative_1334_; lean_object* v_toBind_1335_; lean_object* v_toPure_1336_; uint8_t v___x_1337_; 
v_toApplicative_1334_ = lean_ctor_get(v_inst_1329_, 0);
v_toBind_1335_ = lean_ctor_get(v_inst_1329_, 1);
lean_inc(v_toBind_1335_);
v_toPure_1336_ = lean_ctor_get(v_toApplicative_1334_, 1);
v___x_1337_ = lean_usize_dec_lt(v_i_1332_, v_sz_1331_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
lean_inc(v_toPure_1336_);
lean_dec(v_toBind_1335_);
lean_dec(v_f_1330_);
lean_dec_ref(v_inst_1329_);
v___x_1338_ = lean_apply_2(v_toPure_1336_, lean_box(0), v_bs_1333_);
return v___x_1338_;
}
else
{
lean_object* v_v_1339_; lean_object* v___x_1340_; lean_object* v_bs_x27_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___f_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_v_1339_ = lean_array_uget(v_bs_1333_, v_i_1332_);
v___x_1340_ = lean_unsigned_to_nat(0u);
v_bs_x27_1341_ = lean_array_uset(v_bs_1333_, v_i_1332_, v___x_1340_);
v___x_1342_ = lean_box_usize(v_i_1332_);
v___x_1343_ = lean_box_usize(v_sz_1331_);
lean_inc(v_f_1330_);
v___f_1344_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1344_, 0, v___x_1342_);
lean_closure_set(v___f_1344_, 1, v_bs_x27_1341_);
lean_closure_set(v___f_1344_, 2, v_inst_1329_);
lean_closure_set(v___f_1344_, 3, v_f_1330_);
lean_closure_set(v___f_1344_, 4, v___x_1343_);
v___x_1345_ = lean_apply_1(v_f_1330_, v_v_1339_);
v___x_1346_ = lean_apply_4(v_toBind_1335_, lean_box(0), lean_box(0), v___x_1345_, v___f_1344_);
return v___x_1346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(size_t v_i_1347_, lean_object* v_bs_x27_1348_, lean_object* v_inst_1349_, lean_object* v_f_1350_, size_t v_sz_1351_, lean_object* v_vNew_1352_){
_start:
{
size_t v___x_1353_; size_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1353_ = ((size_t)1ULL);
v___x_1354_ = lean_usize_add(v_i_1347_, v___x_1353_);
v___x_1355_ = lean_array_uset(v_bs_x27_1348_, v_i_1347_, v_vNew_1352_);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1349_, v_f_1350_, v_sz_1351_, v___x_1354_, v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___boxed(lean_object* v_inst_1357_, lean_object* v_f_1358_, lean_object* v_sz_1359_, lean_object* v_i_1360_, lean_object* v_bs_1361_){
_start:
{
size_t v_sz_boxed_1362_; size_t v_i_boxed_1363_; lean_object* v_res_1364_; 
v_sz_boxed_1362_ = lean_unbox_usize(v_sz_1359_);
lean_dec(v_sz_1359_);
v_i_boxed_1363_ = lean_unbox_usize(v_i_1360_);
lean_dec(v_i_1360_);
v_res_1364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1357_, v_f_1358_, v_sz_boxed_1362_, v_i_boxed_1363_, v_bs_1361_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object* v_00_u03b1_1365_, lean_object* v_00_u03b2_1366_, lean_object* v_m_1367_, lean_object* v_inst_1368_, lean_object* v_f_1369_, size_t v_sz_1370_, size_t v_i_1371_, lean_object* v_bs_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1368_, v_f_1369_, v_sz_1370_, v_i_1371_, v_bs_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___boxed(lean_object* v_00_u03b1_1374_, lean_object* v_00_u03b2_1375_, lean_object* v_m_1376_, lean_object* v_inst_1377_, lean_object* v_f_1378_, lean_object* v_sz_1379_, lean_object* v_i_1380_, lean_object* v_bs_1381_){
_start:
{
size_t v_sz_boxed_1382_; size_t v_i_boxed_1383_; lean_object* v_res_1384_; 
v_sz_boxed_1382_ = lean_unbox_usize(v_sz_1379_);
lean_dec(v_sz_1379_);
v_i_boxed_1383_ = lean_unbox_usize(v_i_1380_);
lean_dec(v_i_1380_);
v_res_1384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(v_00_u03b1_1374_, v_00_u03b2_1375_, v_m_1376_, v_inst_1377_, v_f_1378_, v_sz_boxed_1382_, v_i_boxed_1383_, v_bs_1381_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe___redArg(lean_object* v_inst_1385_, lean_object* v_f_1386_, lean_object* v_as_1387_){
_start:
{
size_t v_sz_1388_; size_t v___x_1389_; lean_object* v___x_1390_; 
v_sz_1388_ = lean_array_size(v_as_1387_);
v___x_1389_ = ((size_t)0ULL);
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1385_, v_f_1386_, v_sz_1388_, v___x_1389_, v_as_1387_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe(lean_object* v_00_u03b1_1391_, lean_object* v_00_u03b2_1392_, lean_object* v_m_1393_, lean_object* v_inst_1394_, lean_object* v_f_1395_, lean_object* v_as_1396_){
_start:
{
size_t v_sz_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v_sz_1397_ = lean_array_size(v_as_1396_);
v___x_1398_ = ((size_t)0ULL);
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1394_, v_f_1395_, v_sz_1397_, v___x_1398_, v_as_1396_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0___boxed(lean_object* v_i_1400_, lean_object* v_bs_1401_, lean_object* v_inst_1402_, lean_object* v_f_1403_, lean_object* v_as_1404_, lean_object* v_____do__lift_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0(v_i_1400_, v_bs_1401_, v_inst_1402_, v_f_1403_, v_as_1404_, v_____do__lift_1405_);
lean_dec(v_i_1400_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(lean_object* v_inst_1407_, lean_object* v_f_1408_, lean_object* v_as_1409_, lean_object* v_i_1410_, lean_object* v_bs_1411_){
_start:
{
lean_object* v_toApplicative_1412_; lean_object* v_toBind_1413_; lean_object* v_toPure_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v_toApplicative_1412_ = lean_ctor_get(v_inst_1407_, 0);
v_toBind_1413_ = lean_ctor_get(v_inst_1407_, 1);
lean_inc(v_toBind_1413_);
v_toPure_1414_ = lean_ctor_get(v_toApplicative_1412_, 1);
v___x_1415_ = lean_array_get_size(v_as_1409_);
v___x_1416_ = lean_nat_dec_lt(v_i_1410_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
lean_inc(v_toPure_1414_);
lean_dec(v_toBind_1413_);
lean_dec(v_i_1410_);
lean_dec_ref(v_as_1409_);
lean_dec(v_f_1408_);
lean_dec_ref(v_inst_1407_);
v___x_1417_ = lean_apply_2(v_toPure_1414_, lean_box(0), v_bs_1411_);
return v___x_1417_;
}
else
{
lean_object* v___f_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_inc_ref(v_as_1409_);
lean_inc(v_f_1408_);
lean_inc(v_i_1410_);
v___f_1418_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1418_, 0, v_i_1410_);
lean_closure_set(v___f_1418_, 1, v_bs_1411_);
lean_closure_set(v___f_1418_, 2, v_inst_1407_);
lean_closure_set(v___f_1418_, 3, v_f_1408_);
lean_closure_set(v___f_1418_, 4, v_as_1409_);
v___x_1419_ = lean_array_fget(v_as_1409_, v_i_1410_);
lean_dec(v_i_1410_);
lean_dec_ref(v_as_1409_);
v___x_1420_ = lean_apply_1(v_f_1408_, v___x_1419_);
v___x_1421_ = lean_apply_4(v_toBind_1413_, lean_box(0), lean_box(0), v___x_1420_, v___f_1418_);
return v___x_1421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0(lean_object* v_i_1422_, lean_object* v_bs_1423_, lean_object* v_inst_1424_, lean_object* v_f_1425_, lean_object* v_as_1426_, lean_object* v_____do__lift_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1428_ = lean_unsigned_to_nat(1u);
v___x_1429_ = lean_nat_add(v_i_1422_, v___x_1428_);
v___x_1430_ = lean_array_push(v_bs_1423_, v_____do__lift_1427_);
v___x_1431_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(v_inst_1424_, v_f_1425_, v_as_1426_, v___x_1429_, v___x_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map(lean_object* v_00_u03b1_1432_, lean_object* v_00_u03b2_1433_, lean_object* v_m_1434_, lean_object* v_inst_1435_, lean_object* v_f_1436_, lean_object* v_as_1437_, lean_object* v_i_1438_, lean_object* v_bs_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(v_inst_1435_, v_f_1436_, v_as_1437_, v_i_1438_, v_bs_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0___boxed(lean_object* v_i_1441_, lean_object* v_bs_x27_1442_, lean_object* v_inst_1443_, lean_object* v_f_1444_, lean_object* v_sz_1445_, lean_object* v_vNew_1446_){
_start:
{
size_t v_i_boxed_1447_; size_t v_sz_boxed_1448_; lean_object* v_res_1449_; 
v_i_boxed_1447_ = lean_unbox_usize(v_i_1441_);
lean_dec(v_i_1441_);
v_sz_boxed_1448_ = lean_unbox_usize(v_sz_1445_);
lean_dec(v_sz_1445_);
v_res_1449_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0(v_i_boxed_1447_, v_bs_x27_1442_, v_inst_1443_, v_f_1444_, v_sz_boxed_1448_, v_vNew_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(lean_object* v_inst_1450_, lean_object* v_f_1451_, size_t v_sz_1452_, size_t v_i_1453_, lean_object* v_bs_1454_){
_start:
{
lean_object* v_toApplicative_1455_; lean_object* v_toBind_1456_; lean_object* v_toPure_1457_; uint8_t v___x_1458_; 
v_toApplicative_1455_ = lean_ctor_get(v_inst_1450_, 0);
v_toBind_1456_ = lean_ctor_get(v_inst_1450_, 1);
lean_inc(v_toBind_1456_);
v_toPure_1457_ = lean_ctor_get(v_toApplicative_1455_, 1);
v___x_1458_ = lean_usize_dec_lt(v_i_1453_, v_sz_1452_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; 
lean_inc(v_toPure_1457_);
lean_dec(v_toBind_1456_);
lean_dec(v_f_1451_);
lean_dec_ref(v_inst_1450_);
v___x_1459_ = lean_apply_2(v_toPure_1457_, lean_box(0), v_bs_1454_);
return v___x_1459_;
}
else
{
lean_object* v_v_1460_; lean_object* v___x_1461_; lean_object* v_bs_x27_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___f_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_v_1460_ = lean_array_uget(v_bs_1454_, v_i_1453_);
v___x_1461_ = lean_unsigned_to_nat(0u);
v_bs_x27_1462_ = lean_array_uset(v_bs_1454_, v_i_1453_, v___x_1461_);
v___x_1463_ = lean_box_usize(v_i_1453_);
v___x_1464_ = lean_box_usize(v_sz_1452_);
lean_inc(v_f_1451_);
v___f_1465_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1465_, 0, v___x_1463_);
lean_closure_set(v___f_1465_, 1, v_bs_x27_1462_);
lean_closure_set(v___f_1465_, 2, v_inst_1450_);
lean_closure_set(v___f_1465_, 3, v_f_1451_);
lean_closure_set(v___f_1465_, 4, v___x_1464_);
v___x_1466_ = lean_usize_to_nat(v_i_1453_);
v___x_1467_ = lean_apply_3(v_f_1451_, v___x_1466_, v_v_1460_, lean_box(0));
v___x_1468_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1467_, v___f_1465_);
return v___x_1468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___lam__0(size_t v_i_1469_, lean_object* v_bs_x27_1470_, lean_object* v_inst_1471_, lean_object* v_f_1472_, size_t v_sz_1473_, lean_object* v_vNew_1474_){
_start:
{
size_t v___x_1475_; size_t v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1475_ = ((size_t)1ULL);
v___x_1476_ = lean_usize_add(v_i_1469_, v___x_1475_);
v___x_1477_ = lean_array_uset(v_bs_x27_1470_, v_i_1469_, v_vNew_1474_);
v___x_1478_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1471_, v_f_1472_, v_sz_1473_, v___x_1476_, v___x_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg___boxed(lean_object* v_inst_1479_, lean_object* v_f_1480_, lean_object* v_sz_1481_, lean_object* v_i_1482_, lean_object* v_bs_1483_){
_start:
{
size_t v_sz_boxed_1484_; size_t v_i_boxed_1485_; lean_object* v_res_1486_; 
v_sz_boxed_1484_ = lean_unbox_usize(v_sz_1481_);
lean_dec(v_sz_1481_);
v_i_boxed_1485_ = lean_unbox_usize(v_i_1482_);
lean_dec(v_i_1482_);
v_res_1486_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1479_, v_f_1480_, v_sz_boxed_1484_, v_i_boxed_1485_, v_bs_1483_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object* v_00_u03b1_1487_, lean_object* v_00_u03b2_1488_, lean_object* v_m_1489_, lean_object* v_inst_1490_, lean_object* v_as_1491_, lean_object* v_f_1492_, size_t v_sz_1493_, size_t v_i_1494_, lean_object* v_bs_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1490_, v_f_1492_, v_sz_1493_, v_i_1494_, v_bs_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___boxed(lean_object* v_00_u03b1_1497_, lean_object* v_00_u03b2_1498_, lean_object* v_m_1499_, lean_object* v_inst_1500_, lean_object* v_as_1501_, lean_object* v_f_1502_, lean_object* v_sz_1503_, lean_object* v_i_1504_, lean_object* v_bs_1505_){
_start:
{
size_t v_sz_boxed_1506_; size_t v_i_boxed_1507_; lean_object* v_res_1508_; 
v_sz_boxed_1506_ = lean_unbox_usize(v_sz_1503_);
lean_dec(v_sz_1503_);
v_i_boxed_1507_ = lean_unbox_usize(v_i_1504_);
lean_dec(v_i_1504_);
v_res_1508_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(v_00_u03b1_1497_, v_00_u03b2_1498_, v_m_1499_, v_inst_1500_, v_as_1501_, v_f_1502_, v_sz_boxed_1506_, v_i_boxed_1507_, v_bs_1505_);
lean_dec_ref(v_as_1501_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxMUnsafe___redArg(lean_object* v_inst_1509_, lean_object* v_as_1510_, lean_object* v_f_1511_){
_start:
{
size_t v_sz_1512_; size_t v___x_1513_; lean_object* v___x_1514_; 
v_sz_1512_ = lean_array_size(v_as_1510_);
v___x_1513_ = ((size_t)0ULL);
v___x_1514_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1509_, v_f_1511_, v_sz_1512_, v___x_1513_, v_as_1510_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxMUnsafe(lean_object* v_00_u03b1_1515_, lean_object* v_00_u03b2_1516_, lean_object* v_m_1517_, lean_object* v_inst_1518_, lean_object* v_as_1519_, lean_object* v_f_1520_){
_start:
{
size_t v_sz_1521_; size_t v___x_1522_; lean_object* v___x_1523_; 
v_sz_1521_ = lean_array_size(v_as_1519_);
v___x_1522_ = ((size_t)0ULL);
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1518_, v_f_1520_, v_sz_1521_, v___x_1522_, v_as_1519_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1524_, lean_object* v_bs_1525_, lean_object* v_inst_1526_, lean_object* v_as_1527_, lean_object* v_f_1528_, lean_object* v_n_1529_, lean_object* v_____do__lift_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Array_mapFinIdxM_map___redArg___lam__0(v_j_1524_, v_bs_1525_, v_inst_1526_, v_as_1527_, v_f_1528_, v_n_1529_, v_____do__lift_1530_);
lean_dec(v_n_1529_);
lean_dec(v_j_1524_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg(lean_object* v_inst_1532_, lean_object* v_as_1533_, lean_object* v_f_1534_, lean_object* v_i_1535_, lean_object* v_j_1536_, lean_object* v_bs_1537_){
_start:
{
lean_object* v_toApplicative_1538_; lean_object* v_toBind_1539_; lean_object* v_toPure_1540_; lean_object* v_zero_1541_; uint8_t v_isZero_1542_; 
v_toApplicative_1538_ = lean_ctor_get(v_inst_1532_, 0);
v_toBind_1539_ = lean_ctor_get(v_inst_1532_, 1);
lean_inc(v_toBind_1539_);
v_toPure_1540_ = lean_ctor_get(v_toApplicative_1538_, 1);
v_zero_1541_ = lean_unsigned_to_nat(0u);
v_isZero_1542_ = lean_nat_dec_eq(v_i_1535_, v_zero_1541_);
if (v_isZero_1542_ == 1)
{
lean_object* v___x_1543_; 
lean_inc(v_toPure_1540_);
lean_dec(v_toBind_1539_);
lean_dec(v_j_1536_);
lean_dec(v_f_1534_);
lean_dec_ref(v_as_1533_);
lean_dec_ref(v_inst_1532_);
v___x_1543_ = lean_apply_2(v_toPure_1540_, lean_box(0), v_bs_1537_);
return v___x_1543_;
}
else
{
lean_object* v_one_1544_; lean_object* v_n_1545_; lean_object* v___f_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_one_1544_ = lean_unsigned_to_nat(1u);
v_n_1545_ = lean_nat_sub(v_i_1535_, v_one_1544_);
lean_inc(v_f_1534_);
lean_inc_ref(v_as_1533_);
lean_inc(v_j_1536_);
v___f_1546_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1546_, 0, v_j_1536_);
lean_closure_set(v___f_1546_, 1, v_bs_1537_);
lean_closure_set(v___f_1546_, 2, v_inst_1532_);
lean_closure_set(v___f_1546_, 3, v_as_1533_);
lean_closure_set(v___f_1546_, 4, v_f_1534_);
lean_closure_set(v___f_1546_, 5, v_n_1545_);
v___x_1547_ = lean_array_fget(v_as_1533_, v_j_1536_);
lean_dec_ref(v_as_1533_);
v___x_1548_ = lean_apply_3(v_f_1534_, v_j_1536_, v___x_1547_, lean_box(0));
v___x_1549_ = lean_apply_4(v_toBind_1539_, lean_box(0), lean_box(0), v___x_1548_, v___f_1546_);
return v___x_1549_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1550_, lean_object* v_bs_1551_, lean_object* v_inst_1552_, lean_object* v_as_1553_, lean_object* v_f_1554_, lean_object* v_n_1555_, lean_object* v_____do__lift_1556_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1557_ = lean_unsigned_to_nat(1u);
v___x_1558_ = lean_nat_add(v_j_1550_, v___x_1557_);
v___x_1559_ = lean_array_push(v_bs_1551_, v_____do__lift_1556_);
v___x_1560_ = l_Array_mapFinIdxM_map___redArg(v_inst_1552_, v_as_1553_, v_f_1554_, v_n_1555_, v___x_1558_, v___x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1561_, lean_object* v_as_1562_, lean_object* v_f_1563_, lean_object* v_i_1564_, lean_object* v_j_1565_, lean_object* v_bs_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Array_mapFinIdxM_map___redArg(v_inst_1561_, v_as_1562_, v_f_1563_, v_i_1564_, v_j_1565_, v_bs_1566_);
lean_dec(v_i_1564_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map(lean_object* v_00_u03b1_1568_, lean_object* v_00_u03b2_1569_, lean_object* v_m_1570_, lean_object* v_inst_1571_, lean_object* v_as_1572_, lean_object* v_f_1573_, lean_object* v_i_1574_, lean_object* v_j_1575_, lean_object* v_inv_1576_, lean_object* v_bs_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Array_mapFinIdxM_map___redArg(v_inst_1571_, v_as_1572_, v_f_1573_, v_i_1574_, v_j_1575_, v_bs_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___boxed(lean_object* v_00_u03b1_1579_, lean_object* v_00_u03b2_1580_, lean_object* v_m_1581_, lean_object* v_inst_1582_, lean_object* v_as_1583_, lean_object* v_f_1584_, lean_object* v_i_1585_, lean_object* v_j_1586_, lean_object* v_inv_1587_, lean_object* v_bs_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Array_mapFinIdxM_map(v_00_u03b1_1579_, v_00_u03b2_1580_, v_m_1581_, v_inst_1582_, v_as_1583_, v_f_1584_, v_i_1585_, v_j_1586_, v_inv_1587_, v_bs_1588_);
lean_dec(v_i_1585_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg___lam__0(lean_object* v_f_1590_, lean_object* v_i_1591_, lean_object* v_a_1592_, lean_object* v_x_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_apply_2(v_f_1590_, v_i_1591_, v_a_1592_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg(lean_object* v_inst_1595_, lean_object* v_f_1596_, lean_object* v_as_1597_){
_start:
{
lean_object* v___f_1598_; size_t v_sz_1599_; size_t v___x_1600_; lean_object* v___x_1601_; 
v___f_1598_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1598_, 0, v_f_1596_);
v_sz_1599_ = lean_array_size(v_as_1597_);
v___x_1600_ = ((size_t)0ULL);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1595_, v___f_1598_, v_sz_1599_, v___x_1600_, v_as_1597_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM(lean_object* v_00_u03b1_1602_, lean_object* v_00_u03b2_1603_, lean_object* v_m_1604_, lean_object* v_inst_1605_, lean_object* v_f_1606_, lean_object* v_as_1607_){
_start:
{
lean_object* v___f_1608_; size_t v_sz_1609_; size_t v___x_1610_; lean_object* v___x_1611_; 
v___f_1608_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1608_, 0, v_f_1606_);
v_sz_1609_ = lean_array_size(v_as_1607_);
v___x_1610_ = ((size_t)0ULL);
v___x_1611_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v_inst_1605_, v___f_1608_, v_sz_1609_, v___x_1610_, v_as_1607_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed(lean_object* v_i_1612_, lean_object* v_inst_1613_, lean_object* v_f_1614_, lean_object* v_as_1615_, lean_object* v_x_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(v_i_1612_, v_inst_1613_, v_f_1614_, v_as_1615_, v_x_1616_);
lean_dec(v_i_1612_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(lean_object* v_inst_1618_, lean_object* v_f_1619_, lean_object* v_as_1620_, lean_object* v_i_1621_){
_start:
{
lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = lean_array_get_size(v_as_1620_);
v___x_1623_ = lean_nat_dec_lt(v_i_1621_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_object* v_failure_1624_; lean_object* v___x_1625_; 
lean_dec(v_i_1621_);
lean_dec_ref(v_as_1620_);
lean_dec(v_f_1619_);
v_failure_1624_ = lean_ctor_get(v_inst_1618_, 1);
lean_inc(v_failure_1624_);
lean_dec_ref(v_inst_1618_);
v___x_1625_ = lean_apply_1(v_failure_1624_, lean_box(0));
return v___x_1625_;
}
else
{
lean_object* v_orElse_1626_; lean_object* v___f_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v_orElse_1626_ = lean_ctor_get(v_inst_1618_, 2);
lean_inc(v_orElse_1626_);
lean_inc_ref(v_as_1620_);
lean_inc(v_f_1619_);
lean_inc(v_i_1621_);
v___f_1627_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1627_, 0, v_i_1621_);
lean_closure_set(v___f_1627_, 1, v_inst_1618_);
lean_closure_set(v___f_1627_, 2, v_f_1619_);
lean_closure_set(v___f_1627_, 3, v_as_1620_);
v___x_1628_ = lean_array_fget(v_as_1620_, v_i_1621_);
lean_dec(v_i_1621_);
lean_dec_ref(v_as_1620_);
v___x_1629_ = lean_apply_1(v_f_1619_, v___x_1628_);
v___x_1630_ = lean_apply_3(v_orElse_1626_, lean_box(0), v___x_1629_, v___f_1627_);
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(lean_object* v_i_1631_, lean_object* v_inst_1632_, lean_object* v_f_1633_, lean_object* v_as_1634_, lean_object* v_x_1635_){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = lean_unsigned_to_nat(1u);
v___x_1637_ = lean_nat_add(v_i_1631_, v___x_1636_);
v___x_1638_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1632_, v_f_1633_, v_as_1634_, v___x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_object* v_00_u03b2_1639_, lean_object* v_00_u03b1_1640_, lean_object* v_m_1641_, lean_object* v_inst_1642_, lean_object* v_f_1643_, lean_object* v_as_1644_, lean_object* v_i_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1642_, v_f_1643_, v_as_1644_, v_i_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM___redArg(lean_object* v_inst_1647_, lean_object* v_f_1648_, lean_object* v_as_1649_){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_unsigned_to_nat(0u);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1647_, v_f_1648_, v_as_1649_, v___x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM(lean_object* v_00_u03b2_1652_, lean_object* v_00_u03b1_1653_, lean_object* v_m_1654_, lean_object* v_inst_1655_, lean_object* v_f_1656_, lean_object* v_as_1657_){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1655_, v_f_1656_, v_as_1657_, v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__0(lean_object* v___x_1660_, lean_object* v_toPure_1661_, lean_object* v___x_1662_, lean_object* v_____do__lift_1663_){
_start:
{
if (lean_obj_tag(v_____do__lift_1663_) == 1)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec_ref(v___x_1662_);
v___x_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1664_, 0, v_____do__lift_1663_);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v___x_1660_);
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
v___x_1667_ = lean_apply_2(v_toPure_1661_, lean_box(0), v___x_1666_);
return v___x_1667_;
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec(v_____do__lift_1663_);
v___x_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1662_);
v___x_1669_ = lean_apply_2(v_toPure_1661_, lean_box(0), v___x_1668_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1(lean_object* v_f_1670_, lean_object* v_toBind_1671_, lean_object* v___f_1672_, lean_object* v_a_1673_, lean_object* v_x_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_apply_1(v_f_1670_, v_a_1673_);
v___x_1677_ = lean_apply_4(v_toBind_1671_, lean_box(0), lean_box(0), v___x_1676_, v___f_1672_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1___boxed(lean_object* v_f_1678_, lean_object* v_toBind_1679_, lean_object* v___f_1680_, lean_object* v_a_1681_, lean_object* v_x_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Array_findSomeM_x3f___redArg___lam__1(v_f_1678_, v_toBind_1679_, v___f_1680_, v_a_1681_, v_x_1682_, v___y_1683_);
lean_dec_ref(v___y_1683_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__2(lean_object* v_toPure_1685_, lean_object* v_____s_1686_){
_start:
{
lean_object* v_fst_1687_; 
v_fst_1687_ = lean_ctor_get(v_____s_1686_, 0);
lean_inc(v_fst_1687_);
lean_dec_ref(v_____s_1686_);
if (lean_obj_tag(v_fst_1687_) == 0)
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = lean_box(0);
v___x_1689_ = lean_apply_2(v_toPure_1685_, lean_box(0), v___x_1688_);
return v___x_1689_;
}
else
{
lean_object* v_val_1690_; lean_object* v___x_1691_; 
v_val_1690_ = lean_ctor_get(v_fst_1687_, 0);
lean_inc(v_val_1690_);
lean_dec_ref_known(v_fst_1687_, 1);
v___x_1691_ = lean_apply_2(v_toPure_1685_, lean_box(0), v_val_1690_);
return v___x_1691_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg(lean_object* v_inst_1695_, lean_object* v_f_1696_, lean_object* v_as_1697_){
_start:
{
lean_object* v_toApplicative_1698_; lean_object* v_toBind_1699_; lean_object* v_toPure_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___f_1703_; lean_object* v___f_1704_; lean_object* v___f_1705_; size_t v_sz_1706_; size_t v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_toApplicative_1698_ = lean_ctor_get(v_inst_1695_, 0);
v_toBind_1699_ = lean_ctor_get(v_inst_1695_, 1);
lean_inc_n(v_toBind_1699_, 2);
v_toPure_1700_ = lean_ctor_get(v_toApplicative_1698_, 1);
v___x_1701_ = lean_box(0);
v___x_1702_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1700_, 2);
v___f_1703_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1703_, 0, v___x_1701_);
lean_closure_set(v___f_1703_, 1, v_toPure_1700_);
lean_closure_set(v___f_1703_, 2, v___x_1702_);
v___f_1704_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1704_, 0, v_f_1696_);
lean_closure_set(v___f_1704_, 1, v_toBind_1699_);
lean_closure_set(v___f_1704_, 2, v___f_1703_);
v___f_1705_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1705_, 0, v_toPure_1700_);
v_sz_1706_ = lean_array_size(v_as_1697_);
v___x_1707_ = ((size_t)0ULL);
v___x_1708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1695_, v_as_1697_, v___f_1704_, v_sz_1706_, v___x_1707_, v___x_1702_);
v___x_1709_ = lean_apply_4(v_toBind_1699_, lean_box(0), lean_box(0), v___x_1708_, v___f_1705_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f(lean_object* v_00_u03b1_1710_, lean_object* v_00_u03b2_1711_, lean_object* v_m_1712_, lean_object* v_inst_1713_, lean_object* v_f_1714_, lean_object* v_as_1715_){
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
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0(lean_object* v___x_1728_, lean_object* v_toPure_1729_, lean_object* v_a_1730_, lean_object* v___x_1731_, uint8_t v_____do__lift_1732_){
_start:
{
if (v_____do__lift_1732_ == 0)
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_dec(v_a_1730_);
v___x_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1728_);
v___x_1734_ = lean_apply_2(v_toPure_1729_, lean_box(0), v___x_1733_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec_ref(v___x_1728_);
v___x_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1735_, 0, v_a_1730_);
v___x_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
lean_ctor_set(v___x_1737_, 1, v___x_1731_);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
v___x_1739_ = lean_apply_2(v_toPure_1729_, lean_box(0), v___x_1738_);
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0___boxed(lean_object* v___x_1740_, lean_object* v_toPure_1741_, lean_object* v_a_1742_, lean_object* v___x_1743_, lean_object* v_____do__lift_1744_){
_start:
{
uint8_t v_____do__lift_184__boxed_1745_; lean_object* v_res_1746_; 
v_____do__lift_184__boxed_1745_ = lean_unbox(v_____do__lift_1744_);
v_res_1746_ = l_Array_findM_x3f___redArg___lam__0(v___x_1740_, v_toPure_1741_, v_a_1742_, v___x_1743_, v_____do__lift_184__boxed_1745_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1(lean_object* v___x_1747_, lean_object* v_toPure_1748_, lean_object* v___x_1749_, lean_object* v_p_1750_, lean_object* v_toBind_1751_, lean_object* v_a_1752_, lean_object* v_x_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___f_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_inc(v_a_1752_);
v___f_1755_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1755_, 0, v___x_1747_);
lean_closure_set(v___f_1755_, 1, v_toPure_1748_);
lean_closure_set(v___f_1755_, 2, v_a_1752_);
lean_closure_set(v___f_1755_, 3, v___x_1749_);
v___x_1756_ = lean_apply_1(v_p_1750_, v_a_1752_);
v___x_1757_ = lean_apply_4(v_toBind_1751_, lean_box(0), lean_box(0), v___x_1756_, v___f_1755_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_1758_, lean_object* v_toPure_1759_, lean_object* v___x_1760_, lean_object* v_p_1761_, lean_object* v_toBind_1762_, lean_object* v_a_1763_, lean_object* v_x_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Array_findM_x3f___redArg___lam__1(v___x_1758_, v_toPure_1759_, v___x_1760_, v_p_1761_, v_toBind_1762_, v_a_1763_, v_x_1764_, v___y_1765_);
lean_dec_ref(v___y_1765_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg(lean_object* v_inst_1767_, lean_object* v_p_1768_, lean_object* v_as_1769_){
_start:
{
lean_object* v_toApplicative_1770_; lean_object* v_toBind_1771_; lean_object* v_toPure_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___f_1775_; lean_object* v___f_1776_; size_t v_sz_1777_; size_t v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v_toApplicative_1770_ = lean_ctor_get(v_inst_1767_, 0);
v_toBind_1771_ = lean_ctor_get(v_inst_1767_, 1);
lean_inc_n(v_toBind_1771_, 2);
v_toPure_1772_ = lean_ctor_get(v_toApplicative_1770_, 1);
v___x_1773_ = lean_box(0);
v___x_1774_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1772_, 2);
v___f_1775_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1775_, 0, v___x_1774_);
lean_closure_set(v___f_1775_, 1, v_toPure_1772_);
lean_closure_set(v___f_1775_, 2, v___x_1773_);
lean_closure_set(v___f_1775_, 3, v_p_1768_);
lean_closure_set(v___f_1775_, 4, v_toBind_1771_);
v___f_1776_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1776_, 0, v_toPure_1772_);
v_sz_1777_ = lean_array_size(v_as_1769_);
v___x_1778_ = ((size_t)0ULL);
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1767_, v_as_1769_, v___f_1775_, v_sz_1777_, v___x_1778_, v___x_1774_);
v___x_1780_ = lean_apply_4(v_toBind_1771_, lean_box(0), lean_box(0), v___x_1779_, v___f_1776_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f(lean_object* v_m_1781_, lean_object* v_00_u03b1_1782_, lean_object* v_inst_1783_, lean_object* v_p_1784_, lean_object* v_as_1785_){
_start:
{
lean_object* v_toApplicative_1786_; lean_object* v_toBind_1787_; lean_object* v_toPure_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___f_1791_; lean_object* v___f_1792_; size_t v_sz_1793_; size_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_toApplicative_1786_ = lean_ctor_get(v_inst_1783_, 0);
v_toBind_1787_ = lean_ctor_get(v_inst_1783_, 1);
lean_inc_n(v_toBind_1787_, 2);
v_toPure_1788_ = lean_ctor_get(v_toApplicative_1786_, 1);
v___x_1789_ = lean_box(0);
v___x_1790_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1788_, 2);
v___f_1791_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1791_, 0, v___x_1790_);
lean_closure_set(v___f_1791_, 1, v_toPure_1788_);
lean_closure_set(v___f_1791_, 2, v___x_1789_);
lean_closure_set(v___f_1791_, 3, v_p_1784_);
lean_closure_set(v___f_1791_, 4, v_toBind_1787_);
v___f_1792_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1792_, 0, v_toPure_1788_);
v_sz_1793_ = lean_array_size(v_as_1785_);
v___x_1794_ = ((size_t)0ULL);
v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1783_, v_as_1785_, v___f_1791_, v_sz_1793_, v___x_1794_, v___x_1790_);
v___x_1796_ = lean_apply_4(v_toBind_1787_, lean_box(0), lean_box(0), v___x_1795_, v___f_1792_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0(lean_object* v_snd_1797_, lean_object* v___x_1798_, lean_object* v_toPure_1799_, uint8_t v_____do__lift_1800_){
_start:
{
if (v_____do__lift_1800_ == 0)
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1801_ = lean_unsigned_to_nat(1u);
v___x_1802_ = lean_nat_add(v_snd_1797_, v___x_1801_);
lean_dec(v_snd_1797_);
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1798_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
v___x_1805_ = lean_apply_2(v_toPure_1799_, lean_box(0), v___x_1804_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec(v___x_1798_);
lean_inc(v_snd_1797_);
v___x_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1806_, 0, v_snd_1797_);
v___x_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
lean_ctor_set(v___x_1808_, 1, v_snd_1797_);
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
v___x_1810_ = lean_apply_2(v_toPure_1799_, lean_box(0), v___x_1809_);
return v___x_1810_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0___boxed(lean_object* v_snd_1811_, lean_object* v___x_1812_, lean_object* v_toPure_1813_, lean_object* v_____do__lift_1814_){
_start:
{
uint8_t v_____do__lift_213__boxed_1815_; lean_object* v_res_1816_; 
v_____do__lift_213__boxed_1815_ = lean_unbox(v_____do__lift_1814_);
v_res_1816_ = l_Array_findIdxM_x3f___redArg___lam__0(v_snd_1811_, v___x_1812_, v_toPure_1813_, v_____do__lift_213__boxed_1815_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__1(lean_object* v___x_1817_, lean_object* v_toPure_1818_, lean_object* v_p_1819_, lean_object* v_toBind_1820_, lean_object* v_a_1821_, lean_object* v_x_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_snd_1824_; lean_object* v___f_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v_snd_1824_ = lean_ctor_get(v___y_1823_, 1);
lean_inc(v_snd_1824_);
lean_dec_ref(v___y_1823_);
v___f_1825_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1825_, 0, v_snd_1824_);
lean_closure_set(v___f_1825_, 1, v___x_1817_);
lean_closure_set(v___f_1825_, 2, v_toPure_1818_);
v___x_1826_ = lean_apply_1(v_p_1819_, v_a_1821_);
v___x_1827_ = lean_apply_4(v_toBind_1820_, lean_box(0), lean_box(0), v___x_1826_, v___f_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__2(lean_object* v_toPure_1828_, lean_object* v_____s_1829_){
_start:
{
lean_object* v_fst_1830_; 
v_fst_1830_ = lean_ctor_get(v_____s_1829_, 0);
lean_inc(v_fst_1830_);
lean_dec_ref(v_____s_1829_);
if (lean_obj_tag(v_fst_1830_) == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = lean_box(0);
v___x_1832_ = lean_apply_2(v_toPure_1828_, lean_box(0), v___x_1831_);
return v___x_1832_;
}
else
{
lean_object* v_val_1833_; lean_object* v___x_1834_; 
v_val_1833_ = lean_ctor_get(v_fst_1830_, 0);
lean_inc(v_val_1833_);
lean_dec_ref_known(v_fst_1830_, 1);
v___x_1834_ = lean_apply_2(v_toPure_1828_, lean_box(0), v_val_1833_);
return v___x_1834_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg(lean_object* v_inst_1838_, lean_object* v_p_1839_, lean_object* v_as_1840_){
_start:
{
lean_object* v_toApplicative_1841_; lean_object* v_toBind_1842_; lean_object* v_toPure_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___f_1846_; lean_object* v___f_1847_; size_t v_sz_1848_; size_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_toApplicative_1841_ = lean_ctor_get(v_inst_1838_, 0);
v_toBind_1842_ = lean_ctor_get(v_inst_1838_, 1);
lean_inc_n(v_toBind_1842_, 2);
v_toPure_1843_ = lean_ctor_get(v_toApplicative_1841_, 1);
v___x_1844_ = lean_box(0);
v___x_1845_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1843_, 2);
v___f_1846_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1846_, 0, v___x_1844_);
lean_closure_set(v___f_1846_, 1, v_toPure_1843_);
lean_closure_set(v___f_1846_, 2, v_p_1839_);
lean_closure_set(v___f_1846_, 3, v_toBind_1842_);
v___f_1847_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1847_, 0, v_toPure_1843_);
v_sz_1848_ = lean_array_size(v_as_1840_);
v___x_1849_ = ((size_t)0ULL);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1838_, v_as_1840_, v___f_1846_, v_sz_1848_, v___x_1849_, v___x_1845_);
v___x_1851_ = lean_apply_4(v_toBind_1842_, lean_box(0), lean_box(0), v___x_1850_, v___f_1847_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f(lean_object* v_00_u03b1_1852_, lean_object* v_m_1853_, lean_object* v_inst_1854_, lean_object* v_p_1855_, lean_object* v_as_1856_){
_start:
{
lean_object* v_toApplicative_1857_; lean_object* v_toBind_1858_; lean_object* v_toPure_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___f_1862_; lean_object* v___f_1863_; size_t v_sz_1864_; size_t v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_toApplicative_1857_ = lean_ctor_get(v_inst_1854_, 0);
v_toBind_1858_ = lean_ctor_get(v_inst_1854_, 1);
lean_inc_n(v_toBind_1858_, 2);
v_toPure_1859_ = lean_ctor_get(v_toApplicative_1857_, 1);
v___x_1860_ = lean_box(0);
v___x_1861_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_1859_, 2);
v___f_1862_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1862_, 0, v___x_1860_);
lean_closure_set(v___f_1862_, 1, v_toPure_1859_);
lean_closure_set(v___f_1862_, 2, v_p_1855_);
lean_closure_set(v___f_1862_, 3, v_toBind_1858_);
v___f_1863_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1863_, 0, v_toPure_1859_);
v_sz_1864_ = lean_array_size(v_as_1856_);
v___x_1865_ = ((size_t)0ULL);
v___x_1866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1854_, v_as_1856_, v___f_1862_, v_sz_1864_, v___x_1865_, v___x_1861_);
v___x_1867_ = lean_apply_4(v_toBind_1858_, lean_box(0), lean_box(0), v___x_1866_, v___f_1863_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed(lean_object* v_i_1868_, lean_object* v_inst_1869_, lean_object* v_p_1870_, lean_object* v_as_1871_, lean_object* v_stop_1872_, lean_object* v_toPure_1873_, lean_object* v___x_1874_, lean_object* v_____do__lift_1875_){
_start:
{
size_t v_i_boxed_1876_; size_t v_stop_boxed_1877_; uint8_t v___x_78__boxed_1878_; uint8_t v_____do__lift_79__boxed_1879_; lean_object* v_res_1880_; 
v_i_boxed_1876_ = lean_unbox_usize(v_i_1868_);
lean_dec(v_i_1868_);
v_stop_boxed_1877_ = lean_unbox_usize(v_stop_1872_);
lean_dec(v_stop_1872_);
v___x_78__boxed_1878_ = lean_unbox(v___x_1874_);
v_____do__lift_79__boxed_1879_ = lean_unbox(v_____do__lift_1875_);
v_res_1880_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(v_i_boxed_1876_, v_inst_1869_, v_p_1870_, v_as_1871_, v_stop_boxed_1877_, v_toPure_1873_, v___x_78__boxed_1878_, v_____do__lift_79__boxed_1879_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(lean_object* v_inst_1881_, lean_object* v_p_1882_, lean_object* v_as_1883_, size_t v_i_1884_, size_t v_stop_1885_){
_start:
{
lean_object* v_toApplicative_1886_; lean_object* v_toBind_1887_; lean_object* v_toPure_1888_; uint8_t v___x_1889_; 
v_toApplicative_1886_ = lean_ctor_get(v_inst_1881_, 0);
v_toBind_1887_ = lean_ctor_get(v_inst_1881_, 1);
lean_inc(v_toBind_1887_);
v_toPure_1888_ = lean_ctor_get(v_toApplicative_1886_, 1);
lean_inc(v_toPure_1888_);
v___x_1889_ = lean_usize_dec_eq(v_i_1884_, v_stop_1885_);
if (v___x_1889_ == 0)
{
uint8_t v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___f_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1890_ = 1;
v___x_1891_ = lean_box_usize(v_i_1884_);
v___x_1892_ = lean_box_usize(v_stop_1885_);
v___x_1893_ = lean_box(v___x_1890_);
lean_inc_ref(v_as_1883_);
lean_inc(v_p_1882_);
v___f_1894_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1894_, 0, v___x_1891_);
lean_closure_set(v___f_1894_, 1, v_inst_1881_);
lean_closure_set(v___f_1894_, 2, v_p_1882_);
lean_closure_set(v___f_1894_, 3, v_as_1883_);
lean_closure_set(v___f_1894_, 4, v___x_1892_);
lean_closure_set(v___f_1894_, 5, v_toPure_1888_);
lean_closure_set(v___f_1894_, 6, v___x_1893_);
v___x_1895_ = lean_array_uget(v_as_1883_, v_i_1884_);
lean_dec_ref(v_as_1883_);
v___x_1896_ = lean_apply_1(v_p_1882_, v___x_1895_);
v___x_1897_ = lean_apply_4(v_toBind_1887_, lean_box(0), lean_box(0), v___x_1896_, v___f_1894_);
return v___x_1897_;
}
else
{
uint8_t v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
lean_dec(v_toBind_1887_);
lean_dec_ref(v_as_1883_);
lean_dec(v_p_1882_);
lean_dec_ref(v_inst_1881_);
v___x_1898_ = 0;
v___x_1899_ = lean_box(v___x_1898_);
v___x_1900_ = lean_apply_2(v_toPure_1888_, lean_box(0), v___x_1899_);
return v___x_1900_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(size_t v_i_1901_, lean_object* v_inst_1902_, lean_object* v_p_1903_, lean_object* v_as_1904_, size_t v_stop_1905_, lean_object* v_toPure_1906_, uint8_t v___x_1907_, uint8_t v_____do__lift_1908_){
_start:
{
if (v_____do__lift_1908_ == 0)
{
size_t v___x_1909_; size_t v___x_1910_; lean_object* v___x_1911_; 
lean_dec(v_toPure_1906_);
v___x_1909_ = ((size_t)1ULL);
v___x_1910_ = lean_usize_add(v_i_1901_, v___x_1909_);
v___x_1911_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1902_, v_p_1903_, v_as_1904_, v___x_1910_, v_stop_1905_);
return v___x_1911_;
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_dec_ref(v_as_1904_);
lean_dec(v_p_1903_);
lean_dec_ref(v_inst_1902_);
v___x_1912_ = lean_box(v___x_1907_);
v___x_1913_ = lean_apply_2(v_toPure_1906_, lean_box(0), v___x_1912_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___boxed(lean_object* v_inst_1914_, lean_object* v_p_1915_, lean_object* v_as_1916_, lean_object* v_i_1917_, lean_object* v_stop_1918_){
_start:
{
size_t v_i_boxed_1919_; size_t v_stop_boxed_1920_; lean_object* v_res_1921_; 
v_i_boxed_1919_ = lean_unbox_usize(v_i_1917_);
lean_dec(v_i_1917_);
v_stop_boxed_1920_ = lean_unbox_usize(v_stop_1918_);
lean_dec(v_stop_1918_);
v_res_1921_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1914_, v_p_1915_, v_as_1916_, v_i_boxed_1919_, v_stop_boxed_1920_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object* v_00_u03b1_1922_, lean_object* v_m_1923_, lean_object* v_inst_1924_, lean_object* v_p_1925_, lean_object* v_as_1926_, size_t v_i_1927_, size_t v_stop_1928_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1924_, v_p_1925_, v_as_1926_, v_i_1927_, v_stop_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___boxed(lean_object* v_00_u03b1_1930_, lean_object* v_m_1931_, lean_object* v_inst_1932_, lean_object* v_p_1933_, lean_object* v_as_1934_, lean_object* v_i_1935_, lean_object* v_stop_1936_){
_start:
{
size_t v_i_boxed_1937_; size_t v_stop_boxed_1938_; lean_object* v_res_1939_; 
v_i_boxed_1937_ = lean_unbox_usize(v_i_1935_);
lean_dec(v_i_1935_);
v_stop_boxed_1938_ = lean_unbox_usize(v_stop_1936_);
lean_dec(v_stop_1936_);
v_res_1939_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(v_00_u03b1_1930_, v_m_1931_, v_inst_1932_, v_p_1933_, v_as_1934_, v_i_boxed_1937_, v_stop_boxed_1938_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg(lean_object* v_inst_1940_, lean_object* v_p_1941_, lean_object* v_as_1942_, lean_object* v_start_1943_, lean_object* v_stop_1944_){
_start:
{
lean_object* v_toApplicative_1945_; lean_object* v_toPure_1946_; lean_object* v___y_1948_; uint8_t v___x_1955_; 
v_toApplicative_1945_ = lean_ctor_get(v_inst_1940_, 0);
v_toPure_1946_ = lean_ctor_get(v_toApplicative_1945_, 1);
v___x_1955_ = lean_nat_dec_lt(v_start_1943_, v_stop_1944_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
lean_inc(v_toPure_1946_);
lean_dec(v_stop_1944_);
lean_dec_ref(v_as_1942_);
lean_dec(v_p_1941_);
lean_dec_ref(v_inst_1940_);
v___x_1956_ = lean_box(v___x_1955_);
v___x_1957_ = lean_apply_2(v_toPure_1946_, lean_box(0), v___x_1956_);
return v___x_1957_;
}
else
{
lean_object* v___x_1958_; uint8_t v___x_1959_; 
v___x_1958_ = lean_array_get_size(v_as_1942_);
v___x_1959_ = lean_nat_dec_le(v_stop_1944_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_dec(v_stop_1944_);
v___y_1948_ = v___x_1958_;
goto v___jp_1947_;
}
else
{
v___y_1948_ = v_stop_1944_;
goto v___jp_1947_;
}
}
v___jp_1947_:
{
uint8_t v___x_1949_; 
v___x_1949_ = lean_nat_dec_lt(v_start_1943_, v___y_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_inc(v_toPure_1946_);
lean_dec(v___y_1948_);
lean_dec_ref(v_as_1942_);
lean_dec(v_p_1941_);
lean_dec_ref(v_inst_1940_);
v___x_1950_ = lean_box(v___x_1949_);
v___x_1951_ = lean_apply_2(v_toPure_1946_, lean_box(0), v___x_1950_);
return v___x_1951_;
}
else
{
size_t v___x_1952_; size_t v___x_1953_; lean_object* v___x_1954_; 
v___x_1952_ = lean_usize_of_nat(v_start_1943_);
v___x_1953_ = lean_usize_of_nat(v___y_1948_);
lean_dec(v___y_1948_);
v___x_1954_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1940_, v_p_1941_, v_as_1942_, v___x_1952_, v___x_1953_);
return v___x_1954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg___boxed(lean_object* v_inst_1960_, lean_object* v_p_1961_, lean_object* v_as_1962_, lean_object* v_start_1963_, lean_object* v_stop_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Array_anyMUnsafe___redArg(v_inst_1960_, v_p_1961_, v_as_1962_, v_start_1963_, v_stop_1964_);
lean_dec(v_start_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe(lean_object* v_00_u03b1_1966_, lean_object* v_m_1967_, lean_object* v_inst_1968_, lean_object* v_p_1969_, lean_object* v_as_1970_, lean_object* v_start_1971_, lean_object* v_stop_1972_){
_start:
{
lean_object* v_toApplicative_1973_; lean_object* v_toPure_1974_; lean_object* v___y_1976_; uint8_t v___x_1983_; 
v_toApplicative_1973_ = lean_ctor_get(v_inst_1968_, 0);
v_toPure_1974_ = lean_ctor_get(v_toApplicative_1973_, 1);
v___x_1983_ = lean_nat_dec_lt(v_start_1971_, v_stop_1972_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_inc(v_toPure_1974_);
lean_dec(v_stop_1972_);
lean_dec_ref(v_as_1970_);
lean_dec(v_p_1969_);
lean_dec_ref(v_inst_1968_);
v___x_1984_ = lean_box(v___x_1983_);
v___x_1985_ = lean_apply_2(v_toPure_1974_, lean_box(0), v___x_1984_);
return v___x_1985_;
}
else
{
lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1986_ = lean_array_get_size(v_as_1970_);
v___x_1987_ = lean_nat_dec_le(v_stop_1972_, v___x_1986_);
if (v___x_1987_ == 0)
{
lean_dec(v_stop_1972_);
v___y_1976_ = v___x_1986_;
goto v___jp_1975_;
}
else
{
v___y_1976_ = v_stop_1972_;
goto v___jp_1975_;
}
}
v___jp_1975_:
{
uint8_t v___x_1977_; 
v___x_1977_ = lean_nat_dec_lt(v_start_1971_, v___y_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_inc(v_toPure_1974_);
lean_dec(v___y_1976_);
lean_dec_ref(v_as_1970_);
lean_dec(v_p_1969_);
lean_dec_ref(v_inst_1968_);
v___x_1978_ = lean_box(v___x_1977_);
v___x_1979_ = lean_apply_2(v_toPure_1974_, lean_box(0), v___x_1978_);
return v___x_1979_;
}
else
{
size_t v___x_1980_; size_t v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = lean_usize_of_nat(v_start_1971_);
v___x_1981_ = lean_usize_of_nat(v___y_1976_);
lean_dec(v___y_1976_);
v___x_1982_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1968_, v_p_1969_, v_as_1970_, v___x_1980_, v___x_1981_);
return v___x_1982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___boxed(lean_object* v_00_u03b1_1988_, lean_object* v_m_1989_, lean_object* v_inst_1990_, lean_object* v_p_1991_, lean_object* v_as_1992_, lean_object* v_start_1993_, lean_object* v_stop_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Array_anyMUnsafe(v_00_u03b1_1988_, v_m_1989_, v_inst_1990_, v_p_1991_, v_as_1992_, v_start_1993_, v_stop_1994_);
lean_dec(v_start_1993_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0___boxed(lean_object* v_j_1996_, lean_object* v_inst_1997_, lean_object* v_p_1998_, lean_object* v_as_1999_, lean_object* v_stop_2000_, lean_object* v_toPure_2001_, lean_object* v___x_2002_, lean_object* v_____do__lift_2003_){
_start:
{
uint8_t v___x_63__boxed_2004_; uint8_t v_____do__lift_64__boxed_2005_; lean_object* v_res_2006_; 
v___x_63__boxed_2004_ = lean_unbox(v___x_2002_);
v_____do__lift_64__boxed_2005_ = lean_unbox(v_____do__lift_2003_);
v_res_2006_ = l_Array_anyM_loop___redArg___lam__0(v_j_1996_, v_inst_1997_, v_p_1998_, v_as_1999_, v_stop_2000_, v_toPure_2001_, v___x_63__boxed_2004_, v_____do__lift_64__boxed_2005_);
lean_dec(v_j_1996_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg(lean_object* v_inst_2007_, lean_object* v_p_2008_, lean_object* v_as_2009_, lean_object* v_stop_2010_, lean_object* v_j_2011_){
_start:
{
lean_object* v_toApplicative_2012_; lean_object* v_toBind_2013_; lean_object* v_toPure_2014_; uint8_t v___x_2015_; 
v_toApplicative_2012_ = lean_ctor_get(v_inst_2007_, 0);
v_toBind_2013_ = lean_ctor_get(v_inst_2007_, 1);
lean_inc(v_toBind_2013_);
v_toPure_2014_ = lean_ctor_get(v_toApplicative_2012_, 1);
lean_inc(v_toPure_2014_);
v___x_2015_ = lean_nat_dec_lt(v_j_2011_, v_stop_2010_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
lean_dec(v_toBind_2013_);
lean_dec(v_j_2011_);
lean_dec(v_stop_2010_);
lean_dec_ref(v_as_2009_);
lean_dec(v_p_2008_);
lean_dec_ref(v_inst_2007_);
v___x_2016_ = lean_box(v___x_2015_);
v___x_2017_ = lean_apply_2(v_toPure_2014_, lean_box(0), v___x_2016_);
return v___x_2017_;
}
else
{
lean_object* v___x_2018_; lean_object* v___f_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2018_ = lean_box(v___x_2015_);
lean_inc_ref(v_as_2009_);
lean_inc(v_p_2008_);
lean_inc(v_j_2011_);
v___f_2019_ = lean_alloc_closure((void*)(l_Array_anyM_loop___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_2019_, 0, v_j_2011_);
lean_closure_set(v___f_2019_, 1, v_inst_2007_);
lean_closure_set(v___f_2019_, 2, v_p_2008_);
lean_closure_set(v___f_2019_, 3, v_as_2009_);
lean_closure_set(v___f_2019_, 4, v_stop_2010_);
lean_closure_set(v___f_2019_, 5, v_toPure_2014_);
lean_closure_set(v___f_2019_, 6, v___x_2018_);
v___x_2020_ = lean_array_fget(v_as_2009_, v_j_2011_);
lean_dec(v_j_2011_);
lean_dec_ref(v_as_2009_);
v___x_2021_ = lean_apply_1(v_p_2008_, v___x_2020_);
v___x_2022_ = lean_apply_4(v_toBind_2013_, lean_box(0), lean_box(0), v___x_2021_, v___f_2019_);
return v___x_2022_;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0(lean_object* v_j_2023_, lean_object* v_inst_2024_, lean_object* v_p_2025_, lean_object* v_as_2026_, lean_object* v_stop_2027_, lean_object* v_toPure_2028_, uint8_t v___x_2029_, uint8_t v_____do__lift_2030_){
_start:
{
if (v_____do__lift_2030_ == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_dec(v_toPure_2028_);
v___x_2031_ = lean_unsigned_to_nat(1u);
v___x_2032_ = lean_nat_add(v_j_2023_, v___x_2031_);
v___x_2033_ = l_Array_anyM_loop___redArg(v_inst_2024_, v_p_2025_, v_as_2026_, v_stop_2027_, v___x_2032_);
return v___x_2033_;
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_dec(v_stop_2027_);
lean_dec_ref(v_as_2026_);
lean_dec(v_p_2025_);
lean_dec_ref(v_inst_2024_);
v___x_2034_ = lean_box(v___x_2029_);
v___x_2035_ = lean_apply_2(v_toPure_2028_, lean_box(0), v___x_2034_);
return v___x_2035_;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop(lean_object* v_00_u03b1_2036_, lean_object* v_m_2037_, lean_object* v_inst_2038_, lean_object* v_p_2039_, lean_object* v_as_2040_, lean_object* v_stop_2041_, lean_object* v_h_2042_, lean_object* v_j_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Array_anyM_loop___redArg(v_inst_2038_, v_p_2039_, v_as_2040_, v_stop_2041_, v_j_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0(lean_object* v_toPure_2045_, uint8_t v_____do__lift_2046_){
_start:
{
if (v_____do__lift_2046_ == 0)
{
uint8_t v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = 1;
v___x_2048_ = lean_box(v___x_2047_);
v___x_2049_ = lean_apply_2(v_toPure_2045_, lean_box(0), v___x_2048_);
return v___x_2049_;
}
else
{
uint8_t v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = 0;
v___x_2051_ = lean_box(v___x_2050_);
v___x_2052_ = lean_apply_2(v_toPure_2045_, lean_box(0), v___x_2051_);
return v___x_2052_;
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0___boxed(lean_object* v_toPure_2053_, lean_object* v_____do__lift_2054_){
_start:
{
uint8_t v_____do__lift_116__boxed_2055_; lean_object* v_res_2056_; 
v_____do__lift_116__boxed_2055_ = lean_unbox(v_____do__lift_2054_);
v_res_2056_ = l_Array_allM___redArg___lam__0(v_toPure_2053_, v_____do__lift_116__boxed_2055_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1(lean_object* v_toPure_2057_, uint8_t v___x_2058_, uint8_t v_____do__lift_2059_){
_start:
{
if (v_____do__lift_2059_ == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_box(v___x_2058_);
v___x_2061_ = lean_apply_2(v_toPure_2057_, lean_box(0), v___x_2060_);
return v___x_2061_;
}
else
{
uint8_t v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = 0;
v___x_2063_ = lean_box(v___x_2062_);
v___x_2064_ = lean_apply_2(v_toPure_2057_, lean_box(0), v___x_2063_);
return v___x_2064_;
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1___boxed(lean_object* v_toPure_2065_, lean_object* v___x_2066_, lean_object* v_____do__lift_2067_){
_start:
{
uint8_t v___x_131__boxed_2068_; uint8_t v_____do__lift_132__boxed_2069_; lean_object* v_res_2070_; 
v___x_131__boxed_2068_ = lean_unbox(v___x_2066_);
v_____do__lift_132__boxed_2069_ = lean_unbox(v_____do__lift_2067_);
v_res_2070_ = l_Array_allM___redArg___lam__1(v_toPure_2065_, v___x_131__boxed_2068_, v_____do__lift_132__boxed_2069_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__2(lean_object* v_p_2071_, lean_object* v_toBind_2072_, lean_object* v___f_2073_, lean_object* v_v_2074_){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_apply_1(v_p_2071_, v_v_2074_);
v___x_2076_ = lean_apply_4(v_toBind_2072_, lean_box(0), lean_box(0), v___x_2075_, v___f_2073_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg(lean_object* v_inst_2077_, lean_object* v_p_2078_, lean_object* v_as_2079_, lean_object* v_start_2080_, lean_object* v_stop_2081_){
_start:
{
lean_object* v_toApplicative_2082_; lean_object* v_toBind_2083_; lean_object* v_toPure_2084_; lean_object* v___f_2085_; uint8_t v___x_2086_; 
v_toApplicative_2082_ = lean_ctor_get(v_inst_2077_, 0);
v_toBind_2083_ = lean_ctor_get(v_inst_2077_, 1);
lean_inc(v_toBind_2083_);
v_toPure_2084_ = lean_ctor_get(v_toApplicative_2082_, 1);
lean_inc(v_toPure_2084_);
v___f_2085_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2085_, 0, v_toPure_2084_);
v___x_2086_ = lean_nat_dec_lt(v_start_2080_, v_stop_2081_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_inc(v_toPure_2084_);
lean_dec(v_stop_2081_);
lean_dec_ref(v_as_2079_);
lean_dec(v_p_2078_);
lean_dec_ref(v_inst_2077_);
v___x_2087_ = lean_box(v___x_2086_);
v___x_2088_ = lean_apply_2(v_toPure_2084_, lean_box(0), v___x_2087_);
v___x_2089_ = lean_apply_4(v_toBind_2083_, lean_box(0), lean_box(0), v___x_2088_, v___f_2085_);
return v___x_2089_;
}
else
{
lean_object* v___x_2090_; lean_object* v___f_2091_; lean_object* v___f_2092_; lean_object* v___y_2094_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2090_ = lean_box(v___x_2086_);
lean_inc(v_toPure_2084_);
v___f_2091_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2091_, 0, v_toPure_2084_);
lean_closure_set(v___f_2091_, 1, v___x_2090_);
lean_inc(v_toBind_2083_);
v___f_2092_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2092_, 0, v_p_2078_);
lean_closure_set(v___f_2092_, 1, v_toBind_2083_);
lean_closure_set(v___f_2092_, 2, v___f_2091_);
v___x_2103_ = lean_array_get_size(v_as_2079_);
v___x_2104_ = lean_nat_dec_le(v_stop_2081_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_dec(v_stop_2081_);
v___y_2094_ = v___x_2103_;
goto v___jp_2093_;
}
else
{
v___y_2094_ = v_stop_2081_;
goto v___jp_2093_;
}
v___jp_2093_:
{
uint8_t v___x_2095_; 
v___x_2095_ = lean_nat_dec_lt(v_start_2080_, v___y_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_inc(v_toPure_2084_);
lean_dec(v___y_2094_);
lean_dec_ref(v___f_2092_);
lean_dec_ref(v_as_2079_);
lean_dec_ref(v_inst_2077_);
v___x_2096_ = lean_box(v___x_2095_);
v___x_2097_ = lean_apply_2(v_toPure_2084_, lean_box(0), v___x_2096_);
v___x_2098_ = lean_apply_4(v_toBind_2083_, lean_box(0), lean_box(0), v___x_2097_, v___f_2085_);
return v___x_2098_;
}
else
{
size_t v___x_2099_; size_t v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2099_ = lean_usize_of_nat(v_start_2080_);
v___x_2100_ = lean_usize_of_nat(v___y_2094_);
lean_dec(v___y_2094_);
v___x_2101_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2077_, v___f_2092_, v_as_2079_, v___x_2099_, v___x_2100_);
v___x_2102_ = lean_apply_4(v_toBind_2083_, lean_box(0), lean_box(0), v___x_2101_, v___f_2085_);
return v___x_2102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___boxed(lean_object* v_inst_2105_, lean_object* v_p_2106_, lean_object* v_as_2107_, lean_object* v_start_2108_, lean_object* v_stop_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Array_allM___redArg(v_inst_2105_, v_p_2106_, v_as_2107_, v_start_2108_, v_stop_2109_);
lean_dec(v_start_2108_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Array_allM(lean_object* v_00_u03b1_2111_, lean_object* v_m_2112_, lean_object* v_inst_2113_, lean_object* v_p_2114_, lean_object* v_as_2115_, lean_object* v_start_2116_, lean_object* v_stop_2117_){
_start:
{
lean_object* v_toApplicative_2118_; lean_object* v_toBind_2119_; lean_object* v_toPure_2120_; lean_object* v___f_2121_; uint8_t v___x_2122_; 
v_toApplicative_2118_ = lean_ctor_get(v_inst_2113_, 0);
v_toBind_2119_ = lean_ctor_get(v_inst_2113_, 1);
lean_inc(v_toBind_2119_);
v_toPure_2120_ = lean_ctor_get(v_toApplicative_2118_, 1);
lean_inc(v_toPure_2120_);
v___f_2121_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2121_, 0, v_toPure_2120_);
v___x_2122_ = lean_nat_dec_lt(v_start_2116_, v_stop_2117_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_inc(v_toPure_2120_);
lean_dec(v_stop_2117_);
lean_dec_ref(v_as_2115_);
lean_dec(v_p_2114_);
lean_dec_ref(v_inst_2113_);
v___x_2123_ = lean_box(v___x_2122_);
v___x_2124_ = lean_apply_2(v_toPure_2120_, lean_box(0), v___x_2123_);
v___x_2125_ = lean_apply_4(v_toBind_2119_, lean_box(0), lean_box(0), v___x_2124_, v___f_2121_);
return v___x_2125_;
}
else
{
lean_object* v___x_2126_; lean_object* v___f_2127_; lean_object* v___f_2128_; lean_object* v___y_2130_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2126_ = lean_box(v___x_2122_);
lean_inc(v_toPure_2120_);
v___f_2127_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2127_, 0, v_toPure_2120_);
lean_closure_set(v___f_2127_, 1, v___x_2126_);
lean_inc(v_toBind_2119_);
v___f_2128_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2128_, 0, v_p_2114_);
lean_closure_set(v___f_2128_, 1, v_toBind_2119_);
lean_closure_set(v___f_2128_, 2, v___f_2127_);
v___x_2139_ = lean_array_get_size(v_as_2115_);
v___x_2140_ = lean_nat_dec_le(v_stop_2117_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_dec(v_stop_2117_);
v___y_2130_ = v___x_2139_;
goto v___jp_2129_;
}
else
{
v___y_2130_ = v_stop_2117_;
goto v___jp_2129_;
}
v___jp_2129_:
{
uint8_t v___x_2131_; 
v___x_2131_ = lean_nat_dec_lt(v_start_2116_, v___y_2130_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_inc(v_toPure_2120_);
lean_dec(v___y_2130_);
lean_dec_ref(v___f_2128_);
lean_dec_ref(v_as_2115_);
lean_dec_ref(v_inst_2113_);
v___x_2132_ = lean_box(v___x_2131_);
v___x_2133_ = lean_apply_2(v_toPure_2120_, lean_box(0), v___x_2132_);
v___x_2134_ = lean_apply_4(v_toBind_2119_, lean_box(0), lean_box(0), v___x_2133_, v___f_2121_);
return v___x_2134_;
}
else
{
size_t v___x_2135_; size_t v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2135_ = lean_usize_of_nat(v_start_2116_);
v___x_2136_ = lean_usize_of_nat(v___y_2130_);
lean_dec(v___y_2130_);
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2113_, v___f_2128_, v_as_2115_, v___x_2135_, v___x_2136_);
v___x_2138_ = lean_apply_4(v_toBind_2119_, lean_box(0), lean_box(0), v___x_2137_, v___f_2121_);
return v___x_2138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___boxed(lean_object* v_00_u03b1_2141_, lean_object* v_m_2142_, lean_object* v_inst_2143_, lean_object* v_p_2144_, lean_object* v_as_2145_, lean_object* v_start_2146_, lean_object* v_stop_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Array_allM(v_00_u03b1_2141_, v_m_2142_, v_inst_2143_, v_p_2144_, v_as_2145_, v_start_2146_, v_stop_2147_);
lean_dec(v_start_2146_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed(lean_object* v_inst_2149_, lean_object* v_f_2150_, lean_object* v_as_2151_, lean_object* v_n_2152_, lean_object* v_toPure_2153_, lean_object* v_r_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(v_inst_2149_, v_f_2150_, v_as_2151_, v_n_2152_, v_toPure_2153_, v_r_2154_);
lean_dec(v_n_2152_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(lean_object* v_inst_2156_, lean_object* v_f_2157_, lean_object* v_as_2158_, lean_object* v_i_2159_){
_start:
{
lean_object* v_toApplicative_2160_; lean_object* v_toBind_2161_; lean_object* v_toPure_2162_; lean_object* v_zero_2163_; uint8_t v_isZero_2164_; 
v_toApplicative_2160_ = lean_ctor_get(v_inst_2156_, 0);
v_toBind_2161_ = lean_ctor_get(v_inst_2156_, 1);
lean_inc(v_toBind_2161_);
v_toPure_2162_ = lean_ctor_get(v_toApplicative_2160_, 1);
lean_inc(v_toPure_2162_);
v_zero_2163_ = lean_unsigned_to_nat(0u);
v_isZero_2164_ = lean_nat_dec_eq(v_i_2159_, v_zero_2163_);
if (v_isZero_2164_ == 1)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v_toBind_2161_);
lean_dec_ref(v_as_2158_);
lean_dec(v_f_2157_);
lean_dec_ref(v_inst_2156_);
v___x_2165_ = lean_box(0);
v___x_2166_ = lean_apply_2(v_toPure_2162_, lean_box(0), v___x_2165_);
return v___x_2166_;
}
else
{
lean_object* v_one_2167_; lean_object* v_n_2168_; lean_object* v___f_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_one_2167_ = lean_unsigned_to_nat(1u);
v_n_2168_ = lean_nat_sub(v_i_2159_, v_one_2167_);
lean_inc(v_n_2168_);
lean_inc_ref(v_as_2158_);
lean_inc(v_f_2157_);
v___f_2169_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2169_, 0, v_inst_2156_);
lean_closure_set(v___f_2169_, 1, v_f_2157_);
lean_closure_set(v___f_2169_, 2, v_as_2158_);
lean_closure_set(v___f_2169_, 3, v_n_2168_);
lean_closure_set(v___f_2169_, 4, v_toPure_2162_);
v___x_2170_ = lean_array_fget(v_as_2158_, v_n_2168_);
lean_dec(v_n_2168_);
lean_dec_ref(v_as_2158_);
v___x_2171_ = lean_apply_1(v_f_2157_, v___x_2170_);
v___x_2172_ = lean_apply_4(v_toBind_2161_, lean_box(0), lean_box(0), v___x_2171_, v___f_2169_);
return v___x_2172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(lean_object* v_inst_2173_, lean_object* v_f_2174_, lean_object* v_as_2175_, lean_object* v_n_2176_, lean_object* v_toPure_2177_, lean_object* v_r_2178_){
_start:
{
if (lean_obj_tag(v_r_2178_) == 0)
{
lean_object* v___x_2179_; 
lean_dec(v_toPure_2177_);
v___x_2179_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2173_, v_f_2174_, v_as_2175_, v_n_2176_);
return v___x_2179_;
}
else
{
lean_object* v___x_2180_; 
lean_dec_ref(v_as_2175_);
lean_dec(v_f_2174_);
lean_dec_ref(v_inst_2173_);
v___x_2180_ = lean_apply_2(v_toPure_2177_, lean_box(0), v_r_2178_);
return v___x_2180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___boxed(lean_object* v_inst_2181_, lean_object* v_f_2182_, lean_object* v_as_2183_, lean_object* v_i_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2181_, v_f_2182_, v_as_2183_, v_i_2184_);
lean_dec(v_i_2184_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_object* v_00_u03b1_2186_, lean_object* v_00_u03b2_2187_, lean_object* v_m_2188_, lean_object* v_inst_2189_, lean_object* v_f_2190_, lean_object* v_as_2191_, lean_object* v_i_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2189_, v_f_2190_, v_as_2191_, v_i_2192_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___boxed(lean_object* v_00_u03b1_2195_, lean_object* v_00_u03b2_2196_, lean_object* v_m_2197_, lean_object* v_inst_2198_, lean_object* v_f_2199_, lean_object* v_as_2200_, lean_object* v_i_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(v_00_u03b1_2195_, v_00_u03b2_2196_, v_m_2197_, v_inst_2198_, v_f_2199_, v_as_2200_, v_i_2201_, v_a_2202_);
lean_dec(v_i_2201_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f___redArg(lean_object* v_inst_2204_, lean_object* v_f_2205_, lean_object* v_as_2206_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_array_get_size(v_as_2206_);
v___x_2208_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2204_, v_f_2205_, v_as_2206_, v___x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f(lean_object* v_00_u03b1_2209_, lean_object* v_00_u03b2_2210_, lean_object* v_m_2211_, lean_object* v_inst_2212_, lean_object* v_f_2213_, lean_object* v_as_2214_){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_array_get_size(v_as_2214_);
v___x_2216_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2212_, v_f_2213_, v_as_2214_, v___x_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2217_, lean_object* v_a_2218_, uint8_t v_____do__lift_2219_){
_start:
{
if (v_____do__lift_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_dec(v_a_2218_);
v___x_2220_ = lean_box(0);
v___x_2221_ = lean_apply_2(v_toPure_2217_, lean_box(0), v___x_2220_);
return v___x_2221_;
}
else
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2222_, 0, v_a_2218_);
v___x_2223_ = lean_apply_2(v_toPure_2217_, lean_box(0), v___x_2222_);
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2224_, lean_object* v_a_2225_, lean_object* v_____do__lift_2226_){
_start:
{
uint8_t v_____do__lift_59__boxed_2227_; lean_object* v_res_2228_; 
v_____do__lift_59__boxed_2227_ = lean_unbox(v_____do__lift_2226_);
v_res_2228_ = l_Array_findRevM_x3f___redArg___lam__0(v_toPure_2224_, v_a_2225_, v_____do__lift_59__boxed_2227_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2229_, lean_object* v_p_2230_, lean_object* v_toBind_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v___f_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
lean_inc(v_a_2232_);
v___f_2233_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2233_, 0, v_toPure_2229_);
lean_closure_set(v___f_2233_, 1, v_a_2232_);
v___x_2234_ = lean_apply_1(v_p_2230_, v_a_2232_);
v___x_2235_ = lean_apply_4(v_toBind_2231_, lean_box(0), lean_box(0), v___x_2234_, v___f_2233_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg(lean_object* v_inst_2236_, lean_object* v_p_2237_, lean_object* v_as_2238_){
_start:
{
lean_object* v_toApplicative_2239_; lean_object* v_toBind_2240_; lean_object* v_toPure_2241_; lean_object* v___f_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v_toApplicative_2239_ = lean_ctor_get(v_inst_2236_, 0);
v_toBind_2240_ = lean_ctor_get(v_inst_2236_, 1);
v_toPure_2241_ = lean_ctor_get(v_toApplicative_2239_, 1);
lean_inc(v_toBind_2240_);
lean_inc(v_toPure_2241_);
v___f_2242_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2242_, 0, v_toPure_2241_);
lean_closure_set(v___f_2242_, 1, v_p_2237_);
lean_closure_set(v___f_2242_, 2, v_toBind_2240_);
v___x_2243_ = lean_array_get_size(v_as_2238_);
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2236_, v___f_2242_, v_as_2238_, v___x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f(lean_object* v_00_u03b1_2245_, lean_object* v_m_2246_, lean_object* v_inst_2247_, lean_object* v_p_2248_, lean_object* v_as_2249_){
_start:
{
lean_object* v_toApplicative_2250_; lean_object* v_toBind_2251_; lean_object* v_toPure_2252_; lean_object* v___f_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_toApplicative_2250_ = lean_ctor_get(v_inst_2247_, 0);
v_toBind_2251_ = lean_ctor_get(v_inst_2247_, 1);
v_toPure_2252_ = lean_ctor_get(v_toApplicative_2250_, 1);
lean_inc(v_toBind_2251_);
lean_inc(v_toPure_2252_);
v___f_2253_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2253_, 0, v_toPure_2252_);
lean_closure_set(v___f_2253_, 1, v_p_2248_);
lean_closure_set(v___f_2253_, 2, v_toBind_2251_);
v___x_2254_ = lean_array_get_size(v_as_2249_);
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2247_, v___f_2253_, v_as_2249_, v___x_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___lam__0(lean_object* v_f_2256_, lean_object* v_x_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_apply_1(v_f_2256_, v___y_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg(lean_object* v_inst_2260_, lean_object* v_f_2261_, lean_object* v_as_2262_, lean_object* v_start_2263_, lean_object* v_stop_2264_){
_start:
{
lean_object* v_toApplicative_2265_; lean_object* v_toPure_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v_toApplicative_2265_ = lean_ctor_get(v_inst_2260_, 0);
v_toPure_2266_ = lean_ctor_get(v_toApplicative_2265_, 1);
v___x_2267_ = lean_box(0);
v___x_2268_ = lean_nat_dec_lt(v_start_2263_, v_stop_2264_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; 
lean_inc(v_toPure_2266_);
lean_dec_ref(v_as_2262_);
lean_dec(v_f_2261_);
lean_dec_ref(v_inst_2260_);
v___x_2269_ = lean_apply_2(v_toPure_2266_, lean_box(0), v___x_2267_);
return v___x_2269_;
}
else
{
lean_object* v___f_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___f_2270_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2270_, 0, v_f_2261_);
v___x_2271_ = lean_array_get_size(v_as_2262_);
v___x_2272_ = lean_nat_dec_le(v_stop_2264_, v___x_2271_);
if (v___x_2272_ == 0)
{
uint8_t v___x_2273_; 
v___x_2273_ = lean_nat_dec_lt(v_start_2263_, v___x_2271_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; 
lean_inc(v_toPure_2266_);
lean_dec_ref(v___f_2270_);
lean_dec_ref(v_as_2262_);
lean_dec_ref(v_inst_2260_);
v___x_2274_ = lean_apply_2(v_toPure_2266_, lean_box(0), v___x_2267_);
return v___x_2274_;
}
else
{
size_t v___x_2275_; size_t v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = lean_usize_of_nat(v_start_2263_);
v___x_2276_ = lean_usize_of_nat(v___x_2271_);
v___x_2277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2260_, v___f_2270_, v_as_2262_, v___x_2275_, v___x_2276_, v___x_2267_);
return v___x_2277_;
}
}
else
{
size_t v___x_2278_; size_t v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = lean_usize_of_nat(v_start_2263_);
v___x_2279_ = lean_usize_of_nat(v_stop_2264_);
v___x_2280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2260_, v___f_2270_, v_as_2262_, v___x_2278_, v___x_2279_, v___x_2267_);
return v___x_2280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___boxed(lean_object* v_inst_2281_, lean_object* v_f_2282_, lean_object* v_as_2283_, lean_object* v_start_2284_, lean_object* v_stop_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Array_forM___redArg(v_inst_2281_, v_f_2282_, v_as_2283_, v_start_2284_, v_stop_2285_);
lean_dec(v_stop_2285_);
lean_dec(v_start_2284_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Array_forM(lean_object* v_00_u03b1_2287_, lean_object* v_m_2288_, lean_object* v_inst_2289_, lean_object* v_f_2290_, lean_object* v_as_2291_, lean_object* v_start_2292_, lean_object* v_stop_2293_){
_start:
{
lean_object* v_toApplicative_2294_; lean_object* v_toPure_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; 
v_toApplicative_2294_ = lean_ctor_get(v_inst_2289_, 0);
v_toPure_2295_ = lean_ctor_get(v_toApplicative_2294_, 1);
v___x_2296_ = lean_box(0);
v___x_2297_ = lean_nat_dec_lt(v_start_2292_, v_stop_2293_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; 
lean_inc(v_toPure_2295_);
lean_dec_ref(v_as_2291_);
lean_dec(v_f_2290_);
lean_dec_ref(v_inst_2289_);
v___x_2298_ = lean_apply_2(v_toPure_2295_, lean_box(0), v___x_2296_);
return v___x_2298_;
}
else
{
lean_object* v___f_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___f_2299_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2299_, 0, v_f_2290_);
v___x_2300_ = lean_array_get_size(v_as_2291_);
v___x_2301_ = lean_nat_dec_le(v_stop_2293_, v___x_2300_);
if (v___x_2301_ == 0)
{
uint8_t v___x_2302_; 
v___x_2302_ = lean_nat_dec_lt(v_start_2292_, v___x_2300_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; 
lean_inc(v_toPure_2295_);
lean_dec_ref(v___f_2299_);
lean_dec_ref(v_as_2291_);
lean_dec_ref(v_inst_2289_);
v___x_2303_ = lean_apply_2(v_toPure_2295_, lean_box(0), v___x_2296_);
return v___x_2303_;
}
else
{
size_t v___x_2304_; size_t v___x_2305_; lean_object* v___x_2306_; 
v___x_2304_ = lean_usize_of_nat(v_start_2292_);
v___x_2305_ = lean_usize_of_nat(v___x_2300_);
v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2289_, v___f_2299_, v_as_2291_, v___x_2304_, v___x_2305_, v___x_2296_);
return v___x_2306_;
}
}
else
{
size_t v___x_2307_; size_t v___x_2308_; lean_object* v___x_2309_; 
v___x_2307_ = lean_usize_of_nat(v_start_2292_);
v___x_2308_ = lean_usize_of_nat(v_stop_2293_);
v___x_2309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2289_, v___f_2299_, v_as_2291_, v___x_2307_, v___x_2308_, v___x_2296_);
return v___x_2309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___boxed(lean_object* v_00_u03b1_2310_, lean_object* v_m_2311_, lean_object* v_inst_2312_, lean_object* v_f_2313_, lean_object* v_as_2314_, lean_object* v_start_2315_, lean_object* v_stop_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Array_forM(v_00_u03b1_2310_, v_m_2311_, v_inst_2312_, v_f_2313_, v_as_2314_, v_start_2315_, v_stop_2316_);
lean_dec(v_stop_2316_);
lean_dec(v_start_2315_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg___lam__1(lean_object* v_inst_2318_, lean_object* v_xs_2319_, lean_object* v_f_2320_){
_start:
{
lean_object* v_toApplicative_2321_; lean_object* v_toPure_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v_toApplicative_2321_ = lean_ctor_get(v_inst_2318_, 0);
v_toPure_2322_ = lean_ctor_get(v_toApplicative_2321_, 1);
v___x_2323_ = lean_unsigned_to_nat(0u);
v___x_2324_ = lean_array_get_size(v_xs_2319_);
v___x_2325_ = lean_box(0);
v___x_2326_ = lean_nat_dec_lt(v___x_2323_, v___x_2324_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; 
lean_inc(v_toPure_2322_);
lean_dec(v_f_2320_);
lean_dec_ref(v_xs_2319_);
lean_dec_ref(v_inst_2318_);
v___x_2327_ = lean_apply_2(v_toPure_2322_, lean_box(0), v___x_2325_);
return v___x_2327_;
}
else
{
lean_object* v___f_2328_; uint8_t v___x_2329_; 
v___f_2328_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2328_, 0, v_f_2320_);
v___x_2329_ = lean_nat_dec_le(v___x_2324_, v___x_2324_);
if (v___x_2329_ == 0)
{
if (v___x_2326_ == 0)
{
lean_object* v___x_2330_; 
lean_inc(v_toPure_2322_);
lean_dec_ref(v___f_2328_);
lean_dec_ref(v_xs_2319_);
lean_dec_ref(v_inst_2318_);
v___x_2330_ = lean_apply_2(v_toPure_2322_, lean_box(0), v___x_2325_);
return v___x_2330_;
}
else
{
size_t v___x_2331_; size_t v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = ((size_t)0ULL);
v___x_2332_ = lean_usize_of_nat(v___x_2324_);
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2318_, v___f_2328_, v_xs_2319_, v___x_2331_, v___x_2332_, v___x_2325_);
return v___x_2333_;
}
}
else
{
size_t v___x_2334_; size_t v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = ((size_t)0ULL);
v___x_2335_ = lean_usize_of_nat(v___x_2324_);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2318_, v___f_2328_, v_xs_2319_, v___x_2334_, v___x_2335_, v___x_2325_);
return v___x_2336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg(lean_object* v_inst_2337_){
_start:
{
lean_object* v___f_2338_; 
v___f_2338_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2338_, 0, v_inst_2337_);
return v___f_2338_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad(lean_object* v_00_u03b1_2339_, lean_object* v_m_2340_, lean_object* v_inst_2341_){
_start:
{
lean_object* v___f_2342_; 
v___f_2342_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2342_, 0, v_inst_2341_);
return v___f_2342_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___lam__0(lean_object* v_f_2343_, lean_object* v_a_2344_, lean_object* v_x_2345_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = lean_apply_1(v_f_2343_, v_a_2344_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg(lean_object* v_inst_2347_, lean_object* v_f_2348_, lean_object* v_as_2349_, lean_object* v_start_2350_, lean_object* v_stop_2351_){
_start:
{
lean_object* v_toApplicative_2352_; lean_object* v_toPure_2353_; lean_object* v___f_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v_toApplicative_2352_ = lean_ctor_get(v_inst_2347_, 0);
v_toPure_2353_ = lean_ctor_get(v_toApplicative_2352_, 1);
v___f_2354_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2354_, 0, v_f_2348_);
v___x_2355_ = lean_box(0);
v___x_2356_ = lean_array_get_size(v_as_2349_);
v___x_2357_ = lean_nat_dec_le(v_start_2350_, v___x_2356_);
if (v___x_2357_ == 0)
{
uint8_t v___x_2358_; 
v___x_2358_ = lean_nat_dec_lt(v_stop_2351_, v___x_2356_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; 
lean_inc(v_toPure_2353_);
lean_dec_ref(v___f_2354_);
lean_dec_ref(v_as_2349_);
lean_dec_ref(v_inst_2347_);
v___x_2359_ = lean_apply_2(v_toPure_2353_, lean_box(0), v___x_2355_);
return v___x_2359_;
}
else
{
size_t v___x_2360_; size_t v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = lean_usize_of_nat(v___x_2356_);
v___x_2361_ = lean_usize_of_nat(v_stop_2351_);
v___x_2362_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2347_, v___f_2354_, v_as_2349_, v___x_2360_, v___x_2361_, v___x_2355_);
return v___x_2362_;
}
}
else
{
uint8_t v___x_2363_; 
v___x_2363_ = lean_nat_dec_lt(v_stop_2351_, v_start_2350_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; 
lean_inc(v_toPure_2353_);
lean_dec_ref(v___f_2354_);
lean_dec_ref(v_as_2349_);
lean_dec_ref(v_inst_2347_);
v___x_2364_ = lean_apply_2(v_toPure_2353_, lean_box(0), v___x_2355_);
return v___x_2364_;
}
else
{
size_t v___x_2365_; size_t v___x_2366_; lean_object* v___x_2367_; 
v___x_2365_ = lean_usize_of_nat(v_start_2350_);
v___x_2366_ = lean_usize_of_nat(v_stop_2351_);
v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2347_, v___f_2354_, v_as_2349_, v___x_2365_, v___x_2366_, v___x_2355_);
return v___x_2367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___boxed(lean_object* v_inst_2368_, lean_object* v_f_2369_, lean_object* v_as_2370_, lean_object* v_start_2371_, lean_object* v_stop_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Array_forRevM___redArg(v_inst_2368_, v_f_2369_, v_as_2370_, v_start_2371_, v_stop_2372_);
lean_dec(v_stop_2372_);
lean_dec(v_start_2371_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM(lean_object* v_00_u03b1_2374_, lean_object* v_m_2375_, lean_object* v_inst_2376_, lean_object* v_f_2377_, lean_object* v_as_2378_, lean_object* v_start_2379_, lean_object* v_stop_2380_){
_start:
{
lean_object* v_toApplicative_2381_; lean_object* v_toPure_2382_; lean_object* v___f_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v_toApplicative_2381_ = lean_ctor_get(v_inst_2376_, 0);
v_toPure_2382_ = lean_ctor_get(v_toApplicative_2381_, 1);
v___f_2383_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2383_, 0, v_f_2377_);
v___x_2384_ = lean_box(0);
v___x_2385_ = lean_array_get_size(v_as_2378_);
v___x_2386_ = lean_nat_dec_le(v_start_2379_, v___x_2385_);
if (v___x_2386_ == 0)
{
uint8_t v___x_2387_; 
v___x_2387_ = lean_nat_dec_lt(v_stop_2380_, v___x_2385_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; 
lean_inc(v_toPure_2382_);
lean_dec_ref(v___f_2383_);
lean_dec_ref(v_as_2378_);
lean_dec_ref(v_inst_2376_);
v___x_2388_ = lean_apply_2(v_toPure_2382_, lean_box(0), v___x_2384_);
return v___x_2388_;
}
else
{
size_t v___x_2389_; size_t v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = lean_usize_of_nat(v___x_2385_);
v___x_2390_ = lean_usize_of_nat(v_stop_2380_);
v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2376_, v___f_2383_, v_as_2378_, v___x_2389_, v___x_2390_, v___x_2384_);
return v___x_2391_;
}
}
else
{
uint8_t v___x_2392_; 
v___x_2392_ = lean_nat_dec_lt(v_stop_2380_, v_start_2379_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; 
lean_inc(v_toPure_2382_);
lean_dec_ref(v___f_2383_);
lean_dec_ref(v_as_2378_);
lean_dec_ref(v_inst_2376_);
v___x_2393_ = lean_apply_2(v_toPure_2382_, lean_box(0), v___x_2384_);
return v___x_2393_;
}
else
{
size_t v___x_2394_; size_t v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = lean_usize_of_nat(v_start_2379_);
v___x_2395_ = lean_usize_of_nat(v_stop_2380_);
v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2376_, v___f_2383_, v_as_2378_, v___x_2394_, v___x_2395_, v___x_2384_);
return v___x_2396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___boxed(lean_object* v_00_u03b1_2397_, lean_object* v_m_2398_, lean_object* v_inst_2399_, lean_object* v_f_2400_, lean_object* v_as_2401_, lean_object* v_start_2402_, lean_object* v_stop_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Array_forRevM(v_00_u03b1_2397_, v_m_2398_, v_inst_2399_, v_f_2400_, v_as_2401_, v_start_2402_, v_stop_2403_);
lean_dec(v_stop_2403_);
lean_dec(v_start_2402_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___lam__0(lean_object* v_f_2405_, lean_object* v_x1_2406_, lean_object* v_x2_2407_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_apply_2(v_f_2405_, v_x1_2406_, v_x2_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg(lean_object* v_f_2428_, lean_object* v_init_2429_, lean_object* v_as_2430_, lean_object* v_start_2431_, lean_object* v_stop_2432_){
_start:
{
lean_object* v___x_2433_; uint8_t v___x_2434_; 
v___x_2433_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2434_ = lean_nat_dec_lt(v_start_2431_, v_stop_2432_);
if (v___x_2434_ == 0)
{
lean_dec_ref(v_as_2430_);
lean_dec(v_f_2428_);
return v_init_2429_;
}
else
{
lean_object* v___f_2435_; lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___f_2435_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2435_, 0, v_f_2428_);
v___x_2436_ = lean_array_get_size(v_as_2430_);
v___x_2437_ = lean_nat_dec_le(v_stop_2432_, v___x_2436_);
if (v___x_2437_ == 0)
{
uint8_t v___x_2438_; 
v___x_2438_ = lean_nat_dec_lt(v_start_2431_, v___x_2436_);
if (v___x_2438_ == 0)
{
lean_dec_ref(v___f_2435_);
lean_dec_ref(v_as_2430_);
return v_init_2429_;
}
else
{
size_t v___x_2439_; size_t v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = lean_usize_of_nat(v_start_2431_);
v___x_2440_ = lean_usize_of_nat(v___x_2436_);
v___x_2441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2433_, v___f_2435_, v_as_2430_, v___x_2439_, v___x_2440_, v_init_2429_);
return v___x_2441_;
}
}
else
{
size_t v___x_2442_; size_t v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = lean_usize_of_nat(v_start_2431_);
v___x_2443_ = lean_usize_of_nat(v_stop_2432_);
v___x_2444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2433_, v___f_2435_, v_as_2430_, v___x_2442_, v___x_2443_, v_init_2429_);
return v___x_2444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___boxed(lean_object* v_f_2445_, lean_object* v_init_2446_, lean_object* v_as_2447_, lean_object* v_start_2448_, lean_object* v_stop_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Array_foldl___redArg(v_f_2445_, v_init_2446_, v_as_2447_, v_start_2448_, v_stop_2449_);
lean_dec(v_stop_2449_);
lean_dec(v_start_2448_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl(lean_object* v_00_u03b1_2451_, lean_object* v_00_u03b2_2452_, lean_object* v_f_2453_, lean_object* v_init_2454_, lean_object* v_as_2455_, lean_object* v_start_2456_, lean_object* v_stop_2457_){
_start:
{
lean_object* v___x_2458_; uint8_t v___x_2459_; 
v___x_2458_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2459_ = lean_nat_dec_lt(v_start_2456_, v_stop_2457_);
if (v___x_2459_ == 0)
{
lean_dec_ref(v_as_2455_);
lean_dec(v_f_2453_);
return v_init_2454_;
}
else
{
lean_object* v___f_2460_; lean_object* v___x_2461_; uint8_t v___x_2462_; 
v___f_2460_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2460_, 0, v_f_2453_);
v___x_2461_ = lean_array_get_size(v_as_2455_);
v___x_2462_ = lean_nat_dec_le(v_stop_2457_, v___x_2461_);
if (v___x_2462_ == 0)
{
uint8_t v___x_2463_; 
v___x_2463_ = lean_nat_dec_lt(v_start_2456_, v___x_2461_);
if (v___x_2463_ == 0)
{
lean_dec_ref(v___f_2460_);
lean_dec_ref(v_as_2455_);
return v_init_2454_;
}
else
{
size_t v___x_2464_; size_t v___x_2465_; lean_object* v___x_2466_; 
v___x_2464_ = lean_usize_of_nat(v_start_2456_);
v___x_2465_ = lean_usize_of_nat(v___x_2461_);
v___x_2466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2458_, v___f_2460_, v_as_2455_, v___x_2464_, v___x_2465_, v_init_2454_);
return v___x_2466_;
}
}
else
{
size_t v___x_2467_; size_t v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = lean_usize_of_nat(v_start_2456_);
v___x_2468_ = lean_usize_of_nat(v_stop_2457_);
v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2458_, v___f_2460_, v_as_2455_, v___x_2467_, v___x_2468_, v_init_2454_);
return v___x_2469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___boxed(lean_object* v_00_u03b1_2470_, lean_object* v_00_u03b2_2471_, lean_object* v_f_2472_, lean_object* v_init_2473_, lean_object* v_as_2474_, lean_object* v_start_2475_, lean_object* v_stop_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Array_foldl(v_00_u03b1_2470_, v_00_u03b2_2471_, v_f_2472_, v_init_2473_, v_as_2474_, v_start_2475_, v_stop_2476_);
lean_dec(v_stop_2476_);
lean_dec(v_start_2475_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg(lean_object* v_f_2478_, lean_object* v_init_2479_, lean_object* v_as_2480_, lean_object* v_start_2481_, lean_object* v_stop_2482_){
_start:
{
lean_object* v___f_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___f_2483_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2483_, 0, v_f_2478_);
v___x_2484_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2485_ = lean_array_get_size(v_as_2480_);
v___x_2486_ = lean_nat_dec_le(v_start_2481_, v___x_2485_);
if (v___x_2486_ == 0)
{
uint8_t v___x_2487_; 
v___x_2487_ = lean_nat_dec_lt(v_stop_2482_, v___x_2485_);
if (v___x_2487_ == 0)
{
lean_dec_ref(v___f_2483_);
lean_dec_ref(v_as_2480_);
return v_init_2479_;
}
else
{
size_t v___x_2488_; size_t v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = lean_usize_of_nat(v___x_2485_);
v___x_2489_ = lean_usize_of_nat(v_stop_2482_);
v___x_2490_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2484_, v___f_2483_, v_as_2480_, v___x_2488_, v___x_2489_, v_init_2479_);
return v___x_2490_;
}
}
else
{
uint8_t v___x_2491_; 
v___x_2491_ = lean_nat_dec_lt(v_stop_2482_, v_start_2481_);
if (v___x_2491_ == 0)
{
lean_dec_ref(v___f_2483_);
lean_dec_ref(v_as_2480_);
return v_init_2479_;
}
else
{
size_t v___x_2492_; size_t v___x_2493_; lean_object* v___x_2494_; 
v___x_2492_ = lean_usize_of_nat(v_start_2481_);
v___x_2493_ = lean_usize_of_nat(v_stop_2482_);
v___x_2494_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2484_, v___f_2483_, v_as_2480_, v___x_2492_, v___x_2493_, v_init_2479_);
return v___x_2494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg___boxed(lean_object* v_f_2495_, lean_object* v_init_2496_, lean_object* v_as_2497_, lean_object* v_start_2498_, lean_object* v_stop_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Array_foldr___redArg(v_f_2495_, v_init_2496_, v_as_2497_, v_start_2498_, v_stop_2499_);
lean_dec(v_stop_2499_);
lean_dec(v_start_2498_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr(lean_object* v_00_u03b1_2501_, lean_object* v_00_u03b2_2502_, lean_object* v_f_2503_, lean_object* v_init_2504_, lean_object* v_as_2505_, lean_object* v_start_2506_, lean_object* v_stop_2507_){
_start:
{
lean_object* v___f_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___f_2508_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2508_, 0, v_f_2503_);
v___x_2509_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2510_ = lean_array_get_size(v_as_2505_);
v___x_2511_ = lean_nat_dec_le(v_start_2506_, v___x_2510_);
if (v___x_2511_ == 0)
{
uint8_t v___x_2512_; 
v___x_2512_ = lean_nat_dec_lt(v_stop_2507_, v___x_2510_);
if (v___x_2512_ == 0)
{
lean_dec_ref(v___f_2508_);
lean_dec_ref(v_as_2505_);
return v_init_2504_;
}
else
{
size_t v___x_2513_; size_t v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = lean_usize_of_nat(v___x_2510_);
v___x_2514_ = lean_usize_of_nat(v_stop_2507_);
v___x_2515_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2509_, v___f_2508_, v_as_2505_, v___x_2513_, v___x_2514_, v_init_2504_);
return v___x_2515_;
}
}
else
{
uint8_t v___x_2516_; 
v___x_2516_ = lean_nat_dec_lt(v_stop_2507_, v_start_2506_);
if (v___x_2516_ == 0)
{
lean_dec_ref(v___f_2508_);
lean_dec_ref(v_as_2505_);
return v_init_2504_;
}
else
{
size_t v___x_2517_; size_t v___x_2518_; lean_object* v___x_2519_; 
v___x_2517_ = lean_usize_of_nat(v_start_2506_);
v___x_2518_ = lean_usize_of_nat(v_stop_2507_);
v___x_2519_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2509_, v___f_2508_, v_as_2505_, v___x_2517_, v___x_2518_, v_init_2504_);
return v___x_2519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___boxed(lean_object* v_00_u03b1_2520_, lean_object* v_00_u03b2_2521_, lean_object* v_f_2522_, lean_object* v_init_2523_, lean_object* v_as_2524_, lean_object* v_start_2525_, lean_object* v_stop_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Array_foldr(v_00_u03b1_2520_, v_00_u03b2_2521_, v_f_2522_, v_init_2523_, v_as_2524_, v_start_2525_, v_stop_2526_);
lean_dec(v_stop_2526_);
lean_dec(v_start_2525_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg___lam__0(lean_object* v_inst_2528_, lean_object* v_x1_2529_, lean_object* v_x2_2530_){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = lean_apply_2(v_inst_2528_, v_x1_2529_, v_x2_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg(lean_object* v_inst_2532_, lean_object* v_inst_2533_, lean_object* v_as_2534_){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2535_ = lean_array_get_size(v_as_2534_);
v___x_2536_ = lean_unsigned_to_nat(0u);
v___x_2537_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2538_ = lean_nat_dec_lt(v___x_2536_, v___x_2535_);
if (v___x_2538_ == 0)
{
lean_dec_ref(v_as_2534_);
lean_dec(v_inst_2532_);
return v_inst_2533_;
}
else
{
lean_object* v___f_2539_; size_t v___x_2540_; size_t v___x_2541_; lean_object* v___x_2542_; 
v___f_2539_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2539_, 0, v_inst_2532_);
v___x_2540_ = lean_usize_of_nat(v___x_2535_);
v___x_2541_ = ((size_t)0ULL);
v___x_2542_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2537_, v___f_2539_, v_as_2534_, v___x_2540_, v___x_2541_, v_inst_2533_);
return v___x_2542_;
}
}
}
LEAN_EXPORT lean_object* l_Array_sum(lean_object* v_00_u03b1_2543_, lean_object* v_inst_2544_, lean_object* v_inst_2545_, lean_object* v_as_2546_){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2547_ = lean_array_get_size(v_as_2546_);
v___x_2548_ = lean_unsigned_to_nat(0u);
v___x_2549_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2550_ = lean_nat_dec_lt(v___x_2548_, v___x_2547_);
if (v___x_2550_ == 0)
{
lean_dec_ref(v_as_2546_);
lean_dec(v_inst_2544_);
return v_inst_2545_;
}
else
{
lean_object* v___f_2551_; size_t v___x_2552_; size_t v___x_2553_; lean_object* v___x_2554_; 
v___f_2551_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2551_, 0, v_inst_2544_);
v___x_2552_ = lean_usize_of_nat(v___x_2547_);
v___x_2553_ = ((size_t)0ULL);
v___x_2554_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2549_, v___f_2551_, v_as_2546_, v___x_2552_, v___x_2553_, v_inst_2545_);
return v___x_2554_;
}
}
}
LEAN_EXPORT lean_object* l_Array_prod___redArg(lean_object* v_inst_2555_, lean_object* v_inst_2556_, lean_object* v_as_2557_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2558_ = lean_array_get_size(v_as_2557_);
v___x_2559_ = lean_unsigned_to_nat(0u);
v___x_2560_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2561_ = lean_nat_dec_lt(v___x_2559_, v___x_2558_);
if (v___x_2561_ == 0)
{
lean_dec_ref(v_as_2557_);
lean_dec(v_inst_2555_);
return v_inst_2556_;
}
else
{
lean_object* v___f_2562_; size_t v___x_2563_; size_t v___x_2564_; lean_object* v___x_2565_; 
v___f_2562_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2562_, 0, v_inst_2555_);
v___x_2563_ = lean_usize_of_nat(v___x_2558_);
v___x_2564_ = ((size_t)0ULL);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2560_, v___f_2562_, v_as_2557_, v___x_2563_, v___x_2564_, v_inst_2556_);
return v___x_2565_;
}
}
}
LEAN_EXPORT lean_object* l_Array_prod(lean_object* v_00_u03b1_2566_, lean_object* v_inst_2567_, lean_object* v_inst_2568_, lean_object* v_as_2569_){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2570_ = lean_array_get_size(v_as_2569_);
v___x_2571_ = lean_unsigned_to_nat(0u);
v___x_2572_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2573_ = lean_nat_dec_lt(v___x_2571_, v___x_2570_);
if (v___x_2573_ == 0)
{
lean_dec_ref(v_as_2569_);
lean_dec(v_inst_2567_);
return v_inst_2568_;
}
else
{
lean_object* v___f_2574_; size_t v___x_2575_; size_t v___x_2576_; lean_object* v___x_2577_; 
v___f_2574_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2574_, 0, v_inst_2567_);
v___x_2575_ = lean_usize_of_nat(v___x_2570_);
v___x_2576_ = ((size_t)0ULL);
v___x_2577_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2572_, v___f_2574_, v_as_2569_, v___x_2575_, v___x_2576_, v_inst_2568_);
return v___x_2577_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0(lean_object* v_p_2578_, lean_object* v_x1_2579_, lean_object* v_x2_2580_){
_start:
{
lean_object* v___x_2581_; uint8_t v___x_2582_; 
v___x_2581_ = lean_apply_1(v_p_2578_, v_x1_2579_);
v___x_2582_ = lean_unbox(v___x_2581_);
if (v___x_2582_ == 0)
{
lean_inc(v_x2_2580_);
return v_x2_2580_;
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_unsigned_to_nat(1u);
v___x_2584_ = lean_nat_add(v_x2_2580_, v___x_2583_);
return v___x_2584_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0___boxed(lean_object* v_p_2585_, lean_object* v_x1_2586_, lean_object* v_x2_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Array_countP___redArg___lam__0(v_p_2585_, v_x1_2586_, v_x2_2587_);
lean_dec(v_x2_2587_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg(lean_object* v_p_2589_, lean_object* v_as_2590_){
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
lean_dec_ref(v_p_2589_);
return v___x_2591_;
}
else
{
lean_object* v___f_2595_; size_t v___x_2596_; size_t v___x_2597_; lean_object* v___x_2598_; 
v___f_2595_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2595_, 0, v_p_2589_);
v___x_2596_ = lean_usize_of_nat(v___x_2592_);
v___x_2597_ = ((size_t)0ULL);
v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2593_, v___f_2595_, v_as_2590_, v___x_2596_, v___x_2597_, v___x_2591_);
return v___x_2598_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP(lean_object* v_00_u03b1_2599_, lean_object* v_p_2600_, lean_object* v_as_2601_){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
v___x_2602_ = lean_unsigned_to_nat(0u);
v___x_2603_ = lean_array_get_size(v_as_2601_);
v___x_2604_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2605_ = lean_nat_dec_lt(v___x_2602_, v___x_2603_);
if (v___x_2605_ == 0)
{
lean_dec_ref(v_as_2601_);
lean_dec_ref(v_p_2600_);
return v___x_2602_;
}
else
{
lean_object* v___f_2606_; size_t v___x_2607_; size_t v___x_2608_; lean_object* v___x_2609_; 
v___f_2606_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2606_, 0, v_p_2600_);
v___x_2607_ = lean_usize_of_nat(v___x_2603_);
v___x_2608_ = ((size_t)0ULL);
v___x_2609_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2604_, v___f_2606_, v_as_2601_, v___x_2607_, v___x_2608_, v___x_2602_);
return v___x_2609_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0(lean_object* v_inst_2610_, lean_object* v_a_2611_, lean_object* v_x1_2612_, lean_object* v_x2_2613_){
_start:
{
lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2614_ = lean_apply_2(v_inst_2610_, v_x1_2612_, v_a_2611_);
v___x_2615_ = lean_unbox(v___x_2614_);
if (v___x_2615_ == 0)
{
lean_inc(v_x2_2613_);
return v_x2_2613_;
}
else
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = lean_unsigned_to_nat(1u);
v___x_2617_ = lean_nat_add(v_x2_2613_, v___x_2616_);
return v___x_2617_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0___boxed(lean_object* v_inst_2618_, lean_object* v_a_2619_, lean_object* v_x1_2620_, lean_object* v_x2_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Array_count___redArg___lam__0(v_inst_2618_, v_a_2619_, v_x1_2620_, v_x2_2621_);
lean_dec(v_x2_2621_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg(lean_object* v_inst_2623_, lean_object* v_a_2624_, lean_object* v_as_2625_){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2626_ = lean_unsigned_to_nat(0u);
v___x_2627_ = lean_array_get_size(v_as_2625_);
v___x_2628_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2629_ = lean_nat_dec_lt(v___x_2626_, v___x_2627_);
if (v___x_2629_ == 0)
{
lean_dec_ref(v_as_2625_);
lean_dec(v_a_2624_);
lean_dec_ref(v_inst_2623_);
return v___x_2626_;
}
else
{
lean_object* v___f_2630_; size_t v___x_2631_; size_t v___x_2632_; lean_object* v___x_2633_; 
v___f_2630_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2630_, 0, v_inst_2623_);
lean_closure_set(v___f_2630_, 1, v_a_2624_);
v___x_2631_ = lean_usize_of_nat(v___x_2627_);
v___x_2632_ = ((size_t)0ULL);
v___x_2633_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2628_, v___f_2630_, v_as_2625_, v___x_2631_, v___x_2632_, v___x_2626_);
return v___x_2633_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count(lean_object* v_00_u03b1_2634_, lean_object* v_inst_2635_, lean_object* v_a_2636_, lean_object* v_as_2637_){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; 
v___x_2638_ = lean_unsigned_to_nat(0u);
v___x_2639_ = lean_array_get_size(v_as_2637_);
v___x_2640_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2641_ = lean_nat_dec_lt(v___x_2638_, v___x_2639_);
if (v___x_2641_ == 0)
{
lean_dec_ref(v_as_2637_);
lean_dec(v_a_2636_);
lean_dec_ref(v_inst_2635_);
return v___x_2638_;
}
else
{
lean_object* v___f_2642_; size_t v___x_2643_; size_t v___x_2644_; lean_object* v___x_2645_; 
v___f_2642_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2642_, 0, v_inst_2635_);
lean_closure_set(v___f_2642_, 1, v_a_2636_);
v___x_2643_ = lean_usize_of_nat(v___x_2639_);
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2640_, v___f_2642_, v_as_2637_, v___x_2643_, v___x_2644_, v___x_2638_);
return v___x_2645_;
}
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg___lam__0(lean_object* v_f_2646_, lean_object* v_x_2647_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_apply_1(v_f_2646_, v_x_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg(lean_object* v_f_2649_, lean_object* v_as_2650_){
_start:
{
lean_object* v___f_2651_; lean_object* v___x_2652_; size_t v_sz_2653_; size_t v___x_2654_; lean_object* v___x_2655_; 
v___f_2651_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2651_, 0, v_f_2649_);
v___x_2652_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2653_ = lean_array_size(v_as_2650_);
v___x_2654_ = ((size_t)0ULL);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2652_, v___f_2651_, v_sz_2653_, v___x_2654_, v_as_2650_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Array_map(lean_object* v_00_u03b1_2656_, lean_object* v_00_u03b2_2657_, lean_object* v_f_2658_, lean_object* v_as_2659_){
_start:
{
lean_object* v___f_2660_; lean_object* v___x_2661_; size_t v_sz_2662_; size_t v___x_2663_; lean_object* v___x_2664_; 
v___f_2660_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2660_, 0, v_f_2658_);
v___x_2661_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2662_ = lean_array_size(v_as_2659_);
v___x_2663_ = ((size_t)0ULL);
v___x_2664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2661_, v___f_2660_, v_sz_2662_, v___x_2663_, v_as_2659_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0(lean_object* v___y_2665_, lean_object* v_x_2666_){
_start:
{
lean_inc(v___y_2665_);
return v___y_2665_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0___boxed(lean_object* v___y_2667_, lean_object* v_x_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Array_instFunctor___lam__0(v___y_2667_, v_x_2668_);
lean_dec(v_x_2668_);
lean_dec(v___y_2667_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__1(lean_object* v_00_u03b1_2670_, lean_object* v_00_u03b2_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v___f_2674_; lean_object* v___x_2675_; size_t v_sz_2676_; size_t v___x_2677_; lean_object* v___x_2678_; 
v___f_2674_ = lean_alloc_closure((void*)(l_Array_instFunctor___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2674_, 0, v___y_2672_);
v___x_2675_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2676_ = lean_array_size(v___y_2673_);
v___x_2677_ = ((size_t)0ULL);
v___x_2678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2675_, v___f_2674_, v_sz_2676_, v___x_2677_, v___y_2673_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg___lam__0(lean_object* v_f_2685_, lean_object* v_x1_2686_, lean_object* v_x2_2687_, lean_object* v_x3_2688_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = lean_apply_3(v_f_2685_, v_x1_2686_, v_x2_2687_, lean_box(0));
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg(lean_object* v_as_2690_, lean_object* v_f_2691_){
_start:
{
lean_object* v___f_2692_; lean_object* v___x_2693_; size_t v_sz_2694_; size_t v___x_2695_; lean_object* v___x_2696_; 
v___f_2692_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2692_, 0, v_f_2691_);
v___x_2693_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2694_ = lean_array_size(v_as_2690_);
v___x_2695_ = ((size_t)0ULL);
v___x_2696_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2693_, v___f_2692_, v_sz_2694_, v___x_2695_, v_as_2690_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx(lean_object* v_00_u03b1_2697_, lean_object* v_00_u03b2_2698_, lean_object* v_as_2699_, lean_object* v_f_2700_){
_start:
{
lean_object* v___f_2701_; lean_object* v___x_2702_; size_t v_sz_2703_; size_t v___x_2704_; lean_object* v___x_2705_; 
v___f_2701_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2701_, 0, v_f_2700_);
v___x_2702_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2703_ = lean_array_size(v_as_2699_);
v___x_2704_ = ((size_t)0ULL);
v___x_2705_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2702_, v___f_2701_, v_sz_2703_, v___x_2704_, v_as_2699_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx___redArg(lean_object* v_f_2706_, lean_object* v_as_2707_){
_start:
{
lean_object* v___f_2708_; lean_object* v___x_2709_; size_t v_sz_2710_; size_t v___x_2711_; lean_object* v___x_2712_; 
v___f_2708_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2708_, 0, v_f_2706_);
v___x_2709_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2710_ = lean_array_size(v_as_2707_);
v___x_2711_ = ((size_t)0ULL);
v___x_2712_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2709_, v___f_2708_, v_sz_2710_, v___x_2711_, v_as_2707_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx(lean_object* v_00_u03b1_2713_, lean_object* v_00_u03b2_2714_, lean_object* v_f_2715_, lean_object* v_as_2716_){
_start:
{
lean_object* v___f_2717_; lean_object* v___x_2718_; size_t v_sz_2719_; size_t v___x_2720_; lean_object* v___x_2721_; 
v___f_2717_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2717_, 0, v_f_2715_);
v___x_2718_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2719_ = lean_array_size(v_as_2716_);
v___x_2720_ = ((size_t)0ULL);
v___x_2721_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___redArg(v___x_2718_, v___f_2717_, v_sz_2719_, v___x_2720_, v_as_2716_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(lean_object* v_start_2722_, size_t v_sz_2723_, size_t v_i_2724_, lean_object* v_bs_2725_){
_start:
{
uint8_t v___x_2726_; 
v___x_2726_ = lean_usize_dec_lt(v_i_2724_, v_sz_2723_);
if (v___x_2726_ == 0)
{
return v_bs_2725_;
}
else
{
lean_object* v_v_2727_; lean_object* v___x_2728_; lean_object* v_bs_x27_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; size_t v___x_2733_; size_t v___x_2734_; lean_object* v___x_2735_; 
v_v_2727_ = lean_array_uget(v_bs_2725_, v_i_2724_);
v___x_2728_ = lean_unsigned_to_nat(0u);
v_bs_x27_2729_ = lean_array_uset(v_bs_2725_, v_i_2724_, v___x_2728_);
v___x_2730_ = lean_usize_to_nat(v_i_2724_);
v___x_2731_ = lean_nat_add(v_start_2722_, v___x_2730_);
lean_dec(v___x_2730_);
v___x_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2732_, 0, v_v_2727_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
v___x_2733_ = ((size_t)1ULL);
v___x_2734_ = lean_usize_add(v_i_2724_, v___x_2733_);
v___x_2735_ = lean_array_uset(v_bs_x27_2729_, v_i_2724_, v___x_2732_);
v_i_2724_ = v___x_2734_;
v_bs_2725_ = v___x_2735_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg___boxed(lean_object* v_start_2737_, lean_object* v_sz_2738_, lean_object* v_i_2739_, lean_object* v_bs_2740_){
_start:
{
size_t v_sz_boxed_2741_; size_t v_i_boxed_2742_; lean_object* v_res_2743_; 
v_sz_boxed_2741_ = lean_unbox_usize(v_sz_2738_);
lean_dec(v_sz_2738_);
v_i_boxed_2742_ = lean_unbox_usize(v_i_2739_);
lean_dec(v_i_2739_);
v_res_2743_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2737_, v_sz_boxed_2741_, v_i_boxed_2742_, v_bs_2740_);
lean_dec(v_start_2737_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg(lean_object* v_xs_2744_, lean_object* v_start_2745_){
_start:
{
size_t v_sz_2746_; size_t v___x_2747_; lean_object* v___x_2748_; 
v_sz_2746_ = lean_array_size(v_xs_2744_);
v___x_2747_ = ((size_t)0ULL);
v___x_2748_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2745_, v_sz_2746_, v___x_2747_, v_xs_2744_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg___boxed(lean_object* v_xs_2749_, lean_object* v_start_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Array_zipIdx___redArg(v_xs_2749_, v_start_2750_);
lean_dec(v_start_2750_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx(lean_object* v_00_u03b1_2752_, lean_object* v_xs_2753_, lean_object* v_start_2754_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Array_zipIdx___redArg(v_xs_2753_, v_start_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___boxed(lean_object* v_00_u03b1_2756_, lean_object* v_xs_2757_, lean_object* v_start_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Array_zipIdx(v_00_u03b1_2756_, v_xs_2757_, v_start_2758_);
lean_dec(v_start_2758_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(lean_object* v_00_u03b1_2760_, lean_object* v_start_2761_, lean_object* v_as_2762_, size_t v_sz_2763_, size_t v_i_2764_, lean_object* v_bs_2765_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___redArg(v_start_2761_, v_sz_2763_, v_i_2764_, v_bs_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0___boxed(lean_object* v_00_u03b1_2767_, lean_object* v_start_2768_, lean_object* v_as_2769_, lean_object* v_sz_2770_, lean_object* v_i_2771_, lean_object* v_bs_2772_){
_start:
{
size_t v_sz_boxed_2773_; size_t v_i_boxed_2774_; lean_object* v_res_2775_; 
v_sz_boxed_2773_ = lean_unbox_usize(v_sz_2770_);
lean_dec(v_sz_2770_);
v_i_boxed_2774_ = lean_unbox_usize(v_i_2771_);
lean_dec(v_i_2771_);
v_res_2775_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Array_zipIdx_spec__0(v_00_u03b1_2767_, v_start_2768_, v_as_2769_, v_sz_boxed_2773_, v_i_boxed_2774_, v_bs_2772_);
lean_dec_ref(v_as_2769_);
lean_dec(v_start_2768_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0(lean_object* v_p_2776_, lean_object* v___x_2777_, lean_object* v___x_2778_, lean_object* v_a_2779_, lean_object* v_x_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v___x_2782_; uint8_t v___x_2783_; 
lean_inc(v_a_2779_);
v___x_2782_ = lean_apply_1(v_p_2776_, v_a_2779_);
v___x_2783_ = lean_unbox(v___x_2782_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; 
lean_dec(v_a_2779_);
v___x_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2777_);
return v___x_2784_;
}
else
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_dec_ref(v___x_2777_);
v___x_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2785_, 0, v_a_2779_);
v___x_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
lean_ctor_set(v___x_2787_, 1, v___x_2778_);
v___x_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
return v___x_2788_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0___boxed(lean_object* v_p_2789_, lean_object* v___x_2790_, lean_object* v___x_2791_, lean_object* v_a_2792_, lean_object* v_x_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Array_find_x3f___redArg___lam__0(v_p_2789_, v___x_2790_, v___x_2791_, v_a_2792_, v_x_2793_, v___y_2794_);
lean_dec_ref(v___y_2794_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg(lean_object* v_p_2796_, lean_object* v_as_2797_){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___f_2802_; size_t v_sz_2803_; size_t v___x_2804_; lean_object* v___x_2805_; lean_object* v_fst_2806_; 
v___x_2798_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2799_ = lean_box(0);
v___x_2800_ = lean_box(0);
v___x_2801_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2802_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2802_, 0, v_p_2796_);
lean_closure_set(v___f_2802_, 1, v___x_2801_);
lean_closure_set(v___f_2802_, 2, v___x_2800_);
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
lean_dec_ref_known(v_fst_2806_, 1);
return v_val_2807_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f(lean_object* v_00_u03b1_2808_, lean_object* v_p_2809_, lean_object* v_as_2810_){
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
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0(lean_object* v_f_2821_, lean_object* v___x_2822_, lean_object* v___x_2823_, lean_object* v_a_2824_, lean_object* v_x_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = lean_apply_1(v_f_2821_, v_a_2824_);
if (lean_obj_tag(v___x_2827_) == 1)
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_dec_ref(v___x_2823_);
v___x_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
lean_ctor_set(v___x_2829_, 1, v___x_2822_);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
return v___x_2830_;
}
else
{
lean_object* v___x_2831_; 
lean_dec(v___x_2827_);
v___x_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2823_);
return v___x_2831_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2832_, lean_object* v___x_2833_, lean_object* v___x_2834_, lean_object* v_a_2835_, lean_object* v_x_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Array_findSome_x3f___redArg___lam__0(v_f_2832_, v___x_2833_, v___x_2834_, v_a_2835_, v_x_2836_, v___y_2837_);
lean_dec_ref(v___y_2837_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg(lean_object* v_f_2839_, lean_object* v_as_2840_){
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
LEAN_EXPORT lean_object* l_Array_findSome_x3f(lean_object* v_00_u03b1_2851_, lean_object* v_00_u03b2_2852_, lean_object* v_f_2853_, lean_object* v_as_2854_){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___f_2859_; size_t v_sz_2860_; size_t v___x_2861_; lean_object* v___x_2862_; lean_object* v_fst_2863_; 
v___x_2855_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2856_ = lean_box(0);
v___x_2857_ = lean_box(0);
v___x_2858_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2859_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2859_, 0, v_f_2853_);
lean_closure_set(v___f_2859_, 1, v___x_2857_);
lean_closure_set(v___f_2859_, 2, v___x_2858_);
v_sz_2860_ = lean_array_size(v_as_2854_);
v___x_2861_ = ((size_t)0ULL);
v___x_2862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2855_, v_as_2854_, v___f_2859_, v_sz_2860_, v___x_2861_, v___x_2858_);
v_fst_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_fst_2863_);
lean_dec(v___x_2862_);
if (lean_obj_tag(v_fst_2863_) == 0)
{
return v___x_2856_;
}
else
{
lean_object* v_val_2864_; 
v_val_2864_ = lean_ctor_get(v_fst_2863_, 0);
lean_inc(v_val_2864_);
lean_dec_ref_known(v_fst_2863_, 1);
return v_val_2864_;
}
}
}
static lean_object* _init_l_Array_findSome_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2867_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__1));
v___x_2868_ = lean_unsigned_to_nat(14u);
v___x_2869_ = lean_unsigned_to_nat(1279u);
v___x_2870_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__0));
v___x_2871_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_2872_ = l_mkPanicMessageWithDecl(v___x_2871_, v___x_2870_, v___x_2869_, v___x_2868_, v___x_2867_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg(lean_object* v_inst_2873_, lean_object* v_f_2874_, lean_object* v_xs_2875_){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___f_2882_; size_t v_sz_2883_; size_t v___x_2884_; lean_object* v___x_2885_; lean_object* v_fst_2886_; 
v___x_2879_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2880_ = lean_box(0);
v___x_2881_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2882_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2882_, 0, v_f_2874_);
lean_closure_set(v___f_2882_, 1, v___x_2880_);
lean_closure_set(v___f_2882_, 2, v___x_2881_);
v_sz_2883_ = lean_array_size(v_xs_2875_);
v___x_2884_ = ((size_t)0ULL);
v___x_2885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2879_, v_xs_2875_, v___f_2882_, v_sz_2883_, v___x_2884_, v___x_2881_);
v_fst_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_fst_2886_);
lean_dec(v___x_2885_);
if (lean_obj_tag(v_fst_2886_) == 0)
{
goto v___jp_2876_;
}
else
{
lean_object* v_val_2887_; 
v_val_2887_ = lean_ctor_get(v_fst_2886_, 0);
lean_inc(v_val_2887_);
lean_dec_ref_known(v_fst_2886_, 1);
if (lean_obj_tag(v_val_2887_) == 0)
{
goto v___jp_2876_;
}
else
{
lean_object* v_val_2888_; 
v_val_2888_ = lean_ctor_get(v_val_2887_, 0);
lean_inc(v_val_2888_);
lean_dec_ref_known(v_val_2887_, 1);
return v_val_2888_;
}
}
v___jp_2876_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2878_ = l_panic___redArg(v_inst_2873_, v___x_2877_);
return v___x_2878_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg___boxed(lean_object* v_inst_2889_, lean_object* v_f_2890_, lean_object* v_xs_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Array_findSome_x21___redArg(v_inst_2889_, v_f_2890_, v_xs_2891_);
lean_dec(v_inst_2889_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21(lean_object* v_00_u03b1_2893_, lean_object* v_00_u03b2_2894_, lean_object* v_inst_2895_, lean_object* v_f_2896_, lean_object* v_xs_2897_){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___f_2904_; size_t v_sz_2905_; size_t v___x_2906_; lean_object* v___x_2907_; lean_object* v_fst_2908_; 
v___x_2901_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2902_ = lean_box(0);
v___x_2903_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2904_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2904_, 0, v_f_2896_);
lean_closure_set(v___f_2904_, 1, v___x_2902_);
lean_closure_set(v___f_2904_, 2, v___x_2903_);
v_sz_2905_ = lean_array_size(v_xs_2897_);
v___x_2906_ = ((size_t)0ULL);
v___x_2907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2901_, v_xs_2897_, v___f_2904_, v_sz_2905_, v___x_2906_, v___x_2903_);
v_fst_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_fst_2908_);
lean_dec(v___x_2907_);
if (lean_obj_tag(v_fst_2908_) == 0)
{
goto v___jp_2898_;
}
else
{
lean_object* v_val_2909_; 
v_val_2909_ = lean_ctor_get(v_fst_2908_, 0);
lean_inc(v_val_2909_);
lean_dec_ref_known(v_fst_2908_, 1);
if (lean_obj_tag(v_val_2909_) == 0)
{
goto v___jp_2898_;
}
else
{
lean_object* v_val_2910_; 
v_val_2910_ = lean_ctor_get(v_val_2909_, 0);
lean_inc(v_val_2910_);
lean_dec_ref_known(v_val_2909_, 1);
return v_val_2910_;
}
}
v___jp_2898_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2900_ = l_panic___redArg(v_inst_2895_, v___x_2899_);
return v___x_2900_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___boxed(lean_object* v_00_u03b1_2911_, lean_object* v_00_u03b2_2912_, lean_object* v_inst_2913_, lean_object* v_f_2914_, lean_object* v_xs_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Array_findSome_x21(v_00_u03b1_2911_, v_00_u03b2_2912_, v_inst_2913_, v_f_2914_, v_xs_2915_);
lean_dec(v_inst_2913_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2917_, lean_object* v_x_2918_){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = lean_apply_1(v_f_2917_, v_x_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg(lean_object* v_f_2920_, lean_object* v_as_2921_){
_start:
{
lean_object* v___f_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___f_2922_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2922_, 0, v_f_2920_);
v___x_2923_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2924_ = lean_array_get_size(v_as_2921_);
v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2923_, v___f_2922_, v_as_2921_, v___x_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f(lean_object* v_00_u03b1_2926_, lean_object* v_00_u03b2_2927_, lean_object* v_f_2928_, lean_object* v_as_2929_){
_start:
{
lean_object* v___f_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___f_2930_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2930_, 0, v_f_2928_);
v___x_2931_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2932_ = lean_array_get_size(v_as_2929_);
v___x_2933_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2931_, v___f_2930_, v_as_2929_, v___x_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg___lam__0(lean_object* v_p_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v___x_2936_; uint8_t v___x_2937_; 
lean_inc(v_a_2935_);
v___x_2936_ = lean_apply_1(v_p_2934_, v_a_2935_);
v___x_2937_ = lean_unbox(v___x_2936_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; 
lean_dec(v_a_2935_);
v___x_2938_ = lean_box(0);
return v___x_2938_;
}
else
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2939_, 0, v_a_2935_);
return v___x_2939_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg(lean_object* v_p_2940_, lean_object* v_as_2941_){
_start:
{
lean_object* v___f_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___f_2942_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2942_, 0, v_p_2940_);
v___x_2943_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2944_ = lean_array_get_size(v_as_2941_);
v___x_2945_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2943_, v___f_2942_, v_as_2941_, v___x_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f(lean_object* v_00_u03b1_2946_, lean_object* v_p_2947_, lean_object* v_as_2948_){
_start:
{
lean_object* v___f_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___f_2949_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2949_, 0, v_p_2947_);
v___x_2950_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2951_ = lean_array_get_size(v_as_2948_);
v___x_2952_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2950_, v___f_2949_, v_as_2948_, v___x_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object* v_p_2953_, lean_object* v_as_2954_, lean_object* v_j_2955_){
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
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg___boxed(lean_object* v_p_2966_, lean_object* v_as_2967_, lean_object* v_j_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Array_findIdx_x3f_loop___redArg(v_p_2966_, v_as_2967_, v_j_2968_);
lean_dec_ref(v_as_2967_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop(lean_object* v_00_u03b1_2970_, lean_object* v_p_2971_, lean_object* v_as_2972_, lean_object* v_j_2973_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Array_findIdx_x3f_loop___redArg(v_p_2971_, v_as_2972_, v_j_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___boxed(lean_object* v_00_u03b1_2975_, lean_object* v_p_2976_, lean_object* v_as_2977_, lean_object* v_j_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Array_findIdx_x3f_loop(v_00_u03b1_2975_, v_p_2976_, v_as_2977_, v_j_2978_);
lean_dec_ref(v_as_2977_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg(lean_object* v_p_2980_, lean_object* v_as_2981_){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = lean_unsigned_to_nat(0u);
v___x_2983_ = l_Array_findIdx_x3f_loop___redArg(v_p_2980_, v_as_2981_, v___x_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg___boxed(lean_object* v_p_2984_, lean_object* v_as_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_Array_findIdx_x3f___redArg(v_p_2984_, v_as_2985_);
lean_dec_ref(v_as_2985_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f(lean_object* v_00_u03b1_2987_, lean_object* v_p_2988_, lean_object* v_as_2989_){
_start:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = lean_unsigned_to_nat(0u);
v___x_2991_ = l_Array_findIdx_x3f_loop___redArg(v_p_2988_, v_as_2989_, v___x_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___boxed(lean_object* v_00_u03b1_2992_, lean_object* v_p_2993_, lean_object* v_as_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Array_findIdx_x3f(v_00_u03b1_2992_, v_p_2993_, v_as_2994_);
lean_dec_ref(v_as_2994_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(lean_object* v_p_2996_, lean_object* v_as_2997_, lean_object* v_j_2998_){
_start:
{
lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2999_ = lean_array_get_size(v_as_2997_);
v___x_3000_ = lean_nat_dec_lt(v_j_2998_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
lean_dec(v_j_2998_);
lean_dec_ref(v_p_2996_);
v___x_3001_ = lean_box(0);
return v___x_3001_;
}
else
{
lean_object* v___x_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3002_ = lean_array_fget_borrowed(v_as_2997_, v_j_2998_);
lean_inc_ref(v_p_2996_);
lean_inc(v___x_3002_);
v___x_3003_ = lean_apply_1(v_p_2996_, v___x_3002_);
v___x_3004_ = lean_unbox(v___x_3003_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3005_ = lean_unsigned_to_nat(1u);
v___x_3006_ = lean_nat_add(v_j_2998_, v___x_3005_);
lean_dec(v_j_2998_);
v_j_2998_ = v___x_3006_;
goto _start;
}
else
{
lean_object* v___x_3008_; 
lean_dec_ref(v_p_2996_);
v___x_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3008_, 0, v_j_2998_);
return v___x_3008_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg___boxed(lean_object* v_p_3009_, lean_object* v_as_3010_, lean_object* v_j_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3009_, v_as_3010_, v_j_3011_);
lean_dec_ref(v_as_3010_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object* v_00_u03b1_3013_, lean_object* v_p_3014_, lean_object* v_as_3015_, lean_object* v_j_3016_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3014_, v_as_3015_, v_j_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___boxed(lean_object* v_00_u03b1_3018_, lean_object* v_p_3019_, lean_object* v_as_3020_, lean_object* v_j_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(v_00_u03b1_3018_, v_p_3019_, v_as_3020_, v_j_3021_);
lean_dec_ref(v_as_3020_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg(lean_object* v_p_3023_, lean_object* v_as_3024_){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_unsigned_to_nat(0u);
v___x_3026_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3023_, v_as_3024_, v___x_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg___boxed(lean_object* v_p_3027_, lean_object* v_as_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Array_findFinIdx_x3f___redArg(v_p_3027_, v_as_3028_);
lean_dec_ref(v_as_3028_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f(lean_object* v_00_u03b1_3030_, lean_object* v_p_3031_, lean_object* v_as_3032_){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = lean_unsigned_to_nat(0u);
v___x_3034_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_3031_, v_as_3032_, v___x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_3035_, lean_object* v_p_3036_, lean_object* v_as_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Array_findFinIdx_x3f(v_00_u03b1_3035_, v_p_3036_, v_as_3037_);
lean_dec_ref(v_as_3037_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg(lean_object* v_p_3039_, lean_object* v_as_3040_){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = lean_unsigned_to_nat(0u);
v___x_3042_ = l_Array_findIdx_x3f_loop___redArg(v_p_3039_, v_as_3040_, v___x_3041_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_array_get_size(v_as_3040_);
return v___x_3043_;
}
else
{
lean_object* v_val_3044_; 
v_val_3044_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_val_3044_);
lean_dec_ref_known(v___x_3042_, 1);
return v_val_3044_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg___boxed(lean_object* v_p_3045_, lean_object* v_as_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Array_findIdx___redArg(v_p_3045_, v_as_3046_);
lean_dec_ref(v_as_3046_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx(lean_object* v_00_u03b1_3048_, lean_object* v_p_3049_, lean_object* v_as_3050_){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = lean_unsigned_to_nat(0u);
v___x_3052_ = l_Array_findIdx_x3f_loop___redArg(v_p_3049_, v_as_3050_, v___x_3051_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_array_get_size(v_as_3050_);
return v___x_3053_;
}
else
{
lean_object* v_val_3054_; 
v_val_3054_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_val_3054_);
lean_dec_ref_known(v___x_3052_, 1);
return v_val_3054_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___boxed(lean_object* v_00_u03b1_3055_, lean_object* v_p_3056_, lean_object* v_as_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Array_findIdx(v_00_u03b1_3055_, v_p_3056_, v_as_3057_);
lean_dec_ref(v_as_3057_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg(lean_object* v_inst_3059_, lean_object* v_xs_3060_, lean_object* v_v_3061_, lean_object* v_i_3062_){
_start:
{
lean_object* v___x_3063_; uint8_t v___x_3064_; 
v___x_3063_ = lean_array_get_size(v_xs_3060_);
v___x_3064_ = lean_nat_dec_lt(v_i_3062_, v___x_3063_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; 
lean_dec(v_i_3062_);
lean_dec(v_v_3061_);
lean_dec_ref(v_inst_3059_);
v___x_3065_ = lean_box(0);
return v___x_3065_;
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v___x_3066_ = lean_array_fget_borrowed(v_xs_3060_, v_i_3062_);
lean_inc_ref(v_inst_3059_);
lean_inc(v_v_3061_);
lean_inc(v___x_3066_);
v___x_3067_ = lean_apply_2(v_inst_3059_, v___x_3066_, v_v_3061_);
v___x_3068_ = lean_unbox(v___x_3067_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_unsigned_to_nat(1u);
v___x_3070_ = lean_nat_add(v_i_3062_, v___x_3069_);
lean_dec(v_i_3062_);
v_i_3062_ = v___x_3070_;
goto _start;
}
else
{
lean_object* v___x_3072_; 
lean_dec(v_v_3061_);
lean_dec_ref(v_inst_3059_);
v___x_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3072_, 0, v_i_3062_);
return v___x_3072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg___boxed(lean_object* v_inst_3073_, lean_object* v_xs_3074_, lean_object* v_v_3075_, lean_object* v_i_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Array_idxOfAux___redArg(v_inst_3073_, v_xs_3074_, v_v_3075_, v_i_3076_);
lean_dec_ref(v_xs_3074_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux(lean_object* v_00_u03b1_3078_, lean_object* v_inst_3079_, lean_object* v_xs_3080_, lean_object* v_v_3081_, lean_object* v_i_3082_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = l_Array_idxOfAux___redArg(v_inst_3079_, v_xs_3080_, v_v_3081_, v_i_3082_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___boxed(lean_object* v_00_u03b1_3084_, lean_object* v_inst_3085_, lean_object* v_xs_3086_, lean_object* v_v_3087_, lean_object* v_i_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Array_idxOfAux(v_00_u03b1_3084_, v_inst_3085_, v_xs_3086_, v_v_3087_, v_i_3088_);
lean_dec_ref(v_xs_3086_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg(lean_object* v_inst_3090_, lean_object* v_xs_3091_, lean_object* v_v_3092_){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = lean_unsigned_to_nat(0u);
v___x_3094_ = l_Array_idxOfAux___redArg(v_inst_3090_, v_xs_3091_, v_v_3092_, v___x_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_3095_, lean_object* v_xs_3096_, lean_object* v_v_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Array_finIdxOf_x3f___redArg(v_inst_3095_, v_xs_3096_, v_v_3097_);
lean_dec_ref(v_xs_3096_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f(lean_object* v_00_u03b1_3099_, lean_object* v_inst_3100_, lean_object* v_xs_3101_, lean_object* v_v_3102_){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l_Array_finIdxOf_x3f___redArg(v_inst_3100_, v_xs_3101_, v_v_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_3104_, lean_object* v_inst_3105_, lean_object* v_xs_3106_, lean_object* v_v_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Array_finIdxOf_x3f(v_00_u03b1_3104_, v_inst_3105_, v_xs_3106_, v_v_3107_);
lean_dec_ref(v_xs_3106_);
return v_res_3108_;
}
}
LEAN_EXPORT uint8_t l_Array_idxOf___redArg___lam__0(lean_object* v_inst_3109_, lean_object* v_a_3110_, lean_object* v_x_3111_){
_start:
{
lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = lean_apply_2(v_inst_3109_, v_x_3111_, v_a_3110_);
v___x_3113_ = lean_unbox(v___x_3112_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___lam__0___boxed(lean_object* v_inst_3114_, lean_object* v_a_3115_, lean_object* v_x_3116_){
_start:
{
uint8_t v_res_3117_; lean_object* v_r_3118_; 
v_res_3117_ = l_Array_idxOf___redArg___lam__0(v_inst_3114_, v_a_3115_, v_x_3116_);
v_r_3118_ = lean_box(v_res_3117_);
return v_r_3118_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg(lean_object* v_inst_3119_, lean_object* v_a_3120_, lean_object* v_as_3121_){
_start:
{
lean_object* v___f_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___f_3122_ = lean_alloc_closure((void*)(l_Array_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3122_, 0, v_inst_3119_);
lean_closure_set(v___f_3122_, 1, v_a_3120_);
v___x_3123_ = lean_unsigned_to_nat(0u);
v___x_3124_ = l_Array_findIdx_x3f_loop___redArg(v___f_3122_, v_as_3121_, v___x_3123_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v___x_3125_; 
v___x_3125_ = lean_array_get_size(v_as_3121_);
return v___x_3125_;
}
else
{
lean_object* v_val_3126_; 
v_val_3126_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_val_3126_);
lean_dec_ref_known(v___x_3124_, 1);
return v_val_3126_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___boxed(lean_object* v_inst_3127_, lean_object* v_a_3128_, lean_object* v_as_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Array_idxOf___redArg(v_inst_3127_, v_a_3128_, v_as_3129_);
lean_dec_ref(v_as_3129_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf(lean_object* v_00_u03b1_3131_, lean_object* v_inst_3132_, lean_object* v_a_3133_, lean_object* v_as_3134_){
_start:
{
lean_object* v___x_3135_; 
v___x_3135_ = l_Array_idxOf___redArg(v_inst_3132_, v_a_3133_, v_as_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___boxed(lean_object* v_00_u03b1_3136_, lean_object* v_inst_3137_, lean_object* v_a_3138_, lean_object* v_as_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Array_idxOf(v_00_u03b1_3136_, v_inst_3137_, v_a_3138_, v_as_3139_);
lean_dec_ref(v_as_3139_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg(lean_object* v_inst_3141_, lean_object* v_xs_3142_, lean_object* v_v_3143_){
_start:
{
lean_object* v___x_3144_; 
v___x_3144_ = l_Array_finIdxOf_x3f___redArg(v_inst_3141_, v_xs_3142_, v_v_3143_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v___x_3145_; 
v___x_3145_ = lean_box(0);
return v___x_3145_;
}
else
{
lean_object* v_val_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
v_val_3146_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3144_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_val_3146_);
lean_dec(v___x_3144_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_val_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg___boxed(lean_object* v_inst_3154_, lean_object* v_xs_3155_, lean_object* v_v_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_Array_idxOf_x3f___redArg(v_inst_3154_, v_xs_3155_, v_v_3156_);
lean_dec_ref(v_xs_3155_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f(lean_object* v_00_u03b1_3158_, lean_object* v_inst_3159_, lean_object* v_xs_3160_, lean_object* v_v_3161_){
_start:
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Array_idxOf_x3f___redArg(v_inst_3159_, v_xs_3160_, v_v_3161_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___boxed(lean_object* v_00_u03b1_3163_, lean_object* v_inst_3164_, lean_object* v_xs_3165_, lean_object* v_v_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Array_idxOf_x3f(v_00_u03b1_3163_, v_inst_3164_, v_xs_3165_, v_v_3166_);
lean_dec_ref(v_xs_3165_);
return v_res_3167_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg___lam__0(lean_object* v_p_3168_, lean_object* v_x_3169_){
_start:
{
lean_object* v___x_3170_; uint8_t v___x_3171_; 
v___x_3170_ = lean_apply_1(v_p_3168_, v_x_3169_);
v___x_3171_ = lean_unbox(v___x_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___lam__0___boxed(lean_object* v_p_3172_, lean_object* v_x_3173_){
_start:
{
uint8_t v_res_3174_; lean_object* v_r_3175_; 
v_res_3174_ = l_Array_any___redArg___lam__0(v_p_3172_, v_x_3173_);
v_r_3175_ = lean_box(v_res_3174_);
return v_r_3175_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg(lean_object* v_as_3176_, lean_object* v_p_3177_, lean_object* v_start_3178_, lean_object* v_stop_3179_){
_start:
{
lean_object* v___x_3180_; uint8_t v___x_3181_; 
v___x_3180_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3181_ = lean_nat_dec_lt(v_start_3178_, v_stop_3179_);
if (v___x_3181_ == 0)
{
lean_dec(v_stop_3179_);
lean_dec_ref(v_p_3177_);
lean_dec_ref(v_as_3176_);
return v___x_3181_;
}
else
{
lean_object* v___f_3182_; lean_object* v___y_3184_; lean_object* v___x_3190_; uint8_t v___x_3191_; 
v___f_3182_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3182_, 0, v_p_3177_);
v___x_3190_ = lean_array_get_size(v_as_3176_);
v___x_3191_ = lean_nat_dec_le(v_stop_3179_, v___x_3190_);
if (v___x_3191_ == 0)
{
lean_dec(v_stop_3179_);
v___y_3184_ = v___x_3190_;
goto v___jp_3183_;
}
else
{
v___y_3184_ = v_stop_3179_;
goto v___jp_3183_;
}
v___jp_3183_:
{
uint8_t v___x_3185_; 
v___x_3185_ = lean_nat_dec_lt(v_start_3178_, v___y_3184_);
if (v___x_3185_ == 0)
{
lean_dec(v___y_3184_);
lean_dec_ref(v___f_3182_);
lean_dec_ref(v_as_3176_);
return v___x_3185_;
}
else
{
size_t v___x_3186_; size_t v___x_3187_; lean_object* v___x_3188_; uint8_t v___x_3189_; 
v___x_3186_ = lean_usize_of_nat(v_start_3178_);
v___x_3187_ = lean_usize_of_nat(v___y_3184_);
lean_dec(v___y_3184_);
v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3180_, v___f_3182_, v_as_3176_, v___x_3186_, v___x_3187_);
v___x_3189_ = lean_unbox(v___x_3188_);
lean_dec(v___x_3188_);
return v___x_3189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___boxed(lean_object* v_as_3192_, lean_object* v_p_3193_, lean_object* v_start_3194_, lean_object* v_stop_3195_){
_start:
{
uint8_t v_res_3196_; lean_object* v_r_3197_; 
v_res_3196_ = l_Array_any___redArg(v_as_3192_, v_p_3193_, v_start_3194_, v_stop_3195_);
lean_dec(v_start_3194_);
v_r_3197_ = lean_box(v_res_3196_);
return v_r_3197_;
}
}
LEAN_EXPORT uint8_t l_Array_any(lean_object* v_00_u03b1_3198_, lean_object* v_as_3199_, lean_object* v_p_3200_, lean_object* v_start_3201_, lean_object* v_stop_3202_){
_start:
{
lean_object* v___x_3203_; uint8_t v___x_3204_; 
v___x_3203_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3204_ = lean_nat_dec_lt(v_start_3201_, v_stop_3202_);
if (v___x_3204_ == 0)
{
lean_dec(v_stop_3202_);
lean_dec_ref(v_p_3200_);
lean_dec_ref(v_as_3199_);
return v___x_3204_;
}
else
{
lean_object* v___f_3205_; lean_object* v___y_3207_; lean_object* v___x_3213_; uint8_t v___x_3214_; 
v___f_3205_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3205_, 0, v_p_3200_);
v___x_3213_ = lean_array_get_size(v_as_3199_);
v___x_3214_ = lean_nat_dec_le(v_stop_3202_, v___x_3213_);
if (v___x_3214_ == 0)
{
lean_dec(v_stop_3202_);
v___y_3207_ = v___x_3213_;
goto v___jp_3206_;
}
else
{
v___y_3207_ = v_stop_3202_;
goto v___jp_3206_;
}
v___jp_3206_:
{
uint8_t v___x_3208_; 
v___x_3208_ = lean_nat_dec_lt(v_start_3201_, v___y_3207_);
if (v___x_3208_ == 0)
{
lean_dec(v___y_3207_);
lean_dec_ref(v___f_3205_);
lean_dec_ref(v_as_3199_);
return v___x_3208_;
}
else
{
size_t v___x_3209_; size_t v___x_3210_; lean_object* v___x_3211_; uint8_t v___x_3212_; 
v___x_3209_ = lean_usize_of_nat(v_start_3201_);
v___x_3210_ = lean_usize_of_nat(v___y_3207_);
lean_dec(v___y_3207_);
v___x_3211_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3203_, v___f_3205_, v_as_3199_, v___x_3209_, v___x_3210_);
v___x_3212_ = lean_unbox(v___x_3211_);
lean_dec(v___x_3211_);
return v___x_3212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___boxed(lean_object* v_00_u03b1_3215_, lean_object* v_as_3216_, lean_object* v_p_3217_, lean_object* v_start_3218_, lean_object* v_stop_3219_){
_start:
{
uint8_t v_res_3220_; lean_object* v_r_3221_; 
v_res_3220_ = l_Array_any(v_00_u03b1_3215_, v_as_3216_, v_p_3217_, v_start_3218_, v_stop_3219_);
lean_dec(v_start_3218_);
v_r_3221_ = lean_box(v_res_3220_);
return v_r_3221_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg___lam__0(lean_object* v_p_3222_, uint8_t v___x_3223_, lean_object* v_v_3224_){
_start:
{
lean_object* v___x_3225_; uint8_t v___x_3226_; 
v___x_3225_ = lean_apply_1(v_p_3222_, v_v_3224_);
v___x_3226_ = lean_unbox(v___x_3225_);
if (v___x_3226_ == 0)
{
return v___x_3223_;
}
else
{
uint8_t v___x_3227_; 
v___x_3227_ = 0;
return v___x_3227_;
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___lam__0___boxed(lean_object* v_p_3228_, lean_object* v___x_3229_, lean_object* v_v_3230_){
_start:
{
uint8_t v___x_334__boxed_3231_; uint8_t v_res_3232_; lean_object* v_r_3233_; 
v___x_334__boxed_3231_ = lean_unbox(v___x_3229_);
v_res_3232_ = l_Array_all___redArg___lam__0(v_p_3228_, v___x_334__boxed_3231_, v_v_3230_);
v_r_3233_ = lean_box(v_res_3232_);
return v_r_3233_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg(lean_object* v_as_3234_, lean_object* v_p_3235_, lean_object* v_start_3236_, lean_object* v_stop_3237_){
_start:
{
lean_object* v___x_3238_; uint8_t v___x_3239_; 
v___x_3238_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3239_ = lean_nat_dec_lt(v_start_3236_, v_stop_3237_);
if (v___x_3239_ == 0)
{
uint8_t v___x_3240_; 
lean_dec(v_stop_3237_);
lean_dec_ref(v_p_3235_);
lean_dec_ref(v_as_3234_);
v___x_3240_ = 1;
return v___x_3240_;
}
else
{
lean_object* v___x_3241_; lean_object* v___f_3242_; lean_object* v___y_3244_; lean_object* v___x_3251_; uint8_t v___x_3252_; 
v___x_3241_ = lean_box(v___x_3239_);
v___f_3242_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3242_, 0, v_p_3235_);
lean_closure_set(v___f_3242_, 1, v___x_3241_);
v___x_3251_ = lean_array_get_size(v_as_3234_);
v___x_3252_ = lean_nat_dec_le(v_stop_3237_, v___x_3251_);
if (v___x_3252_ == 0)
{
lean_dec(v_stop_3237_);
v___y_3244_ = v___x_3251_;
goto v___jp_3243_;
}
else
{
v___y_3244_ = v_stop_3237_;
goto v___jp_3243_;
}
v___jp_3243_:
{
uint8_t v___x_3245_; 
v___x_3245_ = lean_nat_dec_lt(v_start_3236_, v___y_3244_);
if (v___x_3245_ == 0)
{
lean_dec(v___y_3244_);
lean_dec_ref(v___f_3242_);
lean_dec_ref(v_as_3234_);
return v___x_3239_;
}
else
{
size_t v___x_3246_; size_t v___x_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; 
v___x_3246_ = lean_usize_of_nat(v_start_3236_);
v___x_3247_ = lean_usize_of_nat(v___y_3244_);
lean_dec(v___y_3244_);
v___x_3248_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3238_, v___f_3242_, v_as_3234_, v___x_3246_, v___x_3247_);
v___x_3249_ = lean_unbox(v___x_3248_);
lean_dec(v___x_3248_);
if (v___x_3249_ == 0)
{
return v___x_3245_;
}
else
{
uint8_t v___x_3250_; 
v___x_3250_ = 0;
return v___x_3250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___boxed(lean_object* v_as_3253_, lean_object* v_p_3254_, lean_object* v_start_3255_, lean_object* v_stop_3256_){
_start:
{
uint8_t v_res_3257_; lean_object* v_r_3258_; 
v_res_3257_ = l_Array_all___redArg(v_as_3253_, v_p_3254_, v_start_3255_, v_stop_3256_);
lean_dec(v_start_3255_);
v_r_3258_ = lean_box(v_res_3257_);
return v_r_3258_;
}
}
LEAN_EXPORT uint8_t l_Array_all(lean_object* v_00_u03b1_3259_, lean_object* v_as_3260_, lean_object* v_p_3261_, lean_object* v_start_3262_, lean_object* v_stop_3263_){
_start:
{
lean_object* v___x_3264_; uint8_t v___x_3265_; 
v___x_3264_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3265_ = lean_nat_dec_lt(v_start_3262_, v_stop_3263_);
if (v___x_3265_ == 0)
{
uint8_t v___x_3266_; 
lean_dec(v_stop_3263_);
lean_dec_ref(v_p_3261_);
lean_dec_ref(v_as_3260_);
v___x_3266_ = 1;
return v___x_3266_;
}
else
{
lean_object* v___x_3267_; lean_object* v___f_3268_; lean_object* v___y_3270_; lean_object* v___x_3277_; uint8_t v___x_3278_; 
v___x_3267_ = lean_box(v___x_3265_);
v___f_3268_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3268_, 0, v_p_3261_);
lean_closure_set(v___f_3268_, 1, v___x_3267_);
v___x_3277_ = lean_array_get_size(v_as_3260_);
v___x_3278_ = lean_nat_dec_le(v_stop_3263_, v___x_3277_);
if (v___x_3278_ == 0)
{
lean_dec(v_stop_3263_);
v___y_3270_ = v___x_3277_;
goto v___jp_3269_;
}
else
{
v___y_3270_ = v_stop_3263_;
goto v___jp_3269_;
}
v___jp_3269_:
{
uint8_t v___x_3271_; 
v___x_3271_ = lean_nat_dec_lt(v_start_3262_, v___y_3270_);
if (v___x_3271_ == 0)
{
lean_dec(v___y_3270_);
lean_dec_ref(v___f_3268_);
lean_dec_ref(v_as_3260_);
return v___x_3265_;
}
else
{
size_t v___x_3272_; size_t v___x_3273_; lean_object* v___x_3274_; uint8_t v___x_3275_; 
v___x_3272_ = lean_usize_of_nat(v_start_3262_);
v___x_3273_ = lean_usize_of_nat(v___y_3270_);
lean_dec(v___y_3270_);
v___x_3274_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3264_, v___f_3268_, v_as_3260_, v___x_3272_, v___x_3273_);
v___x_3275_ = lean_unbox(v___x_3274_);
lean_dec(v___x_3274_);
if (v___x_3275_ == 0)
{
return v___x_3271_;
}
else
{
uint8_t v___x_3276_; 
v___x_3276_ = 0;
return v___x_3276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___boxed(lean_object* v_00_u03b1_3279_, lean_object* v_as_3280_, lean_object* v_p_3281_, lean_object* v_start_3282_, lean_object* v_stop_3283_){
_start:
{
uint8_t v_res_3284_; lean_object* v_r_3285_; 
v_res_3284_ = l_Array_all(v_00_u03b1_3279_, v_as_3280_, v_p_3281_, v_start_3282_, v_stop_3283_);
lean_dec(v_start_3282_);
v_r_3285_ = lean_box(v_res_3284_);
return v_r_3285_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg___lam__0(lean_object* v_inst_3286_, lean_object* v_a_3287_, lean_object* v_x_3288_){
_start:
{
lean_object* v___x_3289_; uint8_t v___x_3290_; 
v___x_3289_ = lean_apply_2(v_inst_3286_, v_a_3287_, v_x_3288_);
v___x_3290_ = lean_unbox(v___x_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___lam__0___boxed(lean_object* v_inst_3291_, lean_object* v_a_3292_, lean_object* v_x_3293_){
_start:
{
uint8_t v_res_3294_; lean_object* v_r_3295_; 
v_res_3294_ = l_Array_contains___redArg___lam__0(v_inst_3291_, v_a_3292_, v_x_3293_);
v_r_3295_ = lean_box(v_res_3294_);
return v_r_3295_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg(lean_object* v_inst_3296_, lean_object* v_as_3297_, lean_object* v_a_3298_){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; uint8_t v___x_3302_; 
v___x_3299_ = lean_unsigned_to_nat(0u);
v___x_3300_ = lean_array_get_size(v_as_3297_);
v___x_3301_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3302_ = lean_nat_dec_lt(v___x_3299_, v___x_3300_);
if (v___x_3302_ == 0)
{
lean_dec(v_a_3298_);
lean_dec_ref(v_as_3297_);
lean_dec_ref(v_inst_3296_);
return v___x_3302_;
}
else
{
if (v___x_3302_ == 0)
{
lean_dec(v_a_3298_);
lean_dec_ref(v_as_3297_);
lean_dec_ref(v_inst_3296_);
return v___x_3302_;
}
else
{
lean_object* v___f_3303_; size_t v___x_3304_; size_t v___x_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___f_3303_ = lean_alloc_closure((void*)(l_Array_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3303_, 0, v_inst_3296_);
lean_closure_set(v___f_3303_, 1, v_a_3298_);
v___x_3304_ = ((size_t)0ULL);
v___x_3305_ = lean_usize_of_nat(v___x_3300_);
v___x_3306_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3301_, v___f_3303_, v_as_3297_, v___x_3304_, v___x_3305_);
v___x_3307_ = lean_unbox(v___x_3306_);
lean_dec(v___x_3306_);
return v___x_3307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___boxed(lean_object* v_inst_3308_, lean_object* v_as_3309_, lean_object* v_a_3310_){
_start:
{
uint8_t v_res_3311_; lean_object* v_r_3312_; 
v_res_3311_ = l_Array_contains___redArg(v_inst_3308_, v_as_3309_, v_a_3310_);
v_r_3312_ = lean_box(v_res_3311_);
return v_r_3312_;
}
}
LEAN_EXPORT uint8_t l_Array_contains(lean_object* v_00_u03b1_3313_, lean_object* v_inst_3314_, lean_object* v_as_3315_, lean_object* v_a_3316_){
_start:
{
uint8_t v___x_3317_; 
v___x_3317_ = l_Array_contains___redArg(v_inst_3314_, v_as_3315_, v_a_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___boxed(lean_object* v_00_u03b1_3318_, lean_object* v_inst_3319_, lean_object* v_as_3320_, lean_object* v_a_3321_){
_start:
{
uint8_t v_res_3322_; lean_object* v_r_3323_; 
v_res_3322_ = l_Array_contains(v_00_u03b1_3318_, v_inst_3319_, v_as_3320_, v_a_3321_);
v_r_3323_ = lean_box(v_res_3322_);
return v_r_3323_;
}
}
LEAN_EXPORT uint8_t l_Array_elem___redArg(lean_object* v_inst_3324_, lean_object* v_a_3325_, lean_object* v_as_3326_){
_start:
{
uint8_t v___x_3327_; 
v___x_3327_ = l_Array_contains___redArg(v_inst_3324_, v_as_3326_, v_a_3325_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___redArg___boxed(lean_object* v_inst_3328_, lean_object* v_a_3329_, lean_object* v_as_3330_){
_start:
{
uint8_t v_res_3331_; lean_object* v_r_3332_; 
v_res_3331_ = l_Array_elem___redArg(v_inst_3328_, v_a_3329_, v_as_3330_);
v_r_3332_ = lean_box(v_res_3331_);
return v_r_3332_;
}
}
LEAN_EXPORT uint8_t l_Array_elem(lean_object* v_00_u03b1_3333_, lean_object* v_inst_3334_, lean_object* v_a_3335_, lean_object* v_as_3336_){
_start:
{
uint8_t v___x_3337_; 
v___x_3337_ = l_Array_contains___redArg(v_inst_3334_, v_as_3336_, v_a_3335_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___boxed(lean_object* v_00_u03b1_3338_, lean_object* v_inst_3339_, lean_object* v_a_3340_, lean_object* v_as_3341_){
_start:
{
uint8_t v_res_3342_; lean_object* v_r_3343_; 
v_res_3342_ = l_Array_elem(v_00_u03b1_3338_, v_inst_3339_, v_a_3340_, v_as_3341_);
v_r_3343_ = lean_box(v_res_3342_);
return v_r_3343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(lean_object* v_as_3344_, size_t v_i_3345_, size_t v_stop_3346_, lean_object* v_b_3347_){
_start:
{
uint8_t v___x_3348_; 
v___x_3348_ = lean_usize_dec_eq(v_i_3345_, v_stop_3346_);
if (v___x_3348_ == 0)
{
size_t v___x_3349_; size_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3349_ = ((size_t)1ULL);
v___x_3350_ = lean_usize_sub(v_i_3345_, v___x_3349_);
v___x_3351_ = lean_array_uget_borrowed(v_as_3344_, v___x_3350_);
lean_inc(v___x_3351_);
v___x_3352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
lean_ctor_set(v___x_3352_, 1, v_b_3347_);
v_i_3345_ = v___x_3350_;
v_b_3347_ = v___x_3352_;
goto _start;
}
else
{
return v_b_3347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg___boxed(lean_object* v_as_3354_, lean_object* v_i_3355_, lean_object* v_stop_3356_, lean_object* v_b_3357_){
_start:
{
size_t v_i_boxed_3358_; size_t v_stop_boxed_3359_; lean_object* v_res_3360_; 
v_i_boxed_3358_ = lean_unbox_usize(v_i_3355_);
lean_dec(v_i_3355_);
v_stop_boxed_3359_ = lean_unbox_usize(v_stop_3356_);
lean_dec(v_stop_3356_);
v_res_3360_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3354_, v_i_boxed_3358_, v_stop_boxed_3359_, v_b_3357_);
lean_dec_ref(v_as_3354_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg(lean_object* v_as_3361_){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v___x_3362_ = lean_box(0);
v___x_3363_ = lean_array_get_size(v_as_3361_);
v___x_3364_ = lean_unsigned_to_nat(0u);
v___x_3365_ = lean_nat_dec_lt(v___x_3364_, v___x_3363_);
if (v___x_3365_ == 0)
{
return v___x_3362_;
}
else
{
size_t v___x_3366_; size_t v___x_3367_; lean_object* v___x_3368_; 
v___x_3366_ = lean_usize_of_nat(v___x_3363_);
v___x_3367_ = ((size_t)0ULL);
v___x_3368_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3361_, v___x_3366_, v___x_3367_, v___x_3362_);
return v___x_3368_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg___boxed(lean_object* v_as_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Array_toListImpl___redArg(v_as_3369_);
lean_dec_ref(v_as_3369_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* lean_array_to_list_impl(lean_object* v_00_u03b1_3371_, lean_object* v_as_3372_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Array_toListImpl___redArg(v_as_3372_);
lean_dec_ref(v_as_3372_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(lean_object* v_00_u03b1_3374_, lean_object* v_as_3375_, size_t v_i_3376_, size_t v_stop_3377_, lean_object* v_b_3378_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3375_, v_i_3376_, v_stop_3377_, v_b_3378_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___boxed(lean_object* v_00_u03b1_3380_, lean_object* v_as_3381_, lean_object* v_i_3382_, lean_object* v_stop_3383_, lean_object* v_b_3384_){
_start:
{
size_t v_i_boxed_3385_; size_t v_stop_boxed_3386_; lean_object* v_res_3387_; 
v_i_boxed_3385_ = lean_unbox_usize(v_i_3382_);
lean_dec(v_i_3382_);
v_stop_boxed_3386_ = lean_unbox_usize(v_stop_3383_);
lean_dec(v_stop_3383_);
v_res_3387_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(v_00_u03b1_3380_, v_as_3381_, v_i_boxed_3385_, v_stop_boxed_3386_, v_b_3384_);
lean_dec_ref(v_as_3381_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg___lam__0(lean_object* v_x1_3388_, lean_object* v_x2_3389_){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3390_, 0, v_x1_3388_);
lean_ctor_set(v___x_3390_, 1, v_x2_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg(lean_object* v_as_3392_, lean_object* v_l_3393_){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v___x_3394_ = lean_array_get_size(v_as_3392_);
v___x_3395_ = lean_unsigned_to_nat(0u);
v___x_3396_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3397_ = lean_nat_dec_lt(v___x_3395_, v___x_3394_);
if (v___x_3397_ == 0)
{
lean_dec_ref(v_as_3392_);
return v_l_3393_;
}
else
{
lean_object* v___f_3398_; size_t v___x_3399_; size_t v___x_3400_; lean_object* v___x_3401_; 
v___f_3398_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3399_ = lean_usize_of_nat(v___x_3394_);
v___x_3400_ = ((size_t)0ULL);
v___x_3401_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3396_, v___f_3398_, v_as_3392_, v___x_3399_, v___x_3400_, v_l_3393_);
return v___x_3401_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend(lean_object* v_00_u03b1_3402_, lean_object* v_as_3403_, lean_object* v_l_3404_){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3405_ = lean_array_get_size(v_as_3403_);
v___x_3406_ = lean_unsigned_to_nat(0u);
v___x_3407_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3408_ = lean_nat_dec_lt(v___x_3406_, v___x_3405_);
if (v___x_3408_ == 0)
{
lean_dec_ref(v_as_3403_);
return v_l_3404_;
}
else
{
lean_object* v___f_3409_; size_t v___x_3410_; size_t v___x_3411_; lean_object* v___x_3412_; 
v___f_3409_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3410_ = lean_usize_of_nat(v___x_3405_);
v___x_3411_ = ((size_t)0ULL);
v___x_3412_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3407_, v___f_3409_, v_as_3403_, v___x_3410_, v___x_3411_, v_l_3404_);
return v___x_3412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(lean_object* v_as_3413_, size_t v_i_3414_, size_t v_stop_3415_, lean_object* v_b_3416_){
_start:
{
uint8_t v___x_3417_; 
v___x_3417_ = lean_usize_dec_eq(v_i_3414_, v_stop_3415_);
if (v___x_3417_ == 0)
{
lean_object* v___x_3418_; lean_object* v___x_3419_; size_t v___x_3420_; size_t v___x_3421_; 
v___x_3418_ = lean_array_uget_borrowed(v_as_3413_, v_i_3414_);
lean_inc(v___x_3418_);
v___x_3419_ = lean_array_push(v_b_3416_, v___x_3418_);
v___x_3420_ = ((size_t)1ULL);
v___x_3421_ = lean_usize_add(v_i_3414_, v___x_3420_);
v_i_3414_ = v___x_3421_;
v_b_3416_ = v___x_3419_;
goto _start;
}
else
{
return v_b_3416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg___boxed(lean_object* v_as_3423_, lean_object* v_i_3424_, lean_object* v_stop_3425_, lean_object* v_b_3426_){
_start:
{
size_t v_i_boxed_3427_; size_t v_stop_boxed_3428_; lean_object* v_res_3429_; 
v_i_boxed_3427_ = lean_unbox_usize(v_i_3424_);
lean_dec(v_i_3424_);
v_stop_boxed_3428_ = lean_unbox_usize(v_stop_3425_);
lean_dec(v_stop_3425_);
v_res_3429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3423_, v_i_boxed_3427_, v_stop_boxed_3428_, v_b_3426_);
lean_dec_ref(v_as_3423_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg(lean_object* v_as_3430_, lean_object* v_bs_3431_){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
v___x_3432_ = lean_unsigned_to_nat(0u);
v___x_3433_ = lean_array_get_size(v_bs_3431_);
v___x_3434_ = lean_nat_dec_lt(v___x_3432_, v___x_3433_);
if (v___x_3434_ == 0)
{
return v_as_3430_;
}
else
{
uint8_t v___x_3435_; 
v___x_3435_ = lean_nat_dec_le(v___x_3433_, v___x_3433_);
if (v___x_3435_ == 0)
{
if (v___x_3434_ == 0)
{
return v_as_3430_;
}
else
{
size_t v___x_3436_; size_t v___x_3437_; lean_object* v___x_3438_; 
v___x_3436_ = ((size_t)0ULL);
v___x_3437_ = lean_usize_of_nat(v___x_3433_);
v___x_3438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3431_, v___x_3436_, v___x_3437_, v_as_3430_);
return v___x_3438_;
}
}
else
{
size_t v___x_3439_; size_t v___x_3440_; lean_object* v___x_3441_; 
v___x_3439_ = ((size_t)0ULL);
v___x_3440_ = lean_usize_of_nat(v___x_3433_);
v___x_3441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3431_, v___x_3439_, v___x_3440_, v_as_3430_);
return v___x_3441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg___boxed(lean_object* v_as_3442_, lean_object* v_bs_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Array_append___redArg(v_as_3442_, v_bs_3443_);
lean_dec_ref(v_bs_3443_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Array_append(lean_object* v_00_u03b1_3445_, lean_object* v_as_3446_, lean_object* v_bs_3447_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Array_append___redArg(v_as_3446_, v_bs_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Array_append___boxed(lean_object* v_00_u03b1_3449_, lean_object* v_as_3450_, lean_object* v_bs_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Array_append(v_00_u03b1_3449_, v_as_3450_, v_bs_3451_);
lean_dec_ref(v_bs_3451_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(lean_object* v_00_u03b1_3453_, lean_object* v_as_3454_, size_t v_i_3455_, size_t v_stop_3456_, lean_object* v_b_3457_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3454_, v_i_3455_, v_stop_3456_, v_b_3457_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___boxed(lean_object* v_00_u03b1_3459_, lean_object* v_as_3460_, lean_object* v_i_3461_, lean_object* v_stop_3462_, lean_object* v_b_3463_){
_start:
{
size_t v_i_boxed_3464_; size_t v_stop_boxed_3465_; lean_object* v_res_3466_; 
v_i_boxed_3464_ = lean_unbox_usize(v_i_3461_);
lean_dec(v_i_3461_);
v_stop_boxed_3465_ = lean_unbox_usize(v_stop_3462_);
lean_dec(v_stop_3462_);
v_res_3466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(v_00_u03b1_3459_, v_as_3460_, v_i_boxed_3464_, v_stop_boxed_3465_, v_b_3463_);
lean_dec_ref(v_as_3460_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend(lean_object* v_00_u03b1_3468_){
_start:
{
lean_object* v___x_3469_; 
v___x_3469_ = ((lean_object*)(l_Array_instAppend___closed__0));
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object* v_x_3470_, lean_object* v_x_3471_){
_start:
{
if (lean_obj_tag(v_x_3471_) == 0)
{
return v_x_3470_;
}
else
{
lean_object* v_head_3472_; lean_object* v_tail_3473_; lean_object* v___x_3474_; 
v_head_3472_ = lean_ctor_get(v_x_3471_, 0);
lean_inc(v_head_3472_);
v_tail_3473_ = lean_ctor_get(v_x_3471_, 1);
lean_inc(v_tail_3473_);
lean_dec_ref_known(v_x_3471_, 2);
v___x_3474_ = lean_array_push(v_x_3470_, v_head_3472_);
v_x_3470_ = v___x_3474_;
v_x_3471_ = v_tail_3473_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_appendList___redArg(lean_object* v_as_3476_, lean_object* v_bs_3477_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3476_, v_bs_3477_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Array_appendList(lean_object* v_00_u03b1_3479_, lean_object* v_as_3480_, lean_object* v_bs_3481_){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3480_, v_bs_3481_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0(lean_object* v_00_u03b1_3483_, lean_object* v_x_3484_, lean_object* v_x_3485_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_3484_, v_x_3485_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList(lean_object* v_00_u03b1_3488_){
_start:
{
lean_object* v___x_3489_; 
v___x_3489_ = ((lean_object*)(l_Array_instHAppendList___closed__0));
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0(lean_object* v_bs_3490_, lean_object* v_toPure_3491_, lean_object* v_____do__lift_3492_){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3493_ = l_Array_append___redArg(v_bs_3490_, v_____do__lift_3492_);
v___x_3494_ = lean_apply_2(v_toPure_3491_, lean_box(0), v___x_3493_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0___boxed(lean_object* v_bs_3495_, lean_object* v_toPure_3496_, lean_object* v_____do__lift_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Array_flatMapM___redArg___lam__0(v_bs_3495_, v_toPure_3496_, v_____do__lift_3497_);
lean_dec_ref(v_____do__lift_3497_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__1(lean_object* v_toPure_3499_, lean_object* v_f_3500_, lean_object* v_toBind_3501_, lean_object* v_bs_3502_, lean_object* v_a_3503_){
_start:
{
lean_object* v___f_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___f_3504_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3504_, 0, v_bs_3502_);
lean_closure_set(v___f_3504_, 1, v_toPure_3499_);
v___x_3505_ = lean_apply_1(v_f_3500_, v_a_3503_);
v___x_3506_ = lean_apply_4(v_toBind_3501_, lean_box(0), lean_box(0), v___x_3505_, v___f_3504_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg(lean_object* v_inst_3507_, lean_object* v_f_3508_, lean_object* v_as_3509_){
_start:
{
lean_object* v_toApplicative_3510_; lean_object* v_toBind_3511_; lean_object* v_toPure_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; 
v_toApplicative_3510_ = lean_ctor_get(v_inst_3507_, 0);
v_toBind_3511_ = lean_ctor_get(v_inst_3507_, 1);
v_toPure_3512_ = lean_ctor_get(v_toApplicative_3510_, 1);
v___x_3513_ = lean_unsigned_to_nat(0u);
v___x_3514_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3515_ = lean_array_get_size(v_as_3509_);
v___x_3516_ = lean_nat_dec_lt(v___x_3513_, v___x_3515_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
lean_inc(v_toPure_3512_);
lean_dec_ref(v_as_3509_);
lean_dec(v_f_3508_);
lean_dec_ref(v_inst_3507_);
v___x_3517_ = lean_apply_2(v_toPure_3512_, lean_box(0), v___x_3514_);
return v___x_3517_;
}
else
{
lean_object* v___f_3518_; uint8_t v___x_3519_; 
lean_inc(v_toBind_3511_);
lean_inc(v_toPure_3512_);
v___f_3518_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3518_, 0, v_toPure_3512_);
lean_closure_set(v___f_3518_, 1, v_f_3508_);
lean_closure_set(v___f_3518_, 2, v_toBind_3511_);
v___x_3519_ = lean_nat_dec_le(v___x_3515_, v___x_3515_);
if (v___x_3519_ == 0)
{
if (v___x_3516_ == 0)
{
lean_object* v___x_3520_; 
lean_inc(v_toPure_3512_);
lean_dec_ref(v___f_3518_);
lean_dec_ref(v_as_3509_);
lean_dec_ref(v_inst_3507_);
v___x_3520_ = lean_apply_2(v_toPure_3512_, lean_box(0), v___x_3514_);
return v___x_3520_;
}
else
{
size_t v___x_3521_; size_t v___x_3522_; lean_object* v___x_3523_; 
v___x_3521_ = ((size_t)0ULL);
v___x_3522_ = lean_usize_of_nat(v___x_3515_);
v___x_3523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3507_, v___f_3518_, v_as_3509_, v___x_3521_, v___x_3522_, v___x_3514_);
return v___x_3523_;
}
}
else
{
size_t v___x_3524_; size_t v___x_3525_; lean_object* v___x_3526_; 
v___x_3524_ = ((size_t)0ULL);
v___x_3525_ = lean_usize_of_nat(v___x_3515_);
v___x_3526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3507_, v___f_3518_, v_as_3509_, v___x_3524_, v___x_3525_, v___x_3514_);
return v___x_3526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM(lean_object* v_00_u03b1_3527_, lean_object* v_m_3528_, lean_object* v_00_u03b2_3529_, lean_object* v_inst_3530_, lean_object* v_f_3531_, lean_object* v_as_3532_){
_start:
{
lean_object* v_toApplicative_3533_; lean_object* v_toBind_3534_; lean_object* v_toPure_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
v_toApplicative_3533_ = lean_ctor_get(v_inst_3530_, 0);
v_toBind_3534_ = lean_ctor_get(v_inst_3530_, 1);
v_toPure_3535_ = lean_ctor_get(v_toApplicative_3533_, 1);
v___x_3536_ = lean_unsigned_to_nat(0u);
v___x_3537_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3538_ = lean_array_get_size(v_as_3532_);
v___x_3539_ = lean_nat_dec_lt(v___x_3536_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3540_; 
lean_inc(v_toPure_3535_);
lean_dec_ref(v_as_3532_);
lean_dec(v_f_3531_);
lean_dec_ref(v_inst_3530_);
v___x_3540_ = lean_apply_2(v_toPure_3535_, lean_box(0), v___x_3537_);
return v___x_3540_;
}
else
{
lean_object* v___f_3541_; uint8_t v___x_3542_; 
lean_inc(v_toBind_3534_);
lean_inc(v_toPure_3535_);
v___f_3541_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3541_, 0, v_toPure_3535_);
lean_closure_set(v___f_3541_, 1, v_f_3531_);
lean_closure_set(v___f_3541_, 2, v_toBind_3534_);
v___x_3542_ = lean_nat_dec_le(v___x_3538_, v___x_3538_);
if (v___x_3542_ == 0)
{
if (v___x_3539_ == 0)
{
lean_object* v___x_3543_; 
lean_inc(v_toPure_3535_);
lean_dec_ref(v___f_3541_);
lean_dec_ref(v_as_3532_);
lean_dec_ref(v_inst_3530_);
v___x_3543_ = lean_apply_2(v_toPure_3535_, lean_box(0), v___x_3537_);
return v___x_3543_;
}
else
{
size_t v___x_3544_; size_t v___x_3545_; lean_object* v___x_3546_; 
v___x_3544_ = ((size_t)0ULL);
v___x_3545_ = lean_usize_of_nat(v___x_3538_);
v___x_3546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3530_, v___f_3541_, v_as_3532_, v___x_3544_, v___x_3545_, v___x_3537_);
return v___x_3546_;
}
}
else
{
size_t v___x_3547_; size_t v___x_3548_; lean_object* v___x_3549_; 
v___x_3547_ = ((size_t)0ULL);
v___x_3548_ = lean_usize_of_nat(v___x_3538_);
v___x_3549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3530_, v___f_3541_, v_as_3532_, v___x_3547_, v___x_3548_, v___x_3537_);
return v___x_3549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg___lam__0(lean_object* v_f_3550_, lean_object* v_x1_3551_, lean_object* v_x2_3552_){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = lean_apply_1(v_f_3550_, v_x2_3552_);
v___x_3554_ = l_Array_append___redArg(v_x1_3551_, v___x_3553_);
lean_dec_ref(v___x_3553_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg(lean_object* v_f_3555_, lean_object* v_as_3556_){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; uint8_t v___x_3561_; 
v___x_3557_ = lean_unsigned_to_nat(0u);
v___x_3558_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3559_ = lean_array_get_size(v_as_3556_);
v___x_3560_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3561_ = lean_nat_dec_lt(v___x_3557_, v___x_3559_);
if (v___x_3561_ == 0)
{
lean_dec_ref(v_as_3556_);
lean_dec_ref(v_f_3555_);
return v___x_3558_;
}
else
{
lean_object* v___f_3562_; uint8_t v___x_3563_; 
v___f_3562_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3562_, 0, v_f_3555_);
v___x_3563_ = lean_nat_dec_le(v___x_3559_, v___x_3559_);
if (v___x_3563_ == 0)
{
if (v___x_3561_ == 0)
{
lean_dec_ref(v___f_3562_);
lean_dec_ref(v_as_3556_);
return v___x_3558_;
}
else
{
size_t v___x_3564_; size_t v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = ((size_t)0ULL);
v___x_3565_ = lean_usize_of_nat(v___x_3559_);
v___x_3566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3560_, v___f_3562_, v_as_3556_, v___x_3564_, v___x_3565_, v___x_3558_);
return v___x_3566_;
}
}
else
{
size_t v___x_3567_; size_t v___x_3568_; lean_object* v___x_3569_; 
v___x_3567_ = ((size_t)0ULL);
v___x_3568_ = lean_usize_of_nat(v___x_3559_);
v___x_3569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3560_, v___f_3562_, v_as_3556_, v___x_3567_, v___x_3568_, v___x_3558_);
return v___x_3569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap(lean_object* v_00_u03b1_3570_, lean_object* v_00_u03b2_3571_, lean_object* v_f_3572_, lean_object* v_as_3573_){
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
LEAN_EXPORT lean_object* l_Array_flatten___redArg(lean_object* v_xss_3588_){
_start:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; uint8_t v___x_3593_; 
v___x_3589_ = lean_unsigned_to_nat(0u);
v___x_3590_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3591_ = lean_array_get_size(v_xss_3588_);
v___x_3592_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3593_ = lean_nat_dec_lt(v___x_3589_, v___x_3591_);
if (v___x_3593_ == 0)
{
lean_dec_ref(v_xss_3588_);
return v___x_3590_;
}
else
{
lean_object* v___f_3594_; uint8_t v___x_3595_; 
v___f_3594_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3595_ = lean_nat_dec_le(v___x_3591_, v___x_3591_);
if (v___x_3595_ == 0)
{
if (v___x_3593_ == 0)
{
lean_dec_ref(v_xss_3588_);
return v___x_3590_;
}
else
{
size_t v___x_3596_; size_t v___x_3597_; lean_object* v___x_3598_; 
v___x_3596_ = ((size_t)0ULL);
v___x_3597_ = lean_usize_of_nat(v___x_3591_);
v___x_3598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3592_, v___f_3594_, v_xss_3588_, v___x_3596_, v___x_3597_, v___x_3590_);
return v___x_3598_;
}
}
else
{
size_t v___x_3599_; size_t v___x_3600_; lean_object* v___x_3601_; 
v___x_3599_ = ((size_t)0ULL);
v___x_3600_ = lean_usize_of_nat(v___x_3591_);
v___x_3601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3592_, v___f_3594_, v_xss_3588_, v___x_3599_, v___x_3600_, v___x_3590_);
return v___x_3601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten(lean_object* v_00_u03b1_3602_, lean_object* v_xss_3603_){
_start:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; 
v___x_3604_ = lean_unsigned_to_nat(0u);
v___x_3605_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3606_ = lean_array_get_size(v_xss_3603_);
v___x_3607_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3608_ = lean_nat_dec_lt(v___x_3604_, v___x_3606_);
if (v___x_3608_ == 0)
{
lean_dec_ref(v_xss_3603_);
return v___x_3605_;
}
else
{
lean_object* v___f_3609_; uint8_t v___x_3610_; 
v___f_3609_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3610_ = lean_nat_dec_le(v___x_3606_, v___x_3606_);
if (v___x_3610_ == 0)
{
if (v___x_3608_ == 0)
{
lean_dec_ref(v_xss_3603_);
return v___x_3605_;
}
else
{
size_t v___x_3611_; size_t v___x_3612_; lean_object* v___x_3613_; 
v___x_3611_ = ((size_t)0ULL);
v___x_3612_ = lean_usize_of_nat(v___x_3606_);
v___x_3613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3607_, v___f_3609_, v_xss_3603_, v___x_3611_, v___x_3612_, v___x_3605_);
return v___x_3613_;
}
}
else
{
size_t v___x_3614_; size_t v___x_3615_; lean_object* v___x_3616_; 
v___x_3614_ = ((size_t)0ULL);
v___x_3615_ = lean_usize_of_nat(v___x_3606_);
v___x_3616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3607_, v___f_3609_, v_xss_3603_, v___x_3614_, v___x_3615_, v___x_3605_);
return v___x_3616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop___redArg(lean_object* v_as_3617_, lean_object* v_i_3618_, lean_object* v_j_3619_){
_start:
{
uint8_t v___x_3620_; 
v___x_3620_ = lean_nat_dec_lt(v_i_3618_, v_j_3619_);
if (v___x_3620_ == 0)
{
lean_dec(v_j_3619_);
lean_dec(v_i_3618_);
return v_as_3617_;
}
else
{
lean_object* v_as_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v_as_3621_ = lean_array_fswap(v_as_3617_, v_i_3618_, v_j_3619_);
v___x_3622_ = lean_unsigned_to_nat(1u);
v___x_3623_ = lean_nat_add(v_i_3618_, v___x_3622_);
lean_dec(v_i_3618_);
v___x_3624_ = lean_nat_sub(v_j_3619_, v___x_3622_);
lean_dec(v_j_3619_);
v_as_3617_ = v_as_3621_;
v_i_3618_ = v___x_3623_;
v_j_3619_ = v___x_3624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop(lean_object* v_00_u03b1_3626_, lean_object* v_as_3627_, lean_object* v_i_3628_, lean_object* v_j_3629_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l_Array_reverse_loop___redArg(v_as_3627_, v_i_3628_, v_j_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Array_reverse___redArg(lean_object* v_as_3631_){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; uint8_t v___x_3634_; 
v___x_3632_ = lean_array_get_size(v_as_3631_);
v___x_3633_ = lean_unsigned_to_nat(1u);
v___x_3634_ = lean_nat_dec_le(v___x_3632_, v___x_3633_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3635_ = lean_unsigned_to_nat(0u);
v___x_3636_ = lean_nat_sub(v___x_3632_, v___x_3633_);
v___x_3637_ = l_Array_reverse_loop___redArg(v_as_3631_, v___x_3635_, v___x_3636_);
return v___x_3637_;
}
else
{
return v_as_3631_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse(lean_object* v_00_u03b1_3638_, lean_object* v_as_3639_){
_start:
{
lean_object* v___x_3640_; 
v___x_3640_ = l_Array_reverse___redArg(v_as_3639_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___lam__0(lean_object* v_p_3641_, lean_object* v_x1_3642_, lean_object* v_x2_3643_){
_start:
{
lean_object* v___x_3644_; uint8_t v___x_3645_; 
lean_inc(v_x2_3643_);
v___x_3644_ = lean_apply_1(v_p_3641_, v_x2_3643_);
v___x_3645_ = lean_unbox(v___x_3644_);
if (v___x_3645_ == 0)
{
lean_dec(v_x2_3643_);
return v_x1_3642_;
}
else
{
lean_object* v___x_3646_; 
v___x_3646_ = lean_array_push(v_x1_3642_, v_x2_3643_);
return v___x_3646_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg(lean_object* v_p_3649_, lean_object* v_as_3650_, lean_object* v_start_3651_, lean_object* v_stop_3652_){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; uint8_t v___x_3655_; 
v___x_3653_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3654_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3655_ = lean_nat_dec_lt(v_start_3651_, v_stop_3652_);
if (v___x_3655_ == 0)
{
lean_dec_ref(v_as_3650_);
lean_dec_ref(v_p_3649_);
return v___x_3653_;
}
else
{
lean_object* v___f_3656_; lean_object* v___x_3657_; uint8_t v___x_3658_; 
v___f_3656_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3656_, 0, v_p_3649_);
v___x_3657_ = lean_array_get_size(v_as_3650_);
v___x_3658_ = lean_nat_dec_le(v_stop_3652_, v___x_3657_);
if (v___x_3658_ == 0)
{
uint8_t v___x_3659_; 
v___x_3659_ = lean_nat_dec_lt(v_start_3651_, v___x_3657_);
if (v___x_3659_ == 0)
{
lean_dec_ref(v___f_3656_);
lean_dec_ref(v_as_3650_);
return v___x_3653_;
}
else
{
size_t v___x_3660_; size_t v___x_3661_; lean_object* v___x_3662_; 
v___x_3660_ = lean_usize_of_nat(v_start_3651_);
v___x_3661_ = lean_usize_of_nat(v___x_3657_);
v___x_3662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3654_, v___f_3656_, v_as_3650_, v___x_3660_, v___x_3661_, v___x_3653_);
return v___x_3662_;
}
}
else
{
size_t v___x_3663_; size_t v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = lean_usize_of_nat(v_start_3651_);
v___x_3664_ = lean_usize_of_nat(v_stop_3652_);
v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3654_, v___f_3656_, v_as_3650_, v___x_3663_, v___x_3664_, v___x_3653_);
return v___x_3665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___boxed(lean_object* v_p_3666_, lean_object* v_as_3667_, lean_object* v_start_3668_, lean_object* v_stop_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l_Array_filter___redArg(v_p_3666_, v_as_3667_, v_start_3668_, v_stop_3669_);
lean_dec(v_stop_3669_);
lean_dec(v_start_3668_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l_Array_filter(lean_object* v_00_u03b1_3671_, lean_object* v_p_3672_, lean_object* v_as_3673_, lean_object* v_start_3674_, lean_object* v_stop_3675_){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; uint8_t v___x_3678_; 
v___x_3676_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3677_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3678_ = lean_nat_dec_lt(v_start_3674_, v_stop_3675_);
if (v___x_3678_ == 0)
{
lean_dec_ref(v_as_3673_);
lean_dec_ref(v_p_3672_);
return v___x_3676_;
}
else
{
lean_object* v___f_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; 
v___f_3679_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3679_, 0, v_p_3672_);
v___x_3680_ = lean_array_get_size(v_as_3673_);
v___x_3681_ = lean_nat_dec_le(v_stop_3675_, v___x_3680_);
if (v___x_3681_ == 0)
{
uint8_t v___x_3682_; 
v___x_3682_ = lean_nat_dec_lt(v_start_3674_, v___x_3680_);
if (v___x_3682_ == 0)
{
lean_dec_ref(v___f_3679_);
lean_dec_ref(v_as_3673_);
return v___x_3676_;
}
else
{
size_t v___x_3683_; size_t v___x_3684_; lean_object* v___x_3685_; 
v___x_3683_ = lean_usize_of_nat(v_start_3674_);
v___x_3684_ = lean_usize_of_nat(v___x_3680_);
v___x_3685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3677_, v___f_3679_, v_as_3673_, v___x_3683_, v___x_3684_, v___x_3676_);
return v___x_3685_;
}
}
else
{
size_t v___x_3686_; size_t v___x_3687_; lean_object* v___x_3688_; 
v___x_3686_ = lean_usize_of_nat(v_start_3674_);
v___x_3687_ = lean_usize_of_nat(v_stop_3675_);
v___x_3688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3677_, v___f_3679_, v_as_3673_, v___x_3686_, v___x_3687_, v___x_3676_);
return v___x_3688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___boxed(lean_object* v_00_u03b1_3689_, lean_object* v_p_3690_, lean_object* v_as_3691_, lean_object* v_start_3692_, lean_object* v_stop_3693_){
_start:
{
lean_object* v_res_3694_; 
v_res_3694_ = l_Array_filter(v_00_u03b1_3689_, v_p_3690_, v_as_3691_, v_start_3692_, v_stop_3693_);
lean_dec(v_stop_3693_);
lean_dec(v_start_3692_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0(lean_object* v_toPure_3695_, lean_object* v_acc_3696_, lean_object* v_a_3697_, uint8_t v_____do__lift_3698_){
_start:
{
if (v_____do__lift_3698_ == 0)
{
lean_object* v___x_3699_; 
lean_dec(v_a_3697_);
v___x_3699_ = lean_apply_2(v_toPure_3695_, lean_box(0), v_acc_3696_);
return v___x_3699_;
}
else
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3700_ = lean_array_push(v_acc_3696_, v_a_3697_);
v___x_3701_ = lean_apply_2(v_toPure_3695_, lean_box(0), v___x_3700_);
return v___x_3701_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0___boxed(lean_object* v_toPure_3702_, lean_object* v_acc_3703_, lean_object* v_a_3704_, lean_object* v_____do__lift_3705_){
_start:
{
uint8_t v_____do__lift_89__boxed_3706_; lean_object* v_res_3707_; 
v_____do__lift_89__boxed_3706_ = lean_unbox(v_____do__lift_3705_);
v_res_3707_ = l_Array_filterM___redArg___lam__0(v_toPure_3702_, v_acc_3703_, v_a_3704_, v_____do__lift_89__boxed_3706_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__1(lean_object* v_toPure_3708_, lean_object* v_p_3709_, lean_object* v_toBind_3710_, lean_object* v_acc_3711_, lean_object* v_a_3712_){
_start:
{
lean_object* v___f_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
lean_inc(v_a_3712_);
v___f_3713_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3713_, 0, v_toPure_3708_);
lean_closure_set(v___f_3713_, 1, v_acc_3711_);
lean_closure_set(v___f_3713_, 2, v_a_3712_);
v___x_3714_ = lean_apply_1(v_p_3709_, v_a_3712_);
v___x_3715_ = lean_apply_4(v_toBind_3710_, lean_box(0), lean_box(0), v___x_3714_, v___f_3713_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg(lean_object* v_inst_3716_, lean_object* v_p_3717_, lean_object* v_as_3718_, lean_object* v_start_3719_, lean_object* v_stop_3720_){
_start:
{
lean_object* v_toApplicative_3721_; lean_object* v_toBind_3722_; lean_object* v_toPure_3723_; lean_object* v___x_3724_; uint8_t v___x_3725_; 
v_toApplicative_3721_ = lean_ctor_get(v_inst_3716_, 0);
v_toBind_3722_ = lean_ctor_get(v_inst_3716_, 1);
v_toPure_3723_ = lean_ctor_get(v_toApplicative_3721_, 1);
v___x_3724_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3725_ = lean_nat_dec_lt(v_start_3719_, v_stop_3720_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; 
lean_inc(v_toPure_3723_);
lean_dec_ref(v_as_3718_);
lean_dec(v_p_3717_);
lean_dec_ref(v_inst_3716_);
v___x_3726_ = lean_apply_2(v_toPure_3723_, lean_box(0), v___x_3724_);
return v___x_3726_;
}
else
{
lean_object* v___f_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; 
lean_inc(v_toBind_3722_);
lean_inc(v_toPure_3723_);
v___f_3727_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3727_, 0, v_toPure_3723_);
lean_closure_set(v___f_3727_, 1, v_p_3717_);
lean_closure_set(v___f_3727_, 2, v_toBind_3722_);
v___x_3728_ = lean_array_get_size(v_as_3718_);
v___x_3729_ = lean_nat_dec_le(v_stop_3720_, v___x_3728_);
if (v___x_3729_ == 0)
{
uint8_t v___x_3730_; 
v___x_3730_ = lean_nat_dec_lt(v_start_3719_, v___x_3728_);
if (v___x_3730_ == 0)
{
lean_object* v___x_3731_; 
lean_inc(v_toPure_3723_);
lean_dec_ref(v___f_3727_);
lean_dec_ref(v_as_3718_);
lean_dec_ref(v_inst_3716_);
v___x_3731_ = lean_apply_2(v_toPure_3723_, lean_box(0), v___x_3724_);
return v___x_3731_;
}
else
{
size_t v___x_3732_; size_t v___x_3733_; lean_object* v___x_3734_; 
v___x_3732_ = lean_usize_of_nat(v_start_3719_);
v___x_3733_ = lean_usize_of_nat(v___x_3728_);
v___x_3734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3716_, v___f_3727_, v_as_3718_, v___x_3732_, v___x_3733_, v___x_3724_);
return v___x_3734_;
}
}
else
{
size_t v___x_3735_; size_t v___x_3736_; lean_object* v___x_3737_; 
v___x_3735_ = lean_usize_of_nat(v_start_3719_);
v___x_3736_ = lean_usize_of_nat(v_stop_3720_);
v___x_3737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3716_, v___f_3727_, v_as_3718_, v___x_3735_, v___x_3736_, v___x_3724_);
return v___x_3737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___boxed(lean_object* v_inst_3738_, lean_object* v_p_3739_, lean_object* v_as_3740_, lean_object* v_start_3741_, lean_object* v_stop_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Array_filterM___redArg(v_inst_3738_, v_p_3739_, v_as_3740_, v_start_3741_, v_stop_3742_);
lean_dec(v_stop_3742_);
lean_dec(v_start_3741_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM(lean_object* v_m_3744_, lean_object* v_00_u03b1_3745_, lean_object* v_inst_3746_, lean_object* v_p_3747_, lean_object* v_as_3748_, lean_object* v_start_3749_, lean_object* v_stop_3750_){
_start:
{
lean_object* v_toApplicative_3751_; lean_object* v_toBind_3752_; lean_object* v_toPure_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
v_toApplicative_3751_ = lean_ctor_get(v_inst_3746_, 0);
v_toBind_3752_ = lean_ctor_get(v_inst_3746_, 1);
v_toPure_3753_ = lean_ctor_get(v_toApplicative_3751_, 1);
v___x_3754_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3755_ = lean_nat_dec_lt(v_start_3749_, v_stop_3750_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; 
lean_inc(v_toPure_3753_);
lean_dec_ref(v_as_3748_);
lean_dec(v_p_3747_);
lean_dec_ref(v_inst_3746_);
v___x_3756_ = lean_apply_2(v_toPure_3753_, lean_box(0), v___x_3754_);
return v___x_3756_;
}
else
{
lean_object* v___f_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
lean_inc(v_toBind_3752_);
lean_inc(v_toPure_3753_);
v___f_3757_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3757_, 0, v_toPure_3753_);
lean_closure_set(v___f_3757_, 1, v_p_3747_);
lean_closure_set(v___f_3757_, 2, v_toBind_3752_);
v___x_3758_ = lean_array_get_size(v_as_3748_);
v___x_3759_ = lean_nat_dec_le(v_stop_3750_, v___x_3758_);
if (v___x_3759_ == 0)
{
uint8_t v___x_3760_; 
v___x_3760_ = lean_nat_dec_lt(v_start_3749_, v___x_3758_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3761_; 
lean_inc(v_toPure_3753_);
lean_dec_ref(v___f_3757_);
lean_dec_ref(v_as_3748_);
lean_dec_ref(v_inst_3746_);
v___x_3761_ = lean_apply_2(v_toPure_3753_, lean_box(0), v___x_3754_);
return v___x_3761_;
}
else
{
size_t v___x_3762_; size_t v___x_3763_; lean_object* v___x_3764_; 
v___x_3762_ = lean_usize_of_nat(v_start_3749_);
v___x_3763_ = lean_usize_of_nat(v___x_3758_);
v___x_3764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3746_, v___f_3757_, v_as_3748_, v___x_3762_, v___x_3763_, v___x_3754_);
return v___x_3764_;
}
}
else
{
size_t v___x_3765_; size_t v___x_3766_; lean_object* v___x_3767_; 
v___x_3765_ = lean_usize_of_nat(v_start_3749_);
v___x_3766_ = lean_usize_of_nat(v_stop_3750_);
v___x_3767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3746_, v___f_3757_, v_as_3748_, v___x_3765_, v___x_3766_, v___x_3754_);
return v___x_3767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___boxed(lean_object* v_m_3768_, lean_object* v_00_u03b1_3769_, lean_object* v_inst_3770_, lean_object* v_p_3771_, lean_object* v_as_3772_, lean_object* v_start_3773_, lean_object* v_stop_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Array_filterM(v_m_3768_, v_00_u03b1_3769_, v_inst_3770_, v_p_3771_, v_as_3772_, v_start_3773_, v_stop_3774_);
lean_dec(v_stop_3774_);
lean_dec(v_start_3773_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__1(lean_object* v_toPure_3776_, lean_object* v_p_3777_, lean_object* v_toBind_3778_, lean_object* v_a_3779_, lean_object* v_acc_3780_){
_start:
{
lean_object* v___f_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
lean_inc(v_a_3779_);
v___f_3781_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3781_, 0, v_toPure_3776_);
lean_closure_set(v___f_3781_, 1, v_acc_3780_);
lean_closure_set(v___f_3781_, 2, v_a_3779_);
v___x_3782_ = lean_apply_1(v_p_3777_, v_a_3779_);
v___x_3783_ = lean_apply_4(v_toBind_3778_, lean_box(0), lean_box(0), v___x_3782_, v___f_3781_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg(lean_object* v_inst_3785_, lean_object* v_p_3786_, lean_object* v_as_3787_, lean_object* v_start_3788_, lean_object* v_stop_3789_){
_start:
{
lean_object* v_toApplicative_3790_; lean_object* v_toFunctor_3791_; lean_object* v_toBind_3792_; lean_object* v_toPure_3793_; lean_object* v_map_3794_; lean_object* v___f_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; uint8_t v___x_3799_; 
v_toApplicative_3790_ = lean_ctor_get(v_inst_3785_, 0);
v_toFunctor_3791_ = lean_ctor_get(v_toApplicative_3790_, 0);
v_toBind_3792_ = lean_ctor_get(v_inst_3785_, 1);
v_toPure_3793_ = lean_ctor_get(v_toApplicative_3790_, 1);
v_map_3794_ = lean_ctor_get(v_toFunctor_3791_, 0);
lean_inc(v_map_3794_);
lean_inc(v_toBind_3792_);
lean_inc(v_toPure_3793_);
v___f_3795_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3795_, 0, v_toPure_3793_);
lean_closure_set(v___f_3795_, 1, v_p_3786_);
lean_closure_set(v___f_3795_, 2, v_toBind_3792_);
v___x_3796_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3797_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3798_ = lean_array_get_size(v_as_3787_);
v___x_3799_ = lean_nat_dec_le(v_start_3788_, v___x_3798_);
if (v___x_3799_ == 0)
{
uint8_t v___x_3800_; 
v___x_3800_ = lean_nat_dec_lt(v_stop_3789_, v___x_3798_);
if (v___x_3800_ == 0)
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
lean_inc(v_toPure_3793_);
lean_dec_ref(v___f_3795_);
lean_dec_ref(v_as_3787_);
lean_dec_ref(v_inst_3785_);
v___x_3801_ = lean_apply_2(v_toPure_3793_, lean_box(0), v___x_3797_);
v___x_3802_ = lean_apply_4(v_map_3794_, lean_box(0), lean_box(0), v___x_3796_, v___x_3801_);
return v___x_3802_;
}
else
{
size_t v___x_3803_; size_t v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3803_ = lean_usize_of_nat(v___x_3798_);
v___x_3804_ = lean_usize_of_nat(v_stop_3789_);
v___x_3805_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3785_, v___f_3795_, v_as_3787_, v___x_3803_, v___x_3804_, v___x_3797_);
v___x_3806_ = lean_apply_4(v_map_3794_, lean_box(0), lean_box(0), v___x_3796_, v___x_3805_);
return v___x_3806_;
}
}
else
{
uint8_t v___x_3807_; 
v___x_3807_ = lean_nat_dec_lt(v_stop_3789_, v_start_3788_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
lean_inc(v_toPure_3793_);
lean_dec_ref(v___f_3795_);
lean_dec_ref(v_as_3787_);
lean_dec_ref(v_inst_3785_);
v___x_3808_ = lean_apply_2(v_toPure_3793_, lean_box(0), v___x_3797_);
v___x_3809_ = lean_apply_4(v_map_3794_, lean_box(0), lean_box(0), v___x_3796_, v___x_3808_);
return v___x_3809_;
}
else
{
size_t v___x_3810_; size_t v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3810_ = lean_usize_of_nat(v_start_3788_);
v___x_3811_ = lean_usize_of_nat(v_stop_3789_);
v___x_3812_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3785_, v___f_3795_, v_as_3787_, v___x_3810_, v___x_3811_, v___x_3797_);
v___x_3813_ = lean_apply_4(v_map_3794_, lean_box(0), lean_box(0), v___x_3796_, v___x_3812_);
return v___x_3813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___boxed(lean_object* v_inst_3814_, lean_object* v_p_3815_, lean_object* v_as_3816_, lean_object* v_start_3817_, lean_object* v_stop_3818_){
_start:
{
lean_object* v_res_3819_; 
v_res_3819_ = l_Array_filterRevM___redArg(v_inst_3814_, v_p_3815_, v_as_3816_, v_start_3817_, v_stop_3818_);
lean_dec(v_stop_3818_);
lean_dec(v_start_3817_);
return v_res_3819_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM(lean_object* v_m_3820_, lean_object* v_00_u03b1_3821_, lean_object* v_inst_3822_, lean_object* v_p_3823_, lean_object* v_as_3824_, lean_object* v_start_3825_, lean_object* v_stop_3826_){
_start:
{
lean_object* v_toApplicative_3827_; lean_object* v_toFunctor_3828_; lean_object* v_toBind_3829_; lean_object* v_toPure_3830_; lean_object* v_map_3831_; lean_object* v___f_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; 
v_toApplicative_3827_ = lean_ctor_get(v_inst_3822_, 0);
v_toFunctor_3828_ = lean_ctor_get(v_toApplicative_3827_, 0);
v_toBind_3829_ = lean_ctor_get(v_inst_3822_, 1);
v_toPure_3830_ = lean_ctor_get(v_toApplicative_3827_, 1);
v_map_3831_ = lean_ctor_get(v_toFunctor_3828_, 0);
lean_inc(v_map_3831_);
lean_inc(v_toBind_3829_);
lean_inc(v_toPure_3830_);
v___f_3832_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3832_, 0, v_toPure_3830_);
lean_closure_set(v___f_3832_, 1, v_p_3823_);
lean_closure_set(v___f_3832_, 2, v_toBind_3829_);
v___x_3833_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3834_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3835_ = lean_array_get_size(v_as_3824_);
v___x_3836_ = lean_nat_dec_le(v_start_3825_, v___x_3835_);
if (v___x_3836_ == 0)
{
uint8_t v___x_3837_; 
v___x_3837_ = lean_nat_dec_lt(v_stop_3826_, v___x_3835_);
if (v___x_3837_ == 0)
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
lean_inc(v_toPure_3830_);
lean_dec_ref(v___f_3832_);
lean_dec_ref(v_as_3824_);
lean_dec_ref(v_inst_3822_);
v___x_3838_ = lean_apply_2(v_toPure_3830_, lean_box(0), v___x_3834_);
v___x_3839_ = lean_apply_4(v_map_3831_, lean_box(0), lean_box(0), v___x_3833_, v___x_3838_);
return v___x_3839_;
}
else
{
size_t v___x_3840_; size_t v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3840_ = lean_usize_of_nat(v___x_3835_);
v___x_3841_ = lean_usize_of_nat(v_stop_3826_);
v___x_3842_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3822_, v___f_3832_, v_as_3824_, v___x_3840_, v___x_3841_, v___x_3834_);
v___x_3843_ = lean_apply_4(v_map_3831_, lean_box(0), lean_box(0), v___x_3833_, v___x_3842_);
return v___x_3843_;
}
}
else
{
uint8_t v___x_3844_; 
v___x_3844_ = lean_nat_dec_lt(v_stop_3826_, v_start_3825_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
lean_inc(v_toPure_3830_);
lean_dec_ref(v___f_3832_);
lean_dec_ref(v_as_3824_);
lean_dec_ref(v_inst_3822_);
v___x_3845_ = lean_apply_2(v_toPure_3830_, lean_box(0), v___x_3834_);
v___x_3846_ = lean_apply_4(v_map_3831_, lean_box(0), lean_box(0), v___x_3833_, v___x_3845_);
return v___x_3846_;
}
else
{
size_t v___x_3847_; size_t v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3847_ = lean_usize_of_nat(v_start_3825_);
v___x_3848_ = lean_usize_of_nat(v_stop_3826_);
v___x_3849_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3822_, v___f_3832_, v_as_3824_, v___x_3847_, v___x_3848_, v___x_3834_);
v___x_3850_ = lean_apply_4(v_map_3831_, lean_box(0), lean_box(0), v___x_3833_, v___x_3849_);
return v___x_3850_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___boxed(lean_object* v_m_3851_, lean_object* v_00_u03b1_3852_, lean_object* v_inst_3853_, lean_object* v_p_3854_, lean_object* v_as_3855_, lean_object* v_start_3856_, lean_object* v_stop_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Array_filterRevM(v_m_3851_, v_00_u03b1_3852_, v_inst_3853_, v_p_3854_, v_as_3855_, v_start_3856_, v_stop_3857_);
lean_dec(v_stop_3857_);
lean_dec(v_start_3856_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__0(lean_object* v_toPure_3859_, lean_object* v_bs_3860_, lean_object* v_____do__lift_3861_){
_start:
{
if (lean_obj_tag(v_____do__lift_3861_) == 0)
{
lean_object* v___x_3862_; 
v___x_3862_ = lean_apply_2(v_toPure_3859_, lean_box(0), v_bs_3860_);
return v___x_3862_;
}
else
{
lean_object* v_val_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v_val_3863_ = lean_ctor_get(v_____do__lift_3861_, 0);
lean_inc(v_val_3863_);
lean_dec_ref_known(v_____do__lift_3861_, 1);
v___x_3864_ = lean_array_push(v_bs_3860_, v_val_3863_);
v___x_3865_ = lean_apply_2(v_toPure_3859_, lean_box(0), v___x_3864_);
return v___x_3865_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__1(lean_object* v_toPure_3866_, lean_object* v_f_3867_, lean_object* v_toBind_3868_, lean_object* v_bs_3869_, lean_object* v_a_3870_){
_start:
{
lean_object* v___f_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___f_3871_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3871_, 0, v_toPure_3866_);
lean_closure_set(v___f_3871_, 1, v_bs_3869_);
v___x_3872_ = lean_apply_1(v_f_3867_, v_a_3870_);
v___x_3873_ = lean_apply_4(v_toBind_3868_, lean_box(0), lean_box(0), v___x_3872_, v___f_3871_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg(lean_object* v_inst_3874_, lean_object* v_f_3875_, lean_object* v_as_3876_, lean_object* v_start_3877_, lean_object* v_stop_3878_){
_start:
{
lean_object* v_toApplicative_3879_; lean_object* v_toBind_3880_; lean_object* v_toPure_3881_; lean_object* v___x_3882_; uint8_t v___x_3883_; 
v_toApplicative_3879_ = lean_ctor_get(v_inst_3874_, 0);
v_toBind_3880_ = lean_ctor_get(v_inst_3874_, 1);
v_toPure_3881_ = lean_ctor_get(v_toApplicative_3879_, 1);
v___x_3882_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3883_ = lean_nat_dec_lt(v_start_3877_, v_stop_3878_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; 
lean_inc(v_toPure_3881_);
lean_dec_ref(v_as_3876_);
lean_dec(v_f_3875_);
lean_dec_ref(v_inst_3874_);
v___x_3884_ = lean_apply_2(v_toPure_3881_, lean_box(0), v___x_3882_);
return v___x_3884_;
}
else
{
lean_object* v___f_3885_; lean_object* v___x_3886_; uint8_t v___x_3887_; 
lean_inc(v_toBind_3880_);
lean_inc(v_toPure_3881_);
v___f_3885_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3885_, 0, v_toPure_3881_);
lean_closure_set(v___f_3885_, 1, v_f_3875_);
lean_closure_set(v___f_3885_, 2, v_toBind_3880_);
v___x_3886_ = lean_array_get_size(v_as_3876_);
v___x_3887_ = lean_nat_dec_le(v_stop_3878_, v___x_3886_);
if (v___x_3887_ == 0)
{
uint8_t v___x_3888_; 
v___x_3888_ = lean_nat_dec_lt(v_start_3877_, v___x_3886_);
if (v___x_3888_ == 0)
{
lean_object* v___x_3889_; 
lean_inc(v_toPure_3881_);
lean_dec_ref(v___f_3885_);
lean_dec_ref(v_as_3876_);
lean_dec_ref(v_inst_3874_);
v___x_3889_ = lean_apply_2(v_toPure_3881_, lean_box(0), v___x_3882_);
return v___x_3889_;
}
else
{
size_t v___x_3890_; size_t v___x_3891_; lean_object* v___x_3892_; 
v___x_3890_ = lean_usize_of_nat(v_start_3877_);
v___x_3891_ = lean_usize_of_nat(v___x_3886_);
v___x_3892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3874_, v___f_3885_, v_as_3876_, v___x_3890_, v___x_3891_, v___x_3882_);
return v___x_3892_;
}
}
else
{
size_t v___x_3893_; size_t v___x_3894_; lean_object* v___x_3895_; 
v___x_3893_ = lean_usize_of_nat(v_start_3877_);
v___x_3894_ = lean_usize_of_nat(v_stop_3878_);
v___x_3895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3874_, v___f_3885_, v_as_3876_, v___x_3893_, v___x_3894_, v___x_3882_);
return v___x_3895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___boxed(lean_object* v_inst_3896_, lean_object* v_f_3897_, lean_object* v_as_3898_, lean_object* v_start_3899_, lean_object* v_stop_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l_Array_filterMapM___redArg(v_inst_3896_, v_f_3897_, v_as_3898_, v_start_3899_, v_stop_3900_);
lean_dec(v_stop_3900_);
lean_dec(v_start_3899_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM(lean_object* v_00_u03b1_3902_, lean_object* v_m_3903_, lean_object* v_00_u03b2_3904_, lean_object* v_inst_3905_, lean_object* v_f_3906_, lean_object* v_as_3907_, lean_object* v_start_3908_, lean_object* v_stop_3909_){
_start:
{
lean_object* v___x_3910_; 
v___x_3910_ = l_Array_filterMapM___redArg(v_inst_3905_, v_f_3906_, v_as_3907_, v_start_3908_, v_stop_3909_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___boxed(lean_object* v_00_u03b1_3911_, lean_object* v_m_3912_, lean_object* v_00_u03b2_3913_, lean_object* v_inst_3914_, lean_object* v_f_3915_, lean_object* v_as_3916_, lean_object* v_start_3917_, lean_object* v_stop_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Array_filterMapM(v_00_u03b1_3911_, v_m_3912_, v_00_u03b2_3913_, v_inst_3914_, v_f_3915_, v_as_3916_, v_start_3917_, v_stop_3918_);
lean_dec(v_stop_3918_);
lean_dec(v_start_3917_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg(lean_object* v_f_3920_, lean_object* v_as_3921_, lean_object* v_start_3922_, lean_object* v_stop_3923_){
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
LEAN_EXPORT lean_object* l_Array_filterMap___redArg___boxed(lean_object* v_f_3927_, lean_object* v_as_3928_, lean_object* v_start_3929_, lean_object* v_stop_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l_Array_filterMap___redArg(v_f_3927_, v_as_3928_, v_start_3929_, v_stop_3930_);
lean_dec(v_stop_3930_);
lean_dec(v_start_3929_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap(lean_object* v_00_u03b1_3932_, lean_object* v_00_u03b2_3933_, lean_object* v_f_3934_, lean_object* v_as_3935_, lean_object* v_start_3936_, lean_object* v_stop_3937_){
_start:
{
lean_object* v___f_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___f_3938_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3938_, 0, v_f_3934_);
v___x_3939_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3940_ = l_Array_filterMapM___redArg(v___x_3939_, v___f_3938_, v_as_3935_, v_start_3936_, v_stop_3937_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___boxed(lean_object* v_00_u03b1_3941_, lean_object* v_00_u03b2_3942_, lean_object* v_f_3943_, lean_object* v_as_3944_, lean_object* v_start_3945_, lean_object* v_stop_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_Array_filterMap(v_00_u03b1_3941_, v_00_u03b2_3942_, v_f_3943_, v_as_3944_, v_start_3945_, v_stop_3946_);
lean_dec(v_stop_3946_);
lean_dec(v_start_3945_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg___lam__0(lean_object* v_lt_3948_, lean_object* v_x1_3949_, lean_object* v_x2_3950_){
_start:
{
lean_object* v___x_3951_; uint8_t v___x_3952_; 
lean_inc(v_x2_3950_);
lean_inc(v_x1_3949_);
v___x_3951_ = lean_apply_2(v_lt_3948_, v_x1_3949_, v_x2_3950_);
v___x_3952_ = lean_unbox(v___x_3951_);
if (v___x_3952_ == 0)
{
lean_dec(v_x2_3950_);
return v_x1_3949_;
}
else
{
lean_dec(v_x1_3949_);
return v_x2_3950_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg(lean_object* v_as_3953_, lean_object* v_lt_3954_){
_start:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; uint8_t v___x_3957_; 
v___x_3955_ = lean_unsigned_to_nat(0u);
v___x_3956_ = lean_array_get_size(v_as_3953_);
v___x_3957_ = lean_nat_dec_lt(v___x_3955_, v___x_3956_);
if (v___x_3957_ == 0)
{
lean_object* v___x_3958_; 
lean_dec_ref(v_lt_3954_);
lean_dec_ref(v_as_3953_);
v___x_3958_ = lean_box(0);
return v___x_3958_;
}
else
{
lean_object* v_a0_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; uint8_t v___x_3962_; 
v_a0_3959_ = lean_array_fget(v_as_3953_, v___x_3955_);
v___x_3960_ = lean_unsigned_to_nat(1u);
v___x_3961_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3962_ = lean_nat_dec_lt(v___x_3960_, v___x_3956_);
if (v___x_3962_ == 0)
{
lean_object* v___x_3963_; 
lean_dec_ref(v_lt_3954_);
lean_dec_ref(v_as_3953_);
v___x_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3963_, 0, v_a0_3959_);
return v___x_3963_;
}
else
{
lean_object* v___f_3964_; uint8_t v___x_3965_; 
v___f_3964_ = lean_alloc_closure((void*)(l_Array_getMax_x3f___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3964_, 0, v_lt_3954_);
v___x_3965_ = lean_nat_dec_le(v___x_3956_, v___x_3956_);
if (v___x_3965_ == 0)
{
if (v___x_3962_ == 0)
{
lean_object* v___x_3966_; 
lean_dec_ref(v___f_3964_);
lean_dec_ref(v_as_3953_);
v___x_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3966_, 0, v_a0_3959_);
return v___x_3966_;
}
else
{
size_t v___x_3967_; size_t v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3967_ = ((size_t)1ULL);
v___x_3968_ = lean_usize_of_nat(v___x_3956_);
v___x_3969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3961_, v___f_3964_, v_as_3953_, v___x_3967_, v___x_3968_, v_a0_3959_);
v___x_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
return v___x_3970_;
}
}
else
{
size_t v___x_3971_; size_t v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3971_ = ((size_t)1ULL);
v___x_3972_ = lean_usize_of_nat(v___x_3956_);
v___x_3973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3961_, v___f_3964_, v_as_3953_, v___x_3971_, v___x_3972_, v_a0_3959_);
v___x_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
return v___x_3974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f(lean_object* v_00_u03b1_3975_, lean_object* v_as_3976_, lean_object* v_lt_3977_){
_start:
{
lean_object* v___x_3978_; 
v___x_3978_ = l_Array_getMax_x3f___redArg(v_as_3976_, v_lt_3977_);
return v___x_3978_;
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg___lam__0(lean_object* v_p_3979_, lean_object* v_a_3980_, lean_object* v_x_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_fst_3983_; lean_object* v_snd_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_4000_; 
v_fst_3983_ = lean_ctor_get(v___y_3982_, 0);
v_snd_3984_ = lean_ctor_get(v___y_3982_, 1);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___y_3982_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3986_ = v___y_3982_;
v_isShared_3987_ = v_isSharedCheck_4000_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_snd_3984_);
lean_inc(v_fst_3983_);
lean_dec(v___y_3982_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_4000_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3988_; uint8_t v___x_3989_; 
lean_inc(v_a_3980_);
v___x_3988_ = lean_apply_1(v_p_3979_, v_a_3980_);
v___x_3989_ = lean_unbox(v___x_3988_);
if (v___x_3989_ == 0)
{
lean_object* v___x_3990_; lean_object* v___x_3992_; 
v___x_3990_ = lean_array_push(v_snd_3984_, v_a_3980_);
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 1, v___x_3990_);
v___x_3992_ = v___x_3986_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_fst_3983_);
lean_ctor_set(v_reuseFailAlloc_3994_, 1, v___x_3990_);
v___x_3992_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
lean_object* v___x_3993_; 
v___x_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3992_);
return v___x_3993_;
}
}
else
{
lean_object* v___x_3995_; lean_object* v___x_3997_; 
v___x_3995_ = lean_array_push(v_fst_3983_, v_a_3980_);
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 0, v___x_3995_);
v___x_3997_ = v___x_3986_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3995_);
lean_ctor_set(v_reuseFailAlloc_3999_, 1, v_snd_3984_);
v___x_3997_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
lean_object* v___x_3998_; 
v___x_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
return v___x_3998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg(lean_object* v_p_4003_, lean_object* v_as_4004_){
_start:
{
lean_object* v___f_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; size_t v_sz_4008_; size_t v___x_4009_; lean_object* v___x_4010_; lean_object* v_fst_4011_; lean_object* v_snd_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
v___f_4005_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4005_, 0, v_p_4003_);
v___x_4006_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4007_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_4008_ = lean_array_size(v_as_4004_);
v___x_4009_ = ((size_t)0ULL);
v___x_4010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_4006_, v_as_4004_, v___f_4005_, v_sz_4008_, v___x_4009_, v___x_4007_);
v_fst_4011_ = lean_ctor_get(v___x_4010_, 0);
v_snd_4012_ = lean_ctor_get(v___x_4010_, 1);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_4010_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_snd_4012_);
lean_inc(v_fst_4011_);
lean_dec(v___x_4010_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_fst_4011_);
lean_ctor_set(v_reuseFailAlloc_4018_, 1, v_snd_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition(lean_object* v_00_u03b1_4020_, lean_object* v_p_4021_, lean_object* v_as_4022_){
_start:
{
lean_object* v___f_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; size_t v_sz_4026_; size_t v___x_4027_; lean_object* v___x_4028_; lean_object* v_fst_4029_; lean_object* v_snd_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
v___f_4023_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4023_, 0, v_p_4021_);
v___x_4024_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4025_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v_sz_4026_ = lean_array_size(v_as_4022_);
v___x_4027_ = ((size_t)0ULL);
v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_4024_, v_as_4022_, v___f_4023_, v_sz_4026_, v___x_4027_, v___x_4025_);
v_fst_4029_ = lean_ctor_get(v___x_4028_, 0);
v_snd_4030_ = lean_ctor_get(v___x_4028_, 1);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_4028_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_snd_4030_);
lean_inc(v_fst_4029_);
lean_dec(v___x_4028_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_fst_4029_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_snd_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile___redArg(lean_object* v_p_4038_, lean_object* v_as_4039_){
_start:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; uint8_t v___x_4042_; 
v___x_4040_ = lean_unsigned_to_nat(0u);
v___x_4041_ = lean_array_get_size(v_as_4039_);
v___x_4042_ = lean_nat_dec_lt(v___x_4040_, v___x_4041_);
if (v___x_4042_ == 0)
{
lean_dec_ref(v_p_4038_);
return v_as_4039_;
}
else
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; uint8_t v___x_4047_; 
v___x_4043_ = lean_unsigned_to_nat(1u);
v___x_4044_ = lean_nat_sub(v___x_4041_, v___x_4043_);
v___x_4045_ = lean_array_fget_borrowed(v_as_4039_, v___x_4044_);
lean_dec(v___x_4044_);
lean_inc_ref(v_p_4038_);
lean_inc(v___x_4045_);
v___x_4046_ = lean_apply_1(v_p_4038_, v___x_4045_);
v___x_4047_ = lean_unbox(v___x_4046_);
if (v___x_4047_ == 0)
{
lean_dec_ref(v_p_4038_);
return v_as_4039_;
}
else
{
lean_object* v___x_4048_; 
v___x_4048_ = lean_array_pop(v_as_4039_);
v_as_4039_ = v___x_4048_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile(lean_object* v_00_u03b1_4050_, lean_object* v_p_4051_, lean_object* v_as_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Array_popWhile___redArg(v_p_4051_, v_as_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(lean_object* v_p_4054_, lean_object* v_as_4055_, lean_object* v_i_4056_, lean_object* v_acc_4057_){
_start:
{
lean_object* v___x_4058_; uint8_t v___x_4059_; 
v___x_4058_ = lean_array_get_size(v_as_4055_);
v___x_4059_ = lean_nat_dec_lt(v_i_4056_, v___x_4058_);
if (v___x_4059_ == 0)
{
lean_dec(v_i_4056_);
lean_dec_ref(v_p_4054_);
return v_acc_4057_;
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4061_; uint8_t v___x_4062_; 
v_a_4060_ = lean_array_fget_borrowed(v_as_4055_, v_i_4056_);
lean_inc_ref(v_p_4054_);
lean_inc(v_a_4060_);
v___x_4061_ = lean_apply_1(v_p_4054_, v_a_4060_);
v___x_4062_ = lean_unbox(v___x_4061_);
if (v___x_4062_ == 0)
{
lean_dec(v_i_4056_);
lean_dec_ref(v_p_4054_);
return v_acc_4057_;
}
else
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4063_ = lean_unsigned_to_nat(1u);
v___x_4064_ = lean_nat_add(v_i_4056_, v___x_4063_);
lean_dec(v_i_4056_);
lean_inc(v_a_4060_);
v___x_4065_ = lean_array_push(v_acc_4057_, v_a_4060_);
v_i_4056_ = v___x_4064_;
v_acc_4057_ = v___x_4065_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg___boxed(lean_object* v_p_4067_, lean_object* v_as_4068_, lean_object* v_i_4069_, lean_object* v_acc_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4067_, v_as_4068_, v_i_4069_, v_acc_4070_);
lean_dec_ref(v_as_4068_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(lean_object* v_00_u03b1_4072_, lean_object* v_p_4073_, lean_object* v_as_4074_, lean_object* v_i_4075_, lean_object* v_acc_4076_){
_start:
{
lean_object* v___x_4077_; 
v___x_4077_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4073_, v_as_4074_, v_i_4075_, v_acc_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___boxed(lean_object* v_00_u03b1_4078_, lean_object* v_p_4079_, lean_object* v_as_4080_, lean_object* v_i_4081_, lean_object* v_acc_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(v_00_u03b1_4078_, v_p_4079_, v_as_4080_, v_i_4081_, v_acc_4082_);
lean_dec_ref(v_as_4080_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg(lean_object* v_p_4084_, lean_object* v_as_4085_){
_start:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4086_ = lean_unsigned_to_nat(0u);
v___x_4087_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4088_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4084_, v_as_4085_, v___x_4086_, v___x_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg___boxed(lean_object* v_p_4089_, lean_object* v_as_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_Array_takeWhile___redArg(v_p_4089_, v_as_4090_);
lean_dec_ref(v_as_4090_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile(lean_object* v_00_u03b1_4092_, lean_object* v_p_4093_, lean_object* v_as_4094_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l_Array_takeWhile___redArg(v_p_4093_, v_as_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___boxed(lean_object* v_00_u03b1_4096_, lean_object* v_p_4097_, lean_object* v_as_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l_Array_takeWhile(v_00_u03b1_4096_, v_p_4097_, v_as_4098_);
lean_dec_ref(v_as_4098_);
return v_res_4099_;
}
}
static lean_object* _init_l_Array_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx___redArg(lean_object* v_xs_4101_, lean_object* v_i_4102_){
_start:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; uint8_t v___x_4106_; 
v___x_4103_ = lean_unsigned_to_nat(1u);
v___x_4104_ = lean_nat_add(v_i_4102_, v___x_4103_);
v___x_4105_ = lean_array_get_size(v_xs_4101_);
v___x_4106_ = lean_nat_dec_lt(v___x_4104_, v___x_4105_);
if (v___x_4106_ == 0)
{
lean_object* v___x_4107_; 
lean_dec(v___x_4104_);
lean_dec(v_i_4102_);
v___x_4107_ = lean_array_pop(v_xs_4101_);
return v___x_4107_;
}
else
{
lean_object* v_xs_x27_4108_; 
v_xs_x27_4108_ = lean_array_fswap(v_xs_4101_, v___x_4104_, v_i_4102_);
lean_dec(v_i_4102_);
v_xs_4101_ = v_xs_x27_4108_;
v_i_4102_ = v___x_4104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx(lean_object* v_00_u03b1_4110_, lean_object* v_xs_4111_, lean_object* v_i_4112_, lean_object* v_h_4113_){
_start:
{
lean_object* v___x_4114_; 
v___x_4114_ = l_Array_eraseIdx___redArg(v_xs_4111_, v_i_4112_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds___redArg(lean_object* v_xs_4115_, lean_object* v_i_4116_){
_start:
{
lean_object* v___x_4117_; uint8_t v___x_4118_; 
v___x_4117_ = lean_array_get_size(v_xs_4115_);
v___x_4118_ = lean_nat_dec_lt(v_i_4116_, v___x_4117_);
if (v___x_4118_ == 0)
{
lean_dec(v_i_4116_);
return v_xs_4115_;
}
else
{
lean_object* v___x_4119_; 
v___x_4119_ = l_Array_eraseIdx___redArg(v_xs_4115_, v_i_4116_);
return v___x_4119_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds(lean_object* v_00_u03b1_4120_, lean_object* v_xs_4121_, lean_object* v_i_4122_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_Array_eraseIdxIfInBounds___redArg(v_xs_4121_, v_i_4122_);
return v___x_4123_;
}
}
static lean_object* _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_Array_instInhabited(lean_box(0));
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(lean_object* v_msg_4125_){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = lean_obj_once(&l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0, &l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0_once, _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0);
v___x_4127_ = lean_panic_fn_borrowed(v___x_4126_, v_msg_4125_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0(lean_object* v_00_u03b1_4128_, lean_object* v_msg_4129_){
_start:
{
lean_object* v___x_4130_; 
v___x_4130_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v_msg_4129_);
return v___x_4130_;
}
}
static lean_object* _init_l_Array_eraseIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4133_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4134_ = lean_unsigned_to_nat(47u);
v___x_4135_ = lean_unsigned_to_nat(1867u);
v___x_4136_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__0));
v___x_4137_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4138_ = l_mkPanicMessageWithDecl(v___x_4137_, v___x_4136_, v___x_4135_, v___x_4134_, v___x_4133_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21___redArg(lean_object* v_xs_4139_, lean_object* v_i_4140_){
_start:
{
lean_object* v___x_4141_; uint8_t v___x_4142_; 
v___x_4141_ = lean_array_get_size(v_xs_4139_);
v___x_4142_ = lean_nat_dec_lt(v_i_4140_, v___x_4141_);
if (v___x_4142_ == 0)
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
lean_dec(v_i_4140_);
lean_dec_ref(v_xs_4139_);
v___x_4143_ = lean_obj_once(&l_Array_eraseIdx_x21___redArg___closed__2, &l_Array_eraseIdx_x21___redArg___closed__2_once, _init_l_Array_eraseIdx_x21___redArg___closed__2);
v___x_4144_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4143_);
return v___x_4144_;
}
else
{
lean_object* v___x_4145_; 
v___x_4145_ = l_Array_eraseIdx___redArg(v_xs_4139_, v_i_4140_);
return v___x_4145_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21(lean_object* v_00_u03b1_4146_, lean_object* v_xs_4147_, lean_object* v_i_4148_){
_start:
{
lean_object* v___x_4149_; 
v___x_4149_ = l_Array_eraseIdx_x21___redArg(v_xs_4147_, v_i_4148_);
return v___x_4149_;
}
}
LEAN_EXPORT lean_object* l_Array_erase___redArg(lean_object* v_inst_4150_, lean_object* v_as_4151_, lean_object* v_a_4152_){
_start:
{
lean_object* v___x_4153_; 
v___x_4153_ = l_Array_finIdxOf_x3f___redArg(v_inst_4150_, v_as_4151_, v_a_4152_);
if (lean_obj_tag(v___x_4153_) == 0)
{
return v_as_4151_;
}
else
{
lean_object* v_val_4154_; lean_object* v___x_4155_; 
v_val_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_val_4154_);
lean_dec_ref_known(v___x_4153_, 1);
v___x_4155_ = l_Array_eraseIdx___redArg(v_as_4151_, v_val_4154_);
return v___x_4155_;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase(lean_object* v_00_u03b1_4156_, lean_object* v_inst_4157_, lean_object* v_as_4158_, lean_object* v_a_4159_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_Array_erase___redArg(v_inst_4157_, v_as_4158_, v_a_4159_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseP___redArg(lean_object* v_as_4161_, lean_object* v_p_4162_){
_start:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4163_ = lean_unsigned_to_nat(0u);
v___x_4164_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_4162_, v_as_4161_, v___x_4163_);
if (lean_obj_tag(v___x_4164_) == 0)
{
return v_as_4161_;
}
else
{
lean_object* v_val_4165_; lean_object* v___x_4166_; 
v_val_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_val_4165_);
lean_dec_ref_known(v___x_4164_, 1);
v___x_4166_ = l_Array_eraseIdx___redArg(v_as_4161_, v_val_4165_);
return v___x_4166_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseP(lean_object* v_00_u03b1_4167_, lean_object* v_as_4168_, lean_object* v_p_4169_){
_start:
{
lean_object* v___x_4170_; 
v___x_4170_ = l_Array_eraseP___redArg(v_as_4168_, v_p_4169_);
return v___x_4170_;
}
}
static lean_object* _init_l_Array_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_4171_; 
v___x_4171_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(lean_object* v_i_4172_, lean_object* v_as_4173_, lean_object* v_j_4174_){
_start:
{
uint8_t v___x_4175_; 
v___x_4175_ = lean_nat_dec_lt(v_i_4172_, v_j_4174_);
if (v___x_4175_ == 0)
{
lean_dec(v_j_4174_);
return v_as_4173_;
}
else
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v_as_4178_; 
v___x_4176_ = lean_unsigned_to_nat(1u);
v___x_4177_ = lean_nat_sub(v_j_4174_, v___x_4176_);
v_as_4178_ = lean_array_fswap(v_as_4173_, v___x_4177_, v_j_4174_);
lean_dec(v_j_4174_);
v_as_4173_ = v_as_4178_;
v_j_4174_ = v___x_4177_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg___boxed(lean_object* v_i_4180_, lean_object* v_as_4181_, lean_object* v_j_4182_){
_start:
{
lean_object* v_res_4183_; 
v_res_4183_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4180_, v_as_4181_, v_j_4182_);
lean_dec(v_i_4180_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object* v_00_u03b1_4184_, lean_object* v_i_4185_, lean_object* v_as_4186_, lean_object* v_j_4187_){
_start:
{
lean_object* v___x_4188_; 
v___x_4188_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4185_, v_as_4186_, v_j_4187_);
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___boxed(lean_object* v_00_u03b1_4189_, lean_object* v_i_4190_, lean_object* v_as_4191_, lean_object* v_j_4192_){
_start:
{
lean_object* v_res_4193_; 
v_res_4193_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(v_00_u03b1_4189_, v_i_4190_, v_as_4191_, v_j_4192_);
lean_dec(v_i_4190_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg(lean_object* v_as_4194_, lean_object* v_i_4195_, lean_object* v_a_4196_){
_start:
{
lean_object* v_j_4197_; lean_object* v_as_4198_; lean_object* v___x_4199_; 
v_j_4197_ = lean_array_get_size(v_as_4194_);
v_as_4198_ = lean_array_push(v_as_4194_, v_a_4196_);
v___x_4199_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4195_, v_as_4198_, v_j_4197_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg___boxed(lean_object* v_as_4200_, lean_object* v_i_4201_, lean_object* v_a_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l_Array_insertIdx___redArg(v_as_4200_, v_i_4201_, v_a_4202_);
lean_dec(v_i_4201_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx(lean_object* v_00_u03b1_4204_, lean_object* v_as_4205_, lean_object* v_i_4206_, lean_object* v_a_4207_, lean_object* v_x_4208_){
_start:
{
lean_object* v_j_4209_; lean_object* v_as_4210_; lean_object* v___x_4211_; 
v_j_4209_ = lean_array_get_size(v_as_4205_);
v_as_4210_ = lean_array_push(v_as_4205_, v_a_4207_);
v___x_4211_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4206_, v_as_4210_, v_j_4209_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___boxed(lean_object* v_00_u03b1_4212_, lean_object* v_as_4213_, lean_object* v_i_4214_, lean_object* v_a_4215_, lean_object* v_x_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l_Array_insertIdx(v_00_u03b1_4212_, v_as_4213_, v_i_4214_, v_a_4215_, v_x_4216_);
lean_dec(v_i_4214_);
return v_res_4217_;
}
}
static lean_object* _init_l_Array_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4219_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4220_ = lean_unsigned_to_nat(7u);
v___x_4221_ = lean_unsigned_to_nat(1949u);
v___x_4222_ = ((lean_object*)(l_Array_insertIdx_x21___redArg___closed__0));
v___x_4223_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4224_ = l_mkPanicMessageWithDecl(v___x_4223_, v___x_4222_, v___x_4221_, v___x_4220_, v___x_4219_);
return v___x_4224_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg(lean_object* v_as_4225_, lean_object* v_i_4226_, lean_object* v_a_4227_){
_start:
{
lean_object* v___x_4228_; uint8_t v___x_4229_; 
v___x_4228_ = lean_array_get_size(v_as_4225_);
v___x_4229_ = lean_nat_dec_le(v_i_4226_, v___x_4228_);
if (v___x_4229_ == 0)
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
lean_dec(v_a_4227_);
lean_dec_ref(v_as_4225_);
v___x_4230_ = lean_obj_once(&l_Array_insertIdx_x21___redArg___closed__1, &l_Array_insertIdx_x21___redArg___closed__1_once, _init_l_Array_insertIdx_x21___redArg___closed__1);
v___x_4231_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4230_);
return v___x_4231_;
}
else
{
lean_object* v_as_4232_; lean_object* v___x_4233_; 
v_as_4232_ = lean_array_push(v_as_4225_, v_a_4227_);
v___x_4233_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4226_, v_as_4232_, v___x_4228_);
return v___x_4233_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg___boxed(lean_object* v_as_4234_, lean_object* v_i_4235_, lean_object* v_a_4236_){
_start:
{
lean_object* v_res_4237_; 
v_res_4237_ = l_Array_insertIdx_x21___redArg(v_as_4234_, v_i_4235_, v_a_4236_);
lean_dec(v_i_4235_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21(lean_object* v_00_u03b1_4238_, lean_object* v_as_4239_, lean_object* v_i_4240_, lean_object* v_a_4241_){
_start:
{
lean_object* v___x_4242_; 
v___x_4242_ = l_Array_insertIdx_x21___redArg(v_as_4239_, v_i_4240_, v_a_4241_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___boxed(lean_object* v_00_u03b1_4243_, lean_object* v_as_4244_, lean_object* v_i_4245_, lean_object* v_a_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Array_insertIdx_x21(v_00_u03b1_4243_, v_as_4244_, v_i_4245_, v_a_4246_);
lean_dec(v_i_4245_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg(lean_object* v_as_4248_, lean_object* v_i_4249_, lean_object* v_a_4250_){
_start:
{
lean_object* v___x_4251_; uint8_t v___x_4252_; 
v___x_4251_ = lean_array_get_size(v_as_4248_);
v___x_4252_ = lean_nat_dec_le(v_i_4249_, v___x_4251_);
if (v___x_4252_ == 0)
{
lean_dec(v_a_4250_);
return v_as_4248_;
}
else
{
lean_object* v_as_4253_; lean_object* v___x_4254_; 
v_as_4253_ = lean_array_push(v_as_4248_, v_a_4250_);
v___x_4254_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4249_, v_as_4253_, v___x_4251_);
return v___x_4254_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg___boxed(lean_object* v_as_4255_, lean_object* v_i_4256_, lean_object* v_a_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l_Array_insertIdxIfInBounds___redArg(v_as_4255_, v_i_4256_, v_a_4257_);
lean_dec(v_i_4256_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds(lean_object* v_00_u03b1_4259_, lean_object* v_as_4260_, lean_object* v_i_4261_, lean_object* v_a_4262_){
_start:
{
lean_object* v___x_4263_; 
v___x_4263_ = l_Array_insertIdxIfInBounds___redArg(v_as_4260_, v_i_4261_, v_a_4262_);
return v___x_4263_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___boxed(lean_object* v_00_u03b1_4264_, lean_object* v_as_4265_, lean_object* v_i_4266_, lean_object* v_a_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l_Array_insertIdxIfInBounds(v_00_u03b1_4264_, v_as_4265_, v_i_4266_, v_a_4267_);
lean_dec(v_i_4266_);
return v_res_4268_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux___redArg(lean_object* v_inst_4269_, lean_object* v_as_4270_, lean_object* v_bs_4271_, lean_object* v_i_4272_){
_start:
{
lean_object* v___x_4273_; uint8_t v___x_4274_; 
v___x_4273_ = lean_array_get_size(v_as_4270_);
v___x_4274_ = lean_nat_dec_lt(v_i_4272_, v___x_4273_);
if (v___x_4274_ == 0)
{
uint8_t v___x_4275_; 
lean_dec(v_i_4272_);
lean_dec_ref(v_inst_4269_);
v___x_4275_ = 1;
return v___x_4275_;
}
else
{
lean_object* v_a_4276_; lean_object* v_b_4277_; lean_object* v___x_4278_; uint8_t v___x_4279_; 
v_a_4276_ = lean_array_fget_borrowed(v_as_4270_, v_i_4272_);
v_b_4277_ = lean_array_fget_borrowed(v_bs_4271_, v_i_4272_);
lean_inc_ref(v_inst_4269_);
lean_inc(v_b_4277_);
lean_inc(v_a_4276_);
v___x_4278_ = lean_apply_2(v_inst_4269_, v_a_4276_, v_b_4277_);
v___x_4279_ = lean_unbox(v___x_4278_);
if (v___x_4279_ == 0)
{
uint8_t v___x_4280_; 
lean_dec(v_i_4272_);
lean_dec_ref(v_inst_4269_);
v___x_4280_ = lean_unbox(v___x_4278_);
return v___x_4280_;
}
else
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = lean_unsigned_to_nat(1u);
v___x_4282_ = lean_nat_add(v_i_4272_, v___x_4281_);
lean_dec(v_i_4272_);
v_i_4272_ = v___x_4282_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___redArg___boxed(lean_object* v_inst_4284_, lean_object* v_as_4285_, lean_object* v_bs_4286_, lean_object* v_i_4287_){
_start:
{
uint8_t v_res_4288_; lean_object* v_r_4289_; 
v_res_4288_ = l_Array_isPrefixOfAux___redArg(v_inst_4284_, v_as_4285_, v_bs_4286_, v_i_4287_);
lean_dec_ref(v_bs_4286_);
lean_dec_ref(v_as_4285_);
v_r_4289_ = lean_box(v_res_4288_);
return v_r_4289_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux(lean_object* v_00_u03b1_4290_, lean_object* v_inst_4291_, lean_object* v_as_4292_, lean_object* v_bs_4293_, lean_object* v_hle_4294_, lean_object* v_i_4295_){
_start:
{
uint8_t v___x_4296_; 
v___x_4296_ = l_Array_isPrefixOfAux___redArg(v_inst_4291_, v_as_4292_, v_bs_4293_, v_i_4295_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___boxed(lean_object* v_00_u03b1_4297_, lean_object* v_inst_4298_, lean_object* v_as_4299_, lean_object* v_bs_4300_, lean_object* v_hle_4301_, lean_object* v_i_4302_){
_start:
{
uint8_t v_res_4303_; lean_object* v_r_4304_; 
v_res_4303_ = l_Array_isPrefixOfAux(v_00_u03b1_4297_, v_inst_4298_, v_as_4299_, v_bs_4300_, v_hle_4301_, v_i_4302_);
lean_dec_ref(v_bs_4300_);
lean_dec_ref(v_as_4299_);
v_r_4304_ = lean_box(v_res_4303_);
return v_r_4304_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf___redArg(lean_object* v_inst_4305_, lean_object* v_as_4306_, lean_object* v_bs_4307_){
_start:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; uint8_t v___x_4310_; 
v___x_4308_ = lean_array_get_size(v_as_4306_);
v___x_4309_ = lean_array_get_size(v_bs_4307_);
v___x_4310_ = lean_nat_dec_le(v___x_4308_, v___x_4309_);
if (v___x_4310_ == 0)
{
lean_dec_ref(v_inst_4305_);
return v___x_4310_;
}
else
{
lean_object* v___x_4311_; uint8_t v___x_4312_; 
v___x_4311_ = lean_unsigned_to_nat(0u);
v___x_4312_ = l_Array_isPrefixOfAux___redArg(v_inst_4305_, v_as_4306_, v_bs_4307_, v___x_4311_);
return v___x_4312_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___redArg___boxed(lean_object* v_inst_4313_, lean_object* v_as_4314_, lean_object* v_bs_4315_){
_start:
{
uint8_t v_res_4316_; lean_object* v_r_4317_; 
v_res_4316_ = l_Array_isPrefixOf___redArg(v_inst_4313_, v_as_4314_, v_bs_4315_);
lean_dec_ref(v_bs_4315_);
lean_dec_ref(v_as_4314_);
v_r_4317_ = lean_box(v_res_4316_);
return v_r_4317_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf(lean_object* v_00_u03b1_4318_, lean_object* v_inst_4319_, lean_object* v_as_4320_, lean_object* v_bs_4321_){
_start:
{
uint8_t v___x_4322_; 
v___x_4322_ = l_Array_isPrefixOf___redArg(v_inst_4319_, v_as_4320_, v_bs_4321_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___boxed(lean_object* v_00_u03b1_4323_, lean_object* v_inst_4324_, lean_object* v_as_4325_, lean_object* v_bs_4326_){
_start:
{
uint8_t v_res_4327_; lean_object* v_r_4328_; 
v_res_4327_ = l_Array_isPrefixOf(v_00_u03b1_4323_, v_inst_4324_, v_as_4325_, v_bs_4326_);
lean_dec_ref(v_bs_4326_);
lean_dec_ref(v_as_4325_);
v_r_4328_ = lean_box(v_res_4327_);
return v_r_4328_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0___boxed(lean_object* v_i_4329_, lean_object* v_cs_4330_, lean_object* v_inst_4331_, lean_object* v_as_4332_, lean_object* v_bs_4333_, lean_object* v_f_4334_, lean_object* v_____do__lift_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l_Array_zipWithMAux___redArg___lam__0(v_i_4329_, v_cs_4330_, v_inst_4331_, v_as_4332_, v_bs_4333_, v_f_4334_, v_____do__lift_4335_);
lean_dec(v_i_4329_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg(lean_object* v_inst_4337_, lean_object* v_as_4338_, lean_object* v_bs_4339_, lean_object* v_f_4340_, lean_object* v_i_4341_, lean_object* v_cs_4342_){
_start:
{
lean_object* v_toApplicative_4343_; lean_object* v_toBind_4344_; lean_object* v_toPure_4345_; lean_object* v___x_4346_; uint8_t v___x_4347_; 
v_toApplicative_4343_ = lean_ctor_get(v_inst_4337_, 0);
v_toBind_4344_ = lean_ctor_get(v_inst_4337_, 1);
lean_inc(v_toBind_4344_);
v_toPure_4345_ = lean_ctor_get(v_toApplicative_4343_, 1);
v___x_4346_ = lean_array_get_size(v_as_4338_);
v___x_4347_ = lean_nat_dec_lt(v_i_4341_, v___x_4346_);
if (v___x_4347_ == 0)
{
lean_object* v___x_4348_; 
lean_inc(v_toPure_4345_);
lean_dec(v_toBind_4344_);
lean_dec(v_i_4341_);
lean_dec(v_f_4340_);
lean_dec_ref(v_bs_4339_);
lean_dec_ref(v_as_4338_);
lean_dec_ref(v_inst_4337_);
v___x_4348_ = lean_apply_2(v_toPure_4345_, lean_box(0), v_cs_4342_);
return v___x_4348_;
}
else
{
lean_object* v___x_4349_; uint8_t v___x_4350_; 
v___x_4349_ = lean_array_get_size(v_bs_4339_);
v___x_4350_ = lean_nat_dec_lt(v_i_4341_, v___x_4349_);
if (v___x_4350_ == 0)
{
lean_object* v___x_4351_; 
lean_inc(v_toPure_4345_);
lean_dec(v_toBind_4344_);
lean_dec(v_i_4341_);
lean_dec(v_f_4340_);
lean_dec_ref(v_bs_4339_);
lean_dec_ref(v_as_4338_);
lean_dec_ref(v_inst_4337_);
v___x_4351_ = lean_apply_2(v_toPure_4345_, lean_box(0), v_cs_4342_);
return v___x_4351_;
}
else
{
lean_object* v___f_4352_; lean_object* v_a_4353_; lean_object* v_b_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
lean_inc(v_f_4340_);
lean_inc_ref(v_bs_4339_);
lean_inc_ref(v_as_4338_);
lean_inc(v_i_4341_);
v___f_4352_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4352_, 0, v_i_4341_);
lean_closure_set(v___f_4352_, 1, v_cs_4342_);
lean_closure_set(v___f_4352_, 2, v_inst_4337_);
lean_closure_set(v___f_4352_, 3, v_as_4338_);
lean_closure_set(v___f_4352_, 4, v_bs_4339_);
lean_closure_set(v___f_4352_, 5, v_f_4340_);
v_a_4353_ = lean_array_fget(v_as_4338_, v_i_4341_);
lean_dec_ref(v_as_4338_);
v_b_4354_ = lean_array_fget(v_bs_4339_, v_i_4341_);
lean_dec(v_i_4341_);
lean_dec_ref(v_bs_4339_);
v___x_4355_ = lean_apply_2(v_f_4340_, v_a_4353_, v_b_4354_);
v___x_4356_ = lean_apply_4(v_toBind_4344_, lean_box(0), lean_box(0), v___x_4355_, v___f_4352_);
return v___x_4356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0(lean_object* v_i_4357_, lean_object* v_cs_4358_, lean_object* v_inst_4359_, lean_object* v_as_4360_, lean_object* v_bs_4361_, lean_object* v_f_4362_, lean_object* v_____do__lift_4363_){
_start:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4364_ = lean_unsigned_to_nat(1u);
v___x_4365_ = lean_nat_add(v_i_4357_, v___x_4364_);
v___x_4366_ = lean_array_push(v_cs_4358_, v_____do__lift_4363_);
v___x_4367_ = l_Array_zipWithMAux___redArg(v_inst_4359_, v_as_4360_, v_bs_4361_, v_f_4362_, v___x_4365_, v___x_4366_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux(lean_object* v_00_u03b1_4368_, lean_object* v_00_u03b2_4369_, lean_object* v_00_u03b3_4370_, lean_object* v_m_4371_, lean_object* v_inst_4372_, lean_object* v_as_4373_, lean_object* v_bs_4374_, lean_object* v_f_4375_, lean_object* v_i_4376_, lean_object* v_cs_4377_){
_start:
{
lean_object* v___x_4378_; 
v___x_4378_ = l_Array_zipWithMAux___redArg(v_inst_4372_, v_as_4373_, v_bs_4374_, v_f_4375_, v_i_4376_, v_cs_4377_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith___redArg(lean_object* v_f_4379_, lean_object* v_as_4380_, lean_object* v_bs_4381_){
_start:
{
lean_object* v___f_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___f_4382_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4382_, 0, v_f_4379_);
v___x_4383_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4384_ = lean_unsigned_to_nat(0u);
v___x_4385_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4386_ = l_Array_zipWithMAux___redArg(v___x_4383_, v_as_4380_, v_bs_4381_, v___f_4382_, v___x_4384_, v___x_4385_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith(lean_object* v_00_u03b1_4387_, lean_object* v_00_u03b2_4388_, lean_object* v_00_u03b3_4389_, lean_object* v_f_4390_, lean_object* v_as_4391_, lean_object* v_bs_4392_){
_start:
{
lean_object* v___f_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___f_4393_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4393_, 0, v_f_4390_);
v___x_4394_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4395_ = lean_unsigned_to_nat(0u);
v___x_4396_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4397_ = l_Array_zipWithMAux___redArg(v___x_4394_, v_as_4391_, v_bs_4392_, v___f_4393_, v___x_4395_, v___x_4396_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(lean_object* v_as_4398_, lean_object* v_bs_4399_, lean_object* v_i_4400_, lean_object* v_cs_4401_){
_start:
{
lean_object* v___x_4402_; uint8_t v___x_4403_; 
v___x_4402_ = lean_array_get_size(v_as_4398_);
v___x_4403_ = lean_nat_dec_lt(v_i_4400_, v___x_4402_);
if (v___x_4403_ == 0)
{
lean_dec(v_i_4400_);
return v_cs_4401_;
}
else
{
lean_object* v___x_4404_; uint8_t v___x_4405_; 
v___x_4404_ = lean_array_get_size(v_bs_4399_);
v___x_4405_ = lean_nat_dec_lt(v_i_4400_, v___x_4404_);
if (v___x_4405_ == 0)
{
lean_dec(v_i_4400_);
return v_cs_4401_;
}
else
{
lean_object* v_a_4406_; lean_object* v_b_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v_a_4406_ = lean_array_fget_borrowed(v_as_4398_, v_i_4400_);
v_b_4407_ = lean_array_fget_borrowed(v_bs_4399_, v_i_4400_);
lean_inc(v_b_4407_);
lean_inc(v_a_4406_);
v___x_4408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4408_, 0, v_a_4406_);
lean_ctor_set(v___x_4408_, 1, v_b_4407_);
v___x_4409_ = lean_unsigned_to_nat(1u);
v___x_4410_ = lean_nat_add(v_i_4400_, v___x_4409_);
lean_dec(v_i_4400_);
v___x_4411_ = lean_array_push(v_cs_4401_, v___x_4408_);
v_i_4400_ = v___x_4410_;
v_cs_4401_ = v___x_4411_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg___boxed(lean_object* v_as_4413_, lean_object* v_bs_4414_, lean_object* v_i_4415_, lean_object* v_cs_4416_){
_start:
{
lean_object* v_res_4417_; 
v_res_4417_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4413_, v_bs_4414_, v_i_4415_, v_cs_4416_);
lean_dec_ref(v_bs_4414_);
lean_dec_ref(v_as_4413_);
return v_res_4417_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg(lean_object* v_as_4420_, lean_object* v_bs_4421_){
_start:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v___x_4422_ = lean_unsigned_to_nat(0u);
v___x_4423_ = ((lean_object*)(l_Array_zip___redArg___closed__0));
v___x_4424_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4420_, v_bs_4421_, v___x_4422_, v___x_4423_);
return v___x_4424_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg___boxed(lean_object* v_as_4425_, lean_object* v_bs_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l_Array_zip___redArg(v_as_4425_, v_bs_4426_);
lean_dec_ref(v_bs_4426_);
lean_dec_ref(v_as_4425_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Array_zip(lean_object* v_00_u03b1_4428_, lean_object* v_00_u03b2_4429_, lean_object* v_as_4430_, lean_object* v_bs_4431_){
_start:
{
lean_object* v___x_4432_; 
v___x_4432_ = l_Array_zip___redArg(v_as_4430_, v_bs_4431_);
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___boxed(lean_object* v_00_u03b1_4433_, lean_object* v_00_u03b2_4434_, lean_object* v_as_4435_, lean_object* v_bs_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_Array_zip(v_00_u03b1_4433_, v_00_u03b2_4434_, v_as_4435_, v_bs_4436_);
lean_dec_ref(v_bs_4436_);
lean_dec_ref(v_as_4435_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0(lean_object* v_00_u03b1_4438_, lean_object* v_00_u03b2_4439_, lean_object* v_as_4440_, lean_object* v_bs_4441_, lean_object* v_i_4442_, lean_object* v_cs_4443_){
_start:
{
lean_object* v___x_4444_; 
v___x_4444_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4440_, v_bs_4441_, v_i_4442_, v_cs_4443_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___boxed(lean_object* v_00_u03b1_4445_, lean_object* v_00_u03b2_4446_, lean_object* v_as_4447_, lean_object* v_bs_4448_, lean_object* v_i_4449_, lean_object* v_cs_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l_Array_zipWithMAux___at___00Array_zip_spec__0(v_00_u03b1_4445_, v_00_u03b2_4446_, v_as_4447_, v_bs_4448_, v_i_4449_, v_cs_4450_);
lean_dec_ref(v_bs_4448_);
lean_dec_ref(v_as_4447_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(lean_object* v_f_4452_, lean_object* v_as_4453_, lean_object* v_bs_4454_, lean_object* v_i_4455_, lean_object* v_cs_4456_){
_start:
{
lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4466_; lean_object* v___y_4473_; lean_object* v___x_4480_; lean_object* v___x_4481_; uint8_t v___x_4482_; 
v___x_4480_ = lean_array_get_size(v_as_4453_);
v___x_4481_ = lean_array_get_size(v_bs_4454_);
v___x_4482_ = lean_nat_dec_le(v___x_4480_, v___x_4481_);
if (v___x_4482_ == 0)
{
v___y_4473_ = v___x_4480_;
goto v___jp_4472_;
}
else
{
v___y_4473_ = v___x_4481_;
goto v___jp_4472_;
}
v___jp_4457_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4460_ = lean_unsigned_to_nat(1u);
v___x_4461_ = lean_nat_add(v_i_4455_, v___x_4460_);
lean_dec(v_i_4455_);
lean_inc(v_f_4452_);
v___x_4462_ = lean_apply_2(v_f_4452_, v___y_4458_, v___y_4459_);
v___x_4463_ = lean_array_push(v_cs_4456_, v___x_4462_);
v_i_4455_ = v___x_4461_;
v_cs_4456_ = v___x_4463_;
goto _start;
}
v___jp_4465_:
{
lean_object* v___x_4467_; uint8_t v___x_4468_; 
v___x_4467_ = lean_array_get_size(v_bs_4454_);
v___x_4468_ = lean_nat_dec_lt(v_i_4455_, v___x_4467_);
if (v___x_4468_ == 0)
{
lean_object* v___x_4469_; 
v___x_4469_ = lean_box(0);
v___y_4458_ = v___y_4466_;
v___y_4459_ = v___x_4469_;
goto v___jp_4457_;
}
else
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4470_ = lean_array_fget_borrowed(v_bs_4454_, v_i_4455_);
lean_inc(v___x_4470_);
v___x_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4470_);
v___y_4458_ = v___y_4466_;
v___y_4459_ = v___x_4471_;
goto v___jp_4457_;
}
}
v___jp_4472_:
{
uint8_t v___x_4474_; 
v___x_4474_ = lean_nat_dec_lt(v_i_4455_, v___y_4473_);
lean_dec(v___y_4473_);
if (v___x_4474_ == 0)
{
lean_dec(v_i_4455_);
lean_dec(v_f_4452_);
return v_cs_4456_;
}
else
{
lean_object* v___x_4475_; uint8_t v___x_4476_; 
v___x_4475_ = lean_array_get_size(v_as_4453_);
v___x_4476_ = lean_nat_dec_lt(v_i_4455_, v___x_4475_);
if (v___x_4476_ == 0)
{
lean_object* v___x_4477_; 
v___x_4477_ = lean_box(0);
v___y_4466_ = v___x_4477_;
goto v___jp_4465_;
}
else
{
lean_object* v___x_4478_; lean_object* v___x_4479_; 
v___x_4478_ = lean_array_fget_borrowed(v_as_4453_, v_i_4455_);
lean_inc(v___x_4478_);
v___x_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4478_);
v___y_4466_ = v___x_4479_;
goto v___jp_4465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg___boxed(lean_object* v_f_4483_, lean_object* v_as_4484_, lean_object* v_bs_4485_, lean_object* v_i_4486_, lean_object* v_cs_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4483_, v_as_4484_, v_bs_4485_, v_i_4486_, v_cs_4487_);
lean_dec_ref(v_bs_4485_);
lean_dec_ref(v_as_4484_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(lean_object* v_00_u03b1_4489_, lean_object* v_00_u03b2_4490_, lean_object* v_00_u03b3_4491_, lean_object* v_f_4492_, lean_object* v_as_4493_, lean_object* v_bs_4494_, lean_object* v_i_4495_, lean_object* v_cs_4496_){
_start:
{
lean_object* v___x_4497_; 
v___x_4497_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4492_, v_as_4493_, v_bs_4494_, v_i_4495_, v_cs_4496_);
return v___x_4497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___boxed(lean_object* v_00_u03b1_4498_, lean_object* v_00_u03b2_4499_, lean_object* v_00_u03b3_4500_, lean_object* v_f_4501_, lean_object* v_as_4502_, lean_object* v_bs_4503_, lean_object* v_i_4504_, lean_object* v_cs_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(v_00_u03b1_4498_, v_00_u03b2_4499_, v_00_u03b3_4500_, v_f_4501_, v_as_4502_, v_bs_4503_, v_i_4504_, v_cs_4505_);
lean_dec_ref(v_bs_4503_);
lean_dec_ref(v_as_4502_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg(lean_object* v_f_4507_, lean_object* v_as_4508_, lean_object* v_bs_4509_){
_start:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4510_ = lean_unsigned_to_nat(0u);
v___x_4511_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4512_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4507_, v_as_4508_, v_bs_4509_, v___x_4510_, v___x_4511_);
return v___x_4512_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg___boxed(lean_object* v_f_4513_, lean_object* v_as_4514_, lean_object* v_bs_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l_Array_zipWithAll___redArg(v_f_4513_, v_as_4514_, v_bs_4515_);
lean_dec_ref(v_bs_4515_);
lean_dec_ref(v_as_4514_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll(lean_object* v_00_u03b1_4517_, lean_object* v_00_u03b2_4518_, lean_object* v_00_u03b3_4519_, lean_object* v_f_4520_, lean_object* v_as_4521_, lean_object* v_bs_4522_){
_start:
{
lean_object* v___x_4523_; 
v___x_4523_ = l_Array_zipWithAll___redArg(v_f_4520_, v_as_4521_, v_bs_4522_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___boxed(lean_object* v_00_u03b1_4524_, lean_object* v_00_u03b2_4525_, lean_object* v_00_u03b3_4526_, lean_object* v_f_4527_, lean_object* v_as_4528_, lean_object* v_bs_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l_Array_zipWithAll(v_00_u03b1_4524_, v_00_u03b2_4525_, v_00_u03b3_4526_, v_f_4527_, v_as_4528_, v_bs_4529_);
lean_dec_ref(v_bs_4529_);
lean_dec_ref(v_as_4528_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM___redArg(lean_object* v_inst_4531_, lean_object* v_f_4532_, lean_object* v_as_4533_, lean_object* v_bs_4534_){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4535_ = lean_unsigned_to_nat(0u);
v___x_4536_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4537_ = l_Array_zipWithMAux___redArg(v_inst_4531_, v_as_4533_, v_bs_4534_, v_f_4532_, v___x_4535_, v___x_4536_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM(lean_object* v_00_u03b1_4538_, lean_object* v_00_u03b2_4539_, lean_object* v_00_u03b3_4540_, lean_object* v_m_4541_, lean_object* v_inst_4542_, lean_object* v_f_4543_, lean_object* v_as_4544_, lean_object* v_bs_4545_){
_start:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4546_ = lean_unsigned_to_nat(0u);
v___x_4547_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4548_ = l_Array_zipWithMAux___redArg(v_inst_4542_, v_as_4544_, v_bs_4545_, v_f_4543_, v___x_4546_, v___x_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(lean_object* v_as_4549_, size_t v_i_4550_, size_t v_stop_4551_, lean_object* v_b_4552_){
_start:
{
uint8_t v___x_4553_; 
v___x_4553_ = lean_usize_dec_eq(v_i_4550_, v_stop_4551_);
if (v___x_4553_ == 0)
{
lean_object* v_fst_4554_; lean_object* v_snd_4555_; lean_object* v___x_4556_; lean_object* v_fst_4557_; lean_object* v_snd_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4570_; 
v_fst_4554_ = lean_ctor_get(v_b_4552_, 0);
lean_inc(v_fst_4554_);
v_snd_4555_ = lean_ctor_get(v_b_4552_, 1);
lean_inc(v_snd_4555_);
lean_dec_ref(v_b_4552_);
v___x_4556_ = lean_array_uget(v_as_4549_, v_i_4550_);
v_fst_4557_ = lean_ctor_get(v___x_4556_, 0);
v_snd_4558_ = lean_ctor_get(v___x_4556_, 1);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4560_ = v___x_4556_;
v_isShared_4561_ = v_isSharedCheck_4570_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_snd_4558_);
lean_inc(v_fst_4557_);
lean_dec(v___x_4556_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4570_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4565_; 
v___x_4562_ = lean_array_push(v_fst_4554_, v_fst_4557_);
v___x_4563_ = lean_array_push(v_snd_4555_, v_snd_4558_);
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 1, v___x_4563_);
lean_ctor_set(v___x_4560_, 0, v___x_4562_);
v___x_4565_ = v___x_4560_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v___x_4562_);
lean_ctor_set(v_reuseFailAlloc_4569_, 1, v___x_4563_);
v___x_4565_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
size_t v___x_4566_; size_t v___x_4567_; 
v___x_4566_ = ((size_t)1ULL);
v___x_4567_ = lean_usize_add(v_i_4550_, v___x_4566_);
v_i_4550_ = v___x_4567_;
v_b_4552_ = v___x_4565_;
goto _start;
}
}
}
else
{
return v_b_4552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg___boxed(lean_object* v_as_4571_, lean_object* v_i_4572_, lean_object* v_stop_4573_, lean_object* v_b_4574_){
_start:
{
size_t v_i_boxed_4575_; size_t v_stop_boxed_4576_; lean_object* v_res_4577_; 
v_i_boxed_4575_ = lean_unbox_usize(v_i_4572_);
lean_dec(v_i_4572_);
v_stop_boxed_4576_ = lean_unbox_usize(v_stop_4573_);
lean_dec(v_stop_4573_);
v_res_4577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4571_, v_i_boxed_4575_, v_stop_boxed_4576_, v_b_4574_);
lean_dec_ref(v_as_4571_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg(lean_object* v_as_4578_){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; uint8_t v___x_4582_; 
v___x_4579_ = lean_unsigned_to_nat(0u);
v___x_4580_ = ((lean_object*)(l_Array_partition___redArg___closed__0));
v___x_4581_ = lean_array_get_size(v_as_4578_);
v___x_4582_ = lean_nat_dec_lt(v___x_4579_, v___x_4581_);
if (v___x_4582_ == 0)
{
return v___x_4580_;
}
else
{
uint8_t v___x_4583_; 
v___x_4583_ = lean_nat_dec_le(v___x_4581_, v___x_4581_);
if (v___x_4583_ == 0)
{
if (v___x_4582_ == 0)
{
return v___x_4580_;
}
else
{
size_t v___x_4584_; size_t v___x_4585_; lean_object* v___x_4586_; 
v___x_4584_ = ((size_t)0ULL);
v___x_4585_ = lean_usize_of_nat(v___x_4581_);
v___x_4586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4578_, v___x_4584_, v___x_4585_, v___x_4580_);
return v___x_4586_;
}
}
else
{
size_t v___x_4587_; size_t v___x_4588_; lean_object* v___x_4589_; 
v___x_4587_ = ((size_t)0ULL);
v___x_4588_ = lean_usize_of_nat(v___x_4581_);
v___x_4589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4578_, v___x_4587_, v___x_4588_, v___x_4580_);
return v___x_4589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg___boxed(lean_object* v_as_4590_){
_start:
{
lean_object* v_res_4591_; 
v_res_4591_ = l_Array_unzip___redArg(v_as_4590_);
lean_dec_ref(v_as_4590_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip(lean_object* v_00_u03b1_4592_, lean_object* v_00_u03b2_4593_, lean_object* v_as_4594_){
_start:
{
lean_object* v___x_4595_; 
v___x_4595_ = l_Array_unzip___redArg(v_as_4594_);
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___boxed(lean_object* v_00_u03b1_4596_, lean_object* v_00_u03b2_4597_, lean_object* v_as_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = l_Array_unzip(v_00_u03b1_4596_, v_00_u03b2_4597_, v_as_4598_);
lean_dec_ref(v_as_4598_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(lean_object* v_00_u03b1_4600_, lean_object* v_00_u03b2_4601_, lean_object* v_as_4602_, size_t v_i_4603_, size_t v_stop_4604_, lean_object* v_b_4605_){
_start:
{
lean_object* v___x_4606_; 
v___x_4606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4602_, v_i_4603_, v_stop_4604_, v_b_4605_);
return v___x_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___boxed(lean_object* v_00_u03b1_4607_, lean_object* v_00_u03b2_4608_, lean_object* v_as_4609_, lean_object* v_i_4610_, lean_object* v_stop_4611_, lean_object* v_b_4612_){
_start:
{
size_t v_i_boxed_4613_; size_t v_stop_boxed_4614_; lean_object* v_res_4615_; 
v_i_boxed_4613_ = lean_unbox_usize(v_i_4610_);
lean_dec(v_i_4610_);
v_stop_boxed_4614_ = lean_unbox_usize(v_stop_4611_);
lean_dec(v_stop_4611_);
v_res_4615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(v_00_u03b1_4607_, v_00_u03b2_4608_, v_as_4609_, v_i_boxed_4613_, v_stop_boxed_4614_, v_b_4612_);
lean_dec_ref(v_as_4609_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_Array_replace___redArg(lean_object* v_inst_4616_, lean_object* v_xs_4617_, lean_object* v_a_4618_, lean_object* v_b_4619_){
_start:
{
lean_object* v___x_4620_; 
v___x_4620_ = l_Array_finIdxOf_x3f___redArg(v_inst_4616_, v_xs_4617_, v_a_4618_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_dec(v_b_4619_);
return v_xs_4617_;
}
else
{
lean_object* v_val_4621_; lean_object* v___x_4622_; 
v_val_4621_ = lean_ctor_get(v___x_4620_, 0);
lean_inc(v_val_4621_);
lean_dec_ref_known(v___x_4620_, 1);
v___x_4622_ = lean_array_fset(v_xs_4617_, v_val_4621_, v_b_4619_);
lean_dec(v_val_4621_);
return v___x_4622_;
}
}
}
LEAN_EXPORT lean_object* l_Array_replace(lean_object* v_00_u03b1_4623_, lean_object* v_inst_4624_, lean_object* v_xs_4625_, lean_object* v_a_4626_, lean_object* v_b_4627_){
_start:
{
lean_object* v___x_4628_; 
v___x_4628_ = l_Array_replace___redArg(v_inst_4624_, v_xs_4625_, v_a_4626_, v_b_4627_);
return v___x_4628_;
}
}
LEAN_EXPORT lean_object* l_Array_instLT(lean_object* v_00_u03b1_4629_, lean_object* v_inst_4630_){
_start:
{
lean_object* v___x_4631_; 
v___x_4631_ = lean_box(0);
return v___x_4631_;
}
}
LEAN_EXPORT lean_object* l_Array_instLE(lean_object* v_00_u03b1_4632_, lean_object* v_inst_4633_){
_start:
{
lean_object* v___x_4634_; 
v___x_4634_ = lean_box(0);
return v___x_4634_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg(lean_object* v_n_4635_, lean_object* v_a_4636_, lean_object* v_xs_4637_){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; 
v___x_4638_ = lean_array_get_size(v_xs_4637_);
v___x_4639_ = lean_nat_sub(v_n_4635_, v___x_4638_);
v___x_4640_ = lean_mk_array(v___x_4639_, v_a_4636_);
v___x_4641_ = l_Array_append___redArg(v___x_4640_, v_xs_4637_);
return v___x_4641_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg___boxed(lean_object* v_n_4642_, lean_object* v_a_4643_, lean_object* v_xs_4644_){
_start:
{
lean_object* v_res_4645_; 
v_res_4645_ = l_Array_leftpad___redArg(v_n_4642_, v_a_4643_, v_xs_4644_);
lean_dec_ref(v_xs_4644_);
lean_dec(v_n_4642_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad(lean_object* v_00_u03b1_4646_, lean_object* v_n_4647_, lean_object* v_a_4648_, lean_object* v_xs_4649_){
_start:
{
lean_object* v___x_4650_; 
v___x_4650_ = l_Array_leftpad___redArg(v_n_4647_, v_a_4648_, v_xs_4649_);
return v___x_4650_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___boxed(lean_object* v_00_u03b1_4651_, lean_object* v_n_4652_, lean_object* v_a_4653_, lean_object* v_xs_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_Array_leftpad(v_00_u03b1_4651_, v_n_4652_, v_a_4653_, v_xs_4654_);
lean_dec_ref(v_xs_4654_);
lean_dec(v_n_4652_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg(lean_object* v_n_4656_, lean_object* v_a_4657_, lean_object* v_xs_4658_){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4659_ = lean_array_get_size(v_xs_4658_);
v___x_4660_ = lean_nat_sub(v_n_4656_, v___x_4659_);
v___x_4661_ = lean_mk_array(v___x_4660_, v_a_4657_);
v___x_4662_ = l_Array_append___redArg(v_xs_4658_, v___x_4661_);
lean_dec_ref(v___x_4661_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg___boxed(lean_object* v_n_4663_, lean_object* v_a_4664_, lean_object* v_xs_4665_){
_start:
{
lean_object* v_res_4666_; 
v_res_4666_ = l_Array_rightpad___redArg(v_n_4663_, v_a_4664_, v_xs_4665_);
lean_dec(v_n_4663_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad(lean_object* v_00_u03b1_4667_, lean_object* v_n_4668_, lean_object* v_a_4669_, lean_object* v_xs_4670_){
_start:
{
lean_object* v___x_4671_; 
v___x_4671_ = l_Array_rightpad___redArg(v_n_4668_, v_a_4669_, v_xs_4670_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___boxed(lean_object* v_00_u03b1_4672_, lean_object* v_n_4673_, lean_object* v_a_4674_, lean_object* v_xs_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l_Array_rightpad(v_00_u03b1_4672_, v_n_4673_, v_a_4674_, v_xs_4675_);
lean_dec(v_n_4673_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0(lean_object* v_x_4677_){
_start:
{
lean_inc(v_x_4677_);
return v_x_4677_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0___boxed(lean_object* v_x_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l_Array_reduceOption___redArg___lam__0(v_x_4678_);
lean_dec(v_x_4678_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg(lean_object* v_as_4681_){
_start:
{
lean_object* v___f_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
v___f_4682_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4683_ = lean_unsigned_to_nat(0u);
v___x_4684_ = lean_array_get_size(v_as_4681_);
v___x_4685_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4686_ = l_Array_filterMapM___redArg(v___x_4685_, v___f_4682_, v_as_4681_, v___x_4683_, v___x_4684_);
return v___x_4686_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption(lean_object* v_00_u03b1_4687_, lean_object* v_as_4688_){
_start:
{
lean_object* v___f_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___f_4689_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4690_ = lean_unsigned_to_nat(0u);
v___x_4691_ = lean_array_get_size(v_as_4688_);
v___x_4692_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4693_ = l_Array_filterMapM___redArg(v___x_4692_, v___f_4689_, v_as_4688_, v___x_4690_, v___x_4691_);
return v___x_4693_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg___lam__0(lean_object* v_inst_4694_, lean_object* v_x1_4695_, lean_object* v_x2_4696_){
_start:
{
lean_object* v_fst_4697_; lean_object* v_snd_4698_; lean_object* v___x_4699_; uint8_t v___x_4700_; 
v_fst_4697_ = lean_ctor_get(v_x1_4695_, 0);
v_snd_4698_ = lean_ctor_get(v_x1_4695_, 1);
lean_inc(v_fst_4697_);
lean_inc(v_x2_4696_);
v___x_4699_ = lean_apply_2(v_inst_4694_, v_x2_4696_, v_fst_4697_);
v___x_4700_ = lean_unbox(v___x_4699_);
if (v___x_4700_ == 0)
{
lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4708_; 
lean_inc(v_snd_4698_);
lean_inc(v_fst_4697_);
v_isSharedCheck_4708_ = !lean_is_exclusive(v_x1_4695_);
if (v_isSharedCheck_4708_ == 0)
{
lean_object* v_unused_4709_; lean_object* v_unused_4710_; 
v_unused_4709_ = lean_ctor_get(v_x1_4695_, 1);
lean_dec(v_unused_4709_);
v_unused_4710_ = lean_ctor_get(v_x1_4695_, 0);
lean_dec(v_unused_4710_);
v___x_4702_ = v_x1_4695_;
v_isShared_4703_ = v_isSharedCheck_4708_;
goto v_resetjp_4701_;
}
else
{
lean_dec(v_x1_4695_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4708_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4704_; lean_object* v___x_4706_; 
v___x_4704_ = lean_array_push(v_snd_4698_, v_fst_4697_);
if (v_isShared_4703_ == 0)
{
lean_ctor_set(v___x_4702_, 1, v___x_4704_);
lean_ctor_set(v___x_4702_, 0, v_x2_4696_);
v___x_4706_ = v___x_4702_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_x2_4696_);
lean_ctor_set(v_reuseFailAlloc_4707_, 1, v___x_4704_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
else
{
lean_dec(v_x2_4696_);
return v_x1_4695_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg(lean_object* v_inst_4711_, lean_object* v_as_4712_){
_start:
{
lean_object* v___y_4714_; lean_object* v___x_4718_; lean_object* v___x_4719_; uint8_t v___x_4720_; 
v___x_4718_ = lean_unsigned_to_nat(0u);
v___x_4719_ = lean_array_get_size(v_as_4712_);
v___x_4720_ = lean_nat_dec_lt(v___x_4718_, v___x_4719_);
if (v___x_4720_ == 0)
{
lean_object* v___x_4721_; 
lean_dec_ref(v_as_4712_);
lean_dec_ref(v_inst_4711_);
v___x_4721_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
return v___x_4721_;
}
else
{
lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; 
v___x_4722_ = lean_array_fget_borrowed(v_as_4712_, v___x_4718_);
v___x_4723_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4724_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
if (v___x_4720_ == 0)
{
lean_object* v___x_4725_; 
lean_inc(v___x_4722_);
lean_dec_ref(v_as_4712_);
lean_dec_ref(v_inst_4711_);
v___x_4725_ = lean_array_push(v___x_4723_, v___x_4722_);
return v___x_4725_;
}
else
{
lean_object* v___f_4726_; lean_object* v___x_4727_; uint8_t v___x_4728_; 
v___f_4726_ = lean_alloc_closure((void*)(l_Array_eraseReps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4726_, 0, v_inst_4711_);
lean_inc(v___x_4722_);
v___x_4727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4722_);
lean_ctor_set(v___x_4727_, 1, v___x_4723_);
v___x_4728_ = lean_nat_dec_le(v___x_4719_, v___x_4719_);
if (v___x_4728_ == 0)
{
if (v___x_4720_ == 0)
{
lean_object* v___x_4729_; 
lean_inc(v___x_4722_);
lean_dec_ref_known(v___x_4727_, 2);
lean_dec_ref(v___f_4726_);
lean_dec_ref(v_as_4712_);
v___x_4729_ = lean_array_push(v___x_4723_, v___x_4722_);
return v___x_4729_;
}
else
{
size_t v___x_4730_; size_t v___x_4731_; lean_object* v___x_4732_; 
v___x_4730_ = ((size_t)0ULL);
v___x_4731_ = lean_usize_of_nat(v___x_4719_);
v___x_4732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4724_, v___f_4726_, v_as_4712_, v___x_4730_, v___x_4731_, v___x_4727_);
v___y_4714_ = v___x_4732_;
goto v___jp_4713_;
}
}
else
{
size_t v___x_4733_; size_t v___x_4734_; lean_object* v___x_4735_; 
v___x_4733_ = ((size_t)0ULL);
v___x_4734_ = lean_usize_of_nat(v___x_4719_);
v___x_4735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4724_, v___f_4726_, v_as_4712_, v___x_4733_, v___x_4734_, v___x_4727_);
v___y_4714_ = v___x_4735_;
goto v___jp_4713_;
}
}
}
v___jp_4713_:
{
lean_object* v_fst_4715_; lean_object* v_snd_4716_; lean_object* v___x_4717_; 
v_fst_4715_ = lean_ctor_get(v___y_4714_, 0);
lean_inc(v_fst_4715_);
v_snd_4716_ = lean_ctor_get(v___y_4714_, 1);
lean_inc(v_snd_4716_);
lean_dec_ref(v___y_4714_);
v___x_4717_ = lean_array_push(v_snd_4716_, v_fst_4715_);
return v___x_4717_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps(lean_object* v_00_u03b1_4736_, lean_object* v_inst_4737_, lean_object* v_as_4738_){
_start:
{
lean_object* v___x_4739_; 
v___x_4739_ = l_Array_eraseReps___redArg(v_inst_4737_, v_as_4738_);
return v___x_4739_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(lean_object* v_inst_4740_, lean_object* v_as_4741_, lean_object* v_a_4742_, lean_object* v_x_4743_){
_start:
{
lean_object* v_zero_4744_; uint8_t v_isZero_4745_; 
v_zero_4744_ = lean_unsigned_to_nat(0u);
v_isZero_4745_ = lean_nat_dec_eq(v_x_4743_, v_zero_4744_);
if (v_isZero_4745_ == 1)
{
lean_dec(v_x_4743_);
lean_dec(v_a_4742_);
lean_dec_ref(v_inst_4740_);
return v_isZero_4745_;
}
else
{
lean_object* v_one_4746_; lean_object* v_n_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; uint8_t v___x_4750_; 
v_one_4746_ = lean_unsigned_to_nat(1u);
v_n_4747_ = lean_nat_sub(v_x_4743_, v_one_4746_);
lean_dec(v_x_4743_);
v___x_4748_ = lean_array_fget_borrowed(v_as_4741_, v_n_4747_);
lean_inc_ref(v_inst_4740_);
lean_inc(v___x_4748_);
lean_inc(v_a_4742_);
v___x_4749_ = lean_apply_2(v_inst_4740_, v_a_4742_, v___x_4748_);
v___x_4750_ = lean_unbox(v___x_4749_);
if (v___x_4750_ == 0)
{
v_x_4743_ = v_n_4747_;
goto _start;
}
else
{
lean_dec(v_n_4747_);
lean_dec(v_a_4742_);
lean_dec_ref(v_inst_4740_);
return v_isZero_4745_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg___boxed(lean_object* v_inst_4752_, lean_object* v_as_4753_, lean_object* v_a_4754_, lean_object* v_x_4755_){
_start:
{
uint8_t v_res_4756_; lean_object* v_r_4757_; 
v_res_4756_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4752_, v_as_4753_, v_a_4754_, v_x_4755_);
lean_dec_ref(v_as_4753_);
v_r_4757_ = lean_box(v_res_4756_);
return v_r_4757_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(lean_object* v_00_u03b1_4758_, lean_object* v_inst_4759_, lean_object* v_as_4760_, lean_object* v_a_4761_, lean_object* v_x_4762_, lean_object* v_x_4763_){
_start:
{
uint8_t v___x_4764_; 
v___x_4764_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4759_, v_as_4760_, v_a_4761_, v_x_4762_);
return v___x_4764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___boxed(lean_object* v_00_u03b1_4765_, lean_object* v_inst_4766_, lean_object* v_as_4767_, lean_object* v_a_4768_, lean_object* v_x_4769_, lean_object* v_x_4770_){
_start:
{
uint8_t v_res_4771_; lean_object* v_r_4772_; 
v_res_4771_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(v_00_u03b1_4765_, v_inst_4766_, v_as_4767_, v_a_4768_, v_x_4769_, v_x_4770_);
lean_dec_ref(v_as_4767_);
v_r_4772_ = lean_box(v_res_4771_);
return v_r_4772_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(lean_object* v_inst_4773_, lean_object* v_as_4774_, lean_object* v_i_4775_){
_start:
{
lean_object* v___x_4776_; uint8_t v___x_4777_; 
v___x_4776_ = lean_array_get_size(v_as_4774_);
v___x_4777_ = lean_nat_dec_lt(v_i_4775_, v___x_4776_);
if (v___x_4777_ == 0)
{
uint8_t v___x_4778_; 
lean_dec(v_i_4775_);
lean_dec_ref(v_inst_4773_);
v___x_4778_ = 1;
return v___x_4778_;
}
else
{
lean_object* v___x_4779_; uint8_t v___x_4780_; 
v___x_4779_ = lean_array_fget_borrowed(v_as_4774_, v_i_4775_);
lean_inc(v_i_4775_);
lean_inc(v___x_4779_);
lean_inc_ref(v_inst_4773_);
v___x_4780_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4773_, v_as_4774_, v___x_4779_, v_i_4775_);
if (v___x_4780_ == 0)
{
lean_dec(v_i_4775_);
lean_dec_ref(v_inst_4773_);
return v___x_4780_;
}
else
{
lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4781_ = lean_unsigned_to_nat(1u);
v___x_4782_ = lean_nat_add(v_i_4775_, v___x_4781_);
lean_dec(v_i_4775_);
v_i_4775_ = v___x_4782_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg___boxed(lean_object* v_inst_4784_, lean_object* v_as_4785_, lean_object* v_i_4786_){
_start:
{
uint8_t v_res_4787_; lean_object* v_r_4788_; 
v_res_4787_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4784_, v_as_4785_, v_i_4786_);
lean_dec_ref(v_as_4785_);
v_r_4788_ = lean_box(v_res_4787_);
return v_r_4788_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux(lean_object* v_00_u03b1_4789_, lean_object* v_inst_4790_, lean_object* v_as_4791_, lean_object* v_i_4792_){
_start:
{
uint8_t v___x_4793_; 
v___x_4793_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4790_, v_as_4791_, v_i_4792_);
return v___x_4793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___boxed(lean_object* v_00_u03b1_4794_, lean_object* v_inst_4795_, lean_object* v_as_4796_, lean_object* v_i_4797_){
_start:
{
uint8_t v_res_4798_; lean_object* v_r_4799_; 
v_res_4798_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux(v_00_u03b1_4794_, v_inst_4795_, v_as_4796_, v_i_4797_);
lean_dec_ref(v_as_4796_);
v_r_4799_ = lean_box(v_res_4798_);
return v_r_4799_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___redArg(lean_object* v_inst_4800_, lean_object* v_as_4801_){
_start:
{
lean_object* v___x_4802_; uint8_t v___x_4803_; 
v___x_4802_ = lean_unsigned_to_nat(0u);
v___x_4803_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4800_, v_as_4801_, v___x_4802_);
return v___x_4803_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___redArg___boxed(lean_object* v_inst_4804_, lean_object* v_as_4805_){
_start:
{
uint8_t v_res_4806_; lean_object* v_r_4807_; 
v_res_4806_ = l_Array_allDiff___redArg(v_inst_4804_, v_as_4805_);
lean_dec_ref(v_as_4805_);
v_r_4807_ = lean_box(v_res_4806_);
return v_r_4807_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff(lean_object* v_00_u03b1_4808_, lean_object* v_inst_4809_, lean_object* v_as_4810_){
_start:
{
uint8_t v___x_4811_; 
v___x_4811_ = l_Array_allDiff___redArg(v_inst_4809_, v_as_4810_);
return v___x_4811_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___boxed(lean_object* v_00_u03b1_4812_, lean_object* v_inst_4813_, lean_object* v_as_4814_){
_start:
{
uint8_t v_res_4815_; lean_object* v_r_4816_; 
v_res_4815_ = l_Array_allDiff(v_00_u03b1_4812_, v_inst_4813_, v_as_4814_);
lean_dec_ref(v_as_4814_);
v_r_4816_ = lean_box(v_res_4815_);
return v_r_4816_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0(uint8_t v___x_4817_, lean_object* v_x1_4818_, lean_object* v_x2_4819_){
_start:
{
lean_object* v_fst_4820_; uint8_t v___x_4821_; 
v_fst_4820_ = lean_ctor_get(v_x1_4818_, 0);
v___x_4821_ = lean_unbox(v_fst_4820_);
if (v___x_4821_ == 0)
{
lean_object* v_snd_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4830_; 
lean_dec(v_x2_4819_);
v_snd_4822_ = lean_ctor_get(v_x1_4818_, 1);
v_isSharedCheck_4830_ = !lean_is_exclusive(v_x1_4818_);
if (v_isSharedCheck_4830_ == 0)
{
lean_object* v_unused_4831_; 
v_unused_4831_ = lean_ctor_get(v_x1_4818_, 0);
lean_dec(v_unused_4831_);
v___x_4824_ = v_x1_4818_;
v_isShared_4825_ = v_isSharedCheck_4830_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_snd_4822_);
lean_dec(v_x1_4818_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4830_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4826_; lean_object* v___x_4828_; 
v___x_4826_ = lean_box(v___x_4817_);
if (v_isShared_4825_ == 0)
{
lean_ctor_set(v___x_4824_, 0, v___x_4826_);
v___x_4828_ = v___x_4824_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4826_);
lean_ctor_set(v_reuseFailAlloc_4829_, 1, v_snd_4822_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
else
{
lean_object* v_snd_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4842_; 
v_snd_4832_ = lean_ctor_get(v_x1_4818_, 1);
v_isSharedCheck_4842_ = !lean_is_exclusive(v_x1_4818_);
if (v_isSharedCheck_4842_ == 0)
{
lean_object* v_unused_4843_; 
v_unused_4843_ = lean_ctor_get(v_x1_4818_, 0);
lean_dec(v_unused_4843_);
v___x_4834_ = v_x1_4818_;
v_isShared_4835_ = v_isSharedCheck_4842_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_snd_4832_);
lean_dec(v_x1_4818_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4842_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
uint8_t v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4840_; 
v___x_4836_ = 0;
v___x_4837_ = lean_array_push(v_snd_4832_, v_x2_4819_);
v___x_4838_ = lean_box(v___x_4836_);
if (v_isShared_4835_ == 0)
{
lean_ctor_set(v___x_4834_, 1, v___x_4837_);
lean_ctor_set(v___x_4834_, 0, v___x_4838_);
v___x_4840_ = v___x_4834_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4838_);
lean_ctor_set(v_reuseFailAlloc_4841_, 1, v___x_4837_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0___boxed(lean_object* v___x_4844_, lean_object* v_x1_4845_, lean_object* v_x2_4846_){
_start:
{
uint8_t v___x_139__boxed_4847_; lean_object* v_res_4848_; 
v___x_139__boxed_4847_ = lean_unbox(v___x_4844_);
v_res_4848_ = l_Array_getEvenElems___redArg___lam__0(v___x_139__boxed_4847_, v_x1_4845_, v_x2_4846_);
return v_res_4848_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg(lean_object* v_as_4849_){
_start:
{
lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; uint8_t v___x_4854_; 
v___x_4850_ = lean_unsigned_to_nat(0u);
v___x_4851_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_4852_ = lean_array_get_size(v_as_4849_);
v___x_4853_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4854_ = lean_nat_dec_lt(v___x_4850_, v___x_4852_);
if (v___x_4854_ == 0)
{
lean_dec_ref(v_as_4849_);
return v___x_4851_;
}
else
{
lean_object* v___x_4855_; lean_object* v___f_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; uint8_t v___x_4859_; 
v___x_4855_ = lean_box(v___x_4854_);
v___f_4856_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4856_, 0, v___x_4855_);
v___x_4857_ = lean_box(v___x_4854_);
v___x_4858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4857_);
lean_ctor_set(v___x_4858_, 1, v___x_4851_);
v___x_4859_ = lean_nat_dec_le(v___x_4852_, v___x_4852_);
if (v___x_4859_ == 0)
{
if (v___x_4854_ == 0)
{
lean_dec_ref_known(v___x_4858_, 2);
lean_dec_ref(v___f_4856_);
lean_dec_ref(v_as_4849_);
return v___x_4851_;
}
else
{
size_t v___x_4860_; size_t v___x_4861_; lean_object* v___x_4862_; lean_object* v_snd_4863_; 
v___x_4860_ = ((size_t)0ULL);
v___x_4861_ = lean_usize_of_nat(v___x_4852_);
v___x_4862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4853_, v___f_4856_, v_as_4849_, v___x_4860_, v___x_4861_, v___x_4858_);
v_snd_4863_ = lean_ctor_get(v___x_4862_, 1);
lean_inc(v_snd_4863_);
lean_dec(v___x_4862_);
return v_snd_4863_;
}
}
else
{
size_t v___x_4864_; size_t v___x_4865_; lean_object* v___x_4866_; lean_object* v_snd_4867_; 
v___x_4864_ = ((size_t)0ULL);
v___x_4865_ = lean_usize_of_nat(v___x_4852_);
v___x_4866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4853_, v___f_4856_, v_as_4849_, v___x_4864_, v___x_4865_, v___x_4858_);
v_snd_4867_ = lean_ctor_get(v___x_4866_, 1);
lean_inc(v_snd_4867_);
lean_dec(v___x_4866_);
return v_snd_4867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems(lean_object* v_00_u03b1_4868_, lean_object* v_as_4869_){
_start:
{
lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; uint8_t v___x_4874_; 
v___x_4870_ = lean_unsigned_to_nat(0u);
v___x_4871_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_4872_ = lean_array_get_size(v_as_4869_);
v___x_4873_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4874_ = lean_nat_dec_lt(v___x_4870_, v___x_4872_);
if (v___x_4874_ == 0)
{
lean_dec_ref(v_as_4869_);
return v___x_4871_;
}
else
{
lean_object* v___x_4875_; lean_object* v___f_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; uint8_t v___x_4879_; 
v___x_4875_ = lean_box(v___x_4874_);
v___f_4876_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4876_, 0, v___x_4875_);
v___x_4877_ = lean_box(v___x_4874_);
v___x_4878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
lean_ctor_set(v___x_4878_, 1, v___x_4871_);
v___x_4879_ = lean_nat_dec_le(v___x_4872_, v___x_4872_);
if (v___x_4879_ == 0)
{
if (v___x_4874_ == 0)
{
lean_dec_ref_known(v___x_4878_, 2);
lean_dec_ref(v___f_4876_);
lean_dec_ref(v_as_4869_);
return v___x_4871_;
}
else
{
size_t v___x_4880_; size_t v___x_4881_; lean_object* v___x_4882_; lean_object* v_snd_4883_; 
v___x_4880_ = ((size_t)0ULL);
v___x_4881_ = lean_usize_of_nat(v___x_4872_);
v___x_4882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4873_, v___f_4876_, v_as_4869_, v___x_4880_, v___x_4881_, v___x_4878_);
v_snd_4883_ = lean_ctor_get(v___x_4882_, 1);
lean_inc(v_snd_4883_);
lean_dec(v___x_4882_);
return v_snd_4883_;
}
}
else
{
size_t v___x_4884_; size_t v___x_4885_; lean_object* v___x_4886_; lean_object* v_snd_4887_; 
v___x_4884_ = ((size_t)0ULL);
v___x_4885_ = lean_usize_of_nat(v___x_4872_);
v___x_4886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4873_, v___f_4876_, v_as_4869_, v___x_4884_, v___x_4885_, v___x_4878_);
v_snd_4887_ = lean_ctor_get(v___x_4886_, 1);
lean_inc(v_snd_4887_);
lean_dec(v___x_4886_);
return v_snd_4887_;
}
}
}
}
static lean_object* _init_l_Array_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_4893_; lean_object* v___x_4894_; 
v___x_4893_ = ((lean_object*)(l_term_x23_x5b___x2c_x5d___closed__4));
v___x_4894_ = lean_string_length(v___x_4893_);
return v___x_4894_;
}
}
static lean_object* _init_l_Array_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_4895_; lean_object* v___x_4896_; 
v___x_4895_ = lean_obj_once(&l_Array_repr___redArg___closed__2, &l_Array_repr___redArg___closed__2_once, _init_l_Array_repr___redArg___closed__2);
v___x_4896_ = lean_nat_to_int(v___x_4895_);
return v___x_4896_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___redArg(lean_object* v_inst_4904_, lean_object* v_xs_4905_){
_start:
{
lean_object* v___x_4906_; lean_object* v___x_4907_; uint8_t v___x_4908_; 
v___x_4906_ = lean_array_get_size(v_xs_4905_);
v___x_4907_ = lean_unsigned_to_nat(0u);
v___x_4908_ = lean_nat_dec_eq(v___x_4906_, v___x_4907_);
if (v___x_4908_ == 0)
{
lean_object* v_x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; 
v_x_4909_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_4909_, 0, lean_box(0));
lean_closure_set(v_x_4909_, 1, v_inst_4904_);
v___x_4910_ = lean_array_to_list(v_xs_4905_);
v___x_4911_ = ((lean_object*)(l_Array_repr___redArg___closed__1));
v___x_4912_ = l_Std_Format_joinSep___redArg(v_x_4909_, v___x_4910_, v___x_4911_);
v___x_4913_ = lean_obj_once(&l_Array_repr___redArg___closed__3, &l_Array_repr___redArg___closed__3_once, _init_l_Array_repr___redArg___closed__3);
v___x_4914_ = ((lean_object*)(l_Array_repr___redArg___closed__4));
v___x_4915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4914_);
lean_ctor_set(v___x_4915_, 1, v___x_4912_);
v___x_4916_ = ((lean_object*)(l_Array_repr___redArg___closed__5));
v___x_4917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4917_, 0, v___x_4915_);
lean_ctor_set(v___x_4917_, 1, v___x_4916_);
v___x_4918_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4913_);
lean_ctor_set(v___x_4918_, 1, v___x_4917_);
v___x_4919_ = l_Std_Format_fill(v___x_4918_);
return v___x_4919_;
}
else
{
lean_object* v___x_4920_; 
lean_dec_ref(v_xs_4905_);
lean_dec_ref(v_inst_4904_);
v___x_4920_ = ((lean_object*)(l_Array_repr___redArg___closed__7));
return v___x_4920_;
}
}
}
LEAN_EXPORT lean_object* l_Array_repr(lean_object* v_00_u03b1_4921_, lean_object* v_inst_4922_, lean_object* v_xs_4923_){
_start:
{
lean_object* v___x_4924_; 
v___x_4924_ = l_Array_repr___redArg(v_inst_4922_, v_xs_4923_);
return v___x_4924_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0(lean_object* v_inst_4925_, lean_object* v_xs_4926_, lean_object* v_x_4927_){
_start:
{
lean_object* v___x_4928_; 
v___x_4928_ = l_Array_repr___redArg(v_inst_4925_, v_xs_4926_);
return v___x_4928_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object* v_inst_4929_, lean_object* v_xs_4930_, lean_object* v_x_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l_Array_instRepr___redArg___lam__0(v_inst_4929_, v_xs_4930_, v_x_4931_);
lean_dec(v_x_4931_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg(lean_object* v_inst_4933_){
_start:
{
lean_object* v___f_4934_; 
v___f_4934_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4934_, 0, v_inst_4933_);
return v___f_4934_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr(lean_object* v_00_u03b1_4935_, lean_object* v_inst_4936_){
_start:
{
lean_object* v___f_4937_; 
v___f_4937_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4937_, 0, v_inst_4936_);
return v___f_4937_;
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
