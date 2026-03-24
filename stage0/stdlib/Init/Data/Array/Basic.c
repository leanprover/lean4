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
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_repr(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_appendCore___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_findSome_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Array_partition___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_partition___redArg___closed__0;
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
lean_dec_ref(v_a_79_);
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
lean_inc(v_quotContext_85_);
v_currMacroScope_86_ = lean_ctor_get(v_a_79_, 2);
lean_inc(v_currMacroScope_86_);
v_ref_87_ = lean_ctor_get(v_a_79_, 5);
lean_inc(v_ref_87_);
lean_dec_ref(v_a_79_);
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = l_Lean_Syntax_getArg(v_x_78_, v___x_88_);
lean_dec(v_x_78_);
v___x_90_ = l_Lean_Syntax_getArgs(v___x_89_);
lean_dec(v___x_89_);
v___x_91_ = 0;
v___x_92_ = l_Lean_SourceInfo_fromRef(v_ref_87_, v___x_91_);
lean_dec(v_ref_87_);
v___x_93_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4));
v___x_94_ = lean_obj_once(&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6, &l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6_once, _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6);
v___x_95_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9));
v___x_96_ = l_Lean_addMacroScope(v_quotContext_85_, v___x_95_, v_currMacroScope_86_);
v___x_97_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__11));
lean_inc(v___x_92_);
v___x_98_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_98_, 0, v___x_92_);
lean_ctor_set(v___x_98_, 1, v___x_94_);
lean_ctor_set(v___x_98_, 2, v___x_96_);
lean_ctor_set(v___x_98_, 3, v___x_97_);
v___x_99_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13));
v___x_100_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__15));
v___x_101_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__16));
lean_inc(v___x_92_);
v___x_102_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_92_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = lean_obj_once(&l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17, &l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17_once, _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17);
v___x_104_ = l_Array_appendCore___redArg(v___x_103_, v___x_90_);
lean_dec_ref(v___x_90_);
lean_inc(v___x_92_);
v___x_105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_105_, 0, v___x_92_);
lean_ctor_set(v___x_105_, 1, v___x_99_);
lean_ctor_set(v___x_105_, 2, v___x_104_);
v___x_106_ = ((lean_object*)(l_term_x23_x5b___x2c_x5d___closed__17));
lean_inc(v___x_92_);
v___x_107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_92_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
lean_inc(v___x_92_);
v___x_108_ = l_Lean_Syntax_node3(v___x_92_, v___x_100_, v___x_102_, v___x_105_, v___x_107_);
lean_inc(v___x_92_);
v___x_109_ = l_Lean_Syntax_node1(v___x_92_, v___x_99_, v___x_108_);
v___x_110_ = l_Lean_Syntax_node2(v___x_92_, v___x_93_, v___x_98_, v___x_109_);
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_a_80_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter___redArg(lean_object* v_x_112_, lean_object* v_x_113_, lean_object* v_h__1_114_, lean_object* v_h__2_115_){
_start:
{
if (lean_obj_tag(v_x_112_) == 0)
{
lean_object* v___x_116_; 
lean_dec(v_h__2_115_);
v___x_116_ = lean_apply_1(v_h__1_114_, v_x_113_);
return v___x_116_;
}
else
{
lean_object* v_head_117_; lean_object* v_tail_118_; lean_object* v___x_119_; 
lean_dec(v_h__1_114_);
v_head_117_ = lean_ctor_get(v_x_112_, 0);
lean_inc(v_head_117_);
v_tail_118_ = lean_ctor_get(v_x_112_, 1);
lean_inc(v_tail_118_);
lean_dec_ref(v_x_112_);
v___x_119_ = lean_apply_3(v_h__2_115_, v_head_117_, v_tail_118_, v_x_113_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter(lean_object* v_00_u03b1_120_, lean_object* v_motive_121_, lean_object* v_x_122_, lean_object* v_x_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_){
_start:
{
if (lean_obj_tag(v_x_122_) == 0)
{
lean_object* v___x_126_; 
lean_dec(v_h__2_125_);
v___x_126_ = lean_apply_1(v_h__1_124_, v_x_123_);
return v___x_126_;
}
else
{
lean_object* v_head_127_; lean_object* v_tail_128_; lean_object* v___x_129_; 
lean_dec(v_h__1_124_);
v_head_127_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_head_127_);
v_tail_128_ = lean_ctor_get(v_x_122_, 1);
lean_inc(v_tail_128_);
lean_dec_ref(v_x_122_);
v___x_129_ = lean_apply_3(v_h__2_125_, v_head_127_, v_tail_128_, v_x_123_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instMembership(lean_object* v_00_u03b1_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_box(0);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter___redArg(lean_object* v_x_132_, lean_object* v_h__1_133_, lean_object* v_h__2_134_){
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
lean_dec_ref(v_x_132_);
v___x_138_ = lean_apply_1(v_h__1_133_, v_val_137_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_139_, lean_object* v_motive_140_, lean_object* v_x_141_, lean_object* v_h__1_142_, lean_object* v_h__2_143_){
_start:
{
if (lean_obj_tag(v_x_141_) == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v_h__1_142_);
v___x_144_ = lean_box(0);
v___x_145_ = lean_apply_1(v_h__2_143_, v___x_144_);
return v___x_145_;
}
else
{
lean_object* v_val_146_; lean_object* v___x_147_; 
lean_dec(v_h__2_143_);
v_val_146_ = lean_ctor_get(v_x_141_, 0);
lean_inc(v_val_146_);
lean_dec_ref(v_x_141_);
v___x_147_ = lean_apply_1(v_h__1_142_, v_val_146_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Array_usize___boxed(lean_object* v_00_u03b1_150_, lean_object* v_xs_151_){
_start:
{
size_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = lean_array_size(v_xs_151_);
lean_dec_ref(v_xs_151_);
v_r_153_ = lean_box_usize(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT lean_object* l_Array_uget___boxed(lean_object* v_00_u03b1_158_, lean_object* v_xs_159_, lean_object* v_i_160_, lean_object* v_h_161_){
_start:
{
size_t v_i_boxed_162_; lean_object* v_res_163_; 
v_i_boxed_162_ = lean_unbox_usize(v_i_160_);
lean_dec(v_i_160_);
v_res_163_ = lean_array_uget(v_xs_159_, v_i_boxed_162_);
lean_dec_ref(v_xs_159_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Array_ugetBorrowed___boxed(lean_object* v_00_u03b1_168_, lean_object* v_xs_169_, lean_object* v_i_170_, lean_object* v_h_171_){
_start:
{
size_t v_i_boxed_172_; lean_object* v_res_173_; 
v_i_boxed_172_ = lean_unbox_usize(v_i_170_);
lean_dec(v_i_170_);
v_res_173_ = lean_array_uget_borrowed(v_xs_169_, v_i_boxed_172_);
lean_dec_ref(v_xs_169_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Array_uset___boxed(lean_object* v_00_u03b1_179_, lean_object* v_xs_180_, lean_object* v_i_181_, lean_object* v_v_182_, lean_object* v_h_183_){
_start:
{
size_t v_i_boxed_184_; lean_object* v_res_185_; 
v_i_boxed_184_ = lean_unbox_usize(v_i_181_);
lean_dec(v_i_181_);
v_res_185_ = lean_array_uset(v_xs_180_, v_i_boxed_184_, v_v_182_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Array_pop___boxed(lean_object* v_00_u03b1_188_, lean_object* v_xs_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = lean_array_pop(v_xs_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Array_replicate___boxed(lean_object* v_00_u03b1_194_, lean_object* v_n_195_, lean_object* v_v_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = lean_mk_array(v_n_195_, v_v_196_);
return v_res_197_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__9(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l_Array_swap___auto__1___closed__8));
v___x_218_ = l_Lean_mkAtom(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__10(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_obj_once(&l_Array_swap___auto__1___closed__9, &l_Array_swap___auto__1___closed__9_once, _init_l_Array_swap___auto__1___closed__9);
v___x_220_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_221_ = lean_array_push(v___x_220_, v___x_219_);
return v___x_221_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__11(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_222_ = lean_obj_once(&l_Array_swap___auto__1___closed__10, &l_Array_swap___auto__1___closed__10_once, _init_l_Array_swap___auto__1___closed__10);
v___x_223_ = ((lean_object*)(l_Array_swap___auto__1___closed__7));
v___x_224_ = lean_box(2);
v___x_225_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v___x_223_);
lean_ctor_set(v___x_225_, 2, v___x_222_);
return v___x_225_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__12(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = lean_obj_once(&l_Array_swap___auto__1___closed__11, &l_Array_swap___auto__1___closed__11_once, _init_l_Array_swap___auto__1___closed__11);
v___x_227_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_228_ = lean_array_push(v___x_227_, v___x_226_);
return v___x_228_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__13(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_229_ = lean_obj_once(&l_Array_swap___auto__1___closed__12, &l_Array_swap___auto__1___closed__12_once, _init_l_Array_swap___auto__1___closed__12);
v___x_230_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13));
v___x_231_ = lean_box(2);
v___x_232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
lean_ctor_set(v___x_232_, 2, v___x_229_);
return v___x_232_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__14(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_obj_once(&l_Array_swap___auto__1___closed__13, &l_Array_swap___auto__1___closed__13_once, _init_l_Array_swap___auto__1___closed__13);
v___x_234_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_235_ = lean_array_push(v___x_234_, v___x_233_);
return v___x_235_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__15(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_236_ = lean_obj_once(&l_Array_swap___auto__1___closed__14, &l_Array_swap___auto__1___closed__14_once, _init_l_Array_swap___auto__1___closed__14);
v___x_237_ = ((lean_object*)(l_Array_swap___auto__1___closed__5));
v___x_238_ = lean_box(2);
v___x_239_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
lean_ctor_set(v___x_239_, 2, v___x_236_);
return v___x_239_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__16(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_obj_once(&l_Array_swap___auto__1___closed__15, &l_Array_swap___auto__1___closed__15_once, _init_l_Array_swap___auto__1___closed__15);
v___x_241_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_242_ = lean_array_push(v___x_241_, v___x_240_);
return v___x_242_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__17(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_243_ = lean_obj_once(&l_Array_swap___auto__1___closed__16, &l_Array_swap___auto__1___closed__16_once, _init_l_Array_swap___auto__1___closed__16);
v___x_244_ = ((lean_object*)(l_Array_swap___auto__1___closed__2));
v___x_245_ = lean_box(2);
v___x_246_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___x_244_);
lean_ctor_set(v___x_246_, 2, v___x_243_);
return v___x_246_;
}
}
static lean_object* _init_l_Array_swap___auto__1(void){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_247_;
}
}
static lean_object* _init_l_Array_swap___auto__3(void){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Array_swap___boxed(lean_object* v_00_u03b1_255_, lean_object* v_xs_256_, lean_object* v_i_257_, lean_object* v_j_258_, lean_object* v_hi_259_, lean_object* v_hj_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = lean_array_fswap(v_xs_256_, v_i_257_, v_j_258_);
lean_dec(v_j_258_);
lean_dec(v_i_257_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Array_swapIfInBounds___boxed(lean_object* v_00_u03b1_266_, lean_object* v_xs_267_, lean_object* v_i_268_, lean_object* v_j_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = lean_array_swap(v_xs_267_, v_i_268_, v_j_269_);
lean_dec(v_j_269_);
lean_dec(v_i_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___lam__0(lean_object* v_xs_271_, size_t v_i_272_, lean_object* v_h_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_array_uget_borrowed(v_xs_271_, v_i_272_);
lean_inc(v___x_274_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___lam__0___boxed(lean_object* v_xs_275_, lean_object* v_i_276_, lean_object* v_h_277_){
_start:
{
size_t v_i_boxed_278_; lean_object* v_res_279_; 
v_i_boxed_278_ = lean_unbox_usize(v_i_276_);
lean_dec(v_i_276_);
v_res_279_ = l_Array_instGetElemUSizeLtNatToNatSize___lam__0(v_xs_275_, v_i_boxed_278_, v_h_277_);
lean_dec_ref(v_xs_275_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize(lean_object* v_00_u03b1_281_){
_start:
{
lean_object* v___f_282_; 
v___f_282_ = ((lean_object*)(l_Array_instGetElemUSizeLtNatToNatSize___closed__0));
return v___f_282_;
}
}
LEAN_EXPORT lean_object* l_Array_instEmptyCollection(lean_object* v_00_u03b1_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Array_instInhabited(lean_object* v_00_u03b1_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
return v___x_288_;
}
}
LEAN_EXPORT uint8_t l_Array_isEmpty___redArg(lean_object* v_xs_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_290_ = lean_array_get_size(v_xs_289_);
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = lean_nat_dec_eq(v___x_290_, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Array_isEmpty___redArg___boxed(lean_object* v_xs_293_){
_start:
{
uint8_t v_res_294_; lean_object* v_r_295_; 
v_res_294_ = l_Array_isEmpty___redArg(v_xs_293_);
lean_dec_ref(v_xs_293_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT uint8_t l_Array_isEmpty(lean_object* v_00_u03b1_296_, lean_object* v_xs_297_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_298_ = lean_array_get_size(v_xs_297_);
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = lean_nat_dec_eq(v___x_298_, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Array_isEmpty___boxed(lean_object* v_00_u03b1_301_, lean_object* v_xs_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Array_isEmpty(v_00_u03b1_301_, v_xs_302_);
lean_dec_ref(v_xs_302_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___redArg(lean_object* v_xs_305_, lean_object* v_ys_306_, lean_object* v_p_307_, lean_object* v_x_308_){
_start:
{
lean_object* v_zero_309_; uint8_t v_isZero_310_; 
v_zero_309_ = lean_unsigned_to_nat(0u);
v_isZero_310_ = lean_nat_dec_eq(v_x_308_, v_zero_309_);
if (v_isZero_310_ == 1)
{
lean_dec(v_x_308_);
lean_dec_ref(v_p_307_);
return v_isZero_310_;
}
else
{
lean_object* v_one_311_; lean_object* v_n_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_one_311_ = lean_unsigned_to_nat(1u);
v_n_312_ = lean_nat_sub(v_x_308_, v_one_311_);
lean_dec(v_x_308_);
v___x_313_ = lean_array_fget_borrowed(v_xs_305_, v_n_312_);
v___x_314_ = lean_array_fget_borrowed(v_ys_306_, v_n_312_);
lean_inc_ref(v_p_307_);
lean_inc(v___x_314_);
lean_inc(v___x_313_);
v___x_315_ = lean_apply_2(v_p_307_, v___x_313_, v___x_314_);
v___x_316_ = lean_unbox(v___x_315_);
if (v___x_316_ == 0)
{
uint8_t v___x_317_; 
lean_dec(v_n_312_);
lean_dec_ref(v_p_307_);
v___x_317_ = lean_unbox(v___x_315_);
return v___x_317_;
}
else
{
v_x_308_ = v_n_312_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___redArg___boxed(lean_object* v_xs_319_, lean_object* v_ys_320_, lean_object* v_p_321_, lean_object* v_x_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_Array_isEqvAux___redArg(v_xs_319_, v_ys_320_, v_p_321_, v_x_322_);
lean_dec_ref(v_ys_320_);
lean_dec_ref(v_xs_319_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux(lean_object* v_00_u03b1_325_, lean_object* v_xs_326_, lean_object* v_ys_327_, lean_object* v_hsz_328_, lean_object* v_p_329_, lean_object* v_x_330_, lean_object* v_x_331_){
_start:
{
uint8_t v___x_332_; 
v___x_332_ = l_Array_isEqvAux___redArg(v_xs_326_, v_ys_327_, v_p_329_, v_x_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___boxed(lean_object* v_00_u03b1_333_, lean_object* v_xs_334_, lean_object* v_ys_335_, lean_object* v_hsz_336_, lean_object* v_p_337_, lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l_Array_isEqvAux(v_00_u03b1_333_, v_xs_334_, v_ys_335_, v_hsz_336_, v_p_337_, v_x_338_, v_x_339_);
lean_dec_ref(v_ys_335_);
lean_dec_ref(v_xs_334_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqv___redArg(lean_object* v_xs_342_, lean_object* v_ys_343_, lean_object* v_p_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_345_ = lean_array_get_size(v_xs_342_);
v___x_346_ = lean_array_get_size(v_ys_343_);
v___x_347_ = lean_nat_dec_eq(v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
lean_dec_ref(v_p_344_);
return v___x_347_;
}
else
{
uint8_t v___x_348_; 
v___x_348_ = l_Array_isEqvAux___redArg(v_xs_342_, v_ys_343_, v_p_344_, v___x_345_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqv___redArg___boxed(lean_object* v_xs_349_, lean_object* v_ys_350_, lean_object* v_p_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l_Array_isEqv___redArg(v_xs_349_, v_ys_350_, v_p_351_);
lean_dec_ref(v_ys_350_);
lean_dec_ref(v_xs_349_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqv(lean_object* v_00_u03b1_354_, lean_object* v_xs_355_, lean_object* v_ys_356_, lean_object* v_p_357_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_358_ = lean_array_get_size(v_xs_355_);
v___x_359_ = lean_array_get_size(v_ys_356_);
v___x_360_ = lean_nat_dec_eq(v___x_358_, v___x_359_);
if (v___x_360_ == 0)
{
lean_dec_ref(v_p_357_);
return v___x_360_;
}
else
{
uint8_t v___x_361_; 
v___x_361_ = l_Array_isEqvAux___redArg(v_xs_355_, v_ys_356_, v_p_357_, v___x_358_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqv___boxed(lean_object* v_00_u03b1_362_, lean_object* v_xs_363_, lean_object* v_ys_364_, lean_object* v_p_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Array_isEqv(v_00_u03b1_362_, v_xs_363_, v_ys_364_, v_p_365_);
lean_dec_ref(v_ys_364_);
lean_dec_ref(v_xs_363_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT uint8_t l_Array_instBEq___redArg___lam__0(lean_object* v_inst_368_, lean_object* v_xs_369_, lean_object* v_ys_370_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_371_ = lean_array_get_size(v_xs_369_);
v___x_372_ = lean_array_get_size(v_ys_370_);
v___x_373_ = lean_nat_dec_eq(v___x_371_, v___x_372_);
if (v___x_373_ == 0)
{
lean_dec_ref(v_inst_368_);
return v___x_373_;
}
else
{
uint8_t v___x_374_; 
v___x_374_ = l_Array_isEqvAux___redArg(v_xs_369_, v_ys_370_, v_inst_368_, v___x_371_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instBEq___redArg___lam__0___boxed(lean_object* v_inst_375_, lean_object* v_xs_376_, lean_object* v_ys_377_){
_start:
{
uint8_t v_res_378_; lean_object* v_r_379_; 
v_res_378_ = l_Array_instBEq___redArg___lam__0(v_inst_375_, v_xs_376_, v_ys_377_);
lean_dec_ref(v_ys_377_);
lean_dec_ref(v_xs_376_);
v_r_379_ = lean_box(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT lean_object* l_Array_instBEq___redArg(lean_object* v_inst_380_){
_start:
{
lean_object* v___f_381_; 
v___f_381_ = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_381_, 0, v_inst_380_);
return v___f_381_;
}
}
LEAN_EXPORT lean_object* l_Array_instBEq(lean_object* v_00_u03b1_382_, lean_object* v_inst_383_){
_start:
{
lean_object* v___f_384_; 
v___f_384_ = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_384_, 0, v_inst_383_);
return v___f_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(lean_object* v_n_385_, lean_object* v_f_386_, lean_object* v_acc_387_, lean_object* v_i_388_){
_start:
{
lean_object* v_zero_389_; uint8_t v_isZero_390_; 
v_zero_389_ = lean_unsigned_to_nat(0u);
v_isZero_390_ = lean_nat_dec_eq(v_i_388_, v_zero_389_);
if (v_isZero_390_ == 1)
{
lean_dec(v_i_388_);
lean_dec(v_f_386_);
return v_acc_387_;
}
else
{
lean_object* v_one_391_; lean_object* v_n_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_one_391_ = lean_unsigned_to_nat(1u);
v_n_392_ = lean_nat_sub(v_i_388_, v_one_391_);
lean_dec(v_i_388_);
v___x_393_ = lean_nat_sub(v_n_385_, v_n_392_);
v___x_394_ = lean_nat_sub(v___x_393_, v_one_391_);
lean_dec(v___x_393_);
lean_inc(v_f_386_);
v___x_395_ = lean_apply_1(v_f_386_, v___x_394_);
v___x_396_ = lean_array_push(v_acc_387_, v___x_395_);
v_acc_387_ = v___x_396_;
v_i_388_ = v_n_392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg___boxed(lean_object* v_n_398_, lean_object* v_f_399_, lean_object* v_acc_400_, lean_object* v_i_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(v_n_398_, v_f_399_, v_acc_400_, v_i_401_);
lean_dec(v_n_398_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go(lean_object* v_00_u03b1_403_, lean_object* v_n_404_, lean_object* v_f_405_, lean_object* v_acc_406_, lean_object* v_i_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(v_n_404_, v_f_405_, v_acc_406_, v_i_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go___boxed(lean_object* v_00_u03b1_410_, lean_object* v_n_411_, lean_object* v_f_412_, lean_object* v_acc_413_, lean_object* v_i_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go(v_00_u03b1_410_, v_n_411_, v_f_412_, v_acc_413_, v_i_414_, v_a_415_);
lean_dec(v_n_411_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn___redArg(lean_object* v_n_417_, lean_object* v_f_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_mk_empty_array_with_capacity(v_n_417_);
lean_inc(v_n_417_);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(v_n_417_, v_f_418_, v___x_419_, v_n_417_);
lean_dec(v_n_417_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn(lean_object* v_00_u03b1_421_, lean_object* v_n_422_, lean_object* v_f_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Array_ofFn___redArg(v_n_422_, v_f_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Array_range___lam__0(lean_object* v_i_425_){
_start:
{
lean_inc(v_i_425_);
return v_i_425_;
}
}
LEAN_EXPORT lean_object* l_Array_range___lam__0___boxed(lean_object* v_i_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Array_range___lam__0(v_i_426_);
lean_dec(v_i_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Array_range(lean_object* v_n_429_){
_start:
{
lean_object* v___f_430_; lean_object* v___x_431_; 
v___f_430_ = ((lean_object*)(l_Array_range___closed__0));
v___x_431_ = l_Array_ofFn___redArg(v_n_429_, v___f_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27___lam__0(lean_object* v_step_432_, lean_object* v_start_433_, lean_object* v_i_434_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_nat_mul(v_step_432_, v_i_434_);
v___x_436_ = lean_nat_add(v_start_433_, v___x_435_);
lean_dec(v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27___lam__0___boxed(lean_object* v_step_437_, lean_object* v_start_438_, lean_object* v_i_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Array_range_x27___lam__0(v_step_437_, v_start_438_, v_i_439_);
lean_dec(v_i_439_);
lean_dec(v_start_438_);
lean_dec(v_step_437_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27(lean_object* v_start_441_, lean_object* v_size_442_, lean_object* v_step_443_){
_start:
{
lean_object* v___f_444_; lean_object* v___x_445_; 
v___f_444_ = lean_alloc_closure((void*)(l_Array_range_x27___lam__0___boxed), 3, 2);
lean_closure_set(v___f_444_, 0, v_step_443_);
lean_closure_set(v___f_444_, 1, v_start_441_);
v___x_445_ = l_Array_ofFn___redArg(v_size_442_, v___f_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Array_singleton___redArg(lean_object* v_v_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_mk_empty_array_with_capacity(v___x_447_);
v___x_449_ = lean_array_push(v___x_448_, v_v_446_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Array_singleton(lean_object* v_00_u03b1_450_, lean_object* v_v_451_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_unsigned_to_nat(1u);
v___x_453_ = lean_mk_empty_array_with_capacity(v___x_452_);
v___x_454_ = lean_array_push(v___x_453_, v_v_451_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___redArg(lean_object* v_inst_455_, lean_object* v_xs_456_){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_457_ = lean_array_get_size(v_xs_456_);
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = lean_nat_sub(v___x_457_, v___x_458_);
v___x_460_ = lean_array_get_borrowed(v_inst_455_, v_xs_456_, v___x_459_);
lean_dec(v___x_459_);
lean_inc(v___x_460_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___redArg___boxed(lean_object* v_inst_461_, lean_object* v_xs_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Array_back_x21___redArg(v_inst_461_, v_xs_462_);
lean_dec_ref(v_xs_462_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21(lean_object* v_00_u03b1_464_, lean_object* v_inst_465_, lean_object* v_xs_466_){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_467_ = lean_array_get_size(v_xs_466_);
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = lean_nat_sub(v___x_467_, v___x_468_);
v___x_470_ = lean_array_get_borrowed(v_inst_465_, v_xs_466_, v___x_469_);
lean_dec(v___x_469_);
lean_inc(v___x_470_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___boxed(lean_object* v_00_u03b1_471_, lean_object* v_inst_472_, lean_object* v_xs_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Array_back_x21(v_00_u03b1_471_, v_inst_472_, v_xs_473_);
lean_dec_ref(v_xs_473_);
return v_res_474_;
}
}
static lean_object* _init_l_Array_back___auto__1(void){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Array_back___redArg(lean_object* v_xs_476_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_477_ = lean_array_get_size(v_xs_476_);
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = lean_nat_sub(v___x_477_, v___x_478_);
v___x_480_ = lean_array_fget_borrowed(v_xs_476_, v___x_479_);
lean_dec(v___x_479_);
lean_inc(v___x_480_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Array_back___redArg___boxed(lean_object* v_xs_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Array_back___redArg(v_xs_481_);
lean_dec_ref(v_xs_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Array_back(lean_object* v_00_u03b1_483_, lean_object* v_xs_484_, lean_object* v_h_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_486_ = lean_array_get_size(v_xs_484_);
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_nat_sub(v___x_486_, v___x_487_);
v___x_489_ = lean_array_fget_borrowed(v_xs_484_, v___x_488_);
lean_dec(v___x_488_);
lean_inc(v___x_489_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Array_back___boxed(lean_object* v_00_u03b1_490_, lean_object* v_xs_491_, lean_object* v_h_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Array_back(v_00_u03b1_490_, v_xs_491_, v_h_492_);
lean_dec_ref(v_xs_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___redArg(lean_object* v_xs_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_495_ = lean_array_get_size(v_xs_494_);
v___x_496_ = lean_unsigned_to_nat(1u);
v___x_497_ = lean_nat_sub(v___x_495_, v___x_496_);
v___x_498_ = lean_nat_dec_lt(v___x_497_, v___x_495_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_dec(v___x_497_);
v___x_499_ = lean_box(0);
return v___x_499_;
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_array_fget_borrowed(v_xs_494_, v___x_497_);
lean_dec(v___x_497_);
lean_inc(v___x_500_);
v___x_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___redArg___boxed(lean_object* v_xs_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Array_back_x3f___redArg(v_xs_502_);
lean_dec_ref(v_xs_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f(lean_object* v_00_u03b1_504_, lean_object* v_xs_505_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_506_ = lean_array_get_size(v_xs_505_);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_sub(v___x_506_, v___x_507_);
v___x_509_ = lean_nat_dec_lt(v___x_508_, v___x_506_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
lean_dec(v___x_508_);
v___x_510_ = lean_box(0);
return v___x_510_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_array_fget_borrowed(v_xs_505_, v___x_508_);
lean_dec(v___x_508_);
lean_inc(v___x_511_);
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___boxed(lean_object* v_00_u03b1_513_, lean_object* v_xs_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Array_back_x3f(v_00_u03b1_513_, v_xs_514_);
lean_dec_ref(v_xs_514_);
return v_res_515_;
}
}
static lean_object* _init_l_Array_swapAt___auto__1(void){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___redArg(lean_object* v_xs_517_, lean_object* v_i_518_, lean_object* v_v_519_){
_start:
{
lean_object* v_e_520_; lean_object* v_xs_x27_521_; lean_object* v___x_522_; 
v_e_520_ = lean_array_fget(v_xs_517_, v_i_518_);
v_xs_x27_521_ = lean_array_fset(v_xs_517_, v_i_518_, v_v_519_);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v_e_520_);
lean_ctor_set(v___x_522_, 1, v_xs_x27_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___redArg___boxed(lean_object* v_xs_523_, lean_object* v_i_524_, lean_object* v_v_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Array_swapAt___redArg(v_xs_523_, v_i_524_, v_v_525_);
lean_dec(v_i_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt(lean_object* v_00_u03b1_527_, lean_object* v_xs_528_, lean_object* v_i_529_, lean_object* v_v_530_, lean_object* v_hi_531_){
_start:
{
lean_object* v_e_532_; lean_object* v_xs_x27_533_; lean_object* v___x_534_; 
v_e_532_ = lean_array_fget(v_xs_528_, v_i_529_);
v_xs_x27_533_ = lean_array_fset(v_xs_528_, v_i_529_, v_v_530_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v_e_532_);
lean_ctor_set(v___x_534_, 1, v_xs_x27_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___boxed(lean_object* v_00_u03b1_535_, lean_object* v_xs_536_, lean_object* v_i_537_, lean_object* v_v_538_, lean_object* v_hi_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Array_swapAt(v_00_u03b1_535_, v_xs_536_, v_i_537_, v_v_538_, v_hi_539_);
lean_dec(v_i_537_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt_x21___redArg(lean_object* v_xs_545_, lean_object* v_i_546_, lean_object* v_v_547_){
_start:
{
lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_548_ = lean_array_get_size(v_xs_545_);
v___x_549_ = lean_nat_dec_lt(v_i_546_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v_this_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_this_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_550_, 0, v_v_547_);
lean_ctor_set(v_this_550_, 1, v_xs_545_);
v___x_551_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_552_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__1));
v___x_553_ = lean_unsigned_to_nat(438u);
v___x_554_ = lean_unsigned_to_nat(4u);
v___x_555_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__2));
v___x_556_ = l_Nat_reprFast(v_i_546_);
v___x_557_ = lean_string_append(v___x_555_, v___x_556_);
lean_dec_ref(v___x_556_);
v___x_558_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__3));
v___x_559_ = lean_string_append(v___x_557_, v___x_558_);
v___x_560_ = l_mkPanicMessageWithDecl(v___x_551_, v___x_552_, v___x_553_, v___x_554_, v___x_559_);
lean_dec_ref(v___x_559_);
v___x_561_ = l_panic___redArg(v_this_550_, v___x_560_);
return v___x_561_;
}
else
{
lean_object* v_e_562_; lean_object* v_xs_x27_563_; lean_object* v___x_564_; 
v_e_562_ = lean_array_fget(v_xs_545_, v_i_546_);
v_xs_x27_563_ = lean_array_fset(v_xs_545_, v_i_546_, v_v_547_);
lean_dec(v_i_546_);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v_e_562_);
lean_ctor_set(v___x_564_, 1, v_xs_x27_563_);
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l_Array_swapAt_x21(lean_object* v_00_u03b1_565_, lean_object* v_xs_566_, lean_object* v_i_567_, lean_object* v_v_568_){
_start:
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_array_get_size(v_xs_566_);
v___x_570_ = lean_nat_dec_lt(v_i_567_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v_this_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_this_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_571_, 0, v_v_568_);
lean_ctor_set(v_this_571_, 1, v_xs_566_);
v___x_572_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_573_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__1));
v___x_574_ = lean_unsigned_to_nat(438u);
v___x_575_ = lean_unsigned_to_nat(4u);
v___x_576_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__2));
v___x_577_ = l_Nat_reprFast(v_i_567_);
v___x_578_ = lean_string_append(v___x_576_, v___x_577_);
lean_dec_ref(v___x_577_);
v___x_579_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__3));
v___x_580_ = lean_string_append(v___x_578_, v___x_579_);
v___x_581_ = l_mkPanicMessageWithDecl(v___x_572_, v___x_573_, v___x_574_, v___x_575_, v___x_580_);
lean_dec_ref(v___x_580_);
v___x_582_ = l_panic___redArg(v_this_571_, v___x_581_);
return v___x_582_;
}
else
{
lean_object* v_e_583_; lean_object* v_xs_x27_584_; lean_object* v___x_585_; 
v_e_583_ = lean_array_fget(v_xs_566_, v_i_567_);
v_xs_x27_584_ = lean_array_fset(v_xs_566_, v_i_567_, v_v_568_);
lean_dec(v_i_567_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_e_583_);
lean_ctor_set(v___x_585_, 1, v_xs_x27_584_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
lean_object* v_zero_588_; uint8_t v_isZero_589_; 
v_zero_588_ = lean_unsigned_to_nat(0u);
v_isZero_589_ = lean_nat_dec_eq(v_x_586_, v_zero_588_);
if (v_isZero_589_ == 1)
{
lean_dec(v_x_586_);
return v_x_587_;
}
else
{
lean_object* v_one_590_; lean_object* v_n_591_; lean_object* v___x_592_; 
v_one_590_ = lean_unsigned_to_nat(1u);
v_n_591_ = lean_nat_sub(v_x_586_, v_one_590_);
lean_dec(v_x_586_);
v___x_592_ = lean_array_pop(v_x_587_);
v_x_586_ = v_n_591_;
v_x_587_ = v___x_592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_shrink_loop(lean_object* v_00_u03b1_594_, lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(v_x_595_, v_x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___redArg(lean_object* v_xs_598_, lean_object* v_n_599_){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_array_get_size(v_xs_598_);
v___x_601_ = lean_nat_sub(v___x_600_, v_n_599_);
v___x_602_ = l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(v___x_601_, v_xs_598_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___redArg___boxed(lean_object* v_xs_603_, lean_object* v_n_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Array_shrink___redArg(v_xs_603_, v_n_604_);
lean_dec(v_n_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink(lean_object* v_00_u03b1_606_, lean_object* v_xs_607_, lean_object* v_n_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Array_shrink___redArg(v_xs_607_, v_n_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___boxed(lean_object* v_00_u03b1_610_, lean_object* v_xs_611_, lean_object* v_n_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Array_shrink(v_00_u03b1_610_, v_xs_611_, v_n_612_);
lean_dec(v_n_612_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Array_take___redArg(lean_object* v_xs_614_, lean_object* v_i_615_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = l_Array_extract___redArg(v_xs_614_, v___x_616_, v_i_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Array_take___redArg___boxed(lean_object* v_xs_618_, lean_object* v_i_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Array_take___redArg(v_xs_618_, v_i_619_);
lean_dec_ref(v_xs_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Array_take(lean_object* v_00_u03b1_621_, lean_object* v_xs_622_, lean_object* v_i_623_){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = l_Array_extract___redArg(v_xs_622_, v___x_624_, v_i_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Array_take___boxed(lean_object* v_00_u03b1_626_, lean_object* v_xs_627_, lean_object* v_i_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Array_take(v_00_u03b1_626_, v_xs_627_, v_i_628_);
lean_dec_ref(v_xs_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___redArg(lean_object* v_xs_630_, lean_object* v_i_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_array_get_size(v_xs_630_);
v___x_633_ = l_Array_extract___redArg(v_xs_630_, v_i_631_, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___redArg___boxed(lean_object* v_xs_634_, lean_object* v_i_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Array_drop___redArg(v_xs_634_, v_i_635_);
lean_dec_ref(v_xs_634_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Array_drop(lean_object* v_00_u03b1_637_, lean_object* v_xs_638_, lean_object* v_i_639_){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_array_get_size(v_xs_638_);
v___x_641_ = l_Array_extract___redArg(v_xs_638_, v_i_639_, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___boxed(lean_object* v_00_u03b1_642_, lean_object* v_xs_643_, lean_object* v_i_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Array_drop(v_00_u03b1_642_, v_xs_643_, v_i_644_);
lean_dec_ref(v_xs_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0(lean_object* v_toApplicative_646_, lean_object* v_xs_x27_647_, lean_object* v_i_648_, lean_object* v_v_649_){
_start:
{
lean_object* v_toPure_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_toPure_650_ = lean_ctor_get(v_toApplicative_646_, 1);
lean_inc(v_toPure_650_);
lean_dec_ref(v_toApplicative_646_);
v___x_651_ = lean_array_fset(v_xs_x27_647_, v_i_648_, v_v_649_);
v___x_652_ = lean_apply_2(v_toPure_650_, lean_box(0), v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0___boxed(lean_object* v_toApplicative_653_, lean_object* v_xs_x27_654_, lean_object* v_i_655_, lean_object* v_v_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Array_modifyMUnsafe___redArg___lam__0(v_toApplicative_653_, v_xs_x27_654_, v_i_655_, v_v_656_);
lean_dec(v_i_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg(lean_object* v_inst_658_, lean_object* v_xs_659_, lean_object* v_i_660_, lean_object* v_f_661_){
_start:
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_array_get_size(v_xs_659_);
v___x_663_ = lean_nat_dec_lt(v_i_660_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v_toApplicative_664_; lean_object* v_toPure_665_; lean_object* v___x_666_; 
lean_dec(v_f_661_);
lean_dec(v_i_660_);
v_toApplicative_664_ = lean_ctor_get(v_inst_658_, 0);
lean_inc_ref(v_toApplicative_664_);
lean_dec_ref(v_inst_658_);
v_toPure_665_ = lean_ctor_get(v_toApplicative_664_, 1);
lean_inc(v_toPure_665_);
lean_dec_ref(v_toApplicative_664_);
v___x_666_ = lean_apply_2(v_toPure_665_, lean_box(0), v_xs_659_);
return v___x_666_;
}
else
{
lean_object* v_toApplicative_667_; lean_object* v_toBind_668_; lean_object* v_v_669_; lean_object* v___x_670_; lean_object* v_xs_x27_671_; lean_object* v___f_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_toApplicative_667_ = lean_ctor_get(v_inst_658_, 0);
lean_inc_ref(v_toApplicative_667_);
v_toBind_668_ = lean_ctor_get(v_inst_658_, 1);
lean_inc(v_toBind_668_);
lean_dec_ref(v_inst_658_);
v_v_669_ = lean_array_fget(v_xs_659_, v_i_660_);
v___x_670_ = lean_box(0);
v_xs_x27_671_ = lean_array_fset(v_xs_659_, v_i_660_, v___x_670_);
v___f_672_ = lean_alloc_closure((void*)(l_Array_modifyMUnsafe___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_672_, 0, v_toApplicative_667_);
lean_closure_set(v___f_672_, 1, v_xs_x27_671_);
lean_closure_set(v___f_672_, 2, v_i_660_);
v___x_673_ = lean_apply_1(v_f_661_, v_v_669_);
v___x_674_ = lean_apply_4(v_toBind_668_, lean_box(0), lean_box(0), v___x_673_, v___f_672_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe(lean_object* v_00_u03b1_675_, lean_object* v_m_676_, lean_object* v_inst_677_, lean_object* v_xs_678_, lean_object* v_i_679_, lean_object* v_f_680_){
_start:
{
lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_681_ = lean_array_get_size(v_xs_678_);
v___x_682_ = lean_nat_dec_lt(v_i_679_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v_toApplicative_683_; lean_object* v_toPure_684_; lean_object* v___x_685_; 
lean_dec(v_f_680_);
lean_dec(v_i_679_);
v_toApplicative_683_ = lean_ctor_get(v_inst_677_, 0);
lean_inc_ref(v_toApplicative_683_);
lean_dec_ref(v_inst_677_);
v_toPure_684_ = lean_ctor_get(v_toApplicative_683_, 1);
lean_inc(v_toPure_684_);
lean_dec_ref(v_toApplicative_683_);
v___x_685_ = lean_apply_2(v_toPure_684_, lean_box(0), v_xs_678_);
return v___x_685_;
}
else
{
lean_object* v_toApplicative_686_; lean_object* v_toBind_687_; lean_object* v_v_688_; lean_object* v___x_689_; lean_object* v_xs_x27_690_; lean_object* v___f_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_toApplicative_686_ = lean_ctor_get(v_inst_677_, 0);
lean_inc_ref(v_toApplicative_686_);
v_toBind_687_ = lean_ctor_get(v_inst_677_, 1);
lean_inc(v_toBind_687_);
lean_dec_ref(v_inst_677_);
v_v_688_ = lean_array_fget(v_xs_678_, v_i_679_);
v___x_689_ = lean_box(0);
v_xs_x27_690_ = lean_array_fset(v_xs_678_, v_i_679_, v___x_689_);
v___f_691_ = lean_alloc_closure((void*)(l_Array_modifyMUnsafe___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_691_, 0, v_toApplicative_686_);
lean_closure_set(v___f_691_, 1, v_xs_x27_690_);
lean_closure_set(v___f_691_, 2, v_i_679_);
v___x_692_ = lean_apply_1(v_f_680_, v_v_688_);
v___x_693_ = lean_apply_4(v_toBind_687_, lean_box(0), lean_box(0), v___x_692_, v___f_691_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___redArg(lean_object* v_xs_694_, lean_object* v_i_695_, lean_object* v_f_696_){
_start:
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = lean_array_get_size(v_xs_694_);
v___x_698_ = lean_nat_dec_lt(v_i_695_, v___x_697_);
if (v___x_698_ == 0)
{
lean_dec(v_f_696_);
return v_xs_694_;
}
else
{
lean_object* v_v_699_; lean_object* v___x_700_; lean_object* v_xs_x27_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v_v_699_ = lean_array_fget(v_xs_694_, v_i_695_);
v___x_700_ = lean_box(0);
v_xs_x27_701_ = lean_array_fset(v_xs_694_, v_i_695_, v___x_700_);
v___x_702_ = lean_apply_1(v_f_696_, v_v_699_);
v___x_703_ = lean_array_fset(v_xs_x27_701_, v_i_695_, v___x_702_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___redArg___boxed(lean_object* v_xs_704_, lean_object* v_i_705_, lean_object* v_f_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Array_modify___redArg(v_xs_704_, v_i_705_, v_f_706_);
lean_dec(v_i_705_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Array_modify(lean_object* v_00_u03b1_708_, lean_object* v_xs_709_, lean_object* v_i_710_, lean_object* v_f_711_){
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
LEAN_EXPORT lean_object* l_Array_modify___boxed(lean_object* v_00_u03b1_719_, lean_object* v_xs_720_, lean_object* v_i_721_, lean_object* v_f_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Array_modify(v_00_u03b1_719_, v_xs_720_, v_i_721_, v_f_722_);
lean_dec(v_i_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg(lean_object* v_xs_724_, lean_object* v_idx_725_, lean_object* v_f_726_){
_start:
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = lean_array_get_size(v_xs_724_);
v___x_728_ = lean_nat_dec_lt(v_idx_725_, v___x_727_);
if (v___x_728_ == 0)
{
lean_dec(v_f_726_);
return v_xs_724_;
}
else
{
lean_object* v_v_729_; lean_object* v___x_730_; lean_object* v_xs_x27_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_v_729_ = lean_array_fget(v_xs_724_, v_idx_725_);
v___x_730_ = lean_box(0);
v_xs_x27_731_ = lean_array_fset(v_xs_724_, v_idx_725_, v___x_730_);
v___x_732_ = lean_apply_1(v_f_726_, v_v_729_);
v___x_733_ = lean_array_fset(v_xs_x27_731_, v_idx_725_, v___x_732_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg___boxed(lean_object* v_xs_734_, lean_object* v_idx_735_, lean_object* v_f_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Array_modifyOp___redArg(v_xs_734_, v_idx_735_, v_f_736_);
lean_dec(v_idx_735_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp(lean_object* v_00_u03b1_738_, lean_object* v_xs_739_, lean_object* v_idx_740_, lean_object* v_f_741_){
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
LEAN_EXPORT lean_object* l_Array_modifyOp___boxed(lean_object* v_00_u03b1_749_, lean_object* v_xs_750_, lean_object* v_idx_751_, lean_object* v_f_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Array_modifyOp(v_00_u03b1_749_, v_xs_750_, v_idx_751_, v_f_752_);
lean_dec(v_idx_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed(lean_object* v_toApplicative_754_, lean_object* v_i_755_, lean_object* v_inst_756_, lean_object* v_as_757_, lean_object* v_f_758_, lean_object* v_sz_759_, lean_object* v_____do__lift_760_){
_start:
{
size_t v_i_boxed_761_; size_t v_sz_boxed_762_; lean_object* v_res_763_; 
v_i_boxed_761_ = lean_unbox_usize(v_i_755_);
lean_dec(v_i_755_);
v_sz_boxed_762_ = lean_unbox_usize(v_sz_759_);
lean_dec(v_sz_759_);
v_res_763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(v_toApplicative_754_, v_i_boxed_761_, v_inst_756_, v_as_757_, v_f_758_, v_sz_boxed_762_, v_____do__lift_760_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(lean_object* v_inst_764_, lean_object* v_as_765_, lean_object* v_f_766_, size_t v_sz_767_, size_t v_i_768_, lean_object* v_b_769_){
_start:
{
uint8_t v___x_770_; 
v___x_770_ = lean_usize_dec_lt(v_i_768_, v_sz_767_);
if (v___x_770_ == 0)
{
lean_object* v_toApplicative_771_; lean_object* v_toPure_772_; lean_object* v___x_773_; 
lean_dec(v_f_766_);
lean_dec_ref(v_as_765_);
v_toApplicative_771_ = lean_ctor_get(v_inst_764_, 0);
lean_inc_ref(v_toApplicative_771_);
lean_dec_ref(v_inst_764_);
v_toPure_772_ = lean_ctor_get(v_toApplicative_771_, 1);
lean_inc(v_toPure_772_);
lean_dec_ref(v_toApplicative_771_);
v___x_773_ = lean_apply_2(v_toPure_772_, lean_box(0), v_b_769_);
return v___x_773_;
}
else
{
lean_object* v_toApplicative_774_; lean_object* v_toBind_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___f_778_; lean_object* v_a_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_toApplicative_774_ = lean_ctor_get(v_inst_764_, 0);
lean_inc_ref(v_toApplicative_774_);
v_toBind_775_ = lean_ctor_get(v_inst_764_, 1);
lean_inc(v_toBind_775_);
v___x_776_ = lean_box_usize(v_i_768_);
v___x_777_ = lean_box_usize(v_sz_767_);
lean_inc(v_f_766_);
lean_inc_ref(v_as_765_);
v___f_778_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_778_, 0, v_toApplicative_774_);
lean_closure_set(v___f_778_, 1, v___x_776_);
lean_closure_set(v___f_778_, 2, v_inst_764_);
lean_closure_set(v___f_778_, 3, v_as_765_);
lean_closure_set(v___f_778_, 4, v_f_766_);
lean_closure_set(v___f_778_, 5, v___x_777_);
v_a_779_ = lean_array_uget(v_as_765_, v_i_768_);
lean_dec_ref(v_as_765_);
v___x_780_ = lean_apply_3(v_f_766_, v_a_779_, lean_box(0), v_b_769_);
v___x_781_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v___x_780_, v___f_778_);
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(lean_object* v_toApplicative_782_, size_t v_i_783_, lean_object* v_inst_784_, lean_object* v_as_785_, lean_object* v_f_786_, size_t v_sz_787_, lean_object* v_____do__lift_788_){
_start:
{
if (lean_obj_tag(v_____do__lift_788_) == 0)
{
lean_object* v_a_789_; lean_object* v_toPure_790_; lean_object* v___x_791_; 
lean_dec(v_f_786_);
lean_dec_ref(v_as_785_);
lean_dec_ref(v_inst_784_);
v_a_789_ = lean_ctor_get(v_____do__lift_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref(v_____do__lift_788_);
v_toPure_790_ = lean_ctor_get(v_toApplicative_782_, 1);
lean_inc(v_toPure_790_);
lean_dec_ref(v_toApplicative_782_);
v___x_791_ = lean_apply_2(v_toPure_790_, lean_box(0), v_a_789_);
return v___x_791_;
}
else
{
lean_object* v_a_792_; size_t v___x_793_; size_t v___x_794_; lean_object* v___x_795_; 
lean_dec_ref(v_toApplicative_782_);
v_a_792_ = lean_ctor_get(v_____do__lift_788_, 0);
lean_inc(v_a_792_);
lean_dec_ref(v_____do__lift_788_);
v___x_793_ = ((size_t)1ULL);
v___x_794_ = lean_usize_add(v_i_783_, v___x_793_);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_784_, v_as_785_, v_f_786_, v_sz_787_, v___x_794_, v_a_792_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___boxed(lean_object* v_inst_796_, lean_object* v_as_797_, lean_object* v_f_798_, lean_object* v_sz_799_, lean_object* v_i_800_, lean_object* v_b_801_){
_start:
{
size_t v_sz_boxed_802_; size_t v_i_boxed_803_; lean_object* v_res_804_; 
v_sz_boxed_802_ = lean_unbox_usize(v_sz_799_);
lean_dec(v_sz_799_);
v_i_boxed_803_ = lean_unbox_usize(v_i_800_);
lean_dec(v_i_800_);
v_res_804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_796_, v_as_797_, v_f_798_, v_sz_boxed_802_, v_i_boxed_803_, v_b_801_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object* v_00_u03b1_805_, lean_object* v_00_u03b2_806_, lean_object* v_m_807_, lean_object* v_inst_808_, lean_object* v_as_809_, lean_object* v_f_810_, size_t v_sz_811_, size_t v_i_812_, lean_object* v_b_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_808_, v_as_809_, v_f_810_, v_sz_811_, v_i_812_, v_b_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___boxed(lean_object* v_00_u03b1_815_, lean_object* v_00_u03b2_816_, lean_object* v_m_817_, lean_object* v_inst_818_, lean_object* v_as_819_, lean_object* v_f_820_, lean_object* v_sz_821_, lean_object* v_i_822_, lean_object* v_b_823_){
_start:
{
size_t v_sz_boxed_824_; size_t v_i_boxed_825_; lean_object* v_res_826_; 
v_sz_boxed_824_ = lean_unbox_usize(v_sz_821_);
lean_dec(v_sz_821_);
v_i_boxed_825_ = lean_unbox_usize(v_i_822_);
lean_dec(v_i_822_);
v_res_826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(v_00_u03b1_815_, v_00_u03b2_816_, v_m_817_, v_inst_818_, v_as_819_, v_f_820_, v_sz_boxed_824_, v_i_boxed_825_, v_b_823_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe___redArg(lean_object* v_inst_827_, lean_object* v_as_828_, lean_object* v_b_829_, lean_object* v_f_830_){
_start:
{
size_t v_sz_831_; size_t v___x_832_; lean_object* v___x_833_; 
v_sz_831_ = lean_array_size(v_as_828_);
v___x_832_ = ((size_t)0ULL);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_827_, v_as_828_, v_f_830_, v_sz_831_, v___x_832_, v_b_829_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe(lean_object* v_00_u03b1_834_, lean_object* v_00_u03b2_835_, lean_object* v_m_836_, lean_object* v_inst_837_, lean_object* v_as_838_, lean_object* v_b_839_, lean_object* v_f_840_){
_start:
{
size_t v_sz_841_; size_t v___x_842_; lean_object* v___x_843_; 
v_sz_841_ = lean_array_size(v_as_838_);
v___x_842_ = ((size_t)0ULL);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_837_, v_as_838_, v_f_840_, v_sz_841_, v___x_842_, v_b_839_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0___boxed(lean_object* v_toPure_844_, lean_object* v_inst_845_, lean_object* v_as_846_, lean_object* v_f_847_, lean_object* v_n_848_, lean_object* v_____do__lift_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Array_forIn_x27_loop___redArg___lam__0(v_toPure_844_, v_inst_845_, v_as_846_, v_f_847_, v_n_848_, v_____do__lift_849_);
lean_dec(v_n_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg(lean_object* v_inst_851_, lean_object* v_as_852_, lean_object* v_f_853_, lean_object* v_i_854_, lean_object* v_b_855_){
_start:
{
lean_object* v_toApplicative_856_; lean_object* v_toBind_857_; lean_object* v_toPure_858_; lean_object* v_zero_859_; uint8_t v_isZero_860_; 
v_toApplicative_856_ = lean_ctor_get(v_inst_851_, 0);
v_toBind_857_ = lean_ctor_get(v_inst_851_, 1);
lean_inc(v_toBind_857_);
v_toPure_858_ = lean_ctor_get(v_toApplicative_856_, 1);
lean_inc(v_toPure_858_);
v_zero_859_ = lean_unsigned_to_nat(0u);
v_isZero_860_ = lean_nat_dec_eq(v_i_854_, v_zero_859_);
if (v_isZero_860_ == 1)
{
lean_object* v___x_861_; 
lean_dec(v_toBind_857_);
lean_dec(v_f_853_);
lean_dec_ref(v_as_852_);
lean_dec_ref(v_inst_851_);
v___x_861_ = lean_apply_2(v_toPure_858_, lean_box(0), v_b_855_);
return v___x_861_;
}
else
{
lean_object* v_one_862_; lean_object* v_n_863_; lean_object* v___f_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_one_862_ = lean_unsigned_to_nat(1u);
v_n_863_ = lean_nat_sub(v_i_854_, v_one_862_);
lean_inc(v_n_863_);
lean_inc(v_f_853_);
lean_inc_ref(v_as_852_);
v___f_864_ = lean_alloc_closure((void*)(l_Array_forIn_x27_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_864_, 0, v_toPure_858_);
lean_closure_set(v___f_864_, 1, v_inst_851_);
lean_closure_set(v___f_864_, 2, v_as_852_);
lean_closure_set(v___f_864_, 3, v_f_853_);
lean_closure_set(v___f_864_, 4, v_n_863_);
v___x_865_ = lean_array_get_size(v_as_852_);
v___x_866_ = lean_nat_sub(v___x_865_, v_one_862_);
v___x_867_ = lean_nat_sub(v___x_866_, v_n_863_);
lean_dec(v_n_863_);
lean_dec(v___x_866_);
v___x_868_ = lean_array_fget(v_as_852_, v___x_867_);
lean_dec(v___x_867_);
lean_dec_ref(v_as_852_);
v___x_869_ = lean_apply_3(v_f_853_, v___x_868_, lean_box(0), v_b_855_);
v___x_870_ = lean_apply_4(v_toBind_857_, lean_box(0), lean_box(0), v___x_869_, v___f_864_);
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0(lean_object* v_toPure_871_, lean_object* v_inst_872_, lean_object* v_as_873_, lean_object* v_f_874_, lean_object* v_n_875_, lean_object* v_____do__lift_876_){
_start:
{
if (lean_obj_tag(v_____do__lift_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_878_; 
lean_dec(v_f_874_);
lean_dec_ref(v_as_873_);
lean_dec_ref(v_inst_872_);
v_a_877_ = lean_ctor_get(v_____do__lift_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref(v_____do__lift_876_);
v___x_878_ = lean_apply_2(v_toPure_871_, lean_box(0), v_a_877_);
return v___x_878_;
}
else
{
lean_object* v_a_879_; lean_object* v___x_880_; 
lean_dec(v_toPure_871_);
v_a_879_ = lean_ctor_get(v_____do__lift_876_, 0);
lean_inc(v_a_879_);
lean_dec_ref(v_____do__lift_876_);
v___x_880_ = l_Array_forIn_x27_loop___redArg(v_inst_872_, v_as_873_, v_f_874_, v_n_875_, v_a_879_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___boxed(lean_object* v_inst_881_, lean_object* v_as_882_, lean_object* v_f_883_, lean_object* v_i_884_, lean_object* v_b_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Array_forIn_x27_loop___redArg(v_inst_881_, v_as_882_, v_f_883_, v_i_884_, v_b_885_);
lean_dec(v_i_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop(lean_object* v_00_u03b1_887_, lean_object* v_00_u03b2_888_, lean_object* v_m_889_, lean_object* v_inst_890_, lean_object* v_as_891_, lean_object* v_f_892_, lean_object* v_i_893_, lean_object* v_h_894_, lean_object* v_b_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Array_forIn_x27_loop___redArg(v_inst_890_, v_as_891_, v_f_892_, v_i_893_, v_b_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___boxed(lean_object* v_00_u03b1_897_, lean_object* v_00_u03b2_898_, lean_object* v_m_899_, lean_object* v_inst_900_, lean_object* v_as_901_, lean_object* v_f_902_, lean_object* v_i_903_, lean_object* v_h_904_, lean_object* v_b_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Array_forIn_x27_loop(v_00_u03b1_897_, v_00_u03b2_898_, v_m_899_, v_inst_900_, v_as_901_, v_f_902_, v_i_903_, v_h_904_, v_b_905_);
lean_dec(v_i_903_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_inst_907_, lean_object* v_00_u03b2_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
size_t v_sz_912_; size_t v___x_913_; lean_object* v___x_914_; 
v_sz_912_ = lean_array_size(v___y_909_);
v___x_913_ = ((size_t)0ULL);
v___x_914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_907_, v___y_909_, v___y_911_, v_sz_912_, v___x_913_, v___y_910_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_915_){
_start:
{
lean_object* v___f_916_; 
v___f_916_ = lean_alloc_closure((void*)(l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_916_, 0, v_inst_915_);
return v___f_916_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_00_u03b1_917_, lean_object* v_m_918_, lean_object* v_inst_919_){
_start:
{
lean_object* v___f_920_; 
v___f_920_ = lean_alloc_closure((void*)(l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_920_, 0, v_inst_919_);
return v___f_920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_921_, lean_object* v_inst_922_, lean_object* v_f_923_, lean_object* v_as_924_, lean_object* v_stop_925_, lean_object* v_____do__lift_926_){
_start:
{
size_t v_i_boxed_927_; size_t v_stop_boxed_928_; lean_object* v_res_929_; 
v_i_boxed_927_ = lean_unbox_usize(v_i_921_);
lean_dec(v_i_921_);
v_stop_boxed_928_ = lean_unbox_usize(v_stop_925_);
lean_dec(v_stop_925_);
v_res_929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_927_, v_inst_922_, v_f_923_, v_as_924_, v_stop_boxed_928_, v_____do__lift_926_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(lean_object* v_inst_930_, lean_object* v_f_931_, lean_object* v_as_932_, size_t v_i_933_, size_t v_stop_934_, lean_object* v_b_935_){
_start:
{
uint8_t v___x_936_; 
v___x_936_ = lean_usize_dec_eq(v_i_933_, v_stop_934_);
if (v___x_936_ == 0)
{
lean_object* v_toBind_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___f_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_toBind_937_ = lean_ctor_get(v_inst_930_, 1);
lean_inc(v_toBind_937_);
v___x_938_ = lean_box_usize(v_i_933_);
v___x_939_ = lean_box_usize(v_stop_934_);
lean_inc_ref(v_as_932_);
lean_inc(v_f_931_);
v___f_940_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_940_, 0, v___x_938_);
lean_closure_set(v___f_940_, 1, v_inst_930_);
lean_closure_set(v___f_940_, 2, v_f_931_);
lean_closure_set(v___f_940_, 3, v_as_932_);
lean_closure_set(v___f_940_, 4, v___x_939_);
v___x_941_ = lean_array_uget(v_as_932_, v_i_933_);
lean_dec_ref(v_as_932_);
v___x_942_ = lean_apply_2(v_f_931_, v_b_935_, v___x_941_);
v___x_943_ = lean_apply_4(v_toBind_937_, lean_box(0), lean_box(0), v___x_942_, v___f_940_);
return v___x_943_;
}
else
{
lean_object* v_toApplicative_944_; lean_object* v_toPure_945_; lean_object* v___x_946_; 
lean_dec_ref(v_as_932_);
lean_dec(v_f_931_);
v_toApplicative_944_ = lean_ctor_get(v_inst_930_, 0);
lean_inc_ref(v_toApplicative_944_);
lean_dec_ref(v_inst_930_);
v_toPure_945_ = lean_ctor_get(v_toApplicative_944_, 1);
lean_inc(v_toPure_945_);
lean_dec_ref(v_toApplicative_944_);
v___x_946_ = lean_apply_2(v_toPure_945_, lean_box(0), v_b_935_);
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_947_, lean_object* v_inst_948_, lean_object* v_f_949_, lean_object* v_as_950_, size_t v_stop_951_, lean_object* v_____do__lift_952_){
_start:
{
size_t v___x_953_; size_t v___x_954_; lean_object* v___x_955_; 
v___x_953_ = ((size_t)1ULL);
v___x_954_ = lean_usize_add(v_i_947_, v___x_953_);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_948_, v_f_949_, v_as_950_, v___x_954_, v_stop_951_, v_____do__lift_952_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_956_, lean_object* v_f_957_, lean_object* v_as_958_, lean_object* v_i_959_, lean_object* v_stop_960_, lean_object* v_b_961_){
_start:
{
size_t v_i_boxed_962_; size_t v_stop_boxed_963_; lean_object* v_res_964_; 
v_i_boxed_962_ = lean_unbox_usize(v_i_959_);
lean_dec(v_i_959_);
v_stop_boxed_963_ = lean_unbox_usize(v_stop_960_);
lean_dec(v_stop_960_);
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_956_, v_f_957_, v_as_958_, v_i_boxed_962_, v_stop_boxed_963_, v_b_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object* v_00_u03b1_965_, lean_object* v_00_u03b2_966_, lean_object* v_m_967_, lean_object* v_inst_968_, lean_object* v_f_969_, lean_object* v_as_970_, size_t v_i_971_, size_t v_stop_972_, lean_object* v_b_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_968_, v_f_969_, v_as_970_, v_i_971_, v_stop_972_, v_b_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b1_975_, lean_object* v_00_u03b2_976_, lean_object* v_m_977_, lean_object* v_inst_978_, lean_object* v_f_979_, lean_object* v_as_980_, lean_object* v_i_981_, lean_object* v_stop_982_, lean_object* v_b_983_){
_start:
{
size_t v_i_boxed_984_; size_t v_stop_boxed_985_; lean_object* v_res_986_; 
v_i_boxed_984_ = lean_unbox_usize(v_i_981_);
lean_dec(v_i_981_);
v_stop_boxed_985_ = lean_unbox_usize(v_stop_982_);
lean_dec(v_stop_982_);
v_res_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(v_00_u03b1_975_, v_00_u03b2_976_, v_m_977_, v_inst_978_, v_f_979_, v_as_980_, v_i_boxed_984_, v_stop_boxed_985_, v_b_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg(lean_object* v_inst_987_, lean_object* v_f_988_, lean_object* v_init_989_, lean_object* v_as_990_, lean_object* v_start_991_, lean_object* v_stop_992_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = lean_nat_dec_lt(v_start_991_, v_stop_992_);
if (v___x_993_ == 0)
{
lean_object* v_toApplicative_994_; lean_object* v_toPure_995_; lean_object* v___x_996_; 
lean_dec_ref(v_as_990_);
lean_dec(v_f_988_);
v_toApplicative_994_ = lean_ctor_get(v_inst_987_, 0);
lean_inc_ref(v_toApplicative_994_);
lean_dec_ref(v_inst_987_);
v_toPure_995_ = lean_ctor_get(v_toApplicative_994_, 1);
lean_inc(v_toPure_995_);
lean_dec_ref(v_toApplicative_994_);
v___x_996_ = lean_apply_2(v_toPure_995_, lean_box(0), v_init_989_);
return v___x_996_;
}
else
{
lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_997_ = lean_array_get_size(v_as_990_);
v___x_998_ = lean_nat_dec_le(v_stop_992_, v___x_997_);
if (v___x_998_ == 0)
{
uint8_t v___x_999_; 
v___x_999_ = lean_nat_dec_lt(v_start_991_, v___x_997_);
if (v___x_999_ == 0)
{
lean_object* v_toApplicative_1000_; lean_object* v_toPure_1001_; lean_object* v___x_1002_; 
lean_dec_ref(v_as_990_);
lean_dec(v_f_988_);
v_toApplicative_1000_ = lean_ctor_get(v_inst_987_, 0);
lean_inc_ref(v_toApplicative_1000_);
lean_dec_ref(v_inst_987_);
v_toPure_1001_ = lean_ctor_get(v_toApplicative_1000_, 1);
lean_inc(v_toPure_1001_);
lean_dec_ref(v_toApplicative_1000_);
v___x_1002_ = lean_apply_2(v_toPure_1001_, lean_box(0), v_init_989_);
return v___x_1002_;
}
else
{
size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_usize_of_nat(v_start_991_);
v___x_1004_ = lean_usize_of_nat(v___x_997_);
v___x_1005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_987_, v_f_988_, v_as_990_, v___x_1003_, v___x_1004_, v_init_989_);
return v___x_1005_;
}
}
else
{
size_t v___x_1006_; size_t v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = lean_usize_of_nat(v_start_991_);
v___x_1007_ = lean_usize_of_nat(v_stop_992_);
v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_987_, v_f_988_, v_as_990_, v___x_1006_, v___x_1007_, v_init_989_);
return v___x_1008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg___boxed(lean_object* v_inst_1009_, lean_object* v_f_1010_, lean_object* v_init_1011_, lean_object* v_as_1012_, lean_object* v_start_1013_, lean_object* v_stop_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Array_foldlMUnsafe___redArg(v_inst_1009_, v_f_1010_, v_init_1011_, v_as_1012_, v_start_1013_, v_stop_1014_);
lean_dec(v_stop_1014_);
lean_dec(v_start_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe(lean_object* v_00_u03b1_1016_, lean_object* v_00_u03b2_1017_, lean_object* v_m_1018_, lean_object* v_inst_1019_, lean_object* v_f_1020_, lean_object* v_init_1021_, lean_object* v_as_1022_, lean_object* v_start_1023_, lean_object* v_stop_1024_){
_start:
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_nat_dec_lt(v_start_1023_, v_stop_1024_);
if (v___x_1025_ == 0)
{
lean_object* v_toApplicative_1026_; lean_object* v_toPure_1027_; lean_object* v___x_1028_; 
lean_dec_ref(v_as_1022_);
lean_dec(v_f_1020_);
v_toApplicative_1026_ = lean_ctor_get(v_inst_1019_, 0);
lean_inc_ref(v_toApplicative_1026_);
lean_dec_ref(v_inst_1019_);
v_toPure_1027_ = lean_ctor_get(v_toApplicative_1026_, 1);
lean_inc(v_toPure_1027_);
lean_dec_ref(v_toApplicative_1026_);
v___x_1028_ = lean_apply_2(v_toPure_1027_, lean_box(0), v_init_1021_);
return v___x_1028_;
}
else
{
lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1029_ = lean_array_get_size(v_as_1022_);
v___x_1030_ = lean_nat_dec_le(v_stop_1024_, v___x_1029_);
if (v___x_1030_ == 0)
{
uint8_t v___x_1031_; 
v___x_1031_ = lean_nat_dec_lt(v_start_1023_, v___x_1029_);
if (v___x_1031_ == 0)
{
lean_object* v_toApplicative_1032_; lean_object* v_toPure_1033_; lean_object* v___x_1034_; 
lean_dec_ref(v_as_1022_);
lean_dec(v_f_1020_);
v_toApplicative_1032_ = lean_ctor_get(v_inst_1019_, 0);
lean_inc_ref(v_toApplicative_1032_);
lean_dec_ref(v_inst_1019_);
v_toPure_1033_ = lean_ctor_get(v_toApplicative_1032_, 1);
lean_inc(v_toPure_1033_);
lean_dec_ref(v_toApplicative_1032_);
v___x_1034_ = lean_apply_2(v_toPure_1033_, lean_box(0), v_init_1021_);
return v___x_1034_;
}
else
{
size_t v___x_1035_; size_t v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = lean_usize_of_nat(v_start_1023_);
v___x_1036_ = lean_usize_of_nat(v___x_1029_);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1019_, v_f_1020_, v_as_1022_, v___x_1035_, v___x_1036_, v_init_1021_);
return v___x_1037_;
}
}
else
{
size_t v___x_1038_; size_t v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = lean_usize_of_nat(v_start_1023_);
v___x_1039_ = lean_usize_of_nat(v_stop_1024_);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1019_, v_f_1020_, v_as_1022_, v___x_1038_, v___x_1039_, v_init_1021_);
return v___x_1040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___boxed(lean_object* v_00_u03b1_1041_, lean_object* v_00_u03b2_1042_, lean_object* v_m_1043_, lean_object* v_inst_1044_, lean_object* v_f_1045_, lean_object* v_init_1046_, lean_object* v_as_1047_, lean_object* v_start_1048_, lean_object* v_stop_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Array_foldlMUnsafe(v_00_u03b1_1041_, v_00_u03b2_1042_, v_m_1043_, v_inst_1044_, v_f_1045_, v_init_1046_, v_as_1047_, v_start_1048_, v_stop_1049_);
lean_dec(v_stop_1049_);
lean_dec(v_start_1048_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_1051_, lean_object* v_inst_1052_, lean_object* v_f_1053_, lean_object* v_as_1054_, lean_object* v_stop_1055_, lean_object* v_n_1056_, lean_object* v_____do__lift_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Array_foldlM_loop___redArg___lam__0(v_j_1051_, v_inst_1052_, v_f_1053_, v_as_1054_, v_stop_1055_, v_n_1056_, v_____do__lift_1057_);
lean_dec(v_n_1056_);
lean_dec(v_j_1051_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg(lean_object* v_inst_1059_, lean_object* v_f_1060_, lean_object* v_as_1061_, lean_object* v_stop_1062_, lean_object* v_i_1063_, lean_object* v_j_1064_, lean_object* v_b_1065_){
_start:
{
uint8_t v___x_1066_; 
v___x_1066_ = lean_nat_dec_lt(v_j_1064_, v_stop_1062_);
if (v___x_1066_ == 0)
{
lean_object* v_toApplicative_1067_; lean_object* v_toPure_1068_; lean_object* v___x_1069_; 
lean_dec(v_j_1064_);
lean_dec(v_stop_1062_);
lean_dec_ref(v_as_1061_);
lean_dec(v_f_1060_);
v_toApplicative_1067_ = lean_ctor_get(v_inst_1059_, 0);
lean_inc_ref(v_toApplicative_1067_);
lean_dec_ref(v_inst_1059_);
v_toPure_1068_ = lean_ctor_get(v_toApplicative_1067_, 1);
lean_inc(v_toPure_1068_);
lean_dec_ref(v_toApplicative_1067_);
v___x_1069_ = lean_apply_2(v_toPure_1068_, lean_box(0), v_b_1065_);
return v___x_1069_;
}
else
{
lean_object* v_zero_1070_; uint8_t v_isZero_1071_; 
v_zero_1070_ = lean_unsigned_to_nat(0u);
v_isZero_1071_ = lean_nat_dec_eq(v_i_1063_, v_zero_1070_);
if (v_isZero_1071_ == 1)
{
lean_object* v_toApplicative_1072_; lean_object* v_toPure_1073_; lean_object* v___x_1074_; 
lean_dec(v_j_1064_);
lean_dec(v_stop_1062_);
lean_dec_ref(v_as_1061_);
lean_dec(v_f_1060_);
v_toApplicative_1072_ = lean_ctor_get(v_inst_1059_, 0);
lean_inc_ref(v_toApplicative_1072_);
lean_dec_ref(v_inst_1059_);
v_toPure_1073_ = lean_ctor_get(v_toApplicative_1072_, 1);
lean_inc(v_toPure_1073_);
lean_dec_ref(v_toApplicative_1072_);
v___x_1074_ = lean_apply_2(v_toPure_1073_, lean_box(0), v_b_1065_);
return v___x_1074_;
}
else
{
lean_object* v_toBind_1075_; lean_object* v_one_1076_; lean_object* v_n_1077_; lean_object* v___f_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_toBind_1075_ = lean_ctor_get(v_inst_1059_, 1);
lean_inc(v_toBind_1075_);
v_one_1076_ = lean_unsigned_to_nat(1u);
v_n_1077_ = lean_nat_sub(v_i_1063_, v_one_1076_);
lean_inc_ref(v_as_1061_);
lean_inc(v_f_1060_);
lean_inc(v_j_1064_);
v___f_1078_ = lean_alloc_closure((void*)(l_Array_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1078_, 0, v_j_1064_);
lean_closure_set(v___f_1078_, 1, v_inst_1059_);
lean_closure_set(v___f_1078_, 2, v_f_1060_);
lean_closure_set(v___f_1078_, 3, v_as_1061_);
lean_closure_set(v___f_1078_, 4, v_stop_1062_);
lean_closure_set(v___f_1078_, 5, v_n_1077_);
v___x_1079_ = lean_array_fget(v_as_1061_, v_j_1064_);
lean_dec(v_j_1064_);
lean_dec_ref(v_as_1061_);
v___x_1080_ = lean_apply_2(v_f_1060_, v_b_1065_, v___x_1079_);
v___x_1081_ = lean_apply_4(v_toBind_1075_, lean_box(0), lean_box(0), v___x_1080_, v___f_1078_);
return v___x_1081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0(lean_object* v_j_1082_, lean_object* v_inst_1083_, lean_object* v_f_1084_, lean_object* v_as_1085_, lean_object* v_stop_1086_, lean_object* v_n_1087_, lean_object* v_____do__lift_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = lean_nat_add(v_j_1082_, v___x_1089_);
v___x_1091_ = l_Array_foldlM_loop___redArg(v_inst_1083_, v_f_1084_, v_as_1085_, v_stop_1086_, v_n_1087_, v___x_1090_, v_____do__lift_1088_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___boxed(lean_object* v_inst_1092_, lean_object* v_f_1093_, lean_object* v_as_1094_, lean_object* v_stop_1095_, lean_object* v_i_1096_, lean_object* v_j_1097_, lean_object* v_b_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Array_foldlM_loop___redArg(v_inst_1092_, v_f_1093_, v_as_1094_, v_stop_1095_, v_i_1096_, v_j_1097_, v_b_1098_);
lean_dec(v_i_1096_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop(lean_object* v_00_u03b1_1100_, lean_object* v_00_u03b2_1101_, lean_object* v_m_1102_, lean_object* v_inst_1103_, lean_object* v_f_1104_, lean_object* v_as_1105_, lean_object* v_stop_1106_, lean_object* v_h_1107_, lean_object* v_i_1108_, lean_object* v_j_1109_, lean_object* v_b_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Array_foldlM_loop___redArg(v_inst_1103_, v_f_1104_, v_as_1105_, v_stop_1106_, v_i_1108_, v_j_1109_, v_b_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___boxed(lean_object* v_00_u03b1_1112_, lean_object* v_00_u03b2_1113_, lean_object* v_m_1114_, lean_object* v_inst_1115_, lean_object* v_f_1116_, lean_object* v_as_1117_, lean_object* v_stop_1118_, lean_object* v_h_1119_, lean_object* v_i_1120_, lean_object* v_j_1121_, lean_object* v_b_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Array_foldlM_loop(v_00_u03b1_1112_, v_00_u03b2_1113_, v_m_1114_, v_inst_1115_, v_f_1116_, v_as_1117_, v_stop_1118_, v_h_1119_, v_i_1120_, v_j_1121_, v_b_1122_);
lean_dec(v_i_1120_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_inst_1124_, lean_object* v_f_1125_, lean_object* v_as_1126_, lean_object* v___x_1127_, lean_object* v_stop_1128_, lean_object* v_____do__lift_1129_){
_start:
{
size_t v___x_94__boxed_1130_; size_t v_stop_boxed_1131_; lean_object* v_res_1132_; 
v___x_94__boxed_1130_ = lean_unbox_usize(v___x_1127_);
lean_dec(v___x_1127_);
v_stop_boxed_1131_ = lean_unbox_usize(v_stop_1128_);
lean_dec(v_stop_1128_);
v_res_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(v_inst_1124_, v_f_1125_, v_as_1126_, v___x_94__boxed_1130_, v_stop_boxed_1131_, v_____do__lift_1129_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(lean_object* v_inst_1133_, lean_object* v_f_1134_, lean_object* v_as_1135_, size_t v_i_1136_, size_t v_stop_1137_, lean_object* v_b_1138_){
_start:
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_usize_dec_eq(v_i_1136_, v_stop_1137_);
if (v___x_1139_ == 0)
{
lean_object* v_toBind_1140_; size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___f_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_toBind_1140_ = lean_ctor_get(v_inst_1133_, 1);
lean_inc(v_toBind_1140_);
v___x_1141_ = ((size_t)1ULL);
v___x_1142_ = lean_usize_sub(v_i_1136_, v___x_1141_);
v___x_1143_ = lean_box_usize(v___x_1142_);
v___x_1144_ = lean_box_usize(v_stop_1137_);
lean_inc_ref(v_as_1135_);
lean_inc(v_f_1134_);
v___f_1145_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1145_, 0, v_inst_1133_);
lean_closure_set(v___f_1145_, 1, v_f_1134_);
lean_closure_set(v___f_1145_, 2, v_as_1135_);
lean_closure_set(v___f_1145_, 3, v___x_1143_);
lean_closure_set(v___f_1145_, 4, v___x_1144_);
v___x_1146_ = lean_array_uget(v_as_1135_, v___x_1142_);
lean_dec_ref(v_as_1135_);
v___x_1147_ = lean_apply_2(v_f_1134_, v___x_1146_, v_b_1138_);
v___x_1148_ = lean_apply_4(v_toBind_1140_, lean_box(0), lean_box(0), v___x_1147_, v___f_1145_);
return v___x_1148_;
}
else
{
lean_object* v_toApplicative_1149_; lean_object* v_toPure_1150_; lean_object* v___x_1151_; 
lean_dec_ref(v_as_1135_);
lean_dec(v_f_1134_);
v_toApplicative_1149_ = lean_ctor_get(v_inst_1133_, 0);
lean_inc_ref(v_toApplicative_1149_);
lean_dec_ref(v_inst_1133_);
v_toPure_1150_ = lean_ctor_get(v_toApplicative_1149_, 1);
lean_inc(v_toPure_1150_);
lean_dec_ref(v_toApplicative_1149_);
v___x_1151_ = lean_apply_2(v_toPure_1150_, lean_box(0), v_b_1138_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(lean_object* v_inst_1152_, lean_object* v_f_1153_, lean_object* v_as_1154_, size_t v___x_1155_, size_t v_stop_1156_, lean_object* v_____do__lift_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1152_, v_f_1153_, v_as_1154_, v___x_1155_, v_stop_1156_, v_____do__lift_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___boxed(lean_object* v_inst_1159_, lean_object* v_f_1160_, lean_object* v_as_1161_, lean_object* v_i_1162_, lean_object* v_stop_1163_, lean_object* v_b_1164_){
_start:
{
size_t v_i_boxed_1165_; size_t v_stop_boxed_1166_; lean_object* v_res_1167_; 
v_i_boxed_1165_ = lean_unbox_usize(v_i_1162_);
lean_dec(v_i_1162_);
v_stop_boxed_1166_ = lean_unbox_usize(v_stop_1163_);
lean_dec(v_stop_1163_);
v_res_1167_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1159_, v_f_1160_, v_as_1161_, v_i_boxed_1165_, v_stop_boxed_1166_, v_b_1164_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object* v_00_u03b1_1168_, lean_object* v_00_u03b2_1169_, lean_object* v_m_1170_, lean_object* v_inst_1171_, lean_object* v_f_1172_, lean_object* v_as_1173_, size_t v_i_1174_, size_t v_stop_1175_, lean_object* v_b_1176_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1171_, v_f_1172_, v_as_1173_, v_i_1174_, v_stop_1175_, v_b_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___boxed(lean_object* v_00_u03b1_1178_, lean_object* v_00_u03b2_1179_, lean_object* v_m_1180_, lean_object* v_inst_1181_, lean_object* v_f_1182_, lean_object* v_as_1183_, lean_object* v_i_1184_, lean_object* v_stop_1185_, lean_object* v_b_1186_){
_start:
{
size_t v_i_boxed_1187_; size_t v_stop_boxed_1188_; lean_object* v_res_1189_; 
v_i_boxed_1187_ = lean_unbox_usize(v_i_1184_);
lean_dec(v_i_1184_);
v_stop_boxed_1188_ = lean_unbox_usize(v_stop_1185_);
lean_dec(v_stop_1185_);
v_res_1189_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(v_00_u03b1_1178_, v_00_u03b2_1179_, v_m_1180_, v_inst_1181_, v_f_1182_, v_as_1183_, v_i_boxed_1187_, v_stop_boxed_1188_, v_b_1186_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg(lean_object* v_inst_1190_, lean_object* v_f_1191_, lean_object* v_init_1192_, lean_object* v_as_1193_, lean_object* v_start_1194_, lean_object* v_stop_1195_){
_start:
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = lean_array_get_size(v_as_1193_);
v___x_1197_ = lean_nat_dec_le(v_start_1194_, v___x_1196_);
if (v___x_1197_ == 0)
{
uint8_t v___x_1198_; 
v___x_1198_ = lean_nat_dec_lt(v_stop_1195_, v___x_1196_);
if (v___x_1198_ == 0)
{
lean_object* v_toApplicative_1199_; lean_object* v_toPure_1200_; lean_object* v___x_1201_; 
lean_dec_ref(v_as_1193_);
lean_dec(v_f_1191_);
v_toApplicative_1199_ = lean_ctor_get(v_inst_1190_, 0);
lean_inc_ref(v_toApplicative_1199_);
lean_dec_ref(v_inst_1190_);
v_toPure_1200_ = lean_ctor_get(v_toApplicative_1199_, 1);
lean_inc(v_toPure_1200_);
lean_dec_ref(v_toApplicative_1199_);
v___x_1201_ = lean_apply_2(v_toPure_1200_, lean_box(0), v_init_1192_);
return v___x_1201_;
}
else
{
size_t v___x_1202_; size_t v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = lean_usize_of_nat(v___x_1196_);
v___x_1203_ = lean_usize_of_nat(v_stop_1195_);
v___x_1204_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1190_, v_f_1191_, v_as_1193_, v___x_1202_, v___x_1203_, v_init_1192_);
return v___x_1204_;
}
}
else
{
uint8_t v___x_1205_; 
v___x_1205_ = lean_nat_dec_lt(v_stop_1195_, v_start_1194_);
if (v___x_1205_ == 0)
{
lean_object* v_toApplicative_1206_; lean_object* v_toPure_1207_; lean_object* v___x_1208_; 
lean_dec_ref(v_as_1193_);
lean_dec(v_f_1191_);
v_toApplicative_1206_ = lean_ctor_get(v_inst_1190_, 0);
lean_inc_ref(v_toApplicative_1206_);
lean_dec_ref(v_inst_1190_);
v_toPure_1207_ = lean_ctor_get(v_toApplicative_1206_, 1);
lean_inc(v_toPure_1207_);
lean_dec_ref(v_toApplicative_1206_);
v___x_1208_ = lean_apply_2(v_toPure_1207_, lean_box(0), v_init_1192_);
return v___x_1208_;
}
else
{
size_t v___x_1209_; size_t v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_usize_of_nat(v_start_1194_);
v___x_1210_ = lean_usize_of_nat(v_stop_1195_);
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1190_, v_f_1191_, v_as_1193_, v___x_1209_, v___x_1210_, v_init_1192_);
return v___x_1211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg___boxed(lean_object* v_inst_1212_, lean_object* v_f_1213_, lean_object* v_init_1214_, lean_object* v_as_1215_, lean_object* v_start_1216_, lean_object* v_stop_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Array_foldrMUnsafe___redArg(v_inst_1212_, v_f_1213_, v_init_1214_, v_as_1215_, v_start_1216_, v_stop_1217_);
lean_dec(v_stop_1217_);
lean_dec(v_start_1216_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe(lean_object* v_00_u03b1_1219_, lean_object* v_00_u03b2_1220_, lean_object* v_m_1221_, lean_object* v_inst_1222_, lean_object* v_f_1223_, lean_object* v_init_1224_, lean_object* v_as_1225_, lean_object* v_start_1226_, lean_object* v_stop_1227_){
_start:
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = lean_array_get_size(v_as_1225_);
v___x_1229_ = lean_nat_dec_le(v_start_1226_, v___x_1228_);
if (v___x_1229_ == 0)
{
uint8_t v___x_1230_; 
v___x_1230_ = lean_nat_dec_lt(v_stop_1227_, v___x_1228_);
if (v___x_1230_ == 0)
{
lean_object* v_toApplicative_1231_; lean_object* v_toPure_1232_; lean_object* v___x_1233_; 
lean_dec_ref(v_as_1225_);
lean_dec(v_f_1223_);
v_toApplicative_1231_ = lean_ctor_get(v_inst_1222_, 0);
lean_inc_ref(v_toApplicative_1231_);
lean_dec_ref(v_inst_1222_);
v_toPure_1232_ = lean_ctor_get(v_toApplicative_1231_, 1);
lean_inc(v_toPure_1232_);
lean_dec_ref(v_toApplicative_1231_);
v___x_1233_ = lean_apply_2(v_toPure_1232_, lean_box(0), v_init_1224_);
return v___x_1233_;
}
else
{
size_t v___x_1234_; size_t v___x_1235_; lean_object* v___x_1236_; 
v___x_1234_ = lean_usize_of_nat(v___x_1228_);
v___x_1235_ = lean_usize_of_nat(v_stop_1227_);
v___x_1236_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1222_, v_f_1223_, v_as_1225_, v___x_1234_, v___x_1235_, v_init_1224_);
return v___x_1236_;
}
}
else
{
uint8_t v___x_1237_; 
v___x_1237_ = lean_nat_dec_lt(v_stop_1227_, v_start_1226_);
if (v___x_1237_ == 0)
{
lean_object* v_toApplicative_1238_; lean_object* v_toPure_1239_; lean_object* v___x_1240_; 
lean_dec_ref(v_as_1225_);
lean_dec(v_f_1223_);
v_toApplicative_1238_ = lean_ctor_get(v_inst_1222_, 0);
lean_inc_ref(v_toApplicative_1238_);
lean_dec_ref(v_inst_1222_);
v_toPure_1239_ = lean_ctor_get(v_toApplicative_1238_, 1);
lean_inc(v_toPure_1239_);
lean_dec_ref(v_toApplicative_1238_);
v___x_1240_ = lean_apply_2(v_toPure_1239_, lean_box(0), v_init_1224_);
return v___x_1240_;
}
else
{
size_t v___x_1241_; size_t v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = lean_usize_of_nat(v_start_1226_);
v___x_1242_ = lean_usize_of_nat(v_stop_1227_);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1222_, v_f_1223_, v_as_1225_, v___x_1241_, v___x_1242_, v_init_1224_);
return v___x_1243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___boxed(lean_object* v_00_u03b1_1244_, lean_object* v_00_u03b2_1245_, lean_object* v_m_1246_, lean_object* v_inst_1247_, lean_object* v_f_1248_, lean_object* v_init_1249_, lean_object* v_as_1250_, lean_object* v_start_1251_, lean_object* v_stop_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Array_foldrMUnsafe(v_00_u03b1_1244_, v_00_u03b2_1245_, v_m_1246_, v_inst_1247_, v_f_1248_, v_init_1249_, v_as_1250_, v_start_1251_, v_stop_1252_);
lean_dec(v_stop_1252_);
lean_dec(v_start_1251_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0___boxed(lean_object* v_inst_1254_, lean_object* v_f_1255_, lean_object* v_as_1256_, lean_object* v_stop_1257_, lean_object* v_n_1258_, lean_object* v_____do__lift_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Array_foldrM_fold___redArg___lam__0(v_inst_1254_, v_f_1255_, v_as_1256_, v_stop_1257_, v_n_1258_, v_____do__lift_1259_);
lean_dec(v_n_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg(lean_object* v_inst_1261_, lean_object* v_f_1262_, lean_object* v_as_1263_, lean_object* v_stop_1264_, lean_object* v_i_1265_, lean_object* v_b_1266_){
_start:
{
uint8_t v___x_1267_; 
v___x_1267_ = lean_nat_dec_eq(v_i_1265_, v_stop_1264_);
if (v___x_1267_ == 0)
{
lean_object* v_zero_1268_; uint8_t v_isZero_1269_; 
v_zero_1268_ = lean_unsigned_to_nat(0u);
v_isZero_1269_ = lean_nat_dec_eq(v_i_1265_, v_zero_1268_);
if (v_isZero_1269_ == 1)
{
lean_object* v_toApplicative_1270_; lean_object* v_toPure_1271_; lean_object* v___x_1272_; 
lean_dec(v_stop_1264_);
lean_dec_ref(v_as_1263_);
lean_dec(v_f_1262_);
v_toApplicative_1270_ = lean_ctor_get(v_inst_1261_, 0);
lean_inc_ref(v_toApplicative_1270_);
lean_dec_ref(v_inst_1261_);
v_toPure_1271_ = lean_ctor_get(v_toApplicative_1270_, 1);
lean_inc(v_toPure_1271_);
lean_dec_ref(v_toApplicative_1270_);
v___x_1272_ = lean_apply_2(v_toPure_1271_, lean_box(0), v_b_1266_);
return v___x_1272_;
}
else
{
lean_object* v_toBind_1273_; lean_object* v_one_1274_; lean_object* v_n_1275_; lean_object* v___f_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_toBind_1273_ = lean_ctor_get(v_inst_1261_, 1);
lean_inc(v_toBind_1273_);
v_one_1274_ = lean_unsigned_to_nat(1u);
v_n_1275_ = lean_nat_sub(v_i_1265_, v_one_1274_);
lean_inc(v_n_1275_);
lean_inc_ref(v_as_1263_);
lean_inc(v_f_1262_);
v___f_1276_ = lean_alloc_closure((void*)(l_Array_foldrM_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1276_, 0, v_inst_1261_);
lean_closure_set(v___f_1276_, 1, v_f_1262_);
lean_closure_set(v___f_1276_, 2, v_as_1263_);
lean_closure_set(v___f_1276_, 3, v_stop_1264_);
lean_closure_set(v___f_1276_, 4, v_n_1275_);
v___x_1277_ = lean_array_fget(v_as_1263_, v_n_1275_);
lean_dec(v_n_1275_);
lean_dec_ref(v_as_1263_);
v___x_1278_ = lean_apply_2(v_f_1262_, v___x_1277_, v_b_1266_);
v___x_1279_ = lean_apply_4(v_toBind_1273_, lean_box(0), lean_box(0), v___x_1278_, v___f_1276_);
return v___x_1279_;
}
}
else
{
lean_object* v_toApplicative_1280_; lean_object* v_toPure_1281_; lean_object* v___x_1282_; 
lean_dec(v_stop_1264_);
lean_dec_ref(v_as_1263_);
lean_dec(v_f_1262_);
v_toApplicative_1280_ = lean_ctor_get(v_inst_1261_, 0);
lean_inc_ref(v_toApplicative_1280_);
lean_dec_ref(v_inst_1261_);
v_toPure_1281_ = lean_ctor_get(v_toApplicative_1280_, 1);
lean_inc(v_toPure_1281_);
lean_dec_ref(v_toApplicative_1280_);
v___x_1282_ = lean_apply_2(v_toPure_1281_, lean_box(0), v_b_1266_);
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0(lean_object* v_inst_1283_, lean_object* v_f_1284_, lean_object* v_as_1285_, lean_object* v_stop_1286_, lean_object* v_n_1287_, lean_object* v_____do__lift_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Array_foldrM_fold___redArg(v_inst_1283_, v_f_1284_, v_as_1285_, v_stop_1286_, v_n_1287_, v_____do__lift_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___boxed(lean_object* v_inst_1290_, lean_object* v_f_1291_, lean_object* v_as_1292_, lean_object* v_stop_1293_, lean_object* v_i_1294_, lean_object* v_b_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Array_foldrM_fold___redArg(v_inst_1290_, v_f_1291_, v_as_1292_, v_stop_1293_, v_i_1294_, v_b_1295_);
lean_dec(v_i_1294_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold(lean_object* v_00_u03b1_1297_, lean_object* v_00_u03b2_1298_, lean_object* v_m_1299_, lean_object* v_inst_1300_, lean_object* v_f_1301_, lean_object* v_as_1302_, lean_object* v_stop_1303_, lean_object* v_i_1304_, lean_object* v_h_1305_, lean_object* v_b_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Array_foldrM_fold___redArg(v_inst_1300_, v_f_1301_, v_as_1302_, v_stop_1303_, v_i_1304_, v_b_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___boxed(lean_object* v_00_u03b1_1308_, lean_object* v_00_u03b2_1309_, lean_object* v_m_1310_, lean_object* v_inst_1311_, lean_object* v_f_1312_, lean_object* v_as_1313_, lean_object* v_stop_1314_, lean_object* v_i_1315_, lean_object* v_h_1316_, lean_object* v_b_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Array_foldrM_fold(v_00_u03b1_1308_, v_00_u03b2_1309_, v_m_1310_, v_inst_1311_, v_f_1312_, v_as_1313_, v_stop_1314_, v_i_1315_, v_h_1316_, v_b_1317_);
lean_dec(v_i_1315_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed(lean_object* v_i_1319_, lean_object* v_bs_x27_1320_, lean_object* v_inst_1321_, lean_object* v_f_1322_, lean_object* v_sz_1323_, lean_object* v_vNew_1324_){
_start:
{
size_t v_i_boxed_1325_; size_t v_sz_boxed_1326_; lean_object* v_res_1327_; 
v_i_boxed_1325_ = lean_unbox_usize(v_i_1319_);
lean_dec(v_i_1319_);
v_sz_boxed_1326_ = lean_unbox_usize(v_sz_1323_);
lean_dec(v_sz_1323_);
v_res_1327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(v_i_boxed_1325_, v_bs_x27_1320_, v_inst_1321_, v_f_1322_, v_sz_boxed_1326_, v_vNew_1324_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(lean_object* v_inst_1328_, lean_object* v_f_1329_, size_t v_sz_1330_, size_t v_i_1331_, lean_object* v_bs_1332_){
_start:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_usize_dec_lt(v_i_1331_, v_sz_1330_);
if (v___x_1333_ == 0)
{
lean_object* v_toApplicative_1334_; lean_object* v_toPure_1335_; lean_object* v___x_1336_; 
lean_dec(v_f_1329_);
v_toApplicative_1334_ = lean_ctor_get(v_inst_1328_, 0);
lean_inc_ref(v_toApplicative_1334_);
lean_dec_ref(v_inst_1328_);
v_toPure_1335_ = lean_ctor_get(v_toApplicative_1334_, 1);
lean_inc(v_toPure_1335_);
lean_dec_ref(v_toApplicative_1334_);
v___x_1336_ = lean_apply_2(v_toPure_1335_, lean_box(0), v_bs_1332_);
return v___x_1336_;
}
else
{
lean_object* v_toBind_1337_; lean_object* v_v_1338_; lean_object* v___x_1339_; lean_object* v_bs_x27_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___f_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_toBind_1337_ = lean_ctor_get(v_inst_1328_, 1);
lean_inc(v_toBind_1337_);
v_v_1338_ = lean_array_uget(v_bs_1332_, v_i_1331_);
v___x_1339_ = lean_unsigned_to_nat(0u);
v_bs_x27_1340_ = lean_array_uset(v_bs_1332_, v_i_1331_, v___x_1339_);
v___x_1341_ = lean_box_usize(v_i_1331_);
v___x_1342_ = lean_box_usize(v_sz_1330_);
lean_inc(v_f_1329_);
v___f_1343_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1343_, 0, v___x_1341_);
lean_closure_set(v___f_1343_, 1, v_bs_x27_1340_);
lean_closure_set(v___f_1343_, 2, v_inst_1328_);
lean_closure_set(v___f_1343_, 3, v_f_1329_);
lean_closure_set(v___f_1343_, 4, v___x_1342_);
v___x_1344_ = lean_apply_1(v_f_1329_, v_v_1338_);
v___x_1345_ = lean_apply_4(v_toBind_1337_, lean_box(0), lean_box(0), v___x_1344_, v___f_1343_);
return v___x_1345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(size_t v_i_1346_, lean_object* v_bs_x27_1347_, lean_object* v_inst_1348_, lean_object* v_f_1349_, size_t v_sz_1350_, lean_object* v_vNew_1351_){
_start:
{
size_t v___x_1352_; size_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1352_ = ((size_t)1ULL);
v___x_1353_ = lean_usize_add(v_i_1346_, v___x_1352_);
v___x_1354_ = lean_array_uset(v_bs_x27_1347_, v_i_1346_, v_vNew_1351_);
v___x_1355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1348_, v_f_1349_, v_sz_1350_, v___x_1353_, v___x_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___boxed(lean_object* v_inst_1356_, lean_object* v_f_1357_, lean_object* v_sz_1358_, lean_object* v_i_1359_, lean_object* v_bs_1360_){
_start:
{
size_t v_sz_boxed_1361_; size_t v_i_boxed_1362_; lean_object* v_res_1363_; 
v_sz_boxed_1361_ = lean_unbox_usize(v_sz_1358_);
lean_dec(v_sz_1358_);
v_i_boxed_1362_ = lean_unbox_usize(v_i_1359_);
lean_dec(v_i_1359_);
v_res_1363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1356_, v_f_1357_, v_sz_boxed_1361_, v_i_boxed_1362_, v_bs_1360_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object* v_00_u03b1_1364_, lean_object* v_00_u03b2_1365_, lean_object* v_m_1366_, lean_object* v_inst_1367_, lean_object* v_f_1368_, size_t v_sz_1369_, size_t v_i_1370_, lean_object* v_bs_1371_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1367_, v_f_1368_, v_sz_1369_, v_i_1370_, v_bs_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___boxed(lean_object* v_00_u03b1_1373_, lean_object* v_00_u03b2_1374_, lean_object* v_m_1375_, lean_object* v_inst_1376_, lean_object* v_f_1377_, lean_object* v_sz_1378_, lean_object* v_i_1379_, lean_object* v_bs_1380_){
_start:
{
size_t v_sz_boxed_1381_; size_t v_i_boxed_1382_; lean_object* v_res_1383_; 
v_sz_boxed_1381_ = lean_unbox_usize(v_sz_1378_);
lean_dec(v_sz_1378_);
v_i_boxed_1382_ = lean_unbox_usize(v_i_1379_);
lean_dec(v_i_1379_);
v_res_1383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(v_00_u03b1_1373_, v_00_u03b2_1374_, v_m_1375_, v_inst_1376_, v_f_1377_, v_sz_boxed_1381_, v_i_boxed_1382_, v_bs_1380_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe___redArg(lean_object* v_inst_1384_, lean_object* v_f_1385_, lean_object* v_as_1386_){
_start:
{
size_t v_sz_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
v_sz_1387_ = lean_array_size(v_as_1386_);
v___x_1388_ = ((size_t)0ULL);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1384_, v_f_1385_, v_sz_1387_, v___x_1388_, v_as_1386_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe(lean_object* v_00_u03b1_1390_, lean_object* v_00_u03b2_1391_, lean_object* v_m_1392_, lean_object* v_inst_1393_, lean_object* v_f_1394_, lean_object* v_as_1395_){
_start:
{
size_t v_sz_1396_; size_t v___x_1397_; lean_object* v___x_1398_; 
v_sz_1396_ = lean_array_size(v_as_1395_);
v___x_1397_ = ((size_t)0ULL);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1393_, v_f_1394_, v_sz_1396_, v___x_1397_, v_as_1395_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0___boxed(lean_object* v_i_1399_, lean_object* v_bs_1400_, lean_object* v_inst_1401_, lean_object* v_f_1402_, lean_object* v_as_1403_, lean_object* v_____do__lift_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0(v_i_1399_, v_bs_1400_, v_inst_1401_, v_f_1402_, v_as_1403_, v_____do__lift_1404_);
lean_dec(v_i_1399_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(lean_object* v_inst_1406_, lean_object* v_f_1407_, lean_object* v_as_1408_, lean_object* v_i_1409_, lean_object* v_bs_1410_){
_start:
{
lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1411_ = lean_array_get_size(v_as_1408_);
v___x_1412_ = lean_nat_dec_lt(v_i_1409_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v_toApplicative_1413_; lean_object* v_toPure_1414_; lean_object* v___x_1415_; 
lean_dec(v_i_1409_);
lean_dec_ref(v_as_1408_);
lean_dec(v_f_1407_);
v_toApplicative_1413_ = lean_ctor_get(v_inst_1406_, 0);
lean_inc_ref(v_toApplicative_1413_);
lean_dec_ref(v_inst_1406_);
v_toPure_1414_ = lean_ctor_get(v_toApplicative_1413_, 1);
lean_inc(v_toPure_1414_);
lean_dec_ref(v_toApplicative_1413_);
v___x_1415_ = lean_apply_2(v_toPure_1414_, lean_box(0), v_bs_1410_);
return v___x_1415_;
}
else
{
lean_object* v_toBind_1416_; lean_object* v___f_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v_toBind_1416_ = lean_ctor_get(v_inst_1406_, 1);
lean_inc(v_toBind_1416_);
lean_inc_ref(v_as_1408_);
lean_inc(v_f_1407_);
lean_inc(v_i_1409_);
v___f_1417_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1417_, 0, v_i_1409_);
lean_closure_set(v___f_1417_, 1, v_bs_1410_);
lean_closure_set(v___f_1417_, 2, v_inst_1406_);
lean_closure_set(v___f_1417_, 3, v_f_1407_);
lean_closure_set(v___f_1417_, 4, v_as_1408_);
v___x_1418_ = lean_array_fget(v_as_1408_, v_i_1409_);
lean_dec(v_i_1409_);
lean_dec_ref(v_as_1408_);
v___x_1419_ = lean_apply_1(v_f_1407_, v___x_1418_);
v___x_1420_ = lean_apply_4(v_toBind_1416_, lean_box(0), lean_box(0), v___x_1419_, v___f_1417_);
return v___x_1420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0(lean_object* v_i_1421_, lean_object* v_bs_1422_, lean_object* v_inst_1423_, lean_object* v_f_1424_, lean_object* v_as_1425_, lean_object* v_____do__lift_1426_){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1427_ = lean_unsigned_to_nat(1u);
v___x_1428_ = lean_nat_add(v_i_1421_, v___x_1427_);
v___x_1429_ = lean_array_push(v_bs_1422_, v_____do__lift_1426_);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(v_inst_1423_, v_f_1424_, v_as_1425_, v___x_1428_, v___x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map(lean_object* v_00_u03b1_1431_, lean_object* v_00_u03b2_1432_, lean_object* v_m_1433_, lean_object* v_inst_1434_, lean_object* v_f_1435_, lean_object* v_as_1436_, lean_object* v_i_1437_, lean_object* v_bs_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(v_inst_1434_, v_f_1435_, v_as_1436_, v_i_1437_, v_bs_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1440_, lean_object* v_bs_1441_, lean_object* v_inst_1442_, lean_object* v_as_1443_, lean_object* v_f_1444_, lean_object* v_n_1445_, lean_object* v_____do__lift_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Array_mapFinIdxM_map___redArg___lam__0(v_j_1440_, v_bs_1441_, v_inst_1442_, v_as_1443_, v_f_1444_, v_n_1445_, v_____do__lift_1446_);
lean_dec(v_n_1445_);
lean_dec(v_j_1440_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg(lean_object* v_inst_1448_, lean_object* v_as_1449_, lean_object* v_f_1450_, lean_object* v_i_1451_, lean_object* v_j_1452_, lean_object* v_bs_1453_){
_start:
{
lean_object* v_toApplicative_1454_; lean_object* v_toBind_1455_; lean_object* v_toPure_1456_; lean_object* v_zero_1457_; uint8_t v_isZero_1458_; 
v_toApplicative_1454_ = lean_ctor_get(v_inst_1448_, 0);
v_toBind_1455_ = lean_ctor_get(v_inst_1448_, 1);
lean_inc(v_toBind_1455_);
v_toPure_1456_ = lean_ctor_get(v_toApplicative_1454_, 1);
v_zero_1457_ = lean_unsigned_to_nat(0u);
v_isZero_1458_ = lean_nat_dec_eq(v_i_1451_, v_zero_1457_);
if (v_isZero_1458_ == 1)
{
lean_object* v___x_1459_; 
lean_inc(v_toPure_1456_);
lean_dec(v_toBind_1455_);
lean_dec(v_j_1452_);
lean_dec(v_f_1450_);
lean_dec_ref(v_as_1449_);
lean_dec_ref(v_inst_1448_);
v___x_1459_ = lean_apply_2(v_toPure_1456_, lean_box(0), v_bs_1453_);
return v___x_1459_;
}
else
{
lean_object* v_one_1460_; lean_object* v_n_1461_; lean_object* v___f_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_one_1460_ = lean_unsigned_to_nat(1u);
v_n_1461_ = lean_nat_sub(v_i_1451_, v_one_1460_);
lean_inc(v_f_1450_);
lean_inc_ref(v_as_1449_);
lean_inc(v_j_1452_);
v___f_1462_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1462_, 0, v_j_1452_);
lean_closure_set(v___f_1462_, 1, v_bs_1453_);
lean_closure_set(v___f_1462_, 2, v_inst_1448_);
lean_closure_set(v___f_1462_, 3, v_as_1449_);
lean_closure_set(v___f_1462_, 4, v_f_1450_);
lean_closure_set(v___f_1462_, 5, v_n_1461_);
v___x_1463_ = lean_array_fget(v_as_1449_, v_j_1452_);
lean_dec_ref(v_as_1449_);
v___x_1464_ = lean_apply_3(v_f_1450_, v_j_1452_, v___x_1463_, lean_box(0));
v___x_1465_ = lean_apply_4(v_toBind_1455_, lean_box(0), lean_box(0), v___x_1464_, v___f_1462_);
return v___x_1465_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1466_, lean_object* v_bs_1467_, lean_object* v_inst_1468_, lean_object* v_as_1469_, lean_object* v_f_1470_, lean_object* v_n_1471_, lean_object* v_____do__lift_1472_){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_add(v_j_1466_, v___x_1473_);
v___x_1475_ = lean_array_push(v_bs_1467_, v_____do__lift_1472_);
v___x_1476_ = l_Array_mapFinIdxM_map___redArg(v_inst_1468_, v_as_1469_, v_f_1470_, v_n_1471_, v___x_1474_, v___x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1477_, lean_object* v_as_1478_, lean_object* v_f_1479_, lean_object* v_i_1480_, lean_object* v_j_1481_, lean_object* v_bs_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Array_mapFinIdxM_map___redArg(v_inst_1477_, v_as_1478_, v_f_1479_, v_i_1480_, v_j_1481_, v_bs_1482_);
lean_dec(v_i_1480_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map(lean_object* v_00_u03b1_1484_, lean_object* v_00_u03b2_1485_, lean_object* v_m_1486_, lean_object* v_inst_1487_, lean_object* v_as_1488_, lean_object* v_f_1489_, lean_object* v_i_1490_, lean_object* v_j_1491_, lean_object* v_inv_1492_, lean_object* v_bs_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Array_mapFinIdxM_map___redArg(v_inst_1487_, v_as_1488_, v_f_1489_, v_i_1490_, v_j_1491_, v_bs_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___boxed(lean_object* v_00_u03b1_1495_, lean_object* v_00_u03b2_1496_, lean_object* v_m_1497_, lean_object* v_inst_1498_, lean_object* v_as_1499_, lean_object* v_f_1500_, lean_object* v_i_1501_, lean_object* v_j_1502_, lean_object* v_inv_1503_, lean_object* v_bs_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Array_mapFinIdxM_map(v_00_u03b1_1495_, v_00_u03b2_1496_, v_m_1497_, v_inst_1498_, v_as_1499_, v_f_1500_, v_i_1501_, v_j_1502_, v_inv_1503_, v_bs_1504_);
lean_dec(v_i_1501_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM___redArg(lean_object* v_inst_1506_, lean_object* v_as_1507_, lean_object* v_f_1508_){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1509_ = lean_array_get_size(v_as_1507_);
v___x_1510_ = lean_unsigned_to_nat(0u);
v___x_1511_ = lean_mk_empty_array_with_capacity(v___x_1509_);
v___x_1512_ = l_Array_mapFinIdxM_map___redArg(v_inst_1506_, v_as_1507_, v_f_1508_, v___x_1509_, v___x_1510_, v___x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM(lean_object* v_00_u03b1_1513_, lean_object* v_00_u03b2_1514_, lean_object* v_m_1515_, lean_object* v_inst_1516_, lean_object* v_as_1517_, lean_object* v_f_1518_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1519_ = lean_array_get_size(v_as_1517_);
v___x_1520_ = lean_unsigned_to_nat(0u);
v___x_1521_ = lean_mk_empty_array_with_capacity(v___x_1519_);
v___x_1522_ = l_Array_mapFinIdxM_map___redArg(v_inst_1516_, v_as_1517_, v_f_1518_, v___x_1519_, v___x_1520_, v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg___lam__0(lean_object* v_f_1523_, lean_object* v_i_1524_, lean_object* v_a_1525_, lean_object* v_x_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_apply_2(v_f_1523_, v_i_1524_, v_a_1525_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg(lean_object* v_inst_1528_, lean_object* v_f_1529_, lean_object* v_as_1530_){
_start:
{
lean_object* v___f_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___f_1531_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1531_, 0, v_f_1529_);
v___x_1532_ = lean_array_get_size(v_as_1530_);
v___x_1533_ = lean_unsigned_to_nat(0u);
v___x_1534_ = lean_mk_empty_array_with_capacity(v___x_1532_);
v___x_1535_ = l_Array_mapFinIdxM_map___redArg(v_inst_1528_, v_as_1530_, v___f_1531_, v___x_1532_, v___x_1533_, v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM(lean_object* v_00_u03b1_1536_, lean_object* v_00_u03b2_1537_, lean_object* v_m_1538_, lean_object* v_inst_1539_, lean_object* v_f_1540_, lean_object* v_as_1541_){
_start:
{
lean_object* v___f_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___f_1542_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1542_, 0, v_f_1540_);
v___x_1543_ = lean_array_get_size(v_as_1541_);
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = lean_mk_empty_array_with_capacity(v___x_1543_);
v___x_1546_ = l_Array_mapFinIdxM_map___redArg(v_inst_1539_, v_as_1541_, v___f_1542_, v___x_1543_, v___x_1544_, v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed(lean_object* v_i_1547_, lean_object* v_inst_1548_, lean_object* v_f_1549_, lean_object* v_as_1550_, lean_object* v_x_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(v_i_1547_, v_inst_1548_, v_f_1549_, v_as_1550_, v_x_1551_);
lean_dec(v_i_1547_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(lean_object* v_inst_1553_, lean_object* v_f_1554_, lean_object* v_as_1555_, lean_object* v_i_1556_){
_start:
{
lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = lean_array_get_size(v_as_1555_);
v___x_1558_ = lean_nat_dec_lt(v_i_1556_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v_failure_1559_; lean_object* v___x_1560_; 
lean_dec(v_i_1556_);
lean_dec_ref(v_as_1555_);
lean_dec(v_f_1554_);
v_failure_1559_ = lean_ctor_get(v_inst_1553_, 1);
lean_inc(v_failure_1559_);
lean_dec_ref(v_inst_1553_);
v___x_1560_ = lean_apply_1(v_failure_1559_, lean_box(0));
return v___x_1560_;
}
else
{
lean_object* v_orElse_1561_; lean_object* v___f_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_orElse_1561_ = lean_ctor_get(v_inst_1553_, 2);
lean_inc(v_orElse_1561_);
lean_inc_ref(v_as_1555_);
lean_inc(v_f_1554_);
lean_inc(v_i_1556_);
v___f_1562_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1562_, 0, v_i_1556_);
lean_closure_set(v___f_1562_, 1, v_inst_1553_);
lean_closure_set(v___f_1562_, 2, v_f_1554_);
lean_closure_set(v___f_1562_, 3, v_as_1555_);
v___x_1563_ = lean_array_fget(v_as_1555_, v_i_1556_);
lean_dec(v_i_1556_);
lean_dec_ref(v_as_1555_);
v___x_1564_ = lean_apply_1(v_f_1554_, v___x_1563_);
v___x_1565_ = lean_apply_3(v_orElse_1561_, lean_box(0), v___x_1564_, v___f_1562_);
return v___x_1565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(lean_object* v_i_1566_, lean_object* v_inst_1567_, lean_object* v_f_1568_, lean_object* v_as_1569_, lean_object* v_x_1570_){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = lean_unsigned_to_nat(1u);
v___x_1572_ = lean_nat_add(v_i_1566_, v___x_1571_);
v___x_1573_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1567_, v_f_1568_, v_as_1569_, v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_object* v_00_u03b2_1574_, lean_object* v_00_u03b1_1575_, lean_object* v_m_1576_, lean_object* v_inst_1577_, lean_object* v_f_1578_, lean_object* v_as_1579_, lean_object* v_i_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1577_, v_f_1578_, v_as_1579_, v_i_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM___redArg(lean_object* v_inst_1582_, lean_object* v_f_1583_, lean_object* v_as_1584_){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_unsigned_to_nat(0u);
v___x_1586_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1582_, v_f_1583_, v_as_1584_, v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM(lean_object* v_00_u03b2_1587_, lean_object* v_00_u03b1_1588_, lean_object* v_m_1589_, lean_object* v_inst_1590_, lean_object* v_f_1591_, lean_object* v_as_1592_){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1590_, v_f_1591_, v_as_1592_, v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__0(lean_object* v___x_1595_, lean_object* v_toPure_1596_, lean_object* v___x_1597_, lean_object* v_____do__lift_1598_){
_start:
{
if (lean_obj_tag(v_____do__lift_1598_) == 1)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_dec_ref(v___x_1597_);
v___x_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1599_, 0, v_____do__lift_1598_);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v___x_1595_);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
v___x_1602_ = lean_apply_2(v_toPure_1596_, lean_box(0), v___x_1601_);
return v___x_1602_;
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v_____do__lift_1598_);
v___x_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1597_);
v___x_1604_ = lean_apply_2(v_toPure_1596_, lean_box(0), v___x_1603_);
return v___x_1604_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1(lean_object* v_f_1605_, lean_object* v_toBind_1606_, lean_object* v___f_1607_, lean_object* v_a_1608_, lean_object* v_x_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_apply_1(v_f_1605_, v_a_1608_);
v___x_1612_ = lean_apply_4(v_toBind_1606_, lean_box(0), lean_box(0), v___x_1611_, v___f_1607_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1___boxed(lean_object* v_f_1613_, lean_object* v_toBind_1614_, lean_object* v___f_1615_, lean_object* v_a_1616_, lean_object* v_x_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Array_findSomeM_x3f___redArg___lam__1(v_f_1613_, v_toBind_1614_, v___f_1615_, v_a_1616_, v_x_1617_, v___y_1618_);
lean_dec_ref(v___y_1618_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__2(lean_object* v_toPure_1620_, lean_object* v_____s_1621_){
_start:
{
lean_object* v_fst_1622_; 
v_fst_1622_ = lean_ctor_get(v_____s_1621_, 0);
lean_inc(v_fst_1622_);
lean_dec_ref(v_____s_1621_);
if (lean_obj_tag(v_fst_1622_) == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_box(0);
v___x_1624_ = lean_apply_2(v_toPure_1620_, lean_box(0), v___x_1623_);
return v___x_1624_;
}
else
{
lean_object* v_val_1625_; lean_object* v___x_1626_; 
v_val_1625_ = lean_ctor_get(v_fst_1622_, 0);
lean_inc(v_val_1625_);
lean_dec_ref(v_fst_1622_);
v___x_1626_ = lean_apply_2(v_toPure_1620_, lean_box(0), v_val_1625_);
return v___x_1626_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg(lean_object* v_inst_1630_, lean_object* v_f_1631_, lean_object* v_as_1632_){
_start:
{
lean_object* v_toApplicative_1633_; lean_object* v_toBind_1634_; lean_object* v_toPure_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___f_1638_; lean_object* v___f_1639_; lean_object* v___f_1640_; size_t v_sz_1641_; size_t v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_toApplicative_1633_ = lean_ctor_get(v_inst_1630_, 0);
v_toBind_1634_ = lean_ctor_get(v_inst_1630_, 1);
lean_inc(v_toBind_1634_);
v_toPure_1635_ = lean_ctor_get(v_toApplicative_1633_, 1);
v___x_1636_ = lean_box(0);
v___x_1637_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc(v_toPure_1635_);
v___f_1638_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1638_, 0, v___x_1636_);
lean_closure_set(v___f_1638_, 1, v_toPure_1635_);
lean_closure_set(v___f_1638_, 2, v___x_1637_);
lean_inc(v_toBind_1634_);
v___f_1639_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1639_, 0, v_f_1631_);
lean_closure_set(v___f_1639_, 1, v_toBind_1634_);
lean_closure_set(v___f_1639_, 2, v___f_1638_);
lean_inc(v_toPure_1635_);
v___f_1640_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1640_, 0, v_toPure_1635_);
v_sz_1641_ = lean_array_size(v_as_1632_);
v___x_1642_ = ((size_t)0ULL);
v___x_1643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1630_, v_as_1632_, v___f_1639_, v_sz_1641_, v___x_1642_, v___x_1637_);
v___x_1644_ = lean_apply_4(v_toBind_1634_, lean_box(0), lean_box(0), v___x_1643_, v___f_1640_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f(lean_object* v_00_u03b1_1645_, lean_object* v_00_u03b2_1646_, lean_object* v_m_1647_, lean_object* v_inst_1648_, lean_object* v_f_1649_, lean_object* v_as_1650_){
_start:
{
lean_object* v_toApplicative_1651_; lean_object* v_toBind_1652_; lean_object* v_toPure_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___f_1656_; lean_object* v___f_1657_; lean_object* v___f_1658_; size_t v_sz_1659_; size_t v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_toApplicative_1651_ = lean_ctor_get(v_inst_1648_, 0);
v_toBind_1652_ = lean_ctor_get(v_inst_1648_, 1);
lean_inc(v_toBind_1652_);
v_toPure_1653_ = lean_ctor_get(v_toApplicative_1651_, 1);
v___x_1654_ = lean_box(0);
v___x_1655_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc(v_toPure_1653_);
v___f_1656_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1656_, 0, v___x_1654_);
lean_closure_set(v___f_1656_, 1, v_toPure_1653_);
lean_closure_set(v___f_1656_, 2, v___x_1655_);
lean_inc(v_toBind_1652_);
v___f_1657_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1657_, 0, v_f_1649_);
lean_closure_set(v___f_1657_, 1, v_toBind_1652_);
lean_closure_set(v___f_1657_, 2, v___f_1656_);
lean_inc(v_toPure_1653_);
v___f_1658_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1658_, 0, v_toPure_1653_);
v_sz_1659_ = lean_array_size(v_as_1650_);
v___x_1660_ = ((size_t)0ULL);
v___x_1661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1648_, v_as_1650_, v___f_1657_, v_sz_1659_, v___x_1660_, v___x_1655_);
v___x_1662_ = lean_apply_4(v_toBind_1652_, lean_box(0), lean_box(0), v___x_1661_, v___f_1658_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0(lean_object* v___x_1663_, lean_object* v_toPure_1664_, lean_object* v_a_1665_, lean_object* v___x_1666_, uint8_t v_____do__lift_1667_){
_start:
{
if (v_____do__lift_1667_ == 0)
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec(v_a_1665_);
v___x_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1663_);
v___x_1669_ = lean_apply_2(v_toPure_1664_, lean_box(0), v___x_1668_);
return v___x_1669_;
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_dec_ref(v___x_1663_);
v___x_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1670_, 0, v_a_1665_);
v___x_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v___x_1666_);
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
v___x_1674_ = lean_apply_2(v_toPure_1664_, lean_box(0), v___x_1673_);
return v___x_1674_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0___boxed(lean_object* v___x_1675_, lean_object* v_toPure_1676_, lean_object* v_a_1677_, lean_object* v___x_1678_, lean_object* v_____do__lift_1679_){
_start:
{
uint8_t v_____do__lift_214__boxed_1680_; lean_object* v_res_1681_; 
v_____do__lift_214__boxed_1680_ = lean_unbox(v_____do__lift_1679_);
v_res_1681_ = l_Array_findM_x3f___redArg___lam__0(v___x_1675_, v_toPure_1676_, v_a_1677_, v___x_1678_, v_____do__lift_214__boxed_1680_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1(lean_object* v___x_1682_, lean_object* v_toPure_1683_, lean_object* v___x_1684_, lean_object* v_p_1685_, lean_object* v_toBind_1686_, lean_object* v_a_1687_, lean_object* v_x_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v___f_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_inc(v_a_1687_);
v___f_1690_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1690_, 0, v___x_1682_);
lean_closure_set(v___f_1690_, 1, v_toPure_1683_);
lean_closure_set(v___f_1690_, 2, v_a_1687_);
lean_closure_set(v___f_1690_, 3, v___x_1684_);
v___x_1691_ = lean_apply_1(v_p_1685_, v_a_1687_);
v___x_1692_ = lean_apply_4(v_toBind_1686_, lean_box(0), lean_box(0), v___x_1691_, v___f_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_1693_, lean_object* v_toPure_1694_, lean_object* v___x_1695_, lean_object* v_p_1696_, lean_object* v_toBind_1697_, lean_object* v_a_1698_, lean_object* v_x_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Array_findM_x3f___redArg___lam__1(v___x_1693_, v_toPure_1694_, v___x_1695_, v_p_1696_, v_toBind_1697_, v_a_1698_, v_x_1699_, v___y_1700_);
lean_dec_ref(v___y_1700_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg(lean_object* v_inst_1702_, lean_object* v_p_1703_, lean_object* v_as_1704_){
_start:
{
lean_object* v_toApplicative_1705_; lean_object* v_toBind_1706_; lean_object* v_toPure_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___f_1710_; lean_object* v___f_1711_; size_t v_sz_1712_; size_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_toApplicative_1705_ = lean_ctor_get(v_inst_1702_, 0);
v_toBind_1706_ = lean_ctor_get(v_inst_1702_, 1);
lean_inc(v_toBind_1706_);
v_toPure_1707_ = lean_ctor_get(v_toApplicative_1705_, 1);
v___x_1708_ = lean_box(0);
v___x_1709_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc(v_toBind_1706_);
lean_inc(v_toPure_1707_);
v___f_1710_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1710_, 0, v___x_1709_);
lean_closure_set(v___f_1710_, 1, v_toPure_1707_);
lean_closure_set(v___f_1710_, 2, v___x_1708_);
lean_closure_set(v___f_1710_, 3, v_p_1703_);
lean_closure_set(v___f_1710_, 4, v_toBind_1706_);
lean_inc(v_toPure_1707_);
v___f_1711_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1711_, 0, v_toPure_1707_);
v_sz_1712_ = lean_array_size(v_as_1704_);
v___x_1713_ = ((size_t)0ULL);
v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1702_, v_as_1704_, v___f_1710_, v_sz_1712_, v___x_1713_, v___x_1709_);
v___x_1715_ = lean_apply_4(v_toBind_1706_, lean_box(0), lean_box(0), v___x_1714_, v___f_1711_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f(lean_object* v_m_1716_, lean_object* v_00_u03b1_1717_, lean_object* v_inst_1718_, lean_object* v_p_1719_, lean_object* v_as_1720_){
_start:
{
lean_object* v_toApplicative_1721_; lean_object* v_toBind_1722_; lean_object* v_toPure_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___f_1726_; lean_object* v___f_1727_; size_t v_sz_1728_; size_t v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_toApplicative_1721_ = lean_ctor_get(v_inst_1718_, 0);
v_toBind_1722_ = lean_ctor_get(v_inst_1718_, 1);
lean_inc(v_toBind_1722_);
v_toPure_1723_ = lean_ctor_get(v_toApplicative_1721_, 1);
v___x_1724_ = lean_box(0);
v___x_1725_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc(v_toBind_1722_);
lean_inc(v_toPure_1723_);
v___f_1726_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1726_, 0, v___x_1725_);
lean_closure_set(v___f_1726_, 1, v_toPure_1723_);
lean_closure_set(v___f_1726_, 2, v___x_1724_);
lean_closure_set(v___f_1726_, 3, v_p_1719_);
lean_closure_set(v___f_1726_, 4, v_toBind_1722_);
lean_inc(v_toPure_1723_);
v___f_1727_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1727_, 0, v_toPure_1723_);
v_sz_1728_ = lean_array_size(v_as_1720_);
v___x_1729_ = ((size_t)0ULL);
v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1718_, v_as_1720_, v___f_1726_, v_sz_1728_, v___x_1729_, v___x_1725_);
v___x_1731_ = lean_apply_4(v_toBind_1722_, lean_box(0), lean_box(0), v___x_1730_, v___f_1727_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0(lean_object* v_snd_1732_, lean_object* v___x_1733_, lean_object* v_toPure_1734_, uint8_t v_____do__lift_1735_){
_start:
{
if (v_____do__lift_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1736_ = lean_unsigned_to_nat(1u);
v___x_1737_ = lean_nat_add(v_snd_1732_, v___x_1736_);
lean_dec(v_snd_1732_);
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1733_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
v___x_1740_ = lean_apply_2(v_toPure_1734_, lean_box(0), v___x_1739_);
return v___x_1740_;
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec(v___x_1733_);
lean_inc(v_snd_1732_);
v___x_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1741_, 0, v_snd_1732_);
v___x_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v_snd_1732_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
v___x_1745_ = lean_apply_2(v_toPure_1734_, lean_box(0), v___x_1744_);
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0___boxed(lean_object* v_snd_1746_, lean_object* v___x_1747_, lean_object* v_toPure_1748_, lean_object* v_____do__lift_1749_){
_start:
{
uint8_t v_____do__lift_249__boxed_1750_; lean_object* v_res_1751_; 
v_____do__lift_249__boxed_1750_ = lean_unbox(v_____do__lift_1749_);
v_res_1751_ = l_Array_findIdxM_x3f___redArg___lam__0(v_snd_1746_, v___x_1747_, v_toPure_1748_, v_____do__lift_249__boxed_1750_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__1(lean_object* v___x_1752_, lean_object* v_toPure_1753_, lean_object* v_p_1754_, lean_object* v_toBind_1755_, lean_object* v_a_1756_, lean_object* v_x_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_snd_1759_; lean_object* v___f_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_snd_1759_ = lean_ctor_get(v___y_1758_, 1);
lean_inc(v_snd_1759_);
lean_dec_ref(v___y_1758_);
v___f_1760_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1760_, 0, v_snd_1759_);
lean_closure_set(v___f_1760_, 1, v___x_1752_);
lean_closure_set(v___f_1760_, 2, v_toPure_1753_);
v___x_1761_ = lean_apply_1(v_p_1754_, v_a_1756_);
v___x_1762_ = lean_apply_4(v_toBind_1755_, lean_box(0), lean_box(0), v___x_1761_, v___f_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__2(lean_object* v_toPure_1763_, lean_object* v_____s_1764_){
_start:
{
lean_object* v_fst_1765_; 
v_fst_1765_ = lean_ctor_get(v_____s_1764_, 0);
lean_inc(v_fst_1765_);
lean_dec_ref(v_____s_1764_);
if (lean_obj_tag(v_fst_1765_) == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_apply_2(v_toPure_1763_, lean_box(0), v___x_1766_);
return v___x_1767_;
}
else
{
lean_object* v_val_1768_; lean_object* v___x_1769_; 
v_val_1768_ = lean_ctor_get(v_fst_1765_, 0);
lean_inc(v_val_1768_);
lean_dec_ref(v_fst_1765_);
v___x_1769_ = lean_apply_2(v_toPure_1763_, lean_box(0), v_val_1768_);
return v___x_1769_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg(lean_object* v_inst_1773_, lean_object* v_p_1774_, lean_object* v_as_1775_){
_start:
{
lean_object* v_toApplicative_1776_; lean_object* v_toBind_1777_; lean_object* v_toPure_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___f_1781_; lean_object* v___f_1782_; size_t v_sz_1783_; size_t v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_toApplicative_1776_ = lean_ctor_get(v_inst_1773_, 0);
v_toBind_1777_ = lean_ctor_get(v_inst_1773_, 1);
lean_inc(v_toBind_1777_);
v_toPure_1778_ = lean_ctor_get(v_toApplicative_1776_, 1);
v___x_1779_ = lean_box(0);
v___x_1780_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc(v_toBind_1777_);
lean_inc(v_toPure_1778_);
v___f_1781_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1781_, 0, v___x_1779_);
lean_closure_set(v___f_1781_, 1, v_toPure_1778_);
lean_closure_set(v___f_1781_, 2, v_p_1774_);
lean_closure_set(v___f_1781_, 3, v_toBind_1777_);
lean_inc(v_toPure_1778_);
v___f_1782_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1782_, 0, v_toPure_1778_);
v_sz_1783_ = lean_array_size(v_as_1775_);
v___x_1784_ = ((size_t)0ULL);
v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1773_, v_as_1775_, v___f_1781_, v_sz_1783_, v___x_1784_, v___x_1780_);
v___x_1786_ = lean_apply_4(v_toBind_1777_, lean_box(0), lean_box(0), v___x_1785_, v___f_1782_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f(lean_object* v_00_u03b1_1787_, lean_object* v_m_1788_, lean_object* v_inst_1789_, lean_object* v_p_1790_, lean_object* v_as_1791_){
_start:
{
lean_object* v_toApplicative_1792_; lean_object* v_toBind_1793_; lean_object* v_toPure_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___f_1797_; lean_object* v___f_1798_; size_t v_sz_1799_; size_t v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_toApplicative_1792_ = lean_ctor_get(v_inst_1789_, 0);
v_toBind_1793_ = lean_ctor_get(v_inst_1789_, 1);
lean_inc(v_toBind_1793_);
v_toPure_1794_ = lean_ctor_get(v_toApplicative_1792_, 1);
v___x_1795_ = lean_box(0);
v___x_1796_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc(v_toBind_1793_);
lean_inc(v_toPure_1794_);
v___f_1797_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1797_, 0, v___x_1795_);
lean_closure_set(v___f_1797_, 1, v_toPure_1794_);
lean_closure_set(v___f_1797_, 2, v_p_1790_);
lean_closure_set(v___f_1797_, 3, v_toBind_1793_);
lean_inc(v_toPure_1794_);
v___f_1798_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1798_, 0, v_toPure_1794_);
v_sz_1799_ = lean_array_size(v_as_1791_);
v___x_1800_ = ((size_t)0ULL);
v___x_1801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1789_, v_as_1791_, v___f_1797_, v_sz_1799_, v___x_1800_, v___x_1796_);
v___x_1802_ = lean_apply_4(v_toBind_1793_, lean_box(0), lean_box(0), v___x_1801_, v___f_1798_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed(lean_object* v_i_1803_, lean_object* v_inst_1804_, lean_object* v_p_1805_, lean_object* v_as_1806_, lean_object* v_stop_1807_, lean_object* v_toApplicative_1808_, lean_object* v___x_1809_, lean_object* v_____do__lift_1810_){
_start:
{
size_t v_i_boxed_1811_; size_t v_stop_boxed_1812_; uint8_t v___x_153__boxed_1813_; uint8_t v_____do__lift_154__boxed_1814_; lean_object* v_res_1815_; 
v_i_boxed_1811_ = lean_unbox_usize(v_i_1803_);
lean_dec(v_i_1803_);
v_stop_boxed_1812_ = lean_unbox_usize(v_stop_1807_);
lean_dec(v_stop_1807_);
v___x_153__boxed_1813_ = lean_unbox(v___x_1809_);
v_____do__lift_154__boxed_1814_ = lean_unbox(v_____do__lift_1810_);
v_res_1815_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(v_i_boxed_1811_, v_inst_1804_, v_p_1805_, v_as_1806_, v_stop_boxed_1812_, v_toApplicative_1808_, v___x_153__boxed_1813_, v_____do__lift_154__boxed_1814_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(lean_object* v_inst_1816_, lean_object* v_p_1817_, lean_object* v_as_1818_, size_t v_i_1819_, size_t v_stop_1820_){
_start:
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_usize_dec_eq(v_i_1819_, v_stop_1820_);
if (v___x_1821_ == 0)
{
lean_object* v_toApplicative_1822_; lean_object* v_toBind_1823_; uint8_t v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___f_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v_toApplicative_1822_ = lean_ctor_get(v_inst_1816_, 0);
lean_inc_ref(v_toApplicative_1822_);
v_toBind_1823_ = lean_ctor_get(v_inst_1816_, 1);
lean_inc(v_toBind_1823_);
v___x_1824_ = 1;
v___x_1825_ = lean_box_usize(v_i_1819_);
v___x_1826_ = lean_box_usize(v_stop_1820_);
v___x_1827_ = lean_box(v___x_1824_);
lean_inc_ref(v_as_1818_);
lean_inc(v_p_1817_);
v___f_1828_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1828_, 0, v___x_1825_);
lean_closure_set(v___f_1828_, 1, v_inst_1816_);
lean_closure_set(v___f_1828_, 2, v_p_1817_);
lean_closure_set(v___f_1828_, 3, v_as_1818_);
lean_closure_set(v___f_1828_, 4, v___x_1826_);
lean_closure_set(v___f_1828_, 5, v_toApplicative_1822_);
lean_closure_set(v___f_1828_, 6, v___x_1827_);
v___x_1829_ = lean_array_uget(v_as_1818_, v_i_1819_);
lean_dec_ref(v_as_1818_);
v___x_1830_ = lean_apply_1(v_p_1817_, v___x_1829_);
v___x_1831_ = lean_apply_4(v_toBind_1823_, lean_box(0), lean_box(0), v___x_1830_, v___f_1828_);
return v___x_1831_;
}
else
{
lean_object* v_toApplicative_1832_; lean_object* v_toPure_1833_; uint8_t v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec_ref(v_as_1818_);
lean_dec(v_p_1817_);
v_toApplicative_1832_ = lean_ctor_get(v_inst_1816_, 0);
lean_inc_ref(v_toApplicative_1832_);
lean_dec_ref(v_inst_1816_);
v_toPure_1833_ = lean_ctor_get(v_toApplicative_1832_, 1);
lean_inc(v_toPure_1833_);
lean_dec_ref(v_toApplicative_1832_);
v___x_1834_ = 0;
v___x_1835_ = lean_box(v___x_1834_);
v___x_1836_ = lean_apply_2(v_toPure_1833_, lean_box(0), v___x_1835_);
return v___x_1836_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(size_t v_i_1837_, lean_object* v_inst_1838_, lean_object* v_p_1839_, lean_object* v_as_1840_, size_t v_stop_1841_, lean_object* v_toApplicative_1842_, uint8_t v___x_1843_, uint8_t v_____do__lift_1844_){
_start:
{
if (v_____do__lift_1844_ == 0)
{
size_t v___x_1845_; size_t v___x_1846_; lean_object* v___x_1847_; 
lean_dec_ref(v_toApplicative_1842_);
v___x_1845_ = ((size_t)1ULL);
v___x_1846_ = lean_usize_add(v_i_1837_, v___x_1845_);
v___x_1847_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1838_, v_p_1839_, v_as_1840_, v___x_1846_, v_stop_1841_);
return v___x_1847_;
}
else
{
lean_object* v_toPure_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
lean_dec_ref(v_as_1840_);
lean_dec(v_p_1839_);
lean_dec_ref(v_inst_1838_);
v_toPure_1848_ = lean_ctor_get(v_toApplicative_1842_, 1);
lean_inc(v_toPure_1848_);
lean_dec_ref(v_toApplicative_1842_);
v___x_1849_ = lean_box(v___x_1843_);
v___x_1850_ = lean_apply_2(v_toPure_1848_, lean_box(0), v___x_1849_);
return v___x_1850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___boxed(lean_object* v_inst_1851_, lean_object* v_p_1852_, lean_object* v_as_1853_, lean_object* v_i_1854_, lean_object* v_stop_1855_){
_start:
{
size_t v_i_boxed_1856_; size_t v_stop_boxed_1857_; lean_object* v_res_1858_; 
v_i_boxed_1856_ = lean_unbox_usize(v_i_1854_);
lean_dec(v_i_1854_);
v_stop_boxed_1857_ = lean_unbox_usize(v_stop_1855_);
lean_dec(v_stop_1855_);
v_res_1858_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1851_, v_p_1852_, v_as_1853_, v_i_boxed_1856_, v_stop_boxed_1857_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object* v_00_u03b1_1859_, lean_object* v_m_1860_, lean_object* v_inst_1861_, lean_object* v_p_1862_, lean_object* v_as_1863_, size_t v_i_1864_, size_t v_stop_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1861_, v_p_1862_, v_as_1863_, v_i_1864_, v_stop_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___boxed(lean_object* v_00_u03b1_1867_, lean_object* v_m_1868_, lean_object* v_inst_1869_, lean_object* v_p_1870_, lean_object* v_as_1871_, lean_object* v_i_1872_, lean_object* v_stop_1873_){
_start:
{
size_t v_i_boxed_1874_; size_t v_stop_boxed_1875_; lean_object* v_res_1876_; 
v_i_boxed_1874_ = lean_unbox_usize(v_i_1872_);
lean_dec(v_i_1872_);
v_stop_boxed_1875_ = lean_unbox_usize(v_stop_1873_);
lean_dec(v_stop_1873_);
v_res_1876_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(v_00_u03b1_1867_, v_m_1868_, v_inst_1869_, v_p_1870_, v_as_1871_, v_i_boxed_1874_, v_stop_boxed_1875_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg(lean_object* v_inst_1877_, lean_object* v_p_1878_, lean_object* v_as_1879_, lean_object* v_start_1880_, lean_object* v_stop_1881_){
_start:
{
lean_object* v___y_1883_; uint8_t v___x_1892_; 
v___x_1892_ = lean_nat_dec_lt(v_start_1880_, v_stop_1881_);
if (v___x_1892_ == 0)
{
lean_object* v_toApplicative_1893_; lean_object* v_toPure_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_dec(v_stop_1881_);
lean_dec_ref(v_as_1879_);
lean_dec(v_p_1878_);
v_toApplicative_1893_ = lean_ctor_get(v_inst_1877_, 0);
lean_inc_ref(v_toApplicative_1893_);
lean_dec_ref(v_inst_1877_);
v_toPure_1894_ = lean_ctor_get(v_toApplicative_1893_, 1);
lean_inc(v_toPure_1894_);
lean_dec_ref(v_toApplicative_1893_);
v___x_1895_ = lean_box(v___x_1892_);
v___x_1896_ = lean_apply_2(v_toPure_1894_, lean_box(0), v___x_1895_);
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1897_ = lean_array_get_size(v_as_1879_);
v___x_1898_ = lean_nat_dec_le(v_stop_1881_, v___x_1897_);
if (v___x_1898_ == 0)
{
lean_dec(v_stop_1881_);
v___y_1883_ = v___x_1897_;
goto v___jp_1882_;
}
else
{
v___y_1883_ = v_stop_1881_;
goto v___jp_1882_;
}
}
v___jp_1882_:
{
uint8_t v___x_1884_; 
v___x_1884_ = lean_nat_dec_lt(v_start_1880_, v___y_1883_);
if (v___x_1884_ == 0)
{
lean_object* v_toApplicative_1885_; lean_object* v_toPure_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_dec(v___y_1883_);
lean_dec_ref(v_as_1879_);
lean_dec(v_p_1878_);
v_toApplicative_1885_ = lean_ctor_get(v_inst_1877_, 0);
lean_inc_ref(v_toApplicative_1885_);
lean_dec_ref(v_inst_1877_);
v_toPure_1886_ = lean_ctor_get(v_toApplicative_1885_, 1);
lean_inc(v_toPure_1886_);
lean_dec_ref(v_toApplicative_1885_);
v___x_1887_ = lean_box(v___x_1884_);
v___x_1888_ = lean_apply_2(v_toPure_1886_, lean_box(0), v___x_1887_);
return v___x_1888_;
}
else
{
size_t v___x_1889_; size_t v___x_1890_; lean_object* v___x_1891_; 
v___x_1889_ = lean_usize_of_nat(v_start_1880_);
v___x_1890_ = lean_usize_of_nat(v___y_1883_);
lean_dec(v___y_1883_);
v___x_1891_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1877_, v_p_1878_, v_as_1879_, v___x_1889_, v___x_1890_);
return v___x_1891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg___boxed(lean_object* v_inst_1899_, lean_object* v_p_1900_, lean_object* v_as_1901_, lean_object* v_start_1902_, lean_object* v_stop_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Array_anyMUnsafe___redArg(v_inst_1899_, v_p_1900_, v_as_1901_, v_start_1902_, v_stop_1903_);
lean_dec(v_start_1902_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe(lean_object* v_00_u03b1_1905_, lean_object* v_m_1906_, lean_object* v_inst_1907_, lean_object* v_p_1908_, lean_object* v_as_1909_, lean_object* v_start_1910_, lean_object* v_stop_1911_){
_start:
{
lean_object* v___y_1913_; uint8_t v___x_1922_; 
v___x_1922_ = lean_nat_dec_lt(v_start_1910_, v_stop_1911_);
if (v___x_1922_ == 0)
{
lean_object* v_toApplicative_1923_; lean_object* v_toPure_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_dec(v_stop_1911_);
lean_dec_ref(v_as_1909_);
lean_dec(v_p_1908_);
v_toApplicative_1923_ = lean_ctor_get(v_inst_1907_, 0);
lean_inc_ref(v_toApplicative_1923_);
lean_dec_ref(v_inst_1907_);
v_toPure_1924_ = lean_ctor_get(v_toApplicative_1923_, 1);
lean_inc(v_toPure_1924_);
lean_dec_ref(v_toApplicative_1923_);
v___x_1925_ = lean_box(v___x_1922_);
v___x_1926_ = lean_apply_2(v_toPure_1924_, lean_box(0), v___x_1925_);
return v___x_1926_;
}
else
{
lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = lean_array_get_size(v_as_1909_);
v___x_1928_ = lean_nat_dec_le(v_stop_1911_, v___x_1927_);
if (v___x_1928_ == 0)
{
lean_dec(v_stop_1911_);
v___y_1913_ = v___x_1927_;
goto v___jp_1912_;
}
else
{
v___y_1913_ = v_stop_1911_;
goto v___jp_1912_;
}
}
v___jp_1912_:
{
uint8_t v___x_1914_; 
v___x_1914_ = lean_nat_dec_lt(v_start_1910_, v___y_1913_);
if (v___x_1914_ == 0)
{
lean_object* v_toApplicative_1915_; lean_object* v_toPure_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_dec(v___y_1913_);
lean_dec_ref(v_as_1909_);
lean_dec(v_p_1908_);
v_toApplicative_1915_ = lean_ctor_get(v_inst_1907_, 0);
lean_inc_ref(v_toApplicative_1915_);
lean_dec_ref(v_inst_1907_);
v_toPure_1916_ = lean_ctor_get(v_toApplicative_1915_, 1);
lean_inc(v_toPure_1916_);
lean_dec_ref(v_toApplicative_1915_);
v___x_1917_ = lean_box(v___x_1914_);
v___x_1918_ = lean_apply_2(v_toPure_1916_, lean_box(0), v___x_1917_);
return v___x_1918_;
}
else
{
size_t v___x_1919_; size_t v___x_1920_; lean_object* v___x_1921_; 
v___x_1919_ = lean_usize_of_nat(v_start_1910_);
v___x_1920_ = lean_usize_of_nat(v___y_1913_);
lean_dec(v___y_1913_);
v___x_1921_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1907_, v_p_1908_, v_as_1909_, v___x_1919_, v___x_1920_);
return v___x_1921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___boxed(lean_object* v_00_u03b1_1929_, lean_object* v_m_1930_, lean_object* v_inst_1931_, lean_object* v_p_1932_, lean_object* v_as_1933_, lean_object* v_start_1934_, lean_object* v_stop_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Array_anyMUnsafe(v_00_u03b1_1929_, v_m_1930_, v_inst_1931_, v_p_1932_, v_as_1933_, v_start_1934_, v_stop_1935_);
lean_dec(v_start_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0___boxed(lean_object* v_j_1937_, lean_object* v_inst_1938_, lean_object* v_p_1939_, lean_object* v_as_1940_, lean_object* v_stop_1941_, lean_object* v_toApplicative_1942_, lean_object* v_____do__lift_1943_){
_start:
{
uint8_t v_____do__lift_82__boxed_1944_; lean_object* v_res_1945_; 
v_____do__lift_82__boxed_1944_ = lean_unbox(v_____do__lift_1943_);
v_res_1945_ = l_Array_anyM_loop___redArg___lam__0(v_j_1937_, v_inst_1938_, v_p_1939_, v_as_1940_, v_stop_1941_, v_toApplicative_1942_, v_____do__lift_82__boxed_1944_);
lean_dec(v_j_1937_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg(lean_object* v_inst_1946_, lean_object* v_p_1947_, lean_object* v_as_1948_, lean_object* v_stop_1949_, lean_object* v_j_1950_){
_start:
{
uint8_t v___x_1951_; 
v___x_1951_ = lean_nat_dec_lt(v_j_1950_, v_stop_1949_);
if (v___x_1951_ == 0)
{
lean_object* v_toApplicative_1952_; lean_object* v_toPure_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec(v_j_1950_);
lean_dec(v_stop_1949_);
lean_dec_ref(v_as_1948_);
lean_dec(v_p_1947_);
v_toApplicative_1952_ = lean_ctor_get(v_inst_1946_, 0);
lean_inc_ref(v_toApplicative_1952_);
lean_dec_ref(v_inst_1946_);
v_toPure_1953_ = lean_ctor_get(v_toApplicative_1952_, 1);
lean_inc(v_toPure_1953_);
lean_dec_ref(v_toApplicative_1952_);
v___x_1954_ = lean_box(v___x_1951_);
v___x_1955_ = lean_apply_2(v_toPure_1953_, lean_box(0), v___x_1954_);
return v___x_1955_;
}
else
{
lean_object* v_toApplicative_1956_; lean_object* v_toBind_1957_; lean_object* v___f_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v_toApplicative_1956_ = lean_ctor_get(v_inst_1946_, 0);
lean_inc_ref(v_toApplicative_1956_);
v_toBind_1957_ = lean_ctor_get(v_inst_1946_, 1);
lean_inc(v_toBind_1957_);
lean_inc_ref(v_as_1948_);
lean_inc(v_p_1947_);
lean_inc(v_j_1950_);
v___f_1958_ = lean_alloc_closure((void*)(l_Array_anyM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1958_, 0, v_j_1950_);
lean_closure_set(v___f_1958_, 1, v_inst_1946_);
lean_closure_set(v___f_1958_, 2, v_p_1947_);
lean_closure_set(v___f_1958_, 3, v_as_1948_);
lean_closure_set(v___f_1958_, 4, v_stop_1949_);
lean_closure_set(v___f_1958_, 5, v_toApplicative_1956_);
v___x_1959_ = lean_array_fget(v_as_1948_, v_j_1950_);
lean_dec(v_j_1950_);
lean_dec_ref(v_as_1948_);
v___x_1960_ = lean_apply_1(v_p_1947_, v___x_1959_);
v___x_1961_ = lean_apply_4(v_toBind_1957_, lean_box(0), lean_box(0), v___x_1960_, v___f_1958_);
return v___x_1961_;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0(lean_object* v_j_1962_, lean_object* v_inst_1963_, lean_object* v_p_1964_, lean_object* v_as_1965_, lean_object* v_stop_1966_, lean_object* v_toApplicative_1967_, uint8_t v_____do__lift_1968_){
_start:
{
if (v_____do__lift_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec_ref(v_toApplicative_1967_);
v___x_1969_ = lean_unsigned_to_nat(1u);
v___x_1970_ = lean_nat_add(v_j_1962_, v___x_1969_);
v___x_1971_ = l_Array_anyM_loop___redArg(v_inst_1963_, v_p_1964_, v_as_1965_, v_stop_1966_, v___x_1970_);
return v___x_1971_;
}
else
{
lean_object* v_toPure_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_dec(v_stop_1966_);
lean_dec_ref(v_as_1965_);
lean_dec(v_p_1964_);
lean_dec_ref(v_inst_1963_);
v_toPure_1972_ = lean_ctor_get(v_toApplicative_1967_, 1);
lean_inc(v_toPure_1972_);
lean_dec_ref(v_toApplicative_1967_);
v___x_1973_ = lean_box(v_____do__lift_1968_);
v___x_1974_ = lean_apply_2(v_toPure_1972_, lean_box(0), v___x_1973_);
return v___x_1974_;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop(lean_object* v_00_u03b1_1975_, lean_object* v_m_1976_, lean_object* v_inst_1977_, lean_object* v_p_1978_, lean_object* v_as_1979_, lean_object* v_stop_1980_, lean_object* v_h_1981_, lean_object* v_j_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Array_anyM_loop___redArg(v_inst_1977_, v_p_1978_, v_as_1979_, v_stop_1980_, v_j_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0(lean_object* v_toPure_1984_, uint8_t v_____do__lift_1985_){
_start:
{
if (v_____do__lift_1985_ == 0)
{
uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = 1;
v___x_1987_ = lean_box(v___x_1986_);
v___x_1988_ = lean_apply_2(v_toPure_1984_, lean_box(0), v___x_1987_);
return v___x_1988_;
}
else
{
uint8_t v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = 0;
v___x_1990_ = lean_box(v___x_1989_);
v___x_1991_ = lean_apply_2(v_toPure_1984_, lean_box(0), v___x_1990_);
return v___x_1991_;
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0___boxed(lean_object* v_toPure_1992_, lean_object* v_____do__lift_1993_){
_start:
{
uint8_t v_____do__lift_123__boxed_1994_; lean_object* v_res_1995_; 
v_____do__lift_123__boxed_1994_ = lean_unbox(v_____do__lift_1993_);
v_res_1995_ = l_Array_allM___redArg___lam__0(v_toPure_1992_, v_____do__lift_123__boxed_1994_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1(lean_object* v_toPure_1996_, uint8_t v___x_1997_, uint8_t v_____do__lift_1998_){
_start:
{
if (v_____do__lift_1998_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_box(v___x_1997_);
v___x_2000_ = lean_apply_2(v_toPure_1996_, lean_box(0), v___x_1999_);
return v___x_2000_;
}
else
{
uint8_t v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2001_ = 0;
v___x_2002_ = lean_box(v___x_2001_);
v___x_2003_ = lean_apply_2(v_toPure_1996_, lean_box(0), v___x_2002_);
return v___x_2003_;
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1___boxed(lean_object* v_toPure_2004_, lean_object* v___x_2005_, lean_object* v_____do__lift_2006_){
_start:
{
uint8_t v___x_138__boxed_2007_; uint8_t v_____do__lift_139__boxed_2008_; lean_object* v_res_2009_; 
v___x_138__boxed_2007_ = lean_unbox(v___x_2005_);
v_____do__lift_139__boxed_2008_ = lean_unbox(v_____do__lift_2006_);
v_res_2009_ = l_Array_allM___redArg___lam__1(v_toPure_2004_, v___x_138__boxed_2007_, v_____do__lift_139__boxed_2008_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__2(lean_object* v_p_2010_, lean_object* v_toBind_2011_, lean_object* v___f_2012_, lean_object* v_v_2013_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = lean_apply_1(v_p_2010_, v_v_2013_);
v___x_2015_ = lean_apply_4(v_toBind_2011_, lean_box(0), lean_box(0), v___x_2014_, v___f_2012_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg(lean_object* v_inst_2016_, lean_object* v_p_2017_, lean_object* v_as_2018_, lean_object* v_start_2019_, lean_object* v_stop_2020_){
_start:
{
lean_object* v_toApplicative_2021_; lean_object* v_toBind_2022_; lean_object* v_toPure_2023_; lean_object* v___f_2024_; uint8_t v___x_2025_; 
v_toApplicative_2021_ = lean_ctor_get(v_inst_2016_, 0);
v_toBind_2022_ = lean_ctor_get(v_inst_2016_, 1);
lean_inc(v_toBind_2022_);
v_toPure_2023_ = lean_ctor_get(v_toApplicative_2021_, 1);
lean_inc(v_toPure_2023_);
v___f_2024_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2024_, 0, v_toPure_2023_);
v___x_2025_ = lean_nat_dec_lt(v_start_2019_, v_stop_2020_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
lean_inc(v_toPure_2023_);
lean_dec(v_stop_2020_);
lean_dec_ref(v_as_2018_);
lean_dec(v_p_2017_);
lean_dec_ref(v_inst_2016_);
v___x_2026_ = lean_box(v___x_2025_);
v___x_2027_ = lean_apply_2(v_toPure_2023_, lean_box(0), v___x_2026_);
v___x_2028_ = lean_apply_4(v_toBind_2022_, lean_box(0), lean_box(0), v___x_2027_, v___f_2024_);
return v___x_2028_;
}
else
{
lean_object* v___x_2029_; lean_object* v___f_2030_; lean_object* v___f_2031_; lean_object* v___y_2033_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2029_ = lean_box(v___x_2025_);
lean_inc(v_toPure_2023_);
v___f_2030_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2030_, 0, v_toPure_2023_);
lean_closure_set(v___f_2030_, 1, v___x_2029_);
lean_inc(v_toBind_2022_);
v___f_2031_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2031_, 0, v_p_2017_);
lean_closure_set(v___f_2031_, 1, v_toBind_2022_);
lean_closure_set(v___f_2031_, 2, v___f_2030_);
v___x_2042_ = lean_array_get_size(v_as_2018_);
v___x_2043_ = lean_nat_dec_le(v_stop_2020_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_dec(v_stop_2020_);
v___y_2033_ = v___x_2042_;
goto v___jp_2032_;
}
else
{
v___y_2033_ = v_stop_2020_;
goto v___jp_2032_;
}
v___jp_2032_:
{
uint8_t v___x_2034_; 
v___x_2034_ = lean_nat_dec_lt(v_start_2019_, v___y_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_inc(v_toPure_2023_);
lean_dec(v___y_2033_);
lean_dec_ref(v___f_2031_);
lean_dec_ref(v_as_2018_);
lean_dec_ref(v_inst_2016_);
v___x_2035_ = lean_box(v___x_2034_);
v___x_2036_ = lean_apply_2(v_toPure_2023_, lean_box(0), v___x_2035_);
v___x_2037_ = lean_apply_4(v_toBind_2022_, lean_box(0), lean_box(0), v___x_2036_, v___f_2024_);
return v___x_2037_;
}
else
{
size_t v___x_2038_; size_t v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2038_ = lean_usize_of_nat(v_start_2019_);
v___x_2039_ = lean_usize_of_nat(v___y_2033_);
lean_dec(v___y_2033_);
v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2016_, v___f_2031_, v_as_2018_, v___x_2038_, v___x_2039_);
v___x_2041_ = lean_apply_4(v_toBind_2022_, lean_box(0), lean_box(0), v___x_2040_, v___f_2024_);
return v___x_2041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___boxed(lean_object* v_inst_2044_, lean_object* v_p_2045_, lean_object* v_as_2046_, lean_object* v_start_2047_, lean_object* v_stop_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Array_allM___redArg(v_inst_2044_, v_p_2045_, v_as_2046_, v_start_2047_, v_stop_2048_);
lean_dec(v_start_2047_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Array_allM(lean_object* v_00_u03b1_2050_, lean_object* v_m_2051_, lean_object* v_inst_2052_, lean_object* v_p_2053_, lean_object* v_as_2054_, lean_object* v_start_2055_, lean_object* v_stop_2056_){
_start:
{
lean_object* v_toApplicative_2057_; lean_object* v_toBind_2058_; lean_object* v_toPure_2059_; lean_object* v___f_2060_; uint8_t v___x_2061_; 
v_toApplicative_2057_ = lean_ctor_get(v_inst_2052_, 0);
v_toBind_2058_ = lean_ctor_get(v_inst_2052_, 1);
lean_inc(v_toBind_2058_);
v_toPure_2059_ = lean_ctor_get(v_toApplicative_2057_, 1);
lean_inc(v_toPure_2059_);
v___f_2060_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2060_, 0, v_toPure_2059_);
v___x_2061_ = lean_nat_dec_lt(v_start_2055_, v_stop_2056_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
lean_inc(v_toPure_2059_);
lean_dec(v_stop_2056_);
lean_dec_ref(v_as_2054_);
lean_dec(v_p_2053_);
lean_dec_ref(v_inst_2052_);
v___x_2062_ = lean_box(v___x_2061_);
v___x_2063_ = lean_apply_2(v_toPure_2059_, lean_box(0), v___x_2062_);
v___x_2064_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___x_2063_, v___f_2060_);
return v___x_2064_;
}
else
{
lean_object* v___x_2065_; lean_object* v___f_2066_; lean_object* v___f_2067_; lean_object* v___y_2069_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2065_ = lean_box(v___x_2061_);
lean_inc(v_toPure_2059_);
v___f_2066_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2066_, 0, v_toPure_2059_);
lean_closure_set(v___f_2066_, 1, v___x_2065_);
lean_inc(v_toBind_2058_);
v___f_2067_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2067_, 0, v_p_2053_);
lean_closure_set(v___f_2067_, 1, v_toBind_2058_);
lean_closure_set(v___f_2067_, 2, v___f_2066_);
v___x_2078_ = lean_array_get_size(v_as_2054_);
v___x_2079_ = lean_nat_dec_le(v_stop_2056_, v___x_2078_);
if (v___x_2079_ == 0)
{
lean_dec(v_stop_2056_);
v___y_2069_ = v___x_2078_;
goto v___jp_2068_;
}
else
{
v___y_2069_ = v_stop_2056_;
goto v___jp_2068_;
}
v___jp_2068_:
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_nat_dec_lt(v_start_2055_, v___y_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_inc(v_toPure_2059_);
lean_dec(v___y_2069_);
lean_dec_ref(v___f_2067_);
lean_dec_ref(v_as_2054_);
lean_dec_ref(v_inst_2052_);
v___x_2071_ = lean_box(v___x_2070_);
v___x_2072_ = lean_apply_2(v_toPure_2059_, lean_box(0), v___x_2071_);
v___x_2073_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___x_2072_, v___f_2060_);
return v___x_2073_;
}
else
{
size_t v___x_2074_; size_t v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2074_ = lean_usize_of_nat(v_start_2055_);
v___x_2075_ = lean_usize_of_nat(v___y_2069_);
lean_dec(v___y_2069_);
v___x_2076_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2052_, v___f_2067_, v_as_2054_, v___x_2074_, v___x_2075_);
v___x_2077_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___x_2076_, v___f_2060_);
return v___x_2077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___boxed(lean_object* v_00_u03b1_2080_, lean_object* v_m_2081_, lean_object* v_inst_2082_, lean_object* v_p_2083_, lean_object* v_as_2084_, lean_object* v_start_2085_, lean_object* v_stop_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Array_allM(v_00_u03b1_2080_, v_m_2081_, v_inst_2082_, v_p_2083_, v_as_2084_, v_start_2085_, v_stop_2086_);
lean_dec(v_start_2085_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed(lean_object* v_inst_2088_, lean_object* v_f_2089_, lean_object* v_as_2090_, lean_object* v_n_2091_, lean_object* v_toPure_2092_, lean_object* v_r_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(v_inst_2088_, v_f_2089_, v_as_2090_, v_n_2091_, v_toPure_2092_, v_r_2093_);
lean_dec(v_n_2091_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(lean_object* v_inst_2095_, lean_object* v_f_2096_, lean_object* v_as_2097_, lean_object* v_i_2098_){
_start:
{
lean_object* v_toApplicative_2099_; lean_object* v_toBind_2100_; lean_object* v_toPure_2101_; lean_object* v_zero_2102_; uint8_t v_isZero_2103_; 
v_toApplicative_2099_ = lean_ctor_get(v_inst_2095_, 0);
v_toBind_2100_ = lean_ctor_get(v_inst_2095_, 1);
lean_inc(v_toBind_2100_);
v_toPure_2101_ = lean_ctor_get(v_toApplicative_2099_, 1);
lean_inc(v_toPure_2101_);
v_zero_2102_ = lean_unsigned_to_nat(0u);
v_isZero_2103_ = lean_nat_dec_eq(v_i_2098_, v_zero_2102_);
if (v_isZero_2103_ == 1)
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
lean_dec(v_toBind_2100_);
lean_dec_ref(v_as_2097_);
lean_dec(v_f_2096_);
lean_dec_ref(v_inst_2095_);
v___x_2104_ = lean_box(0);
v___x_2105_ = lean_apply_2(v_toPure_2101_, lean_box(0), v___x_2104_);
return v___x_2105_;
}
else
{
lean_object* v_one_2106_; lean_object* v_n_2107_; lean_object* v___f_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v_one_2106_ = lean_unsigned_to_nat(1u);
v_n_2107_ = lean_nat_sub(v_i_2098_, v_one_2106_);
lean_inc(v_n_2107_);
lean_inc_ref(v_as_2097_);
lean_inc(v_f_2096_);
v___f_2108_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2108_, 0, v_inst_2095_);
lean_closure_set(v___f_2108_, 1, v_f_2096_);
lean_closure_set(v___f_2108_, 2, v_as_2097_);
lean_closure_set(v___f_2108_, 3, v_n_2107_);
lean_closure_set(v___f_2108_, 4, v_toPure_2101_);
v___x_2109_ = lean_array_fget(v_as_2097_, v_n_2107_);
lean_dec(v_n_2107_);
lean_dec_ref(v_as_2097_);
v___x_2110_ = lean_apply_1(v_f_2096_, v___x_2109_);
v___x_2111_ = lean_apply_4(v_toBind_2100_, lean_box(0), lean_box(0), v___x_2110_, v___f_2108_);
return v___x_2111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(lean_object* v_inst_2112_, lean_object* v_f_2113_, lean_object* v_as_2114_, lean_object* v_n_2115_, lean_object* v_toPure_2116_, lean_object* v_r_2117_){
_start:
{
if (lean_obj_tag(v_r_2117_) == 0)
{
lean_object* v___x_2118_; 
lean_dec(v_toPure_2116_);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2112_, v_f_2113_, v_as_2114_, v_n_2115_);
return v___x_2118_;
}
else
{
lean_object* v___x_2119_; 
lean_dec_ref(v_as_2114_);
lean_dec(v_f_2113_);
lean_dec_ref(v_inst_2112_);
v___x_2119_ = lean_apply_2(v_toPure_2116_, lean_box(0), v_r_2117_);
return v___x_2119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___boxed(lean_object* v_inst_2120_, lean_object* v_f_2121_, lean_object* v_as_2122_, lean_object* v_i_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2120_, v_f_2121_, v_as_2122_, v_i_2123_);
lean_dec(v_i_2123_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_object* v_00_u03b1_2125_, lean_object* v_00_u03b2_2126_, lean_object* v_m_2127_, lean_object* v_inst_2128_, lean_object* v_f_2129_, lean_object* v_as_2130_, lean_object* v_i_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2128_, v_f_2129_, v_as_2130_, v_i_2131_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___boxed(lean_object* v_00_u03b1_2134_, lean_object* v_00_u03b2_2135_, lean_object* v_m_2136_, lean_object* v_inst_2137_, lean_object* v_f_2138_, lean_object* v_as_2139_, lean_object* v_i_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(v_00_u03b1_2134_, v_00_u03b2_2135_, v_m_2136_, v_inst_2137_, v_f_2138_, v_as_2139_, v_i_2140_, v_a_2141_);
lean_dec(v_i_2140_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f___redArg(lean_object* v_inst_2143_, lean_object* v_f_2144_, lean_object* v_as_2145_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_array_get_size(v_as_2145_);
v___x_2147_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2143_, v_f_2144_, v_as_2145_, v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f(lean_object* v_00_u03b1_2148_, lean_object* v_00_u03b2_2149_, lean_object* v_m_2150_, lean_object* v_inst_2151_, lean_object* v_f_2152_, lean_object* v_as_2153_){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_array_get_size(v_as_2153_);
v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2151_, v_f_2152_, v_as_2153_, v___x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2156_, lean_object* v_a_2157_, uint8_t v_____do__lift_2158_){
_start:
{
if (v_____do__lift_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec(v_a_2157_);
v___x_2159_ = lean_box(0);
v___x_2160_ = lean_apply_2(v_toPure_2156_, lean_box(0), v___x_2159_);
return v___x_2160_;
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2161_, 0, v_a_2157_);
v___x_2162_ = lean_apply_2(v_toPure_2156_, lean_box(0), v___x_2161_);
return v___x_2162_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2163_, lean_object* v_a_2164_, lean_object* v_____do__lift_2165_){
_start:
{
uint8_t v_____do__lift_74__boxed_2166_; lean_object* v_res_2167_; 
v_____do__lift_74__boxed_2166_ = lean_unbox(v_____do__lift_2165_);
v_res_2167_ = l_Array_findRevM_x3f___redArg___lam__0(v_toPure_2163_, v_a_2164_, v_____do__lift_74__boxed_2166_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2168_, lean_object* v_p_2169_, lean_object* v_toBind_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v___f_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
lean_inc(v_a_2171_);
v___f_2172_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2172_, 0, v_toPure_2168_);
lean_closure_set(v___f_2172_, 1, v_a_2171_);
v___x_2173_ = lean_apply_1(v_p_2169_, v_a_2171_);
v___x_2174_ = lean_apply_4(v_toBind_2170_, lean_box(0), lean_box(0), v___x_2173_, v___f_2172_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg(lean_object* v_inst_2175_, lean_object* v_p_2176_, lean_object* v_as_2177_){
_start:
{
lean_object* v_toApplicative_2178_; lean_object* v_toBind_2179_; lean_object* v_toPure_2180_; lean_object* v___f_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_toApplicative_2178_ = lean_ctor_get(v_inst_2175_, 0);
v_toBind_2179_ = lean_ctor_get(v_inst_2175_, 1);
v_toPure_2180_ = lean_ctor_get(v_toApplicative_2178_, 1);
lean_inc(v_toBind_2179_);
lean_inc(v_toPure_2180_);
v___f_2181_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2181_, 0, v_toPure_2180_);
lean_closure_set(v___f_2181_, 1, v_p_2176_);
lean_closure_set(v___f_2181_, 2, v_toBind_2179_);
v___x_2182_ = lean_array_get_size(v_as_2177_);
v___x_2183_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2175_, v___f_2181_, v_as_2177_, v___x_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f(lean_object* v_00_u03b1_2184_, lean_object* v_m_2185_, lean_object* v_inst_2186_, lean_object* v_p_2187_, lean_object* v_as_2188_){
_start:
{
lean_object* v_toApplicative_2189_; lean_object* v_toBind_2190_; lean_object* v_toPure_2191_; lean_object* v___f_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v_toApplicative_2189_ = lean_ctor_get(v_inst_2186_, 0);
v_toBind_2190_ = lean_ctor_get(v_inst_2186_, 1);
v_toPure_2191_ = lean_ctor_get(v_toApplicative_2189_, 1);
lean_inc(v_toBind_2190_);
lean_inc(v_toPure_2191_);
v___f_2192_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2192_, 0, v_toPure_2191_);
lean_closure_set(v___f_2192_, 1, v_p_2187_);
lean_closure_set(v___f_2192_, 2, v_toBind_2190_);
v___x_2193_ = lean_array_get_size(v_as_2188_);
v___x_2194_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2186_, v___f_2192_, v_as_2188_, v___x_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___lam__0(lean_object* v_f_2195_, lean_object* v_x_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = lean_apply_1(v_f_2195_, v___y_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg(lean_object* v_inst_2199_, lean_object* v_f_2200_, lean_object* v_as_2201_, lean_object* v_start_2202_, lean_object* v_stop_2203_){
_start:
{
lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = lean_box(0);
v___x_2205_ = lean_nat_dec_lt(v_start_2202_, v_stop_2203_);
if (v___x_2205_ == 0)
{
lean_object* v_toApplicative_2206_; lean_object* v_toPure_2207_; lean_object* v___x_2208_; 
lean_dec_ref(v_as_2201_);
lean_dec(v_f_2200_);
v_toApplicative_2206_ = lean_ctor_get(v_inst_2199_, 0);
lean_inc_ref(v_toApplicative_2206_);
lean_dec_ref(v_inst_2199_);
v_toPure_2207_ = lean_ctor_get(v_toApplicative_2206_, 1);
lean_inc(v_toPure_2207_);
lean_dec_ref(v_toApplicative_2206_);
v___x_2208_ = lean_apply_2(v_toPure_2207_, lean_box(0), v___x_2204_);
return v___x_2208_;
}
else
{
lean_object* v___f_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
v___f_2209_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2209_, 0, v_f_2200_);
v___x_2210_ = lean_array_get_size(v_as_2201_);
v___x_2211_ = lean_nat_dec_le(v_stop_2203_, v___x_2210_);
if (v___x_2211_ == 0)
{
uint8_t v___x_2212_; 
v___x_2212_ = lean_nat_dec_lt(v_start_2202_, v___x_2210_);
if (v___x_2212_ == 0)
{
lean_object* v_toApplicative_2213_; lean_object* v_toPure_2214_; lean_object* v___x_2215_; 
lean_dec_ref(v___f_2209_);
lean_dec_ref(v_as_2201_);
v_toApplicative_2213_ = lean_ctor_get(v_inst_2199_, 0);
lean_inc_ref(v_toApplicative_2213_);
lean_dec_ref(v_inst_2199_);
v_toPure_2214_ = lean_ctor_get(v_toApplicative_2213_, 1);
lean_inc(v_toPure_2214_);
lean_dec_ref(v_toApplicative_2213_);
v___x_2215_ = lean_apply_2(v_toPure_2214_, lean_box(0), v___x_2204_);
return v___x_2215_;
}
else
{
size_t v___x_2216_; size_t v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = lean_usize_of_nat(v_start_2202_);
v___x_2217_ = lean_usize_of_nat(v___x_2210_);
v___x_2218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2199_, v___f_2209_, v_as_2201_, v___x_2216_, v___x_2217_, v___x_2204_);
return v___x_2218_;
}
}
else
{
size_t v___x_2219_; size_t v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = lean_usize_of_nat(v_start_2202_);
v___x_2220_ = lean_usize_of_nat(v_stop_2203_);
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2199_, v___f_2209_, v_as_2201_, v___x_2219_, v___x_2220_, v___x_2204_);
return v___x_2221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___boxed(lean_object* v_inst_2222_, lean_object* v_f_2223_, lean_object* v_as_2224_, lean_object* v_start_2225_, lean_object* v_stop_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Array_forM___redArg(v_inst_2222_, v_f_2223_, v_as_2224_, v_start_2225_, v_stop_2226_);
lean_dec(v_stop_2226_);
lean_dec(v_start_2225_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Array_forM(lean_object* v_00_u03b1_2228_, lean_object* v_m_2229_, lean_object* v_inst_2230_, lean_object* v_f_2231_, lean_object* v_as_2232_, lean_object* v_start_2233_, lean_object* v_stop_2234_){
_start:
{
lean_object* v___x_2235_; uint8_t v___x_2236_; 
v___x_2235_ = lean_box(0);
v___x_2236_ = lean_nat_dec_lt(v_start_2233_, v_stop_2234_);
if (v___x_2236_ == 0)
{
lean_object* v_toApplicative_2237_; lean_object* v_toPure_2238_; lean_object* v___x_2239_; 
lean_dec_ref(v_as_2232_);
lean_dec(v_f_2231_);
v_toApplicative_2237_ = lean_ctor_get(v_inst_2230_, 0);
lean_inc_ref(v_toApplicative_2237_);
lean_dec_ref(v_inst_2230_);
v_toPure_2238_ = lean_ctor_get(v_toApplicative_2237_, 1);
lean_inc(v_toPure_2238_);
lean_dec_ref(v_toApplicative_2237_);
v___x_2239_ = lean_apply_2(v_toPure_2238_, lean_box(0), v___x_2235_);
return v___x_2239_;
}
else
{
lean_object* v___f_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___f_2240_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2240_, 0, v_f_2231_);
v___x_2241_ = lean_array_get_size(v_as_2232_);
v___x_2242_ = lean_nat_dec_le(v_stop_2234_, v___x_2241_);
if (v___x_2242_ == 0)
{
uint8_t v___x_2243_; 
v___x_2243_ = lean_nat_dec_lt(v_start_2233_, v___x_2241_);
if (v___x_2243_ == 0)
{
lean_object* v_toApplicative_2244_; lean_object* v_toPure_2245_; lean_object* v___x_2246_; 
lean_dec_ref(v___f_2240_);
lean_dec_ref(v_as_2232_);
v_toApplicative_2244_ = lean_ctor_get(v_inst_2230_, 0);
lean_inc_ref(v_toApplicative_2244_);
lean_dec_ref(v_inst_2230_);
v_toPure_2245_ = lean_ctor_get(v_toApplicative_2244_, 1);
lean_inc(v_toPure_2245_);
lean_dec_ref(v_toApplicative_2244_);
v___x_2246_ = lean_apply_2(v_toPure_2245_, lean_box(0), v___x_2235_);
return v___x_2246_;
}
else
{
size_t v___x_2247_; size_t v___x_2248_; lean_object* v___x_2249_; 
v___x_2247_ = lean_usize_of_nat(v_start_2233_);
v___x_2248_ = lean_usize_of_nat(v___x_2241_);
v___x_2249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2230_, v___f_2240_, v_as_2232_, v___x_2247_, v___x_2248_, v___x_2235_);
return v___x_2249_;
}
}
else
{
size_t v___x_2250_; size_t v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = lean_usize_of_nat(v_start_2233_);
v___x_2251_ = lean_usize_of_nat(v_stop_2234_);
v___x_2252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2230_, v___f_2240_, v_as_2232_, v___x_2250_, v___x_2251_, v___x_2235_);
return v___x_2252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___boxed(lean_object* v_00_u03b1_2253_, lean_object* v_m_2254_, lean_object* v_inst_2255_, lean_object* v_f_2256_, lean_object* v_as_2257_, lean_object* v_start_2258_, lean_object* v_stop_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Array_forM(v_00_u03b1_2253_, v_m_2254_, v_inst_2255_, v_f_2256_, v_as_2257_, v_start_2258_, v_stop_2259_);
lean_dec(v_stop_2259_);
lean_dec(v_start_2258_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg___lam__1(lean_object* v_inst_2261_, lean_object* v_xs_2262_, lean_object* v_f_2263_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2264_ = lean_unsigned_to_nat(0u);
v___x_2265_ = lean_array_get_size(v_xs_2262_);
v___x_2266_ = lean_box(0);
v___x_2267_ = lean_nat_dec_lt(v___x_2264_, v___x_2265_);
if (v___x_2267_ == 0)
{
lean_object* v_toApplicative_2268_; lean_object* v_toPure_2269_; lean_object* v___x_2270_; 
lean_dec(v_f_2263_);
lean_dec_ref(v_xs_2262_);
v_toApplicative_2268_ = lean_ctor_get(v_inst_2261_, 0);
lean_inc_ref(v_toApplicative_2268_);
lean_dec_ref(v_inst_2261_);
v_toPure_2269_ = lean_ctor_get(v_toApplicative_2268_, 1);
lean_inc(v_toPure_2269_);
lean_dec_ref(v_toApplicative_2268_);
v___x_2270_ = lean_apply_2(v_toPure_2269_, lean_box(0), v___x_2266_);
return v___x_2270_;
}
else
{
lean_object* v___f_2271_; uint8_t v___x_2272_; 
v___f_2271_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2271_, 0, v_f_2263_);
v___x_2272_ = lean_nat_dec_le(v___x_2265_, v___x_2265_);
if (v___x_2272_ == 0)
{
if (v___x_2267_ == 0)
{
lean_object* v_toApplicative_2273_; lean_object* v_toPure_2274_; lean_object* v___x_2275_; 
lean_dec_ref(v___f_2271_);
lean_dec_ref(v_xs_2262_);
v_toApplicative_2273_ = lean_ctor_get(v_inst_2261_, 0);
lean_inc_ref(v_toApplicative_2273_);
lean_dec_ref(v_inst_2261_);
v_toPure_2274_ = lean_ctor_get(v_toApplicative_2273_, 1);
lean_inc(v_toPure_2274_);
lean_dec_ref(v_toApplicative_2273_);
v___x_2275_ = lean_apply_2(v_toPure_2274_, lean_box(0), v___x_2266_);
return v___x_2275_;
}
else
{
size_t v___x_2276_; size_t v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = ((size_t)0ULL);
v___x_2277_ = lean_usize_of_nat(v___x_2265_);
v___x_2278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2261_, v___f_2271_, v_xs_2262_, v___x_2276_, v___x_2277_, v___x_2266_);
return v___x_2278_;
}
}
else
{
size_t v___x_2279_; size_t v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = ((size_t)0ULL);
v___x_2280_ = lean_usize_of_nat(v___x_2265_);
v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2261_, v___f_2271_, v_xs_2262_, v___x_2279_, v___x_2280_, v___x_2266_);
return v___x_2281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg(lean_object* v_inst_2282_){
_start:
{
lean_object* v___f_2283_; 
v___f_2283_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2283_, 0, v_inst_2282_);
return v___f_2283_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad(lean_object* v_00_u03b1_2284_, lean_object* v_m_2285_, lean_object* v_inst_2286_){
_start:
{
lean_object* v___f_2287_; 
v___f_2287_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2287_, 0, v_inst_2286_);
return v___f_2287_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___lam__0(lean_object* v_f_2288_, lean_object* v_a_2289_, lean_object* v_x_2290_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_apply_1(v_f_2288_, v_a_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg(lean_object* v_inst_2292_, lean_object* v_f_2293_, lean_object* v_as_2294_, lean_object* v_start_2295_, lean_object* v_stop_2296_){
_start:
{
lean_object* v___f_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___f_2297_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2297_, 0, v_f_2293_);
v___x_2298_ = lean_box(0);
v___x_2299_ = lean_array_get_size(v_as_2294_);
v___x_2300_ = lean_nat_dec_le(v_start_2295_, v___x_2299_);
if (v___x_2300_ == 0)
{
uint8_t v___x_2301_; 
v___x_2301_ = lean_nat_dec_lt(v_stop_2296_, v___x_2299_);
if (v___x_2301_ == 0)
{
lean_object* v_toApplicative_2302_; lean_object* v_toPure_2303_; lean_object* v___x_2304_; 
lean_dec_ref(v___f_2297_);
lean_dec_ref(v_as_2294_);
v_toApplicative_2302_ = lean_ctor_get(v_inst_2292_, 0);
lean_inc_ref(v_toApplicative_2302_);
lean_dec_ref(v_inst_2292_);
v_toPure_2303_ = lean_ctor_get(v_toApplicative_2302_, 1);
lean_inc(v_toPure_2303_);
lean_dec_ref(v_toApplicative_2302_);
v___x_2304_ = lean_apply_2(v_toPure_2303_, lean_box(0), v___x_2298_);
return v___x_2304_;
}
else
{
size_t v___x_2305_; size_t v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_usize_of_nat(v___x_2299_);
v___x_2306_ = lean_usize_of_nat(v_stop_2296_);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2292_, v___f_2297_, v_as_2294_, v___x_2305_, v___x_2306_, v___x_2298_);
return v___x_2307_;
}
}
else
{
uint8_t v___x_2308_; 
v___x_2308_ = lean_nat_dec_lt(v_stop_2296_, v_start_2295_);
if (v___x_2308_ == 0)
{
lean_object* v_toApplicative_2309_; lean_object* v_toPure_2310_; lean_object* v___x_2311_; 
lean_dec_ref(v___f_2297_);
lean_dec_ref(v_as_2294_);
v_toApplicative_2309_ = lean_ctor_get(v_inst_2292_, 0);
lean_inc_ref(v_toApplicative_2309_);
lean_dec_ref(v_inst_2292_);
v_toPure_2310_ = lean_ctor_get(v_toApplicative_2309_, 1);
lean_inc(v_toPure_2310_);
lean_dec_ref(v_toApplicative_2309_);
v___x_2311_ = lean_apply_2(v_toPure_2310_, lean_box(0), v___x_2298_);
return v___x_2311_;
}
else
{
size_t v___x_2312_; size_t v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = lean_usize_of_nat(v_start_2295_);
v___x_2313_ = lean_usize_of_nat(v_stop_2296_);
v___x_2314_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2292_, v___f_2297_, v_as_2294_, v___x_2312_, v___x_2313_, v___x_2298_);
return v___x_2314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___boxed(lean_object* v_inst_2315_, lean_object* v_f_2316_, lean_object* v_as_2317_, lean_object* v_start_2318_, lean_object* v_stop_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Array_forRevM___redArg(v_inst_2315_, v_f_2316_, v_as_2317_, v_start_2318_, v_stop_2319_);
lean_dec(v_stop_2319_);
lean_dec(v_start_2318_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM(lean_object* v_00_u03b1_2321_, lean_object* v_m_2322_, lean_object* v_inst_2323_, lean_object* v_f_2324_, lean_object* v_as_2325_, lean_object* v_start_2326_, lean_object* v_stop_2327_){
_start:
{
lean_object* v___f_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___f_2328_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2328_, 0, v_f_2324_);
v___x_2329_ = lean_box(0);
v___x_2330_ = lean_array_get_size(v_as_2325_);
v___x_2331_ = lean_nat_dec_le(v_start_2326_, v___x_2330_);
if (v___x_2331_ == 0)
{
uint8_t v___x_2332_; 
v___x_2332_ = lean_nat_dec_lt(v_stop_2327_, v___x_2330_);
if (v___x_2332_ == 0)
{
lean_object* v_toApplicative_2333_; lean_object* v_toPure_2334_; lean_object* v___x_2335_; 
lean_dec_ref(v___f_2328_);
lean_dec_ref(v_as_2325_);
v_toApplicative_2333_ = lean_ctor_get(v_inst_2323_, 0);
lean_inc_ref(v_toApplicative_2333_);
lean_dec_ref(v_inst_2323_);
v_toPure_2334_ = lean_ctor_get(v_toApplicative_2333_, 1);
lean_inc(v_toPure_2334_);
lean_dec_ref(v_toApplicative_2333_);
v___x_2335_ = lean_apply_2(v_toPure_2334_, lean_box(0), v___x_2329_);
return v___x_2335_;
}
else
{
size_t v___x_2336_; size_t v___x_2337_; lean_object* v___x_2338_; 
v___x_2336_ = lean_usize_of_nat(v___x_2330_);
v___x_2337_ = lean_usize_of_nat(v_stop_2327_);
v___x_2338_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2323_, v___f_2328_, v_as_2325_, v___x_2336_, v___x_2337_, v___x_2329_);
return v___x_2338_;
}
}
else
{
uint8_t v___x_2339_; 
v___x_2339_ = lean_nat_dec_lt(v_stop_2327_, v_start_2326_);
if (v___x_2339_ == 0)
{
lean_object* v_toApplicative_2340_; lean_object* v_toPure_2341_; lean_object* v___x_2342_; 
lean_dec_ref(v___f_2328_);
lean_dec_ref(v_as_2325_);
v_toApplicative_2340_ = lean_ctor_get(v_inst_2323_, 0);
lean_inc_ref(v_toApplicative_2340_);
lean_dec_ref(v_inst_2323_);
v_toPure_2341_ = lean_ctor_get(v_toApplicative_2340_, 1);
lean_inc(v_toPure_2341_);
lean_dec_ref(v_toApplicative_2340_);
v___x_2342_ = lean_apply_2(v_toPure_2341_, lean_box(0), v___x_2329_);
return v___x_2342_;
}
else
{
size_t v___x_2343_; size_t v___x_2344_; lean_object* v___x_2345_; 
v___x_2343_ = lean_usize_of_nat(v_start_2326_);
v___x_2344_ = lean_usize_of_nat(v_stop_2327_);
v___x_2345_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2323_, v___f_2328_, v_as_2325_, v___x_2343_, v___x_2344_, v___x_2329_);
return v___x_2345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___boxed(lean_object* v_00_u03b1_2346_, lean_object* v_m_2347_, lean_object* v_inst_2348_, lean_object* v_f_2349_, lean_object* v_as_2350_, lean_object* v_start_2351_, lean_object* v_stop_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Array_forRevM(v_00_u03b1_2346_, v_m_2347_, v_inst_2348_, v_f_2349_, v_as_2350_, v_start_2351_, v_stop_2352_);
lean_dec(v_stop_2352_);
lean_dec(v_start_2351_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___lam__0(lean_object* v_f_2354_, lean_object* v_x1_2355_, lean_object* v_x2_2356_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = lean_apply_2(v_f_2354_, v_x1_2355_, v_x2_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg(lean_object* v_f_2377_, lean_object* v_init_2378_, lean_object* v_as_2379_, lean_object* v_start_2380_, lean_object* v_stop_2381_){
_start:
{
lean_object* v___x_2382_; uint8_t v___x_2383_; 
v___x_2382_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2383_ = lean_nat_dec_lt(v_start_2380_, v_stop_2381_);
if (v___x_2383_ == 0)
{
lean_dec_ref(v_as_2379_);
lean_dec(v_f_2377_);
return v_init_2378_;
}
else
{
lean_object* v___f_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v___f_2384_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2384_, 0, v_f_2377_);
v___x_2385_ = lean_array_get_size(v_as_2379_);
v___x_2386_ = lean_nat_dec_le(v_stop_2381_, v___x_2385_);
if (v___x_2386_ == 0)
{
uint8_t v___x_2387_; 
v___x_2387_ = lean_nat_dec_lt(v_start_2380_, v___x_2385_);
if (v___x_2387_ == 0)
{
lean_dec_ref(v___f_2384_);
lean_dec_ref(v_as_2379_);
return v_init_2378_;
}
else
{
size_t v___x_2388_; size_t v___x_2389_; lean_object* v___x_2390_; 
v___x_2388_ = lean_usize_of_nat(v_start_2380_);
v___x_2389_ = lean_usize_of_nat(v___x_2385_);
v___x_2390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2382_, v___f_2384_, v_as_2379_, v___x_2388_, v___x_2389_, v_init_2378_);
return v___x_2390_;
}
}
else
{
size_t v___x_2391_; size_t v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = lean_usize_of_nat(v_start_2380_);
v___x_2392_ = lean_usize_of_nat(v_stop_2381_);
v___x_2393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2382_, v___f_2384_, v_as_2379_, v___x_2391_, v___x_2392_, v_init_2378_);
return v___x_2393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___boxed(lean_object* v_f_2394_, lean_object* v_init_2395_, lean_object* v_as_2396_, lean_object* v_start_2397_, lean_object* v_stop_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Array_foldl___redArg(v_f_2394_, v_init_2395_, v_as_2396_, v_start_2397_, v_stop_2398_);
lean_dec(v_stop_2398_);
lean_dec(v_start_2397_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl(lean_object* v_00_u03b1_2400_, lean_object* v_00_u03b2_2401_, lean_object* v_f_2402_, lean_object* v_init_2403_, lean_object* v_as_2404_, lean_object* v_start_2405_, lean_object* v_stop_2406_){
_start:
{
lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2407_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2408_ = lean_nat_dec_lt(v_start_2405_, v_stop_2406_);
if (v___x_2408_ == 0)
{
lean_dec_ref(v_as_2404_);
lean_dec(v_f_2402_);
return v_init_2403_;
}
else
{
lean_object* v___f_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___f_2409_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2409_, 0, v_f_2402_);
v___x_2410_ = lean_array_get_size(v_as_2404_);
v___x_2411_ = lean_nat_dec_le(v_stop_2406_, v___x_2410_);
if (v___x_2411_ == 0)
{
uint8_t v___x_2412_; 
v___x_2412_ = lean_nat_dec_lt(v_start_2405_, v___x_2410_);
if (v___x_2412_ == 0)
{
lean_dec_ref(v___f_2409_);
lean_dec_ref(v_as_2404_);
return v_init_2403_;
}
else
{
size_t v___x_2413_; size_t v___x_2414_; lean_object* v___x_2415_; 
v___x_2413_ = lean_usize_of_nat(v_start_2405_);
v___x_2414_ = lean_usize_of_nat(v___x_2410_);
v___x_2415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2407_, v___f_2409_, v_as_2404_, v___x_2413_, v___x_2414_, v_init_2403_);
return v___x_2415_;
}
}
else
{
size_t v___x_2416_; size_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = lean_usize_of_nat(v_start_2405_);
v___x_2417_ = lean_usize_of_nat(v_stop_2406_);
v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2407_, v___f_2409_, v_as_2404_, v___x_2416_, v___x_2417_, v_init_2403_);
return v___x_2418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___boxed(lean_object* v_00_u03b1_2419_, lean_object* v_00_u03b2_2420_, lean_object* v_f_2421_, lean_object* v_init_2422_, lean_object* v_as_2423_, lean_object* v_start_2424_, lean_object* v_stop_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Array_foldl(v_00_u03b1_2419_, v_00_u03b2_2420_, v_f_2421_, v_init_2422_, v_as_2423_, v_start_2424_, v_stop_2425_);
lean_dec(v_stop_2425_);
lean_dec(v_start_2424_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg(lean_object* v_f_2427_, lean_object* v_init_2428_, lean_object* v_as_2429_, lean_object* v_start_2430_, lean_object* v_stop_2431_){
_start:
{
lean_object* v___f_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___f_2432_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2432_, 0, v_f_2427_);
v___x_2433_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2434_ = lean_array_get_size(v_as_2429_);
v___x_2435_ = lean_nat_dec_le(v_start_2430_, v___x_2434_);
if (v___x_2435_ == 0)
{
uint8_t v___x_2436_; 
v___x_2436_ = lean_nat_dec_lt(v_stop_2431_, v___x_2434_);
if (v___x_2436_ == 0)
{
lean_dec_ref(v___f_2432_);
lean_dec_ref(v_as_2429_);
return v_init_2428_;
}
else
{
size_t v___x_2437_; size_t v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = lean_usize_of_nat(v___x_2434_);
v___x_2438_ = lean_usize_of_nat(v_stop_2431_);
v___x_2439_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2433_, v___f_2432_, v_as_2429_, v___x_2437_, v___x_2438_, v_init_2428_);
return v___x_2439_;
}
}
else
{
uint8_t v___x_2440_; 
v___x_2440_ = lean_nat_dec_lt(v_stop_2431_, v_start_2430_);
if (v___x_2440_ == 0)
{
lean_dec_ref(v___f_2432_);
lean_dec_ref(v_as_2429_);
return v_init_2428_;
}
else
{
size_t v___x_2441_; size_t v___x_2442_; lean_object* v___x_2443_; 
v___x_2441_ = lean_usize_of_nat(v_start_2430_);
v___x_2442_ = lean_usize_of_nat(v_stop_2431_);
v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2433_, v___f_2432_, v_as_2429_, v___x_2441_, v___x_2442_, v_init_2428_);
return v___x_2443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg___boxed(lean_object* v_f_2444_, lean_object* v_init_2445_, lean_object* v_as_2446_, lean_object* v_start_2447_, lean_object* v_stop_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Array_foldr___redArg(v_f_2444_, v_init_2445_, v_as_2446_, v_start_2447_, v_stop_2448_);
lean_dec(v_stop_2448_);
lean_dec(v_start_2447_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr(lean_object* v_00_u03b1_2450_, lean_object* v_00_u03b2_2451_, lean_object* v_f_2452_, lean_object* v_init_2453_, lean_object* v_as_2454_, lean_object* v_start_2455_, lean_object* v_stop_2456_){
_start:
{
lean_object* v___f_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___f_2457_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2457_, 0, v_f_2452_);
v___x_2458_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2459_ = lean_array_get_size(v_as_2454_);
v___x_2460_ = lean_nat_dec_le(v_start_2455_, v___x_2459_);
if (v___x_2460_ == 0)
{
uint8_t v___x_2461_; 
v___x_2461_ = lean_nat_dec_lt(v_stop_2456_, v___x_2459_);
if (v___x_2461_ == 0)
{
lean_dec_ref(v___f_2457_);
lean_dec_ref(v_as_2454_);
return v_init_2453_;
}
else
{
size_t v___x_2462_; size_t v___x_2463_; lean_object* v___x_2464_; 
v___x_2462_ = lean_usize_of_nat(v___x_2459_);
v___x_2463_ = lean_usize_of_nat(v_stop_2456_);
v___x_2464_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2458_, v___f_2457_, v_as_2454_, v___x_2462_, v___x_2463_, v_init_2453_);
return v___x_2464_;
}
}
else
{
uint8_t v___x_2465_; 
v___x_2465_ = lean_nat_dec_lt(v_stop_2456_, v_start_2455_);
if (v___x_2465_ == 0)
{
lean_dec_ref(v___f_2457_);
lean_dec_ref(v_as_2454_);
return v_init_2453_;
}
else
{
size_t v___x_2466_; size_t v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = lean_usize_of_nat(v_start_2455_);
v___x_2467_ = lean_usize_of_nat(v_stop_2456_);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2458_, v___f_2457_, v_as_2454_, v___x_2466_, v___x_2467_, v_init_2453_);
return v___x_2468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___boxed(lean_object* v_00_u03b1_2469_, lean_object* v_00_u03b2_2470_, lean_object* v_f_2471_, lean_object* v_init_2472_, lean_object* v_as_2473_, lean_object* v_start_2474_, lean_object* v_stop_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Array_foldr(v_00_u03b1_2469_, v_00_u03b2_2470_, v_f_2471_, v_init_2472_, v_as_2473_, v_start_2474_, v_stop_2475_);
lean_dec(v_stop_2475_);
lean_dec(v_start_2474_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg___lam__0(lean_object* v_inst_2477_, lean_object* v_x1_2478_, lean_object* v_x2_2479_){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = lean_apply_2(v_inst_2477_, v_x1_2478_, v_x2_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg(lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_as_2483_){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; uint8_t v___x_2487_; 
v___x_2484_ = lean_array_get_size(v_as_2483_);
v___x_2485_ = lean_unsigned_to_nat(0u);
v___x_2486_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2487_ = lean_nat_dec_lt(v___x_2485_, v___x_2484_);
if (v___x_2487_ == 0)
{
lean_dec_ref(v_as_2483_);
lean_dec(v_inst_2481_);
return v_inst_2482_;
}
else
{
lean_object* v___f_2488_; size_t v___x_2489_; size_t v___x_2490_; lean_object* v___x_2491_; 
v___f_2488_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2488_, 0, v_inst_2481_);
v___x_2489_ = lean_usize_of_nat(v___x_2484_);
v___x_2490_ = ((size_t)0ULL);
v___x_2491_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2486_, v___f_2488_, v_as_2483_, v___x_2489_, v___x_2490_, v_inst_2482_);
return v___x_2491_;
}
}
}
LEAN_EXPORT lean_object* l_Array_sum(lean_object* v_00_u03b1_2492_, lean_object* v_inst_2493_, lean_object* v_inst_2494_, lean_object* v_as_2495_){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2496_ = lean_array_get_size(v_as_2495_);
v___x_2497_ = lean_unsigned_to_nat(0u);
v___x_2498_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2499_ = lean_nat_dec_lt(v___x_2497_, v___x_2496_);
if (v___x_2499_ == 0)
{
lean_dec_ref(v_as_2495_);
lean_dec(v_inst_2493_);
return v_inst_2494_;
}
else
{
lean_object* v___f_2500_; size_t v___x_2501_; size_t v___x_2502_; lean_object* v___x_2503_; 
v___f_2500_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2500_, 0, v_inst_2493_);
v___x_2501_ = lean_usize_of_nat(v___x_2496_);
v___x_2502_ = ((size_t)0ULL);
v___x_2503_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2498_, v___f_2500_, v_as_2495_, v___x_2501_, v___x_2502_, v_inst_2494_);
return v___x_2503_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0(lean_object* v_p_2504_, lean_object* v_x1_2505_, lean_object* v_x2_2506_){
_start:
{
lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2507_ = lean_apply_1(v_p_2504_, v_x1_2505_);
v___x_2508_ = lean_unbox(v___x_2507_);
if (v___x_2508_ == 0)
{
lean_inc(v_x2_2506_);
return v_x2_2506_;
}
else
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = lean_unsigned_to_nat(1u);
v___x_2510_ = lean_nat_add(v_x2_2506_, v___x_2509_);
return v___x_2510_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0___boxed(lean_object* v_p_2511_, lean_object* v_x1_2512_, lean_object* v_x2_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Array_countP___redArg___lam__0(v_p_2511_, v_x1_2512_, v_x2_2513_);
lean_dec(v_x2_2513_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg(lean_object* v_p_2515_, lean_object* v_as_2516_){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; uint8_t v___x_2520_; 
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = lean_array_get_size(v_as_2516_);
v___x_2519_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2520_ = lean_nat_dec_lt(v___x_2517_, v___x_2518_);
if (v___x_2520_ == 0)
{
lean_dec_ref(v_as_2516_);
lean_dec_ref(v_p_2515_);
return v___x_2517_;
}
else
{
lean_object* v___f_2521_; size_t v___x_2522_; size_t v___x_2523_; lean_object* v___x_2524_; 
v___f_2521_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2521_, 0, v_p_2515_);
v___x_2522_ = lean_usize_of_nat(v___x_2518_);
v___x_2523_ = ((size_t)0ULL);
v___x_2524_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2519_, v___f_2521_, v_as_2516_, v___x_2522_, v___x_2523_, v___x_2517_);
return v___x_2524_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP(lean_object* v_00_u03b1_2525_, lean_object* v_p_2526_, lean_object* v_as_2527_){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2528_ = lean_unsigned_to_nat(0u);
v___x_2529_ = lean_array_get_size(v_as_2527_);
v___x_2530_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2531_ = lean_nat_dec_lt(v___x_2528_, v___x_2529_);
if (v___x_2531_ == 0)
{
lean_dec_ref(v_as_2527_);
lean_dec_ref(v_p_2526_);
return v___x_2528_;
}
else
{
lean_object* v___f_2532_; size_t v___x_2533_; size_t v___x_2534_; lean_object* v___x_2535_; 
v___f_2532_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2532_, 0, v_p_2526_);
v___x_2533_ = lean_usize_of_nat(v___x_2529_);
v___x_2534_ = ((size_t)0ULL);
v___x_2535_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2530_, v___f_2532_, v_as_2527_, v___x_2533_, v___x_2534_, v___x_2528_);
return v___x_2535_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0(lean_object* v_inst_2536_, lean_object* v_a_2537_, lean_object* v_x1_2538_, lean_object* v_x2_2539_){
_start:
{
lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2540_ = lean_apply_2(v_inst_2536_, v_x1_2538_, v_a_2537_);
v___x_2541_ = lean_unbox(v___x_2540_);
if (v___x_2541_ == 0)
{
lean_inc(v_x2_2539_);
return v_x2_2539_;
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = lean_unsigned_to_nat(1u);
v___x_2543_ = lean_nat_add(v_x2_2539_, v___x_2542_);
return v___x_2543_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0___boxed(lean_object* v_inst_2544_, lean_object* v_a_2545_, lean_object* v_x1_2546_, lean_object* v_x2_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Array_count___redArg___lam__0(v_inst_2544_, v_a_2545_, v_x1_2546_, v_x2_2547_);
lean_dec(v_x2_2547_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg(lean_object* v_inst_2549_, lean_object* v_a_2550_, lean_object* v_as_2551_){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; 
v___x_2552_ = lean_unsigned_to_nat(0u);
v___x_2553_ = lean_array_get_size(v_as_2551_);
v___x_2554_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2555_ = lean_nat_dec_lt(v___x_2552_, v___x_2553_);
if (v___x_2555_ == 0)
{
lean_dec_ref(v_as_2551_);
lean_dec(v_a_2550_);
lean_dec_ref(v_inst_2549_);
return v___x_2552_;
}
else
{
lean_object* v___f_2556_; size_t v___x_2557_; size_t v___x_2558_; lean_object* v___x_2559_; 
v___f_2556_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2556_, 0, v_inst_2549_);
lean_closure_set(v___f_2556_, 1, v_a_2550_);
v___x_2557_ = lean_usize_of_nat(v___x_2553_);
v___x_2558_ = ((size_t)0ULL);
v___x_2559_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2554_, v___f_2556_, v_as_2551_, v___x_2557_, v___x_2558_, v___x_2552_);
return v___x_2559_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count(lean_object* v_00_u03b1_2560_, lean_object* v_inst_2561_, lean_object* v_a_2562_, lean_object* v_as_2563_){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
v___x_2564_ = lean_unsigned_to_nat(0u);
v___x_2565_ = lean_array_get_size(v_as_2563_);
v___x_2566_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2567_ = lean_nat_dec_lt(v___x_2564_, v___x_2565_);
if (v___x_2567_ == 0)
{
lean_dec_ref(v_as_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_inst_2561_);
return v___x_2564_;
}
else
{
lean_object* v___f_2568_; size_t v___x_2569_; size_t v___x_2570_; lean_object* v___x_2571_; 
v___f_2568_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2568_, 0, v_inst_2561_);
lean_closure_set(v___f_2568_, 1, v_a_2562_);
v___x_2569_ = lean_usize_of_nat(v___x_2565_);
v___x_2570_ = ((size_t)0ULL);
v___x_2571_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2566_, v___f_2568_, v_as_2563_, v___x_2569_, v___x_2570_, v___x_2564_);
return v___x_2571_;
}
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg___lam__0(lean_object* v_f_2572_, lean_object* v_x_2573_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = lean_apply_1(v_f_2572_, v_x_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg(lean_object* v_f_2575_, lean_object* v_as_2576_){
_start:
{
lean_object* v___f_2577_; lean_object* v___x_2578_; size_t v_sz_2579_; size_t v___x_2580_; lean_object* v___x_2581_; 
v___f_2577_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2577_, 0, v_f_2575_);
v___x_2578_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2579_ = lean_array_size(v_as_2576_);
v___x_2580_ = ((size_t)0ULL);
v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2578_, v___f_2577_, v_sz_2579_, v___x_2580_, v_as_2576_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Array_map(lean_object* v_00_u03b1_2582_, lean_object* v_00_u03b2_2583_, lean_object* v_f_2584_, lean_object* v_as_2585_){
_start:
{
lean_object* v___f_2586_; lean_object* v___x_2587_; size_t v_sz_2588_; size_t v___x_2589_; lean_object* v___x_2590_; 
v___f_2586_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2586_, 0, v_f_2584_);
v___x_2587_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2588_ = lean_array_size(v_as_2585_);
v___x_2589_ = ((size_t)0ULL);
v___x_2590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2587_, v___f_2586_, v_sz_2588_, v___x_2589_, v_as_2585_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0(lean_object* v___y_2591_, lean_object* v_x_2592_){
_start:
{
lean_inc(v___y_2591_);
return v___y_2591_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0___boxed(lean_object* v___y_2593_, lean_object* v_x_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Array_instFunctor___lam__0(v___y_2593_, v_x_2594_);
lean_dec(v_x_2594_);
lean_dec(v___y_2593_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__1(lean_object* v_00_u03b1_2596_, lean_object* v_00_u03b2_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v___f_2600_; lean_object* v___x_2601_; size_t v_sz_2602_; size_t v___x_2603_; lean_object* v___x_2604_; 
v___f_2600_ = lean_alloc_closure((void*)(l_Array_instFunctor___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2600_, 0, v___y_2598_);
v___x_2601_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2602_ = lean_array_size(v___y_2599_);
v___x_2603_ = ((size_t)0ULL);
v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2601_, v___f_2600_, v_sz_2602_, v___x_2603_, v___y_2599_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg___lam__0(lean_object* v_f_2611_, lean_object* v_x1_2612_, lean_object* v_x2_2613_, lean_object* v_x3_2614_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = lean_apply_3(v_f_2611_, v_x1_2612_, v_x2_2613_, lean_box(0));
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg(lean_object* v_as_2616_, lean_object* v_f_2617_){
_start:
{
lean_object* v___f_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___f_2618_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2618_, 0, v_f_2617_);
v___x_2619_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2620_ = lean_array_get_size(v_as_2616_);
v___x_2621_ = lean_unsigned_to_nat(0u);
v___x_2622_ = lean_mk_empty_array_with_capacity(v___x_2620_);
v___x_2623_ = l_Array_mapFinIdxM_map___redArg(v___x_2619_, v_as_2616_, v___f_2618_, v___x_2620_, v___x_2621_, v___x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx(lean_object* v_00_u03b1_2624_, lean_object* v_00_u03b2_2625_, lean_object* v_as_2626_, lean_object* v_f_2627_){
_start:
{
lean_object* v___f_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___f_2628_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2628_, 0, v_f_2627_);
v___x_2629_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2630_ = lean_array_get_size(v_as_2626_);
v___x_2631_ = lean_unsigned_to_nat(0u);
v___x_2632_ = lean_mk_empty_array_with_capacity(v___x_2630_);
v___x_2633_ = l_Array_mapFinIdxM_map___redArg(v___x_2629_, v_as_2626_, v___f_2628_, v___x_2630_, v___x_2631_, v___x_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx___redArg(lean_object* v_f_2634_, lean_object* v_as_2635_){
_start:
{
lean_object* v___f_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___f_2636_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2636_, 0, v_f_2634_);
v___x_2637_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2638_ = lean_array_get_size(v_as_2635_);
v___x_2639_ = lean_unsigned_to_nat(0u);
v___x_2640_ = lean_mk_empty_array_with_capacity(v___x_2638_);
v___x_2641_ = l_Array_mapFinIdxM_map___redArg(v___x_2637_, v_as_2635_, v___f_2636_, v___x_2638_, v___x_2639_, v___x_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx(lean_object* v_00_u03b1_2642_, lean_object* v_00_u03b2_2643_, lean_object* v_f_2644_, lean_object* v_as_2645_){
_start:
{
lean_object* v___f_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___f_2646_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2646_, 0, v_f_2644_);
v___x_2647_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2648_ = lean_array_get_size(v_as_2645_);
v___x_2649_ = lean_unsigned_to_nat(0u);
v___x_2650_ = lean_mk_empty_array_with_capacity(v___x_2648_);
v___x_2651_ = l_Array_mapFinIdxM_map___redArg(v___x_2647_, v_as_2645_, v___f_2646_, v___x_2648_, v___x_2649_, v___x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(lean_object* v_start_2652_, lean_object* v_as_2653_, lean_object* v_i_2654_, lean_object* v_j_2655_, lean_object* v_bs_2656_){
_start:
{
lean_object* v_zero_2657_; uint8_t v_isZero_2658_; 
v_zero_2657_ = lean_unsigned_to_nat(0u);
v_isZero_2658_ = lean_nat_dec_eq(v_i_2654_, v_zero_2657_);
if (v_isZero_2658_ == 1)
{
lean_dec(v_j_2655_);
lean_dec(v_i_2654_);
return v_bs_2656_;
}
else
{
lean_object* v_one_2659_; lean_object* v_n_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v_one_2659_ = lean_unsigned_to_nat(1u);
v_n_2660_ = lean_nat_sub(v_i_2654_, v_one_2659_);
lean_dec(v_i_2654_);
v___x_2661_ = lean_array_fget_borrowed(v_as_2653_, v_j_2655_);
v___x_2662_ = lean_nat_add(v_start_2652_, v_j_2655_);
lean_inc(v___x_2661_);
v___x_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2661_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
v___x_2664_ = lean_nat_add(v_j_2655_, v_one_2659_);
lean_dec(v_j_2655_);
v___x_2665_ = lean_array_push(v_bs_2656_, v___x_2663_);
v_i_2654_ = v_n_2660_;
v_j_2655_ = v___x_2664_;
v_bs_2656_ = v___x_2665_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg___boxed(lean_object* v_start_2667_, lean_object* v_as_2668_, lean_object* v_i_2669_, lean_object* v_j_2670_, lean_object* v_bs_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(v_start_2667_, v_as_2668_, v_i_2669_, v_j_2670_, v_bs_2671_);
lean_dec_ref(v_as_2668_);
lean_dec(v_start_2667_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg(lean_object* v_xs_2673_, lean_object* v_start_2674_){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2675_ = lean_array_get_size(v_xs_2673_);
v___x_2676_ = lean_unsigned_to_nat(0u);
v___x_2677_ = lean_mk_empty_array_with_capacity(v___x_2675_);
v___x_2678_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(v_start_2674_, v_xs_2673_, v___x_2675_, v___x_2676_, v___x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg___boxed(lean_object* v_xs_2679_, lean_object* v_start_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Array_zipIdx___redArg(v_xs_2679_, v_start_2680_);
lean_dec(v_start_2680_);
lean_dec_ref(v_xs_2679_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx(lean_object* v_00_u03b1_2682_, lean_object* v_xs_2683_, lean_object* v_start_2684_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_Array_zipIdx___redArg(v_xs_2683_, v_start_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___boxed(lean_object* v_00_u03b1_2686_, lean_object* v_xs_2687_, lean_object* v_start_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_Array_zipIdx(v_00_u03b1_2686_, v_xs_2687_, v_start_2688_);
lean_dec(v_start_2688_);
lean_dec_ref(v_xs_2687_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0(lean_object* v_00_u03b1_2690_, lean_object* v_start_2691_, lean_object* v_as_2692_, lean_object* v_i_2693_, lean_object* v_j_2694_, lean_object* v_inv_2695_, lean_object* v_bs_2696_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(v_start_2691_, v_as_2692_, v_i_2693_, v_j_2694_, v_bs_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___boxed(lean_object* v_00_u03b1_2698_, lean_object* v_start_2699_, lean_object* v_as_2700_, lean_object* v_i_2701_, lean_object* v_j_2702_, lean_object* v_inv_2703_, lean_object* v_bs_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0(v_00_u03b1_2698_, v_start_2699_, v_as_2700_, v_i_2701_, v_j_2702_, v_inv_2703_, v_bs_2704_);
lean_dec_ref(v_as_2700_);
lean_dec(v_start_2699_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0(lean_object* v_p_2706_, lean_object* v___x_2707_, lean_object* v___x_2708_, lean_object* v_a_2709_, lean_object* v_x_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v___x_2712_; uint8_t v___x_2713_; 
lean_inc(v_a_2709_);
v___x_2712_ = lean_apply_1(v_p_2706_, v_a_2709_);
v___x_2713_ = lean_unbox(v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; 
lean_dec(v_a_2709_);
v___x_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2707_);
return v___x_2714_;
}
else
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_dec_ref(v___x_2707_);
v___x_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2715_, 0, v_a_2709_);
v___x_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
v___x_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v___x_2708_);
v___x_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
return v___x_2718_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0___boxed(lean_object* v_p_2719_, lean_object* v___x_2720_, lean_object* v___x_2721_, lean_object* v_a_2722_, lean_object* v_x_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Array_find_x3f___redArg___lam__0(v_p_2719_, v___x_2720_, v___x_2721_, v_a_2722_, v_x_2723_, v___y_2724_);
lean_dec_ref(v___y_2724_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg(lean_object* v_p_2726_, lean_object* v_as_2727_){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___f_2732_; size_t v_sz_2733_; size_t v___x_2734_; lean_object* v___x_2735_; lean_object* v_fst_2736_; 
v___x_2728_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_box(0);
v___x_2731_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2732_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2732_, 0, v_p_2726_);
lean_closure_set(v___f_2732_, 1, v___x_2731_);
lean_closure_set(v___f_2732_, 2, v___x_2730_);
v_sz_2733_ = lean_array_size(v_as_2727_);
v___x_2734_ = ((size_t)0ULL);
v___x_2735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2728_, v_as_2727_, v___f_2732_, v_sz_2733_, v___x_2734_, v___x_2731_);
v_fst_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_fst_2736_);
lean_dec(v___x_2735_);
if (lean_obj_tag(v_fst_2736_) == 0)
{
return v___x_2729_;
}
else
{
lean_object* v_val_2737_; 
v_val_2737_ = lean_ctor_get(v_fst_2736_, 0);
lean_inc(v_val_2737_);
lean_dec_ref(v_fst_2736_);
return v_val_2737_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f(lean_object* v_00_u03b1_2738_, lean_object* v_p_2739_, lean_object* v_as_2740_){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___f_2745_; size_t v_sz_2746_; size_t v___x_2747_; lean_object* v___x_2748_; lean_object* v_fst_2749_; 
v___x_2741_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2742_ = lean_box(0);
v___x_2743_ = lean_box(0);
v___x_2744_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2745_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2745_, 0, v_p_2739_);
lean_closure_set(v___f_2745_, 1, v___x_2744_);
lean_closure_set(v___f_2745_, 2, v___x_2743_);
v_sz_2746_ = lean_array_size(v_as_2740_);
v___x_2747_ = ((size_t)0ULL);
v___x_2748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2741_, v_as_2740_, v___f_2745_, v_sz_2746_, v___x_2747_, v___x_2744_);
v_fst_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_fst_2749_);
lean_dec(v___x_2748_);
if (lean_obj_tag(v_fst_2749_) == 0)
{
return v___x_2742_;
}
else
{
lean_object* v_val_2750_; 
v_val_2750_ = lean_ctor_get(v_fst_2749_, 0);
lean_inc(v_val_2750_);
lean_dec_ref(v_fst_2749_);
return v_val_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0(lean_object* v_f_2751_, lean_object* v___x_2752_, lean_object* v___x_2753_, lean_object* v_a_2754_, lean_object* v_x_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = lean_apply_1(v_f_2751_, v_a_2754_);
if (lean_obj_tag(v___x_2757_) == 1)
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
lean_dec_ref(v___x_2753_);
v___x_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
lean_ctor_set(v___x_2759_, 1, v___x_2752_);
v___x_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
return v___x_2760_;
}
else
{
lean_object* v___x_2761_; 
lean_dec(v___x_2757_);
v___x_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2753_);
return v___x_2761_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2762_, lean_object* v___x_2763_, lean_object* v___x_2764_, lean_object* v_a_2765_, lean_object* v_x_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Array_findSome_x3f___redArg___lam__0(v_f_2762_, v___x_2763_, v___x_2764_, v_a_2765_, v_x_2766_, v___y_2767_);
lean_dec_ref(v___y_2767_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg(lean_object* v_f_2769_, lean_object* v_as_2770_){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___f_2775_; size_t v_sz_2776_; size_t v___x_2777_; lean_object* v___x_2778_; lean_object* v_fst_2779_; 
v___x_2771_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2772_ = lean_box(0);
v___x_2773_ = lean_box(0);
v___x_2774_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2775_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2775_, 0, v_f_2769_);
lean_closure_set(v___f_2775_, 1, v___x_2773_);
lean_closure_set(v___f_2775_, 2, v___x_2774_);
v_sz_2776_ = lean_array_size(v_as_2770_);
v___x_2777_ = ((size_t)0ULL);
v___x_2778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2771_, v_as_2770_, v___f_2775_, v_sz_2776_, v___x_2777_, v___x_2774_);
v_fst_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_fst_2779_);
lean_dec(v___x_2778_);
if (lean_obj_tag(v_fst_2779_) == 0)
{
return v___x_2772_;
}
else
{
lean_object* v_val_2780_; 
v_val_2780_ = lean_ctor_get(v_fst_2779_, 0);
lean_inc(v_val_2780_);
lean_dec_ref(v_fst_2779_);
return v_val_2780_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f(lean_object* v_00_u03b1_2781_, lean_object* v_00_u03b2_2782_, lean_object* v_f_2783_, lean_object* v_as_2784_){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___f_2789_; size_t v_sz_2790_; size_t v___x_2791_; lean_object* v___x_2792_; lean_object* v_fst_2793_; 
v___x_2785_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2786_ = lean_box(0);
v___x_2787_ = lean_box(0);
v___x_2788_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2789_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2789_, 0, v_f_2783_);
lean_closure_set(v___f_2789_, 1, v___x_2787_);
lean_closure_set(v___f_2789_, 2, v___x_2788_);
v_sz_2790_ = lean_array_size(v_as_2784_);
v___x_2791_ = ((size_t)0ULL);
v___x_2792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2785_, v_as_2784_, v___f_2789_, v_sz_2790_, v___x_2791_, v___x_2788_);
v_fst_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_fst_2793_);
lean_dec(v___x_2792_);
if (lean_obj_tag(v_fst_2793_) == 0)
{
return v___x_2786_;
}
else
{
lean_object* v_val_2794_; 
v_val_2794_ = lean_ctor_get(v_fst_2793_, 0);
lean_inc(v_val_2794_);
lean_dec_ref(v_fst_2793_);
return v_val_2794_;
}
}
}
static lean_object* _init_l_Array_findSome_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2797_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__1));
v___x_2798_ = lean_unsigned_to_nat(14u);
v___x_2799_ = lean_unsigned_to_nat(1220u);
v___x_2800_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__0));
v___x_2801_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_2802_ = l_mkPanicMessageWithDecl(v___x_2801_, v___x_2800_, v___x_2799_, v___x_2798_, v___x_2797_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg(lean_object* v_inst_2803_, lean_object* v_f_2804_, lean_object* v_xs_2805_){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___f_2812_; size_t v_sz_2813_; size_t v___x_2814_; lean_object* v___x_2815_; lean_object* v_fst_2816_; 
v___x_2809_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2810_ = lean_box(0);
v___x_2811_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2812_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2812_, 0, v_f_2804_);
lean_closure_set(v___f_2812_, 1, v___x_2810_);
lean_closure_set(v___f_2812_, 2, v___x_2811_);
v_sz_2813_ = lean_array_size(v_xs_2805_);
v___x_2814_ = ((size_t)0ULL);
v___x_2815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2809_, v_xs_2805_, v___f_2812_, v_sz_2813_, v___x_2814_, v___x_2811_);
v_fst_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_fst_2816_);
lean_dec(v___x_2815_);
if (lean_obj_tag(v_fst_2816_) == 0)
{
goto v___jp_2806_;
}
else
{
lean_object* v_val_2817_; 
v_val_2817_ = lean_ctor_get(v_fst_2816_, 0);
lean_inc(v_val_2817_);
lean_dec_ref(v_fst_2816_);
if (lean_obj_tag(v_val_2817_) == 0)
{
goto v___jp_2806_;
}
else
{
lean_object* v_val_2818_; 
lean_dec(v_inst_2803_);
v_val_2818_ = lean_ctor_get(v_val_2817_, 0);
lean_inc(v_val_2818_);
lean_dec_ref(v_val_2817_);
return v_val_2818_;
}
}
v___jp_2806_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2808_ = l_panic___redArg(v_inst_2803_, v___x_2807_);
return v___x_2808_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21(lean_object* v_00_u03b1_2819_, lean_object* v_00_u03b2_2820_, lean_object* v_inst_2821_, lean_object* v_f_2822_, lean_object* v_xs_2823_){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___f_2830_; size_t v_sz_2831_; size_t v___x_2832_; lean_object* v___x_2833_; lean_object* v_fst_2834_; 
v___x_2827_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2828_ = lean_box(0);
v___x_2829_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2830_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2830_, 0, v_f_2822_);
lean_closure_set(v___f_2830_, 1, v___x_2828_);
lean_closure_set(v___f_2830_, 2, v___x_2829_);
v_sz_2831_ = lean_array_size(v_xs_2823_);
v___x_2832_ = ((size_t)0ULL);
v___x_2833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2827_, v_xs_2823_, v___f_2830_, v_sz_2831_, v___x_2832_, v___x_2829_);
v_fst_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_fst_2834_);
lean_dec(v___x_2833_);
if (lean_obj_tag(v_fst_2834_) == 0)
{
goto v___jp_2824_;
}
else
{
lean_object* v_val_2835_; 
v_val_2835_ = lean_ctor_get(v_fst_2834_, 0);
lean_inc(v_val_2835_);
lean_dec_ref(v_fst_2834_);
if (lean_obj_tag(v_val_2835_) == 0)
{
goto v___jp_2824_;
}
else
{
lean_object* v_val_2836_; 
lean_dec(v_inst_2821_);
v_val_2836_ = lean_ctor_get(v_val_2835_, 0);
lean_inc(v_val_2836_);
lean_dec_ref(v_val_2835_);
return v_val_2836_;
}
}
v___jp_2824_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2826_ = l_panic___redArg(v_inst_2821_, v___x_2825_);
return v___x_2826_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2837_, lean_object* v_x_2838_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_apply_1(v_f_2837_, v_x_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg(lean_object* v_f_2840_, lean_object* v_as_2841_){
_start:
{
lean_object* v___f_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___f_2842_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2842_, 0, v_f_2840_);
v___x_2843_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2844_ = lean_array_get_size(v_as_2841_);
v___x_2845_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2843_, v___f_2842_, v_as_2841_, v___x_2844_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f(lean_object* v_00_u03b1_2846_, lean_object* v_00_u03b2_2847_, lean_object* v_f_2848_, lean_object* v_as_2849_){
_start:
{
lean_object* v___f_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___f_2850_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2850_, 0, v_f_2848_);
v___x_2851_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2852_ = lean_array_get_size(v_as_2849_);
v___x_2853_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2851_, v___f_2850_, v_as_2849_, v___x_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg___lam__0(lean_object* v_p_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v___x_2856_; uint8_t v___x_2857_; 
lean_inc(v_a_2855_);
v___x_2856_ = lean_apply_1(v_p_2854_, v_a_2855_);
v___x_2857_ = lean_unbox(v___x_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; 
lean_dec(v_a_2855_);
v___x_2858_ = lean_box(0);
return v___x_2858_;
}
else
{
lean_object* v___x_2859_; 
v___x_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2859_, 0, v_a_2855_);
return v___x_2859_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg(lean_object* v_p_2860_, lean_object* v_as_2861_){
_start:
{
lean_object* v___f_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___f_2862_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2862_, 0, v_p_2860_);
v___x_2863_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2864_ = lean_array_get_size(v_as_2861_);
v___x_2865_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2863_, v___f_2862_, v_as_2861_, v___x_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f(lean_object* v_00_u03b1_2866_, lean_object* v_p_2867_, lean_object* v_as_2868_){
_start:
{
lean_object* v___f_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___f_2869_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2869_, 0, v_p_2867_);
v___x_2870_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2871_ = lean_array_get_size(v_as_2868_);
v___x_2872_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2870_, v___f_2869_, v_as_2868_, v___x_2871_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object* v_p_2873_, lean_object* v_as_2874_, lean_object* v_j_2875_){
_start:
{
lean_object* v___x_2876_; uint8_t v___x_2877_; 
v___x_2876_ = lean_array_get_size(v_as_2874_);
v___x_2877_ = lean_nat_dec_lt(v_j_2875_, v___x_2876_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
lean_dec(v_j_2875_);
lean_dec_ref(v_p_2873_);
v___x_2878_ = lean_box(0);
return v___x_2878_;
}
else
{
lean_object* v___x_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; 
v___x_2879_ = lean_array_fget_borrowed(v_as_2874_, v_j_2875_);
lean_inc_ref(v_p_2873_);
lean_inc(v___x_2879_);
v___x_2880_ = lean_apply_1(v_p_2873_, v___x_2879_);
v___x_2881_ = lean_unbox(v___x_2880_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = lean_unsigned_to_nat(1u);
v___x_2883_ = lean_nat_add(v_j_2875_, v___x_2882_);
lean_dec(v_j_2875_);
v_j_2875_ = v___x_2883_;
goto _start;
}
else
{
lean_object* v___x_2885_; 
lean_dec_ref(v_p_2873_);
v___x_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2885_, 0, v_j_2875_);
return v___x_2885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg___boxed(lean_object* v_p_2886_, lean_object* v_as_2887_, lean_object* v_j_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Array_findIdx_x3f_loop___redArg(v_p_2886_, v_as_2887_, v_j_2888_);
lean_dec_ref(v_as_2887_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop(lean_object* v_00_u03b1_2890_, lean_object* v_p_2891_, lean_object* v_as_2892_, lean_object* v_j_2893_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Array_findIdx_x3f_loop___redArg(v_p_2891_, v_as_2892_, v_j_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___boxed(lean_object* v_00_u03b1_2895_, lean_object* v_p_2896_, lean_object* v_as_2897_, lean_object* v_j_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Array_findIdx_x3f_loop(v_00_u03b1_2895_, v_p_2896_, v_as_2897_, v_j_2898_);
lean_dec_ref(v_as_2897_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg(lean_object* v_p_2900_, lean_object* v_as_2901_){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = lean_unsigned_to_nat(0u);
v___x_2903_ = l_Array_findIdx_x3f_loop___redArg(v_p_2900_, v_as_2901_, v___x_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg___boxed(lean_object* v_p_2904_, lean_object* v_as_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Array_findIdx_x3f___redArg(v_p_2904_, v_as_2905_);
lean_dec_ref(v_as_2905_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f(lean_object* v_00_u03b1_2907_, lean_object* v_p_2908_, lean_object* v_as_2909_){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = lean_unsigned_to_nat(0u);
v___x_2911_ = l_Array_findIdx_x3f_loop___redArg(v_p_2908_, v_as_2909_, v___x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___boxed(lean_object* v_00_u03b1_2912_, lean_object* v_p_2913_, lean_object* v_as_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Array_findIdx_x3f(v_00_u03b1_2912_, v_p_2913_, v_as_2914_);
lean_dec_ref(v_as_2914_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(lean_object* v_p_2916_, lean_object* v_as_2917_, lean_object* v_j_2918_){
_start:
{
lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = lean_array_get_size(v_as_2917_);
v___x_2920_ = lean_nat_dec_lt(v_j_2918_, v___x_2919_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; 
lean_dec(v_j_2918_);
lean_dec_ref(v_p_2916_);
v___x_2921_ = lean_box(0);
return v___x_2921_;
}
else
{
lean_object* v___x_2922_; lean_object* v___x_2923_; uint8_t v___x_2924_; 
v___x_2922_ = lean_array_fget_borrowed(v_as_2917_, v_j_2918_);
lean_inc_ref(v_p_2916_);
lean_inc(v___x_2922_);
v___x_2923_ = lean_apply_1(v_p_2916_, v___x_2922_);
v___x_2924_ = lean_unbox(v___x_2923_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = lean_unsigned_to_nat(1u);
v___x_2926_ = lean_nat_add(v_j_2918_, v___x_2925_);
lean_dec(v_j_2918_);
v_j_2918_ = v___x_2926_;
goto _start;
}
else
{
lean_object* v___x_2928_; 
lean_dec_ref(v_p_2916_);
v___x_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2928_, 0, v_j_2918_);
return v___x_2928_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg___boxed(lean_object* v_p_2929_, lean_object* v_as_2930_, lean_object* v_j_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2929_, v_as_2930_, v_j_2931_);
lean_dec_ref(v_as_2930_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object* v_00_u03b1_2933_, lean_object* v_p_2934_, lean_object* v_as_2935_, lean_object* v_j_2936_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2934_, v_as_2935_, v_j_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___boxed(lean_object* v_00_u03b1_2938_, lean_object* v_p_2939_, lean_object* v_as_2940_, lean_object* v_j_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(v_00_u03b1_2938_, v_p_2939_, v_as_2940_, v_j_2941_);
lean_dec_ref(v_as_2940_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg(lean_object* v_p_2943_, lean_object* v_as_2944_){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = lean_unsigned_to_nat(0u);
v___x_2946_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2943_, v_as_2944_, v___x_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg___boxed(lean_object* v_p_2947_, lean_object* v_as_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Array_findFinIdx_x3f___redArg(v_p_2947_, v_as_2948_);
lean_dec_ref(v_as_2948_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f(lean_object* v_00_u03b1_2950_, lean_object* v_p_2951_, lean_object* v_as_2952_){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = lean_unsigned_to_nat(0u);
v___x_2954_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2951_, v_as_2952_, v___x_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_2955_, lean_object* v_p_2956_, lean_object* v_as_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_Array_findFinIdx_x3f(v_00_u03b1_2955_, v_p_2956_, v_as_2957_);
lean_dec_ref(v_as_2957_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg(lean_object* v_p_2959_, lean_object* v_as_2960_){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = lean_unsigned_to_nat(0u);
v___x_2962_ = l_Array_findIdx_x3f_loop___redArg(v_p_2959_, v_as_2960_, v___x_2961_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_array_get_size(v_as_2960_);
return v___x_2963_;
}
else
{
lean_object* v_val_2964_; 
v_val_2964_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_val_2964_);
lean_dec_ref(v___x_2962_);
return v_val_2964_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg___boxed(lean_object* v_p_2965_, lean_object* v_as_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Array_findIdx___redArg(v_p_2965_, v_as_2966_);
lean_dec_ref(v_as_2966_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx(lean_object* v_00_u03b1_2968_, lean_object* v_p_2969_, lean_object* v_as_2970_){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = lean_unsigned_to_nat(0u);
v___x_2972_ = l_Array_findIdx_x3f_loop___redArg(v_p_2969_, v_as_2970_, v___x_2971_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v___x_2973_; 
v___x_2973_ = lean_array_get_size(v_as_2970_);
return v___x_2973_;
}
else
{
lean_object* v_val_2974_; 
v_val_2974_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_val_2974_);
lean_dec_ref(v___x_2972_);
return v_val_2974_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___boxed(lean_object* v_00_u03b1_2975_, lean_object* v_p_2976_, lean_object* v_as_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Array_findIdx(v_00_u03b1_2975_, v_p_2976_, v_as_2977_);
lean_dec_ref(v_as_2977_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg(lean_object* v_inst_2979_, lean_object* v_xs_2980_, lean_object* v_v_2981_, lean_object* v_i_2982_){
_start:
{
lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2983_ = lean_array_get_size(v_xs_2980_);
v___x_2984_ = lean_nat_dec_lt(v_i_2982_, v___x_2983_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; 
lean_dec(v_i_2982_);
lean_dec(v_v_2981_);
lean_dec_ref(v_inst_2979_);
v___x_2985_ = lean_box(0);
return v___x_2985_;
}
else
{
lean_object* v___x_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; 
v___x_2986_ = lean_array_fget_borrowed(v_xs_2980_, v_i_2982_);
lean_inc_ref(v_inst_2979_);
lean_inc(v_v_2981_);
lean_inc(v___x_2986_);
v___x_2987_ = lean_apply_2(v_inst_2979_, v___x_2986_, v_v_2981_);
v___x_2988_ = lean_unbox(v___x_2987_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = lean_unsigned_to_nat(1u);
v___x_2990_ = lean_nat_add(v_i_2982_, v___x_2989_);
lean_dec(v_i_2982_);
v_i_2982_ = v___x_2990_;
goto _start;
}
else
{
lean_object* v___x_2992_; 
lean_dec(v_v_2981_);
lean_dec_ref(v_inst_2979_);
v___x_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2992_, 0, v_i_2982_);
return v___x_2992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg___boxed(lean_object* v_inst_2993_, lean_object* v_xs_2994_, lean_object* v_v_2995_, lean_object* v_i_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Array_idxOfAux___redArg(v_inst_2993_, v_xs_2994_, v_v_2995_, v_i_2996_);
lean_dec_ref(v_xs_2994_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux(lean_object* v_00_u03b1_2998_, lean_object* v_inst_2999_, lean_object* v_xs_3000_, lean_object* v_v_3001_, lean_object* v_i_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Array_idxOfAux___redArg(v_inst_2999_, v_xs_3000_, v_v_3001_, v_i_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___boxed(lean_object* v_00_u03b1_3004_, lean_object* v_inst_3005_, lean_object* v_xs_3006_, lean_object* v_v_3007_, lean_object* v_i_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Array_idxOfAux(v_00_u03b1_3004_, v_inst_3005_, v_xs_3006_, v_v_3007_, v_i_3008_);
lean_dec_ref(v_xs_3006_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg(lean_object* v_inst_3010_, lean_object* v_xs_3011_, lean_object* v_v_3012_){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = lean_unsigned_to_nat(0u);
v___x_3014_ = l_Array_idxOfAux___redArg(v_inst_3010_, v_xs_3011_, v_v_3012_, v___x_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_3015_, lean_object* v_xs_3016_, lean_object* v_v_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Array_finIdxOf_x3f___redArg(v_inst_3015_, v_xs_3016_, v_v_3017_);
lean_dec_ref(v_xs_3016_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f(lean_object* v_00_u03b1_3019_, lean_object* v_inst_3020_, lean_object* v_xs_3021_, lean_object* v_v_3022_){
_start:
{
lean_object* v___x_3023_; 
v___x_3023_ = l_Array_finIdxOf_x3f___redArg(v_inst_3020_, v_xs_3021_, v_v_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_3024_, lean_object* v_inst_3025_, lean_object* v_xs_3026_, lean_object* v_v_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Array_finIdxOf_x3f(v_00_u03b1_3024_, v_inst_3025_, v_xs_3026_, v_v_3027_);
lean_dec_ref(v_xs_3026_);
return v_res_3028_;
}
}
LEAN_EXPORT uint8_t l_Array_idxOf___redArg___lam__0(lean_object* v_inst_3029_, lean_object* v_a_3030_, lean_object* v_x_3031_){
_start:
{
lean_object* v___x_3032_; uint8_t v___x_3033_; 
v___x_3032_ = lean_apply_2(v_inst_3029_, v_x_3031_, v_a_3030_);
v___x_3033_ = lean_unbox(v___x_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___lam__0___boxed(lean_object* v_inst_3034_, lean_object* v_a_3035_, lean_object* v_x_3036_){
_start:
{
uint8_t v_res_3037_; lean_object* v_r_3038_; 
v_res_3037_ = l_Array_idxOf___redArg___lam__0(v_inst_3034_, v_a_3035_, v_x_3036_);
v_r_3038_ = lean_box(v_res_3037_);
return v_r_3038_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg(lean_object* v_inst_3039_, lean_object* v_a_3040_, lean_object* v_as_3041_){
_start:
{
lean_object* v___f_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___f_3042_ = lean_alloc_closure((void*)(l_Array_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3042_, 0, v_inst_3039_);
lean_closure_set(v___f_3042_, 1, v_a_3040_);
v___x_3043_ = lean_unsigned_to_nat(0u);
v___x_3044_ = l_Array_findIdx_x3f_loop___redArg(v___f_3042_, v_as_3041_, v___x_3043_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v___x_3045_; 
v___x_3045_ = lean_array_get_size(v_as_3041_);
return v___x_3045_;
}
else
{
lean_object* v_val_3046_; 
v_val_3046_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_val_3046_);
lean_dec_ref(v___x_3044_);
return v_val_3046_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___boxed(lean_object* v_inst_3047_, lean_object* v_a_3048_, lean_object* v_as_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Array_idxOf___redArg(v_inst_3047_, v_a_3048_, v_as_3049_);
lean_dec_ref(v_as_3049_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf(lean_object* v_00_u03b1_3051_, lean_object* v_inst_3052_, lean_object* v_a_3053_, lean_object* v_as_3054_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l_Array_idxOf___redArg(v_inst_3052_, v_a_3053_, v_as_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___boxed(lean_object* v_00_u03b1_3056_, lean_object* v_inst_3057_, lean_object* v_a_3058_, lean_object* v_as_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Array_idxOf(v_00_u03b1_3056_, v_inst_3057_, v_a_3058_, v_as_3059_);
lean_dec_ref(v_as_3059_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg(lean_object* v_inst_3061_, lean_object* v_xs_3062_, lean_object* v_v_3063_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_Array_finIdxOf_x3f___redArg(v_inst_3061_, v_xs_3062_, v_v_3063_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v___x_3065_; 
v___x_3065_ = lean_box(0);
return v___x_3065_;
}
else
{
lean_object* v_val_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
v_val_3066_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3064_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_val_3066_);
lean_dec(v___x_3064_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_val_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg___boxed(lean_object* v_inst_3074_, lean_object* v_xs_3075_, lean_object* v_v_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Array_idxOf_x3f___redArg(v_inst_3074_, v_xs_3075_, v_v_3076_);
lean_dec_ref(v_xs_3075_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f(lean_object* v_00_u03b1_3078_, lean_object* v_inst_3079_, lean_object* v_xs_3080_, lean_object* v_v_3081_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_Array_idxOf_x3f___redArg(v_inst_3079_, v_xs_3080_, v_v_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___boxed(lean_object* v_00_u03b1_3083_, lean_object* v_inst_3084_, lean_object* v_xs_3085_, lean_object* v_v_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l_Array_idxOf_x3f(v_00_u03b1_3083_, v_inst_3084_, v_xs_3085_, v_v_3086_);
lean_dec_ref(v_xs_3085_);
return v_res_3087_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg___lam__0(lean_object* v_p_3088_, lean_object* v_x_3089_){
_start:
{
lean_object* v___x_3090_; uint8_t v___x_3091_; 
v___x_3090_ = lean_apply_1(v_p_3088_, v_x_3089_);
v___x_3091_ = lean_unbox(v___x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___lam__0___boxed(lean_object* v_p_3092_, lean_object* v_x_3093_){
_start:
{
uint8_t v_res_3094_; lean_object* v_r_3095_; 
v_res_3094_ = l_Array_any___redArg___lam__0(v_p_3092_, v_x_3093_);
v_r_3095_ = lean_box(v_res_3094_);
return v_r_3095_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg(lean_object* v_as_3096_, lean_object* v_p_3097_, lean_object* v_start_3098_, lean_object* v_stop_3099_){
_start:
{
lean_object* v___x_3100_; uint8_t v___x_3101_; 
v___x_3100_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3101_ = lean_nat_dec_lt(v_start_3098_, v_stop_3099_);
if (v___x_3101_ == 0)
{
lean_dec(v_stop_3099_);
lean_dec_ref(v_p_3097_);
lean_dec_ref(v_as_3096_);
return v___x_3101_;
}
else
{
lean_object* v___f_3102_; lean_object* v___y_3104_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___f_3102_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3102_, 0, v_p_3097_);
v___x_3110_ = lean_array_get_size(v_as_3096_);
v___x_3111_ = lean_nat_dec_le(v_stop_3099_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_dec(v_stop_3099_);
v___y_3104_ = v___x_3110_;
goto v___jp_3103_;
}
else
{
v___y_3104_ = v_stop_3099_;
goto v___jp_3103_;
}
v___jp_3103_:
{
uint8_t v___x_3105_; 
v___x_3105_ = lean_nat_dec_lt(v_start_3098_, v___y_3104_);
if (v___x_3105_ == 0)
{
lean_dec(v___y_3104_);
lean_dec_ref(v___f_3102_);
lean_dec_ref(v_as_3096_);
return v___x_3105_;
}
else
{
size_t v___x_3106_; size_t v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; 
v___x_3106_ = lean_usize_of_nat(v_start_3098_);
v___x_3107_ = lean_usize_of_nat(v___y_3104_);
lean_dec(v___y_3104_);
v___x_3108_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3100_, v___f_3102_, v_as_3096_, v___x_3106_, v___x_3107_);
v___x_3109_ = lean_unbox(v___x_3108_);
lean_dec(v___x_3108_);
return v___x_3109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___boxed(lean_object* v_as_3112_, lean_object* v_p_3113_, lean_object* v_start_3114_, lean_object* v_stop_3115_){
_start:
{
uint8_t v_res_3116_; lean_object* v_r_3117_; 
v_res_3116_ = l_Array_any___redArg(v_as_3112_, v_p_3113_, v_start_3114_, v_stop_3115_);
lean_dec(v_start_3114_);
v_r_3117_ = lean_box(v_res_3116_);
return v_r_3117_;
}
}
LEAN_EXPORT uint8_t l_Array_any(lean_object* v_00_u03b1_3118_, lean_object* v_as_3119_, lean_object* v_p_3120_, lean_object* v_start_3121_, lean_object* v_stop_3122_){
_start:
{
lean_object* v___x_3123_; uint8_t v___x_3124_; 
v___x_3123_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3124_ = lean_nat_dec_lt(v_start_3121_, v_stop_3122_);
if (v___x_3124_ == 0)
{
lean_dec(v_stop_3122_);
lean_dec_ref(v_p_3120_);
lean_dec_ref(v_as_3119_);
return v___x_3124_;
}
else
{
lean_object* v___f_3125_; lean_object* v___y_3127_; lean_object* v___x_3133_; uint8_t v___x_3134_; 
v___f_3125_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3125_, 0, v_p_3120_);
v___x_3133_ = lean_array_get_size(v_as_3119_);
v___x_3134_ = lean_nat_dec_le(v_stop_3122_, v___x_3133_);
if (v___x_3134_ == 0)
{
lean_dec(v_stop_3122_);
v___y_3127_ = v___x_3133_;
goto v___jp_3126_;
}
else
{
v___y_3127_ = v_stop_3122_;
goto v___jp_3126_;
}
v___jp_3126_:
{
uint8_t v___x_3128_; 
v___x_3128_ = lean_nat_dec_lt(v_start_3121_, v___y_3127_);
if (v___x_3128_ == 0)
{
lean_dec(v___y_3127_);
lean_dec_ref(v___f_3125_);
lean_dec_ref(v_as_3119_);
return v___x_3128_;
}
else
{
size_t v___x_3129_; size_t v___x_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; 
v___x_3129_ = lean_usize_of_nat(v_start_3121_);
v___x_3130_ = lean_usize_of_nat(v___y_3127_);
lean_dec(v___y_3127_);
v___x_3131_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3123_, v___f_3125_, v_as_3119_, v___x_3129_, v___x_3130_);
v___x_3132_ = lean_unbox(v___x_3131_);
lean_dec(v___x_3131_);
return v___x_3132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___boxed(lean_object* v_00_u03b1_3135_, lean_object* v_as_3136_, lean_object* v_p_3137_, lean_object* v_start_3138_, lean_object* v_stop_3139_){
_start:
{
uint8_t v_res_3140_; lean_object* v_r_3141_; 
v_res_3140_ = l_Array_any(v_00_u03b1_3135_, v_as_3136_, v_p_3137_, v_start_3138_, v_stop_3139_);
lean_dec(v_start_3138_);
v_r_3141_ = lean_box(v_res_3140_);
return v_r_3141_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg___lam__0(lean_object* v_p_3142_, uint8_t v___x_3143_, lean_object* v_v_3144_){
_start:
{
lean_object* v___x_3145_; uint8_t v___x_3146_; 
v___x_3145_ = lean_apply_1(v_p_3142_, v_v_3144_);
v___x_3146_ = lean_unbox(v___x_3145_);
if (v___x_3146_ == 0)
{
return v___x_3143_;
}
else
{
uint8_t v___x_3147_; 
v___x_3147_ = 0;
return v___x_3147_;
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___lam__0___boxed(lean_object* v_p_3148_, lean_object* v___x_3149_, lean_object* v_v_3150_){
_start:
{
uint8_t v___x_339__boxed_3151_; uint8_t v_res_3152_; lean_object* v_r_3153_; 
v___x_339__boxed_3151_ = lean_unbox(v___x_3149_);
v_res_3152_ = l_Array_all___redArg___lam__0(v_p_3148_, v___x_339__boxed_3151_, v_v_3150_);
v_r_3153_ = lean_box(v_res_3152_);
return v_r_3153_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg(lean_object* v_as_3154_, lean_object* v_p_3155_, lean_object* v_start_3156_, lean_object* v_stop_3157_){
_start:
{
lean_object* v___x_3158_; uint8_t v___x_3159_; 
v___x_3158_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3159_ = lean_nat_dec_lt(v_start_3156_, v_stop_3157_);
if (v___x_3159_ == 0)
{
uint8_t v___x_3160_; 
lean_dec(v_stop_3157_);
lean_dec_ref(v_p_3155_);
lean_dec_ref(v_as_3154_);
v___x_3160_ = 1;
return v___x_3160_;
}
else
{
lean_object* v___x_3161_; lean_object* v___f_3162_; lean_object* v___y_3164_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v___x_3161_ = lean_box(v___x_3159_);
v___f_3162_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3162_, 0, v_p_3155_);
lean_closure_set(v___f_3162_, 1, v___x_3161_);
v___x_3171_ = lean_array_get_size(v_as_3154_);
v___x_3172_ = lean_nat_dec_le(v_stop_3157_, v___x_3171_);
if (v___x_3172_ == 0)
{
lean_dec(v_stop_3157_);
v___y_3164_ = v___x_3171_;
goto v___jp_3163_;
}
else
{
v___y_3164_ = v_stop_3157_;
goto v___jp_3163_;
}
v___jp_3163_:
{
uint8_t v___x_3165_; 
v___x_3165_ = lean_nat_dec_lt(v_start_3156_, v___y_3164_);
if (v___x_3165_ == 0)
{
lean_dec(v___y_3164_);
lean_dec_ref(v___f_3162_);
lean_dec_ref(v_as_3154_);
return v___x_3159_;
}
else
{
size_t v___x_3166_; size_t v___x_3167_; lean_object* v___x_3168_; uint8_t v___x_3169_; 
v___x_3166_ = lean_usize_of_nat(v_start_3156_);
v___x_3167_ = lean_usize_of_nat(v___y_3164_);
lean_dec(v___y_3164_);
v___x_3168_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3158_, v___f_3162_, v_as_3154_, v___x_3166_, v___x_3167_);
v___x_3169_ = lean_unbox(v___x_3168_);
lean_dec(v___x_3168_);
if (v___x_3169_ == 0)
{
return v___x_3165_;
}
else
{
uint8_t v___x_3170_; 
v___x_3170_ = 0;
return v___x_3170_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___boxed(lean_object* v_as_3173_, lean_object* v_p_3174_, lean_object* v_start_3175_, lean_object* v_stop_3176_){
_start:
{
uint8_t v_res_3177_; lean_object* v_r_3178_; 
v_res_3177_ = l_Array_all___redArg(v_as_3173_, v_p_3174_, v_start_3175_, v_stop_3176_);
lean_dec(v_start_3175_);
v_r_3178_ = lean_box(v_res_3177_);
return v_r_3178_;
}
}
LEAN_EXPORT uint8_t l_Array_all(lean_object* v_00_u03b1_3179_, lean_object* v_as_3180_, lean_object* v_p_3181_, lean_object* v_start_3182_, lean_object* v_stop_3183_){
_start:
{
lean_object* v___x_3184_; uint8_t v___x_3185_; 
v___x_3184_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3185_ = lean_nat_dec_lt(v_start_3182_, v_stop_3183_);
if (v___x_3185_ == 0)
{
uint8_t v___x_3186_; 
lean_dec(v_stop_3183_);
lean_dec_ref(v_p_3181_);
lean_dec_ref(v_as_3180_);
v___x_3186_ = 1;
return v___x_3186_;
}
else
{
lean_object* v___x_3187_; lean_object* v___f_3188_; lean_object* v___y_3190_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
v___x_3187_ = lean_box(v___x_3185_);
v___f_3188_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3188_, 0, v_p_3181_);
lean_closure_set(v___f_3188_, 1, v___x_3187_);
v___x_3197_ = lean_array_get_size(v_as_3180_);
v___x_3198_ = lean_nat_dec_le(v_stop_3183_, v___x_3197_);
if (v___x_3198_ == 0)
{
lean_dec(v_stop_3183_);
v___y_3190_ = v___x_3197_;
goto v___jp_3189_;
}
else
{
v___y_3190_ = v_stop_3183_;
goto v___jp_3189_;
}
v___jp_3189_:
{
uint8_t v___x_3191_; 
v___x_3191_ = lean_nat_dec_lt(v_start_3182_, v___y_3190_);
if (v___x_3191_ == 0)
{
lean_dec(v___y_3190_);
lean_dec_ref(v___f_3188_);
lean_dec_ref(v_as_3180_);
return v___x_3185_;
}
else
{
size_t v___x_3192_; size_t v___x_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; 
v___x_3192_ = lean_usize_of_nat(v_start_3182_);
v___x_3193_ = lean_usize_of_nat(v___y_3190_);
lean_dec(v___y_3190_);
v___x_3194_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3184_, v___f_3188_, v_as_3180_, v___x_3192_, v___x_3193_);
v___x_3195_ = lean_unbox(v___x_3194_);
lean_dec(v___x_3194_);
if (v___x_3195_ == 0)
{
return v___x_3191_;
}
else
{
uint8_t v___x_3196_; 
v___x_3196_ = 0;
return v___x_3196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___boxed(lean_object* v_00_u03b1_3199_, lean_object* v_as_3200_, lean_object* v_p_3201_, lean_object* v_start_3202_, lean_object* v_stop_3203_){
_start:
{
uint8_t v_res_3204_; lean_object* v_r_3205_; 
v_res_3204_ = l_Array_all(v_00_u03b1_3199_, v_as_3200_, v_p_3201_, v_start_3202_, v_stop_3203_);
lean_dec(v_start_3202_);
v_r_3205_ = lean_box(v_res_3204_);
return v_r_3205_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg___lam__0(lean_object* v_inst_3206_, lean_object* v_a_3207_, lean_object* v_x_3208_){
_start:
{
lean_object* v___x_3209_; uint8_t v___x_3210_; 
v___x_3209_ = lean_apply_2(v_inst_3206_, v_a_3207_, v_x_3208_);
v___x_3210_ = lean_unbox(v___x_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___lam__0___boxed(lean_object* v_inst_3211_, lean_object* v_a_3212_, lean_object* v_x_3213_){
_start:
{
uint8_t v_res_3214_; lean_object* v_r_3215_; 
v_res_3214_ = l_Array_contains___redArg___lam__0(v_inst_3211_, v_a_3212_, v_x_3213_);
v_r_3215_ = lean_box(v_res_3214_);
return v_r_3215_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg(lean_object* v_inst_3216_, lean_object* v_as_3217_, lean_object* v_a_3218_){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; uint8_t v___x_3222_; 
v___x_3219_ = lean_unsigned_to_nat(0u);
v___x_3220_ = lean_array_get_size(v_as_3217_);
v___x_3221_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3222_ = lean_nat_dec_lt(v___x_3219_, v___x_3220_);
if (v___x_3222_ == 0)
{
lean_dec(v_a_3218_);
lean_dec_ref(v_as_3217_);
lean_dec_ref(v_inst_3216_);
return v___x_3222_;
}
else
{
if (v___x_3222_ == 0)
{
lean_dec(v_a_3218_);
lean_dec_ref(v_as_3217_);
lean_dec_ref(v_inst_3216_);
return v___x_3222_;
}
else
{
lean_object* v___f_3223_; size_t v___x_3224_; size_t v___x_3225_; lean_object* v___x_3226_; uint8_t v___x_3227_; 
v___f_3223_ = lean_alloc_closure((void*)(l_Array_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3223_, 0, v_inst_3216_);
lean_closure_set(v___f_3223_, 1, v_a_3218_);
v___x_3224_ = ((size_t)0ULL);
v___x_3225_ = lean_usize_of_nat(v___x_3220_);
v___x_3226_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3221_, v___f_3223_, v_as_3217_, v___x_3224_, v___x_3225_);
v___x_3227_ = lean_unbox(v___x_3226_);
lean_dec(v___x_3226_);
return v___x_3227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___boxed(lean_object* v_inst_3228_, lean_object* v_as_3229_, lean_object* v_a_3230_){
_start:
{
uint8_t v_res_3231_; lean_object* v_r_3232_; 
v_res_3231_ = l_Array_contains___redArg(v_inst_3228_, v_as_3229_, v_a_3230_);
v_r_3232_ = lean_box(v_res_3231_);
return v_r_3232_;
}
}
LEAN_EXPORT uint8_t l_Array_contains(lean_object* v_00_u03b1_3233_, lean_object* v_inst_3234_, lean_object* v_as_3235_, lean_object* v_a_3236_){
_start:
{
uint8_t v___x_3237_; 
v___x_3237_ = l_Array_contains___redArg(v_inst_3234_, v_as_3235_, v_a_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___boxed(lean_object* v_00_u03b1_3238_, lean_object* v_inst_3239_, lean_object* v_as_3240_, lean_object* v_a_3241_){
_start:
{
uint8_t v_res_3242_; lean_object* v_r_3243_; 
v_res_3242_ = l_Array_contains(v_00_u03b1_3238_, v_inst_3239_, v_as_3240_, v_a_3241_);
v_r_3243_ = lean_box(v_res_3242_);
return v_r_3243_;
}
}
LEAN_EXPORT uint8_t l_Array_elem___redArg(lean_object* v_inst_3244_, lean_object* v_a_3245_, lean_object* v_as_3246_){
_start:
{
uint8_t v___x_3247_; 
v___x_3247_ = l_Array_contains___redArg(v_inst_3244_, v_as_3246_, v_a_3245_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___redArg___boxed(lean_object* v_inst_3248_, lean_object* v_a_3249_, lean_object* v_as_3250_){
_start:
{
uint8_t v_res_3251_; lean_object* v_r_3252_; 
v_res_3251_ = l_Array_elem___redArg(v_inst_3248_, v_a_3249_, v_as_3250_);
v_r_3252_ = lean_box(v_res_3251_);
return v_r_3252_;
}
}
LEAN_EXPORT uint8_t l_Array_elem(lean_object* v_00_u03b1_3253_, lean_object* v_inst_3254_, lean_object* v_a_3255_, lean_object* v_as_3256_){
_start:
{
uint8_t v___x_3257_; 
v___x_3257_ = l_Array_contains___redArg(v_inst_3254_, v_as_3256_, v_a_3255_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___boxed(lean_object* v_00_u03b1_3258_, lean_object* v_inst_3259_, lean_object* v_a_3260_, lean_object* v_as_3261_){
_start:
{
uint8_t v_res_3262_; lean_object* v_r_3263_; 
v_res_3262_ = l_Array_elem(v_00_u03b1_3258_, v_inst_3259_, v_a_3260_, v_as_3261_);
v_r_3263_ = lean_box(v_res_3262_);
return v_r_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(lean_object* v_as_3264_, size_t v_i_3265_, size_t v_stop_3266_, lean_object* v_b_3267_){
_start:
{
uint8_t v___x_3268_; 
v___x_3268_ = lean_usize_dec_eq(v_i_3265_, v_stop_3266_);
if (v___x_3268_ == 0)
{
size_t v___x_3269_; size_t v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3269_ = ((size_t)1ULL);
v___x_3270_ = lean_usize_sub(v_i_3265_, v___x_3269_);
v___x_3271_ = lean_array_uget_borrowed(v_as_3264_, v___x_3270_);
lean_inc(v___x_3271_);
v___x_3272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
lean_ctor_set(v___x_3272_, 1, v_b_3267_);
v_i_3265_ = v___x_3270_;
v_b_3267_ = v___x_3272_;
goto _start;
}
else
{
return v_b_3267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg___boxed(lean_object* v_as_3274_, lean_object* v_i_3275_, lean_object* v_stop_3276_, lean_object* v_b_3277_){
_start:
{
size_t v_i_boxed_3278_; size_t v_stop_boxed_3279_; lean_object* v_res_3280_; 
v_i_boxed_3278_ = lean_unbox_usize(v_i_3275_);
lean_dec(v_i_3275_);
v_stop_boxed_3279_ = lean_unbox_usize(v_stop_3276_);
lean_dec(v_stop_3276_);
v_res_3280_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3274_, v_i_boxed_3278_, v_stop_boxed_3279_, v_b_3277_);
lean_dec_ref(v_as_3274_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg(lean_object* v_as_3281_){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v___x_3282_ = lean_box(0);
v___x_3283_ = lean_array_get_size(v_as_3281_);
v___x_3284_ = lean_unsigned_to_nat(0u);
v___x_3285_ = lean_nat_dec_lt(v___x_3284_, v___x_3283_);
if (v___x_3285_ == 0)
{
return v___x_3282_;
}
else
{
size_t v___x_3286_; size_t v___x_3287_; lean_object* v___x_3288_; 
v___x_3286_ = lean_usize_of_nat(v___x_3283_);
v___x_3287_ = ((size_t)0ULL);
v___x_3288_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3281_, v___x_3286_, v___x_3287_, v___x_3282_);
return v___x_3288_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg___boxed(lean_object* v_as_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Array_toListImpl___redArg(v_as_3289_);
lean_dec_ref(v_as_3289_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* lean_array_to_list_impl(lean_object* v_00_u03b1_3291_, lean_object* v_as_3292_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Array_toListImpl___redArg(v_as_3292_);
lean_dec_ref(v_as_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(lean_object* v_00_u03b1_3294_, lean_object* v_as_3295_, size_t v_i_3296_, size_t v_stop_3297_, lean_object* v_b_3298_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3295_, v_i_3296_, v_stop_3297_, v_b_3298_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___boxed(lean_object* v_00_u03b1_3300_, lean_object* v_as_3301_, lean_object* v_i_3302_, lean_object* v_stop_3303_, lean_object* v_b_3304_){
_start:
{
size_t v_i_boxed_3305_; size_t v_stop_boxed_3306_; lean_object* v_res_3307_; 
v_i_boxed_3305_ = lean_unbox_usize(v_i_3302_);
lean_dec(v_i_3302_);
v_stop_boxed_3306_ = lean_unbox_usize(v_stop_3303_);
lean_dec(v_stop_3303_);
v_res_3307_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(v_00_u03b1_3300_, v_as_3301_, v_i_boxed_3305_, v_stop_boxed_3306_, v_b_3304_);
lean_dec_ref(v_as_3301_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg___lam__0(lean_object* v_x1_3308_, lean_object* v_x2_3309_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3310_, 0, v_x1_3308_);
lean_ctor_set(v___x_3310_, 1, v_x2_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg(lean_object* v_as_3312_, lean_object* v_l_3313_){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; uint8_t v___x_3317_; 
v___x_3314_ = lean_array_get_size(v_as_3312_);
v___x_3315_ = lean_unsigned_to_nat(0u);
v___x_3316_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3317_ = lean_nat_dec_lt(v___x_3315_, v___x_3314_);
if (v___x_3317_ == 0)
{
lean_dec_ref(v_as_3312_);
return v_l_3313_;
}
else
{
lean_object* v___f_3318_; size_t v___x_3319_; size_t v___x_3320_; lean_object* v___x_3321_; 
v___f_3318_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3319_ = lean_usize_of_nat(v___x_3314_);
v___x_3320_ = ((size_t)0ULL);
v___x_3321_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3316_, v___f_3318_, v_as_3312_, v___x_3319_, v___x_3320_, v_l_3313_);
return v___x_3321_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend(lean_object* v_00_u03b1_3322_, lean_object* v_as_3323_, lean_object* v_l_3324_){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; 
v___x_3325_ = lean_array_get_size(v_as_3323_);
v___x_3326_ = lean_unsigned_to_nat(0u);
v___x_3327_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3328_ = lean_nat_dec_lt(v___x_3326_, v___x_3325_);
if (v___x_3328_ == 0)
{
lean_dec_ref(v_as_3323_);
return v_l_3324_;
}
else
{
lean_object* v___f_3329_; size_t v___x_3330_; size_t v___x_3331_; lean_object* v___x_3332_; 
v___f_3329_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3330_ = lean_usize_of_nat(v___x_3325_);
v___x_3331_ = ((size_t)0ULL);
v___x_3332_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3327_, v___f_3329_, v_as_3323_, v___x_3330_, v___x_3331_, v_l_3324_);
return v___x_3332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(lean_object* v_as_3333_, size_t v_i_3334_, size_t v_stop_3335_, lean_object* v_b_3336_){
_start:
{
uint8_t v___x_3337_; 
v___x_3337_ = lean_usize_dec_eq(v_i_3334_, v_stop_3335_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; lean_object* v___x_3339_; size_t v___x_3340_; size_t v___x_3341_; 
v___x_3338_ = lean_array_uget_borrowed(v_as_3333_, v_i_3334_);
lean_inc(v___x_3338_);
v___x_3339_ = lean_array_push(v_b_3336_, v___x_3338_);
v___x_3340_ = ((size_t)1ULL);
v___x_3341_ = lean_usize_add(v_i_3334_, v___x_3340_);
v_i_3334_ = v___x_3341_;
v_b_3336_ = v___x_3339_;
goto _start;
}
else
{
return v_b_3336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg___boxed(lean_object* v_as_3343_, lean_object* v_i_3344_, lean_object* v_stop_3345_, lean_object* v_b_3346_){
_start:
{
size_t v_i_boxed_3347_; size_t v_stop_boxed_3348_; lean_object* v_res_3349_; 
v_i_boxed_3347_ = lean_unbox_usize(v_i_3344_);
lean_dec(v_i_3344_);
v_stop_boxed_3348_ = lean_unbox_usize(v_stop_3345_);
lean_dec(v_stop_3345_);
v_res_3349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3343_, v_i_boxed_3347_, v_stop_boxed_3348_, v_b_3346_);
lean_dec_ref(v_as_3343_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg(lean_object* v_as_3350_, lean_object* v_bs_3351_){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
v___x_3352_ = lean_unsigned_to_nat(0u);
v___x_3353_ = lean_array_get_size(v_bs_3351_);
v___x_3354_ = lean_nat_dec_lt(v___x_3352_, v___x_3353_);
if (v___x_3354_ == 0)
{
return v_as_3350_;
}
else
{
uint8_t v___x_3355_; 
v___x_3355_ = lean_nat_dec_le(v___x_3353_, v___x_3353_);
if (v___x_3355_ == 0)
{
if (v___x_3354_ == 0)
{
return v_as_3350_;
}
else
{
size_t v___x_3356_; size_t v___x_3357_; lean_object* v___x_3358_; 
v___x_3356_ = ((size_t)0ULL);
v___x_3357_ = lean_usize_of_nat(v___x_3353_);
v___x_3358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3351_, v___x_3356_, v___x_3357_, v_as_3350_);
return v___x_3358_;
}
}
else
{
size_t v___x_3359_; size_t v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = ((size_t)0ULL);
v___x_3360_ = lean_usize_of_nat(v___x_3353_);
v___x_3361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3351_, v___x_3359_, v___x_3360_, v_as_3350_);
return v___x_3361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg___boxed(lean_object* v_as_3362_, lean_object* v_bs_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Array_append___redArg(v_as_3362_, v_bs_3363_);
lean_dec_ref(v_bs_3363_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Array_append(lean_object* v_00_u03b1_3365_, lean_object* v_as_3366_, lean_object* v_bs_3367_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Array_append___redArg(v_as_3366_, v_bs_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Array_append___boxed(lean_object* v_00_u03b1_3369_, lean_object* v_as_3370_, lean_object* v_bs_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Array_append(v_00_u03b1_3369_, v_as_3370_, v_bs_3371_);
lean_dec_ref(v_bs_3371_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(lean_object* v_00_u03b1_3373_, lean_object* v_as_3374_, size_t v_i_3375_, size_t v_stop_3376_, lean_object* v_b_3377_){
_start:
{
lean_object* v___x_3378_; 
v___x_3378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3374_, v_i_3375_, v_stop_3376_, v_b_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___boxed(lean_object* v_00_u03b1_3379_, lean_object* v_as_3380_, lean_object* v_i_3381_, lean_object* v_stop_3382_, lean_object* v_b_3383_){
_start:
{
size_t v_i_boxed_3384_; size_t v_stop_boxed_3385_; lean_object* v_res_3386_; 
v_i_boxed_3384_ = lean_unbox_usize(v_i_3381_);
lean_dec(v_i_3381_);
v_stop_boxed_3385_ = lean_unbox_usize(v_stop_3382_);
lean_dec(v_stop_3382_);
v_res_3386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(v_00_u03b1_3379_, v_as_3380_, v_i_boxed_3384_, v_stop_boxed_3385_, v_b_3383_);
lean_dec_ref(v_as_3380_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend(lean_object* v_00_u03b1_3388_){
_start:
{
lean_object* v___x_3389_; 
v___x_3389_ = ((lean_object*)(l_Array_instAppend___closed__0));
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object* v_x_3390_, lean_object* v_x_3391_){
_start:
{
if (lean_obj_tag(v_x_3391_) == 0)
{
return v_x_3390_;
}
else
{
lean_object* v_head_3392_; lean_object* v_tail_3393_; lean_object* v___x_3394_; 
v_head_3392_ = lean_ctor_get(v_x_3391_, 0);
lean_inc(v_head_3392_);
v_tail_3393_ = lean_ctor_get(v_x_3391_, 1);
lean_inc(v_tail_3393_);
lean_dec_ref(v_x_3391_);
v___x_3394_ = lean_array_push(v_x_3390_, v_head_3392_);
v_x_3390_ = v___x_3394_;
v_x_3391_ = v_tail_3393_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_appendList___redArg(lean_object* v_as_3396_, lean_object* v_bs_3397_){
_start:
{
lean_object* v___x_3398_; 
v___x_3398_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3396_, v_bs_3397_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Array_appendList(lean_object* v_00_u03b1_3399_, lean_object* v_as_3400_, lean_object* v_bs_3401_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3400_, v_bs_3401_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0(lean_object* v_00_u03b1_3403_, lean_object* v_x_3404_, lean_object* v_x_3405_){
_start:
{
lean_object* v___x_3406_; 
v___x_3406_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_3404_, v_x_3405_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList(lean_object* v_00_u03b1_3408_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = ((lean_object*)(l_Array_instHAppendList___closed__0));
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0(lean_object* v_bs_3410_, lean_object* v_toPure_3411_, lean_object* v_____do__lift_3412_){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = l_Array_append___redArg(v_bs_3410_, v_____do__lift_3412_);
v___x_3414_ = lean_apply_2(v_toPure_3411_, lean_box(0), v___x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0___boxed(lean_object* v_bs_3415_, lean_object* v_toPure_3416_, lean_object* v_____do__lift_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Array_flatMapM___redArg___lam__0(v_bs_3415_, v_toPure_3416_, v_____do__lift_3417_);
lean_dec_ref(v_____do__lift_3417_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__1(lean_object* v_toPure_3419_, lean_object* v_f_3420_, lean_object* v_toBind_3421_, lean_object* v_bs_3422_, lean_object* v_a_3423_){
_start:
{
lean_object* v___f_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___f_3424_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3424_, 0, v_bs_3422_);
lean_closure_set(v___f_3424_, 1, v_toPure_3419_);
v___x_3425_ = lean_apply_1(v_f_3420_, v_a_3423_);
v___x_3426_ = lean_apply_4(v_toBind_3421_, lean_box(0), lean_box(0), v___x_3425_, v___f_3424_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg(lean_object* v_inst_3427_, lean_object* v_f_3428_, lean_object* v_as_3429_){
_start:
{
lean_object* v_toApplicative_3430_; lean_object* v_toBind_3431_; lean_object* v_toPure_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; uint8_t v___x_3436_; 
v_toApplicative_3430_ = lean_ctor_get(v_inst_3427_, 0);
v_toBind_3431_ = lean_ctor_get(v_inst_3427_, 1);
v_toPure_3432_ = lean_ctor_get(v_toApplicative_3430_, 1);
v___x_3433_ = lean_unsigned_to_nat(0u);
v___x_3434_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3435_ = lean_array_get_size(v_as_3429_);
v___x_3436_ = lean_nat_dec_lt(v___x_3433_, v___x_3435_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; 
lean_inc(v_toPure_3432_);
lean_dec_ref(v_as_3429_);
lean_dec(v_f_3428_);
lean_dec_ref(v_inst_3427_);
v___x_3437_ = lean_apply_2(v_toPure_3432_, lean_box(0), v___x_3434_);
return v___x_3437_;
}
else
{
lean_object* v___f_3438_; uint8_t v___x_3439_; 
lean_inc(v_toBind_3431_);
lean_inc(v_toPure_3432_);
v___f_3438_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3438_, 0, v_toPure_3432_);
lean_closure_set(v___f_3438_, 1, v_f_3428_);
lean_closure_set(v___f_3438_, 2, v_toBind_3431_);
v___x_3439_ = lean_nat_dec_le(v___x_3435_, v___x_3435_);
if (v___x_3439_ == 0)
{
if (v___x_3436_ == 0)
{
lean_object* v___x_3440_; 
lean_inc(v_toPure_3432_);
lean_dec_ref(v___f_3438_);
lean_dec_ref(v_as_3429_);
lean_dec_ref(v_inst_3427_);
v___x_3440_ = lean_apply_2(v_toPure_3432_, lean_box(0), v___x_3434_);
return v___x_3440_;
}
else
{
size_t v___x_3441_; size_t v___x_3442_; lean_object* v___x_3443_; 
v___x_3441_ = ((size_t)0ULL);
v___x_3442_ = lean_usize_of_nat(v___x_3435_);
v___x_3443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3427_, v___f_3438_, v_as_3429_, v___x_3441_, v___x_3442_, v___x_3434_);
return v___x_3443_;
}
}
else
{
size_t v___x_3444_; size_t v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = ((size_t)0ULL);
v___x_3445_ = lean_usize_of_nat(v___x_3435_);
v___x_3446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3427_, v___f_3438_, v_as_3429_, v___x_3444_, v___x_3445_, v___x_3434_);
return v___x_3446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM(lean_object* v_00_u03b1_3447_, lean_object* v_m_3448_, lean_object* v_00_u03b2_3449_, lean_object* v_inst_3450_, lean_object* v_f_3451_, lean_object* v_as_3452_){
_start:
{
lean_object* v_toApplicative_3453_; lean_object* v_toBind_3454_; lean_object* v_toPure_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; uint8_t v___x_3459_; 
v_toApplicative_3453_ = lean_ctor_get(v_inst_3450_, 0);
v_toBind_3454_ = lean_ctor_get(v_inst_3450_, 1);
v_toPure_3455_ = lean_ctor_get(v_toApplicative_3453_, 1);
v___x_3456_ = lean_unsigned_to_nat(0u);
v___x_3457_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3458_ = lean_array_get_size(v_as_3452_);
v___x_3459_ = lean_nat_dec_lt(v___x_3456_, v___x_3458_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; 
lean_inc(v_toPure_3455_);
lean_dec_ref(v_as_3452_);
lean_dec(v_f_3451_);
lean_dec_ref(v_inst_3450_);
v___x_3460_ = lean_apply_2(v_toPure_3455_, lean_box(0), v___x_3457_);
return v___x_3460_;
}
else
{
lean_object* v___f_3461_; uint8_t v___x_3462_; 
lean_inc(v_toBind_3454_);
lean_inc(v_toPure_3455_);
v___f_3461_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3461_, 0, v_toPure_3455_);
lean_closure_set(v___f_3461_, 1, v_f_3451_);
lean_closure_set(v___f_3461_, 2, v_toBind_3454_);
v___x_3462_ = lean_nat_dec_le(v___x_3458_, v___x_3458_);
if (v___x_3462_ == 0)
{
if (v___x_3459_ == 0)
{
lean_object* v___x_3463_; 
lean_inc(v_toPure_3455_);
lean_dec_ref(v___f_3461_);
lean_dec_ref(v_as_3452_);
lean_dec_ref(v_inst_3450_);
v___x_3463_ = lean_apply_2(v_toPure_3455_, lean_box(0), v___x_3457_);
return v___x_3463_;
}
else
{
size_t v___x_3464_; size_t v___x_3465_; lean_object* v___x_3466_; 
v___x_3464_ = ((size_t)0ULL);
v___x_3465_ = lean_usize_of_nat(v___x_3458_);
v___x_3466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3450_, v___f_3461_, v_as_3452_, v___x_3464_, v___x_3465_, v___x_3457_);
return v___x_3466_;
}
}
else
{
size_t v___x_3467_; size_t v___x_3468_; lean_object* v___x_3469_; 
v___x_3467_ = ((size_t)0ULL);
v___x_3468_ = lean_usize_of_nat(v___x_3458_);
v___x_3469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3450_, v___f_3461_, v_as_3452_, v___x_3467_, v___x_3468_, v___x_3457_);
return v___x_3469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg___lam__0(lean_object* v_f_3470_, lean_object* v_x1_3471_, lean_object* v_x2_3472_){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3473_ = lean_apply_1(v_f_3470_, v_x2_3472_);
v___x_3474_ = l_Array_append___redArg(v_x1_3471_, v___x_3473_);
lean_dec_ref(v___x_3473_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg(lean_object* v_f_3475_, lean_object* v_as_3476_){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v___x_3477_ = lean_unsigned_to_nat(0u);
v___x_3478_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3479_ = lean_array_get_size(v_as_3476_);
v___x_3480_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3481_ = lean_nat_dec_lt(v___x_3477_, v___x_3479_);
if (v___x_3481_ == 0)
{
lean_dec_ref(v_as_3476_);
lean_dec_ref(v_f_3475_);
return v___x_3478_;
}
else
{
lean_object* v___f_3482_; uint8_t v___x_3483_; 
v___f_3482_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3482_, 0, v_f_3475_);
v___x_3483_ = lean_nat_dec_le(v___x_3479_, v___x_3479_);
if (v___x_3483_ == 0)
{
if (v___x_3481_ == 0)
{
lean_dec_ref(v___f_3482_);
lean_dec_ref(v_as_3476_);
return v___x_3478_;
}
else
{
size_t v___x_3484_; size_t v___x_3485_; lean_object* v___x_3486_; 
v___x_3484_ = ((size_t)0ULL);
v___x_3485_ = lean_usize_of_nat(v___x_3479_);
v___x_3486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3480_, v___f_3482_, v_as_3476_, v___x_3484_, v___x_3485_, v___x_3478_);
return v___x_3486_;
}
}
else
{
size_t v___x_3487_; size_t v___x_3488_; lean_object* v___x_3489_; 
v___x_3487_ = ((size_t)0ULL);
v___x_3488_ = lean_usize_of_nat(v___x_3479_);
v___x_3489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3480_, v___f_3482_, v_as_3476_, v___x_3487_, v___x_3488_, v___x_3478_);
return v___x_3489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap(lean_object* v_00_u03b1_3490_, lean_object* v_00_u03b2_3491_, lean_object* v_f_3492_, lean_object* v_as_3493_){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_3494_ = lean_unsigned_to_nat(0u);
v___x_3495_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3496_ = lean_array_get_size(v_as_3493_);
v___x_3497_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3498_ = lean_nat_dec_lt(v___x_3494_, v___x_3496_);
if (v___x_3498_ == 0)
{
lean_dec_ref(v_as_3493_);
lean_dec_ref(v_f_3492_);
return v___x_3495_;
}
else
{
lean_object* v___f_3499_; uint8_t v___x_3500_; 
v___f_3499_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3499_, 0, v_f_3492_);
v___x_3500_ = lean_nat_dec_le(v___x_3496_, v___x_3496_);
if (v___x_3500_ == 0)
{
if (v___x_3498_ == 0)
{
lean_dec_ref(v___f_3499_);
lean_dec_ref(v_as_3493_);
return v___x_3495_;
}
else
{
size_t v___x_3501_; size_t v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = ((size_t)0ULL);
v___x_3502_ = lean_usize_of_nat(v___x_3496_);
v___x_3503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3497_, v___f_3499_, v_as_3493_, v___x_3501_, v___x_3502_, v___x_3495_);
return v___x_3503_;
}
}
else
{
size_t v___x_3504_; size_t v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = ((size_t)0ULL);
v___x_3505_ = lean_usize_of_nat(v___x_3496_);
v___x_3506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3497_, v___f_3499_, v_as_3493_, v___x_3504_, v___x_3505_, v___x_3495_);
return v___x_3506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten___redArg(lean_object* v_xss_3508_){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; uint8_t v___x_3513_; 
v___x_3509_ = lean_unsigned_to_nat(0u);
v___x_3510_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3511_ = lean_array_get_size(v_xss_3508_);
v___x_3512_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3513_ = lean_nat_dec_lt(v___x_3509_, v___x_3511_);
if (v___x_3513_ == 0)
{
lean_dec_ref(v_xss_3508_);
return v___x_3510_;
}
else
{
lean_object* v___f_3514_; uint8_t v___x_3515_; 
v___f_3514_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3515_ = lean_nat_dec_le(v___x_3511_, v___x_3511_);
if (v___x_3515_ == 0)
{
if (v___x_3513_ == 0)
{
lean_dec_ref(v_xss_3508_);
return v___x_3510_;
}
else
{
size_t v___x_3516_; size_t v___x_3517_; lean_object* v___x_3518_; 
v___x_3516_ = ((size_t)0ULL);
v___x_3517_ = lean_usize_of_nat(v___x_3511_);
v___x_3518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3512_, v___f_3514_, v_xss_3508_, v___x_3516_, v___x_3517_, v___x_3510_);
return v___x_3518_;
}
}
else
{
size_t v___x_3519_; size_t v___x_3520_; lean_object* v___x_3521_; 
v___x_3519_ = ((size_t)0ULL);
v___x_3520_ = lean_usize_of_nat(v___x_3511_);
v___x_3521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3512_, v___f_3514_, v_xss_3508_, v___x_3519_, v___x_3520_, v___x_3510_);
return v___x_3521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten(lean_object* v_00_u03b1_3522_, lean_object* v_xss_3523_){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; uint8_t v___x_3528_; 
v___x_3524_ = lean_unsigned_to_nat(0u);
v___x_3525_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3526_ = lean_array_get_size(v_xss_3523_);
v___x_3527_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3528_ = lean_nat_dec_lt(v___x_3524_, v___x_3526_);
if (v___x_3528_ == 0)
{
lean_dec_ref(v_xss_3523_);
return v___x_3525_;
}
else
{
lean_object* v___f_3529_; uint8_t v___x_3530_; 
v___f_3529_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3530_ = lean_nat_dec_le(v___x_3526_, v___x_3526_);
if (v___x_3530_ == 0)
{
if (v___x_3528_ == 0)
{
lean_dec_ref(v_xss_3523_);
return v___x_3525_;
}
else
{
size_t v___x_3531_; size_t v___x_3532_; lean_object* v___x_3533_; 
v___x_3531_ = ((size_t)0ULL);
v___x_3532_ = lean_usize_of_nat(v___x_3526_);
v___x_3533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3527_, v___f_3529_, v_xss_3523_, v___x_3531_, v___x_3532_, v___x_3525_);
return v___x_3533_;
}
}
else
{
size_t v___x_3534_; size_t v___x_3535_; lean_object* v___x_3536_; 
v___x_3534_ = ((size_t)0ULL);
v___x_3535_ = lean_usize_of_nat(v___x_3526_);
v___x_3536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3527_, v___f_3529_, v_xss_3523_, v___x_3534_, v___x_3535_, v___x_3525_);
return v___x_3536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop___redArg(lean_object* v_as_3537_, lean_object* v_i_3538_, lean_object* v_j_3539_){
_start:
{
uint8_t v___x_3540_; 
v___x_3540_ = lean_nat_dec_lt(v_i_3538_, v_j_3539_);
if (v___x_3540_ == 0)
{
lean_dec(v_j_3539_);
lean_dec(v_i_3538_);
return v_as_3537_;
}
else
{
lean_object* v_as_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v_as_3541_ = lean_array_fswap(v_as_3537_, v_i_3538_, v_j_3539_);
v___x_3542_ = lean_unsigned_to_nat(1u);
v___x_3543_ = lean_nat_add(v_i_3538_, v___x_3542_);
lean_dec(v_i_3538_);
v___x_3544_ = lean_nat_sub(v_j_3539_, v___x_3542_);
lean_dec(v_j_3539_);
v_as_3537_ = v_as_3541_;
v_i_3538_ = v___x_3543_;
v_j_3539_ = v___x_3544_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop(lean_object* v_00_u03b1_3546_, lean_object* v_as_3547_, lean_object* v_i_3548_, lean_object* v_j_3549_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Array_reverse_loop___redArg(v_as_3547_, v_i_3548_, v_j_3549_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Array_reverse___redArg(lean_object* v_as_3551_){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v___x_3552_ = lean_array_get_size(v_as_3551_);
v___x_3553_ = lean_unsigned_to_nat(1u);
v___x_3554_ = lean_nat_dec_le(v___x_3552_, v___x_3553_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3555_ = lean_unsigned_to_nat(0u);
v___x_3556_ = lean_nat_sub(v___x_3552_, v___x_3553_);
v___x_3557_ = l_Array_reverse_loop___redArg(v_as_3551_, v___x_3555_, v___x_3556_);
return v___x_3557_;
}
else
{
return v_as_3551_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse(lean_object* v_00_u03b1_3558_, lean_object* v_as_3559_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Array_reverse___redArg(v_as_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___lam__0(lean_object* v_p_3561_, lean_object* v_x1_3562_, lean_object* v_x2_3563_){
_start:
{
lean_object* v___x_3564_; uint8_t v___x_3565_; 
lean_inc(v_x2_3563_);
v___x_3564_ = lean_apply_1(v_p_3561_, v_x2_3563_);
v___x_3565_ = lean_unbox(v___x_3564_);
if (v___x_3565_ == 0)
{
lean_dec(v_x2_3563_);
return v_x1_3562_;
}
else
{
lean_object* v___x_3566_; 
v___x_3566_ = lean_array_push(v_x1_3562_, v_x2_3563_);
return v___x_3566_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg(lean_object* v_p_3569_, lean_object* v_as_3570_, lean_object* v_start_3571_, lean_object* v_stop_3572_){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; uint8_t v___x_3575_; 
v___x_3573_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3574_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3575_ = lean_nat_dec_lt(v_start_3571_, v_stop_3572_);
if (v___x_3575_ == 0)
{
lean_dec_ref(v_as_3570_);
lean_dec_ref(v_p_3569_);
return v___x_3573_;
}
else
{
lean_object* v___f_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___f_3576_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3576_, 0, v_p_3569_);
v___x_3577_ = lean_array_get_size(v_as_3570_);
v___x_3578_ = lean_nat_dec_le(v_stop_3572_, v___x_3577_);
if (v___x_3578_ == 0)
{
uint8_t v___x_3579_; 
v___x_3579_ = lean_nat_dec_lt(v_start_3571_, v___x_3577_);
if (v___x_3579_ == 0)
{
lean_dec_ref(v___f_3576_);
lean_dec_ref(v_as_3570_);
return v___x_3573_;
}
else
{
size_t v___x_3580_; size_t v___x_3581_; lean_object* v___x_3582_; 
v___x_3580_ = lean_usize_of_nat(v_start_3571_);
v___x_3581_ = lean_usize_of_nat(v___x_3577_);
v___x_3582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3574_, v___f_3576_, v_as_3570_, v___x_3580_, v___x_3581_, v___x_3573_);
return v___x_3582_;
}
}
else
{
size_t v___x_3583_; size_t v___x_3584_; lean_object* v___x_3585_; 
v___x_3583_ = lean_usize_of_nat(v_start_3571_);
v___x_3584_ = lean_usize_of_nat(v_stop_3572_);
v___x_3585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3574_, v___f_3576_, v_as_3570_, v___x_3583_, v___x_3584_, v___x_3573_);
return v___x_3585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___boxed(lean_object* v_p_3586_, lean_object* v_as_3587_, lean_object* v_start_3588_, lean_object* v_stop_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Array_filter___redArg(v_p_3586_, v_as_3587_, v_start_3588_, v_stop_3589_);
lean_dec(v_stop_3589_);
lean_dec(v_start_3588_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Array_filter(lean_object* v_00_u03b1_3591_, lean_object* v_p_3592_, lean_object* v_as_3593_, lean_object* v_start_3594_, lean_object* v_stop_3595_){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; 
v___x_3596_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3597_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3598_ = lean_nat_dec_lt(v_start_3594_, v_stop_3595_);
if (v___x_3598_ == 0)
{
lean_dec_ref(v_as_3593_);
lean_dec_ref(v_p_3592_);
return v___x_3596_;
}
else
{
lean_object* v___f_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___f_3599_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3599_, 0, v_p_3592_);
v___x_3600_ = lean_array_get_size(v_as_3593_);
v___x_3601_ = lean_nat_dec_le(v_stop_3595_, v___x_3600_);
if (v___x_3601_ == 0)
{
uint8_t v___x_3602_; 
v___x_3602_ = lean_nat_dec_lt(v_start_3594_, v___x_3600_);
if (v___x_3602_ == 0)
{
lean_dec_ref(v___f_3599_);
lean_dec_ref(v_as_3593_);
return v___x_3596_;
}
else
{
size_t v___x_3603_; size_t v___x_3604_; lean_object* v___x_3605_; 
v___x_3603_ = lean_usize_of_nat(v_start_3594_);
v___x_3604_ = lean_usize_of_nat(v___x_3600_);
v___x_3605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3597_, v___f_3599_, v_as_3593_, v___x_3603_, v___x_3604_, v___x_3596_);
return v___x_3605_;
}
}
else
{
size_t v___x_3606_; size_t v___x_3607_; lean_object* v___x_3608_; 
v___x_3606_ = lean_usize_of_nat(v_start_3594_);
v___x_3607_ = lean_usize_of_nat(v_stop_3595_);
v___x_3608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3597_, v___f_3599_, v_as_3593_, v___x_3606_, v___x_3607_, v___x_3596_);
return v___x_3608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___boxed(lean_object* v_00_u03b1_3609_, lean_object* v_p_3610_, lean_object* v_as_3611_, lean_object* v_start_3612_, lean_object* v_stop_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Array_filter(v_00_u03b1_3609_, v_p_3610_, v_as_3611_, v_start_3612_, v_stop_3613_);
lean_dec(v_stop_3613_);
lean_dec(v_start_3612_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0(lean_object* v_toApplicative_3615_, lean_object* v_acc_3616_, lean_object* v_a_3617_, uint8_t v_____do__lift_3618_){
_start:
{
if (v_____do__lift_3618_ == 0)
{
lean_object* v_toPure_3619_; lean_object* v___x_3620_; 
lean_dec(v_a_3617_);
v_toPure_3619_ = lean_ctor_get(v_toApplicative_3615_, 1);
lean_inc(v_toPure_3619_);
lean_dec_ref(v_toApplicative_3615_);
v___x_3620_ = lean_apply_2(v_toPure_3619_, lean_box(0), v_acc_3616_);
return v___x_3620_;
}
else
{
lean_object* v_toPure_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v_toPure_3621_ = lean_ctor_get(v_toApplicative_3615_, 1);
lean_inc(v_toPure_3621_);
lean_dec_ref(v_toApplicative_3615_);
v___x_3622_ = lean_array_push(v_acc_3616_, v_a_3617_);
v___x_3623_ = lean_apply_2(v_toPure_3621_, lean_box(0), v___x_3622_);
return v___x_3623_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0___boxed(lean_object* v_toApplicative_3624_, lean_object* v_acc_3625_, lean_object* v_a_3626_, lean_object* v_____do__lift_3627_){
_start:
{
uint8_t v_____do__lift_119__boxed_3628_; lean_object* v_res_3629_; 
v_____do__lift_119__boxed_3628_ = lean_unbox(v_____do__lift_3627_);
v_res_3629_ = l_Array_filterM___redArg___lam__0(v_toApplicative_3624_, v_acc_3625_, v_a_3626_, v_____do__lift_119__boxed_3628_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__1(lean_object* v_toApplicative_3630_, lean_object* v_p_3631_, lean_object* v_toBind_3632_, lean_object* v_acc_3633_, lean_object* v_a_3634_){
_start:
{
lean_object* v___f_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
lean_inc(v_a_3634_);
v___f_3635_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3635_, 0, v_toApplicative_3630_);
lean_closure_set(v___f_3635_, 1, v_acc_3633_);
lean_closure_set(v___f_3635_, 2, v_a_3634_);
v___x_3636_ = lean_apply_1(v_p_3631_, v_a_3634_);
v___x_3637_ = lean_apply_4(v_toBind_3632_, lean_box(0), lean_box(0), v___x_3636_, v___f_3635_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg(lean_object* v_inst_3638_, lean_object* v_p_3639_, lean_object* v_as_3640_, lean_object* v_start_3641_, lean_object* v_stop_3642_){
_start:
{
lean_object* v_toApplicative_3643_; lean_object* v_toBind_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
v_toApplicative_3643_ = lean_ctor_get(v_inst_3638_, 0);
v_toBind_3644_ = lean_ctor_get(v_inst_3638_, 1);
v___x_3645_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3646_ = lean_nat_dec_lt(v_start_3641_, v_stop_3642_);
if (v___x_3646_ == 0)
{
lean_object* v_toPure_3647_; lean_object* v___x_3648_; 
lean_inc_ref(v_toApplicative_3643_);
lean_dec_ref(v_as_3640_);
lean_dec(v_p_3639_);
lean_dec_ref(v_inst_3638_);
v_toPure_3647_ = lean_ctor_get(v_toApplicative_3643_, 1);
lean_inc(v_toPure_3647_);
lean_dec_ref(v_toApplicative_3643_);
v___x_3648_ = lean_apply_2(v_toPure_3647_, lean_box(0), v___x_3645_);
return v___x_3648_;
}
else
{
lean_object* v___f_3649_; lean_object* v___x_3650_; uint8_t v___x_3651_; 
lean_inc(v_toBind_3644_);
lean_inc_ref(v_toApplicative_3643_);
v___f_3649_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3649_, 0, v_toApplicative_3643_);
lean_closure_set(v___f_3649_, 1, v_p_3639_);
lean_closure_set(v___f_3649_, 2, v_toBind_3644_);
v___x_3650_ = lean_array_get_size(v_as_3640_);
v___x_3651_ = lean_nat_dec_le(v_stop_3642_, v___x_3650_);
if (v___x_3651_ == 0)
{
uint8_t v___x_3652_; 
v___x_3652_ = lean_nat_dec_lt(v_start_3641_, v___x_3650_);
if (v___x_3652_ == 0)
{
lean_object* v_toPure_3653_; lean_object* v___x_3654_; 
lean_inc_ref(v_toApplicative_3643_);
lean_dec_ref(v___f_3649_);
lean_dec_ref(v_as_3640_);
lean_dec_ref(v_inst_3638_);
v_toPure_3653_ = lean_ctor_get(v_toApplicative_3643_, 1);
lean_inc(v_toPure_3653_);
lean_dec_ref(v_toApplicative_3643_);
v___x_3654_ = lean_apply_2(v_toPure_3653_, lean_box(0), v___x_3645_);
return v___x_3654_;
}
else
{
size_t v___x_3655_; size_t v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = lean_usize_of_nat(v_start_3641_);
v___x_3656_ = lean_usize_of_nat(v___x_3650_);
v___x_3657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3638_, v___f_3649_, v_as_3640_, v___x_3655_, v___x_3656_, v___x_3645_);
return v___x_3657_;
}
}
else
{
size_t v___x_3658_; size_t v___x_3659_; lean_object* v___x_3660_; 
v___x_3658_ = lean_usize_of_nat(v_start_3641_);
v___x_3659_ = lean_usize_of_nat(v_stop_3642_);
v___x_3660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3638_, v___f_3649_, v_as_3640_, v___x_3658_, v___x_3659_, v___x_3645_);
return v___x_3660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___boxed(lean_object* v_inst_3661_, lean_object* v_p_3662_, lean_object* v_as_3663_, lean_object* v_start_3664_, lean_object* v_stop_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Array_filterM___redArg(v_inst_3661_, v_p_3662_, v_as_3663_, v_start_3664_, v_stop_3665_);
lean_dec(v_stop_3665_);
lean_dec(v_start_3664_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM(lean_object* v_m_3667_, lean_object* v_00_u03b1_3668_, lean_object* v_inst_3669_, lean_object* v_p_3670_, lean_object* v_as_3671_, lean_object* v_start_3672_, lean_object* v_stop_3673_){
_start:
{
lean_object* v_toApplicative_3674_; lean_object* v_toBind_3675_; lean_object* v___x_3676_; uint8_t v___x_3677_; 
v_toApplicative_3674_ = lean_ctor_get(v_inst_3669_, 0);
v_toBind_3675_ = lean_ctor_get(v_inst_3669_, 1);
v___x_3676_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3677_ = lean_nat_dec_lt(v_start_3672_, v_stop_3673_);
if (v___x_3677_ == 0)
{
lean_object* v_toPure_3678_; lean_object* v___x_3679_; 
lean_inc_ref(v_toApplicative_3674_);
lean_dec_ref(v_as_3671_);
lean_dec(v_p_3670_);
lean_dec_ref(v_inst_3669_);
v_toPure_3678_ = lean_ctor_get(v_toApplicative_3674_, 1);
lean_inc(v_toPure_3678_);
lean_dec_ref(v_toApplicative_3674_);
v___x_3679_ = lean_apply_2(v_toPure_3678_, lean_box(0), v___x_3676_);
return v___x_3679_;
}
else
{
lean_object* v___f_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
lean_inc(v_toBind_3675_);
lean_inc_ref(v_toApplicative_3674_);
v___f_3680_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3680_, 0, v_toApplicative_3674_);
lean_closure_set(v___f_3680_, 1, v_p_3670_);
lean_closure_set(v___f_3680_, 2, v_toBind_3675_);
v___x_3681_ = lean_array_get_size(v_as_3671_);
v___x_3682_ = lean_nat_dec_le(v_stop_3673_, v___x_3681_);
if (v___x_3682_ == 0)
{
uint8_t v___x_3683_; 
v___x_3683_ = lean_nat_dec_lt(v_start_3672_, v___x_3681_);
if (v___x_3683_ == 0)
{
lean_object* v_toPure_3684_; lean_object* v___x_3685_; 
lean_inc_ref(v_toApplicative_3674_);
lean_dec_ref(v___f_3680_);
lean_dec_ref(v_as_3671_);
lean_dec_ref(v_inst_3669_);
v_toPure_3684_ = lean_ctor_get(v_toApplicative_3674_, 1);
lean_inc(v_toPure_3684_);
lean_dec_ref(v_toApplicative_3674_);
v___x_3685_ = lean_apply_2(v_toPure_3684_, lean_box(0), v___x_3676_);
return v___x_3685_;
}
else
{
size_t v___x_3686_; size_t v___x_3687_; lean_object* v___x_3688_; 
v___x_3686_ = lean_usize_of_nat(v_start_3672_);
v___x_3687_ = lean_usize_of_nat(v___x_3681_);
v___x_3688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3669_, v___f_3680_, v_as_3671_, v___x_3686_, v___x_3687_, v___x_3676_);
return v___x_3688_;
}
}
else
{
size_t v___x_3689_; size_t v___x_3690_; lean_object* v___x_3691_; 
v___x_3689_ = lean_usize_of_nat(v_start_3672_);
v___x_3690_ = lean_usize_of_nat(v_stop_3673_);
v___x_3691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3669_, v___f_3680_, v_as_3671_, v___x_3689_, v___x_3690_, v___x_3676_);
return v___x_3691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___boxed(lean_object* v_m_3692_, lean_object* v_00_u03b1_3693_, lean_object* v_inst_3694_, lean_object* v_p_3695_, lean_object* v_as_3696_, lean_object* v_start_3697_, lean_object* v_stop_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Array_filterM(v_m_3692_, v_00_u03b1_3693_, v_inst_3694_, v_p_3695_, v_as_3696_, v_start_3697_, v_stop_3698_);
lean_dec(v_stop_3698_);
lean_dec(v_start_3697_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__0(lean_object* v_toPure_3700_, lean_object* v_acc_3701_, lean_object* v_a_3702_, uint8_t v_____do__lift_3703_){
_start:
{
if (v_____do__lift_3703_ == 0)
{
lean_object* v___x_3704_; 
lean_dec(v_a_3702_);
v___x_3704_ = lean_apply_2(v_toPure_3700_, lean_box(0), v_acc_3701_);
return v___x_3704_;
}
else
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3705_ = lean_array_push(v_acc_3701_, v_a_3702_);
v___x_3706_ = lean_apply_2(v_toPure_3700_, lean_box(0), v___x_3705_);
return v___x_3706_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__0___boxed(lean_object* v_toPure_3707_, lean_object* v_acc_3708_, lean_object* v_a_3709_, lean_object* v_____do__lift_3710_){
_start:
{
uint8_t v_____do__lift_129__boxed_3711_; lean_object* v_res_3712_; 
v_____do__lift_129__boxed_3711_ = lean_unbox(v_____do__lift_3710_);
v_res_3712_ = l_Array_filterRevM___redArg___lam__0(v_toPure_3707_, v_acc_3708_, v_a_3709_, v_____do__lift_129__boxed_3711_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__1(lean_object* v_toPure_3713_, lean_object* v_p_3714_, lean_object* v_toBind_3715_, lean_object* v_a_3716_, lean_object* v_acc_3717_){
_start:
{
lean_object* v___f_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
lean_inc(v_a_3716_);
v___f_3718_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3718_, 0, v_toPure_3713_);
lean_closure_set(v___f_3718_, 1, v_acc_3717_);
lean_closure_set(v___f_3718_, 2, v_a_3716_);
v___x_3719_ = lean_apply_1(v_p_3714_, v_a_3716_);
v___x_3720_ = lean_apply_4(v_toBind_3715_, lean_box(0), lean_box(0), v___x_3719_, v___f_3718_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg(lean_object* v_inst_3722_, lean_object* v_p_3723_, lean_object* v_as_3724_, lean_object* v_start_3725_, lean_object* v_stop_3726_){
_start:
{
lean_object* v_toApplicative_3727_; lean_object* v_toFunctor_3728_; lean_object* v_toBind_3729_; lean_object* v_toPure_3730_; lean_object* v_map_3731_; lean_object* v___f_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; uint8_t v___x_3736_; 
v_toApplicative_3727_ = lean_ctor_get(v_inst_3722_, 0);
v_toFunctor_3728_ = lean_ctor_get(v_toApplicative_3727_, 0);
v_toBind_3729_ = lean_ctor_get(v_inst_3722_, 1);
v_toPure_3730_ = lean_ctor_get(v_toApplicative_3727_, 1);
v_map_3731_ = lean_ctor_get(v_toFunctor_3728_, 0);
lean_inc(v_map_3731_);
lean_inc(v_toBind_3729_);
lean_inc(v_toPure_3730_);
v___f_3732_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3732_, 0, v_toPure_3730_);
lean_closure_set(v___f_3732_, 1, v_p_3723_);
lean_closure_set(v___f_3732_, 2, v_toBind_3729_);
v___x_3733_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3734_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3735_ = lean_array_get_size(v_as_3724_);
v___x_3736_ = lean_nat_dec_le(v_start_3725_, v___x_3735_);
if (v___x_3736_ == 0)
{
uint8_t v___x_3737_; 
v___x_3737_ = lean_nat_dec_lt(v_stop_3726_, v___x_3735_);
if (v___x_3737_ == 0)
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
lean_inc(v_toPure_3730_);
lean_dec_ref(v___f_3732_);
lean_dec_ref(v_as_3724_);
lean_dec_ref(v_inst_3722_);
v___x_3738_ = lean_apply_2(v_toPure_3730_, lean_box(0), v___x_3734_);
v___x_3739_ = lean_apply_4(v_map_3731_, lean_box(0), lean_box(0), v___x_3733_, v___x_3738_);
return v___x_3739_;
}
else
{
size_t v___x_3740_; size_t v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3740_ = lean_usize_of_nat(v___x_3735_);
v___x_3741_ = lean_usize_of_nat(v_stop_3726_);
v___x_3742_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3722_, v___f_3732_, v_as_3724_, v___x_3740_, v___x_3741_, v___x_3734_);
v___x_3743_ = lean_apply_4(v_map_3731_, lean_box(0), lean_box(0), v___x_3733_, v___x_3742_);
return v___x_3743_;
}
}
else
{
uint8_t v___x_3744_; 
v___x_3744_ = lean_nat_dec_lt(v_stop_3726_, v_start_3725_);
if (v___x_3744_ == 0)
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
lean_inc(v_toPure_3730_);
lean_dec_ref(v___f_3732_);
lean_dec_ref(v_as_3724_);
lean_dec_ref(v_inst_3722_);
v___x_3745_ = lean_apply_2(v_toPure_3730_, lean_box(0), v___x_3734_);
v___x_3746_ = lean_apply_4(v_map_3731_, lean_box(0), lean_box(0), v___x_3733_, v___x_3745_);
return v___x_3746_;
}
else
{
size_t v___x_3747_; size_t v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3747_ = lean_usize_of_nat(v_start_3725_);
v___x_3748_ = lean_usize_of_nat(v_stop_3726_);
v___x_3749_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3722_, v___f_3732_, v_as_3724_, v___x_3747_, v___x_3748_, v___x_3734_);
v___x_3750_ = lean_apply_4(v_map_3731_, lean_box(0), lean_box(0), v___x_3733_, v___x_3749_);
return v___x_3750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___boxed(lean_object* v_inst_3751_, lean_object* v_p_3752_, lean_object* v_as_3753_, lean_object* v_start_3754_, lean_object* v_stop_3755_){
_start:
{
lean_object* v_res_3756_; 
v_res_3756_ = l_Array_filterRevM___redArg(v_inst_3751_, v_p_3752_, v_as_3753_, v_start_3754_, v_stop_3755_);
lean_dec(v_stop_3755_);
lean_dec(v_start_3754_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM(lean_object* v_m_3757_, lean_object* v_00_u03b1_3758_, lean_object* v_inst_3759_, lean_object* v_p_3760_, lean_object* v_as_3761_, lean_object* v_start_3762_, lean_object* v_stop_3763_){
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
LEAN_EXPORT lean_object* l_Array_filterRevM___boxed(lean_object* v_m_3788_, lean_object* v_00_u03b1_3789_, lean_object* v_inst_3790_, lean_object* v_p_3791_, lean_object* v_as_3792_, lean_object* v_start_3793_, lean_object* v_stop_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_Array_filterRevM(v_m_3788_, v_00_u03b1_3789_, v_inst_3790_, v_p_3791_, v_as_3792_, v_start_3793_, v_stop_3794_);
lean_dec(v_stop_3794_);
lean_dec(v_start_3793_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__0(lean_object* v_toPure_3796_, lean_object* v_bs_3797_, lean_object* v_____do__lift_3798_){
_start:
{
if (lean_obj_tag(v_____do__lift_3798_) == 0)
{
lean_object* v___x_3799_; 
v___x_3799_ = lean_apply_2(v_toPure_3796_, lean_box(0), v_bs_3797_);
return v___x_3799_;
}
else
{
lean_object* v_val_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v_val_3800_ = lean_ctor_get(v_____do__lift_3798_, 0);
lean_inc(v_val_3800_);
lean_dec_ref(v_____do__lift_3798_);
v___x_3801_ = lean_array_push(v_bs_3797_, v_val_3800_);
v___x_3802_ = lean_apply_2(v_toPure_3796_, lean_box(0), v___x_3801_);
return v___x_3802_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__1(lean_object* v_toPure_3803_, lean_object* v_f_3804_, lean_object* v_toBind_3805_, lean_object* v_bs_3806_, lean_object* v_a_3807_){
_start:
{
lean_object* v___f_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___f_3808_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3808_, 0, v_toPure_3803_);
lean_closure_set(v___f_3808_, 1, v_bs_3806_);
v___x_3809_ = lean_apply_1(v_f_3804_, v_a_3807_);
v___x_3810_ = lean_apply_4(v_toBind_3805_, lean_box(0), lean_box(0), v___x_3809_, v___f_3808_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg(lean_object* v_inst_3811_, lean_object* v_f_3812_, lean_object* v_as_3813_, lean_object* v_start_3814_, lean_object* v_stop_3815_){
_start:
{
lean_object* v_toApplicative_3816_; lean_object* v_toBind_3817_; lean_object* v_toPure_3818_; lean_object* v___x_3819_; uint8_t v___x_3820_; 
v_toApplicative_3816_ = lean_ctor_get(v_inst_3811_, 0);
v_toBind_3817_ = lean_ctor_get(v_inst_3811_, 1);
v_toPure_3818_ = lean_ctor_get(v_toApplicative_3816_, 1);
v___x_3819_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3820_ = lean_nat_dec_lt(v_start_3814_, v_stop_3815_);
if (v___x_3820_ == 0)
{
lean_object* v___x_3821_; 
lean_inc(v_toPure_3818_);
lean_dec_ref(v_as_3813_);
lean_dec(v_f_3812_);
lean_dec_ref(v_inst_3811_);
v___x_3821_ = lean_apply_2(v_toPure_3818_, lean_box(0), v___x_3819_);
return v___x_3821_;
}
else
{
lean_object* v___f_3822_; lean_object* v___x_3823_; uint8_t v___x_3824_; 
lean_inc(v_toBind_3817_);
lean_inc(v_toPure_3818_);
v___f_3822_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3822_, 0, v_toPure_3818_);
lean_closure_set(v___f_3822_, 1, v_f_3812_);
lean_closure_set(v___f_3822_, 2, v_toBind_3817_);
v___x_3823_ = lean_array_get_size(v_as_3813_);
v___x_3824_ = lean_nat_dec_le(v_stop_3815_, v___x_3823_);
if (v___x_3824_ == 0)
{
uint8_t v___x_3825_; 
v___x_3825_ = lean_nat_dec_lt(v_start_3814_, v___x_3823_);
if (v___x_3825_ == 0)
{
lean_object* v___x_3826_; 
lean_inc(v_toPure_3818_);
lean_dec_ref(v___f_3822_);
lean_dec_ref(v_as_3813_);
lean_dec_ref(v_inst_3811_);
v___x_3826_ = lean_apply_2(v_toPure_3818_, lean_box(0), v___x_3819_);
return v___x_3826_;
}
else
{
size_t v___x_3827_; size_t v___x_3828_; lean_object* v___x_3829_; 
v___x_3827_ = lean_usize_of_nat(v_start_3814_);
v___x_3828_ = lean_usize_of_nat(v___x_3823_);
v___x_3829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3811_, v___f_3822_, v_as_3813_, v___x_3827_, v___x_3828_, v___x_3819_);
return v___x_3829_;
}
}
else
{
size_t v___x_3830_; size_t v___x_3831_; lean_object* v___x_3832_; 
v___x_3830_ = lean_usize_of_nat(v_start_3814_);
v___x_3831_ = lean_usize_of_nat(v_stop_3815_);
v___x_3832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3811_, v___f_3822_, v_as_3813_, v___x_3830_, v___x_3831_, v___x_3819_);
return v___x_3832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___boxed(lean_object* v_inst_3833_, lean_object* v_f_3834_, lean_object* v_as_3835_, lean_object* v_start_3836_, lean_object* v_stop_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Array_filterMapM___redArg(v_inst_3833_, v_f_3834_, v_as_3835_, v_start_3836_, v_stop_3837_);
lean_dec(v_stop_3837_);
lean_dec(v_start_3836_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM(lean_object* v_00_u03b1_3839_, lean_object* v_m_3840_, lean_object* v_00_u03b2_3841_, lean_object* v_inst_3842_, lean_object* v_f_3843_, lean_object* v_as_3844_, lean_object* v_start_3845_, lean_object* v_stop_3846_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l_Array_filterMapM___redArg(v_inst_3842_, v_f_3843_, v_as_3844_, v_start_3845_, v_stop_3846_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___boxed(lean_object* v_00_u03b1_3848_, lean_object* v_m_3849_, lean_object* v_00_u03b2_3850_, lean_object* v_inst_3851_, lean_object* v_f_3852_, lean_object* v_as_3853_, lean_object* v_start_3854_, lean_object* v_stop_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Array_filterMapM(v_00_u03b1_3848_, v_m_3849_, v_00_u03b2_3850_, v_inst_3851_, v_f_3852_, v_as_3853_, v_start_3854_, v_stop_3855_);
lean_dec(v_stop_3855_);
lean_dec(v_start_3854_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg(lean_object* v_f_3857_, lean_object* v_as_3858_, lean_object* v_start_3859_, lean_object* v_stop_3860_){
_start:
{
lean_object* v___f_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___f_3861_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3861_, 0, v_f_3857_);
v___x_3862_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3863_ = l_Array_filterMapM___redArg(v___x_3862_, v___f_3861_, v_as_3858_, v_start_3859_, v_stop_3860_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg___boxed(lean_object* v_f_3864_, lean_object* v_as_3865_, lean_object* v_start_3866_, lean_object* v_stop_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_Array_filterMap___redArg(v_f_3864_, v_as_3865_, v_start_3866_, v_stop_3867_);
lean_dec(v_stop_3867_);
lean_dec(v_start_3866_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap(lean_object* v_00_u03b1_3869_, lean_object* v_00_u03b2_3870_, lean_object* v_f_3871_, lean_object* v_as_3872_, lean_object* v_start_3873_, lean_object* v_stop_3874_){
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
LEAN_EXPORT lean_object* l_Array_filterMap___boxed(lean_object* v_00_u03b1_3878_, lean_object* v_00_u03b2_3879_, lean_object* v_f_3880_, lean_object* v_as_3881_, lean_object* v_start_3882_, lean_object* v_stop_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Array_filterMap(v_00_u03b1_3878_, v_00_u03b2_3879_, v_f_3880_, v_as_3881_, v_start_3882_, v_stop_3883_);
lean_dec(v_stop_3883_);
lean_dec(v_start_3882_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg___lam__0(lean_object* v_lt_3885_, lean_object* v_x1_3886_, lean_object* v_x2_3887_){
_start:
{
lean_object* v___x_3888_; uint8_t v___x_3889_; 
lean_inc(v_x2_3887_);
lean_inc(v_x1_3886_);
v___x_3888_ = lean_apply_2(v_lt_3885_, v_x1_3886_, v_x2_3887_);
v___x_3889_ = lean_unbox(v___x_3888_);
if (v___x_3889_ == 0)
{
lean_dec(v_x2_3887_);
return v_x1_3886_;
}
else
{
lean_dec(v_x1_3886_);
return v_x2_3887_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg(lean_object* v_as_3890_, lean_object* v_lt_3891_){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; uint8_t v___x_3894_; 
v___x_3892_ = lean_unsigned_to_nat(0u);
v___x_3893_ = lean_array_get_size(v_as_3890_);
v___x_3894_ = lean_nat_dec_lt(v___x_3892_, v___x_3893_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; 
lean_dec_ref(v_lt_3891_);
lean_dec_ref(v_as_3890_);
v___x_3895_ = lean_box(0);
return v___x_3895_;
}
else
{
lean_object* v_a0_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; uint8_t v___x_3899_; 
v_a0_3896_ = lean_array_fget(v_as_3890_, v___x_3892_);
v___x_3897_ = lean_unsigned_to_nat(1u);
v___x_3898_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3899_ = lean_nat_dec_lt(v___x_3897_, v___x_3893_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; 
lean_dec_ref(v_lt_3891_);
lean_dec_ref(v_as_3890_);
v___x_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3900_, 0, v_a0_3896_);
return v___x_3900_;
}
else
{
lean_object* v___f_3901_; uint8_t v___x_3902_; 
v___f_3901_ = lean_alloc_closure((void*)(l_Array_getMax_x3f___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3901_, 0, v_lt_3891_);
v___x_3902_ = lean_nat_dec_le(v___x_3893_, v___x_3893_);
if (v___x_3902_ == 0)
{
if (v___x_3899_ == 0)
{
lean_object* v___x_3903_; 
lean_dec_ref(v___f_3901_);
lean_dec_ref(v_as_3890_);
v___x_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3903_, 0, v_a0_3896_);
return v___x_3903_;
}
else
{
size_t v___x_3904_; size_t v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3904_ = ((size_t)1ULL);
v___x_3905_ = lean_usize_of_nat(v___x_3893_);
v___x_3906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3898_, v___f_3901_, v_as_3890_, v___x_3904_, v___x_3905_, v_a0_3896_);
v___x_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3906_);
return v___x_3907_;
}
}
else
{
size_t v___x_3908_; size_t v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3908_ = ((size_t)1ULL);
v___x_3909_ = lean_usize_of_nat(v___x_3893_);
v___x_3910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3898_, v___f_3901_, v_as_3890_, v___x_3908_, v___x_3909_, v_a0_3896_);
v___x_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3910_);
return v___x_3911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f(lean_object* v_00_u03b1_3912_, lean_object* v_as_3913_, lean_object* v_lt_3914_){
_start:
{
lean_object* v___x_3915_; 
v___x_3915_ = l_Array_getMax_x3f___redArg(v_as_3913_, v_lt_3914_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg___lam__0(lean_object* v_p_3916_, lean_object* v_a_3917_, lean_object* v_x_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v_fst_3920_; lean_object* v_snd_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3937_; 
v_fst_3920_ = lean_ctor_get(v___y_3919_, 0);
v_snd_3921_ = lean_ctor_get(v___y_3919_, 1);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___y_3919_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3923_ = v___y_3919_;
v_isShared_3924_ = v_isSharedCheck_3937_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_snd_3921_);
lean_inc(v_fst_3920_);
lean_dec(v___y_3919_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3937_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3925_; uint8_t v___x_3926_; 
lean_inc(v_a_3917_);
v___x_3925_ = lean_apply_1(v_p_3916_, v_a_3917_);
v___x_3926_ = lean_unbox(v___x_3925_);
if (v___x_3926_ == 0)
{
lean_object* v___x_3927_; lean_object* v___x_3929_; 
v___x_3927_ = lean_array_push(v_snd_3921_, v_a_3917_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 1, v___x_3927_);
v___x_3929_ = v___x_3923_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_fst_3920_);
lean_ctor_set(v_reuseFailAlloc_3931_, 1, v___x_3927_);
v___x_3929_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
lean_object* v___x_3930_; 
v___x_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
return v___x_3930_;
}
}
else
{
lean_object* v___x_3932_; lean_object* v___x_3934_; 
v___x_3932_ = lean_array_push(v_fst_3920_, v_a_3917_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 0, v___x_3932_);
v___x_3934_ = v___x_3923_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_snd_3921_);
v___x_3934_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3935_; 
v___x_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3934_);
return v___x_3935_;
}
}
}
}
}
static lean_object* _init_l_Array_partition___redArg___closed__0(void){
_start:
{
lean_object* v_bs_3938_; lean_object* v___x_3939_; 
v_bs_3938_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3939_, 0, v_bs_3938_);
lean_ctor_set(v___x_3939_, 1, v_bs_3938_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg(lean_object* v_p_3940_, lean_object* v_as_3941_){
_start:
{
lean_object* v___f_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; size_t v_sz_3945_; size_t v___x_3946_; lean_object* v___x_3947_; lean_object* v_fst_3948_; lean_object* v_snd_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
v___f_3942_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3942_, 0, v_p_3940_);
v___x_3943_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3944_ = lean_obj_once(&l_Array_partition___redArg___closed__0, &l_Array_partition___redArg___closed__0_once, _init_l_Array_partition___redArg___closed__0);
v_sz_3945_ = lean_array_size(v_as_3941_);
v___x_3946_ = ((size_t)0ULL);
v___x_3947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_3943_, v_as_3941_, v___f_3942_, v_sz_3945_, v___x_3946_, v___x_3944_);
v_fst_3948_ = lean_ctor_get(v___x_3947_, 0);
v_snd_3949_ = lean_ctor_get(v___x_3947_, 1);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3947_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_snd_3949_);
lean_inc(v_fst_3948_);
lean_dec(v___x_3947_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_fst_3948_);
lean_ctor_set(v_reuseFailAlloc_3955_, 1, v_snd_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition(lean_object* v_00_u03b1_3957_, lean_object* v_p_3958_, lean_object* v_as_3959_){
_start:
{
lean_object* v___f_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; size_t v_sz_3963_; size_t v___x_3964_; lean_object* v___x_3965_; lean_object* v_fst_3966_; lean_object* v_snd_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
v___f_3960_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3960_, 0, v_p_3958_);
v___x_3961_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3962_ = lean_obj_once(&l_Array_partition___redArg___closed__0, &l_Array_partition___redArg___closed__0_once, _init_l_Array_partition___redArg___closed__0);
v_sz_3963_ = lean_array_size(v_as_3959_);
v___x_3964_ = ((size_t)0ULL);
v___x_3965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_3961_, v_as_3959_, v___f_3960_, v_sz_3963_, v___x_3964_, v___x_3962_);
v_fst_3966_ = lean_ctor_get(v___x_3965_, 0);
v_snd_3967_ = lean_ctor_get(v___x_3965_, 1);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3965_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_snd_3967_);
lean_inc(v_fst_3966_);
lean_dec(v___x_3965_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_fst_3966_);
lean_ctor_set(v_reuseFailAlloc_3973_, 1, v_snd_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile___redArg(lean_object* v_p_3975_, lean_object* v_as_3976_){
_start:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; uint8_t v___x_3979_; 
v___x_3977_ = lean_unsigned_to_nat(0u);
v___x_3978_ = lean_array_get_size(v_as_3976_);
v___x_3979_ = lean_nat_dec_lt(v___x_3977_, v___x_3978_);
if (v___x_3979_ == 0)
{
lean_dec_ref(v_p_3975_);
return v_as_3976_;
}
else
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; 
v___x_3980_ = lean_unsigned_to_nat(1u);
v___x_3981_ = lean_nat_sub(v___x_3978_, v___x_3980_);
v___x_3982_ = lean_array_fget_borrowed(v_as_3976_, v___x_3981_);
lean_dec(v___x_3981_);
lean_inc_ref(v_p_3975_);
lean_inc(v___x_3982_);
v___x_3983_ = lean_apply_1(v_p_3975_, v___x_3982_);
v___x_3984_ = lean_unbox(v___x_3983_);
if (v___x_3984_ == 0)
{
lean_dec_ref(v_p_3975_);
return v_as_3976_;
}
else
{
lean_object* v___x_3985_; 
v___x_3985_ = lean_array_pop(v_as_3976_);
v_as_3976_ = v___x_3985_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile(lean_object* v_00_u03b1_3987_, lean_object* v_p_3988_, lean_object* v_as_3989_){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = l_Array_popWhile___redArg(v_p_3988_, v_as_3989_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(lean_object* v_p_3991_, lean_object* v_as_3992_, lean_object* v_i_3993_, lean_object* v_acc_3994_){
_start:
{
lean_object* v___x_3995_; uint8_t v___x_3996_; 
v___x_3995_ = lean_array_get_size(v_as_3992_);
v___x_3996_ = lean_nat_dec_lt(v_i_3993_, v___x_3995_);
if (v___x_3996_ == 0)
{
lean_dec(v_i_3993_);
lean_dec_ref(v_p_3991_);
return v_acc_3994_;
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3998_; uint8_t v___x_3999_; 
v_a_3997_ = lean_array_fget_borrowed(v_as_3992_, v_i_3993_);
lean_inc_ref(v_p_3991_);
lean_inc(v_a_3997_);
v___x_3998_ = lean_apply_1(v_p_3991_, v_a_3997_);
v___x_3999_ = lean_unbox(v___x_3998_);
if (v___x_3999_ == 0)
{
lean_dec(v_i_3993_);
lean_dec_ref(v_p_3991_);
return v_acc_3994_;
}
else
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4000_ = lean_unsigned_to_nat(1u);
v___x_4001_ = lean_nat_add(v_i_3993_, v___x_4000_);
lean_dec(v_i_3993_);
lean_inc(v_a_3997_);
v___x_4002_ = lean_array_push(v_acc_3994_, v_a_3997_);
v_i_3993_ = v___x_4001_;
v_acc_3994_ = v___x_4002_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg___boxed(lean_object* v_p_4004_, lean_object* v_as_4005_, lean_object* v_i_4006_, lean_object* v_acc_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4004_, v_as_4005_, v_i_4006_, v_acc_4007_);
lean_dec_ref(v_as_4005_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(lean_object* v_00_u03b1_4009_, lean_object* v_p_4010_, lean_object* v_as_4011_, lean_object* v_i_4012_, lean_object* v_acc_4013_){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4010_, v_as_4011_, v_i_4012_, v_acc_4013_);
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___boxed(lean_object* v_00_u03b1_4015_, lean_object* v_p_4016_, lean_object* v_as_4017_, lean_object* v_i_4018_, lean_object* v_acc_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(v_00_u03b1_4015_, v_p_4016_, v_as_4017_, v_i_4018_, v_acc_4019_);
lean_dec_ref(v_as_4017_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg(lean_object* v_p_4021_, lean_object* v_as_4022_){
_start:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4023_ = lean_unsigned_to_nat(0u);
v___x_4024_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4025_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4021_, v_as_4022_, v___x_4023_, v___x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg___boxed(lean_object* v_p_4026_, lean_object* v_as_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_Array_takeWhile___redArg(v_p_4026_, v_as_4027_);
lean_dec_ref(v_as_4027_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile(lean_object* v_00_u03b1_4029_, lean_object* v_p_4030_, lean_object* v_as_4031_){
_start:
{
lean_object* v___x_4032_; 
v___x_4032_ = l_Array_takeWhile___redArg(v_p_4030_, v_as_4031_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___boxed(lean_object* v_00_u03b1_4033_, lean_object* v_p_4034_, lean_object* v_as_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Array_takeWhile(v_00_u03b1_4033_, v_p_4034_, v_as_4035_);
lean_dec_ref(v_as_4035_);
return v_res_4036_;
}
}
static lean_object* _init_l_Array_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx___redArg(lean_object* v_xs_4038_, lean_object* v_i_4039_){
_start:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; uint8_t v___x_4043_; 
v___x_4040_ = lean_unsigned_to_nat(1u);
v___x_4041_ = lean_nat_add(v_i_4039_, v___x_4040_);
v___x_4042_ = lean_array_get_size(v_xs_4038_);
v___x_4043_ = lean_nat_dec_lt(v___x_4041_, v___x_4042_);
if (v___x_4043_ == 0)
{
lean_object* v___x_4044_; 
lean_dec(v___x_4041_);
lean_dec(v_i_4039_);
v___x_4044_ = lean_array_pop(v_xs_4038_);
return v___x_4044_;
}
else
{
lean_object* v_xs_x27_4045_; 
v_xs_x27_4045_ = lean_array_fswap(v_xs_4038_, v___x_4041_, v_i_4039_);
lean_dec(v_i_4039_);
v_xs_4038_ = v_xs_x27_4045_;
v_i_4039_ = v___x_4041_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx(lean_object* v_00_u03b1_4047_, lean_object* v_xs_4048_, lean_object* v_i_4049_, lean_object* v_h_4050_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = l_Array_eraseIdx___redArg(v_xs_4048_, v_i_4049_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds___redArg(lean_object* v_xs_4052_, lean_object* v_i_4053_){
_start:
{
lean_object* v___x_4054_; uint8_t v___x_4055_; 
v___x_4054_ = lean_array_get_size(v_xs_4052_);
v___x_4055_ = lean_nat_dec_lt(v_i_4053_, v___x_4054_);
if (v___x_4055_ == 0)
{
lean_dec(v_i_4053_);
return v_xs_4052_;
}
else
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Array_eraseIdx___redArg(v_xs_4052_, v_i_4053_);
return v___x_4056_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds(lean_object* v_00_u03b1_4057_, lean_object* v_xs_4058_, lean_object* v_i_4059_){
_start:
{
lean_object* v___x_4060_; 
v___x_4060_ = l_Array_eraseIdxIfInBounds___redArg(v_xs_4058_, v_i_4059_);
return v___x_4060_;
}
}
static lean_object* _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4061_; 
v___x_4061_ = l_Array_instInhabited(lean_box(0));
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(lean_object* v_msg_4062_){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = lean_obj_once(&l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0, &l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0_once, _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0);
v___x_4064_ = lean_panic_fn(v___x_4063_, v_msg_4062_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0(lean_object* v_00_u03b1_4065_, lean_object* v_msg_4066_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v_msg_4066_);
return v___x_4067_;
}
}
static lean_object* _init_l_Array_eraseIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4070_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4071_ = lean_unsigned_to_nat(47u);
v___x_4072_ = lean_unsigned_to_nat(1808u);
v___x_4073_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__0));
v___x_4074_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4075_ = l_mkPanicMessageWithDecl(v___x_4074_, v___x_4073_, v___x_4072_, v___x_4071_, v___x_4070_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21___redArg(lean_object* v_xs_4076_, lean_object* v_i_4077_){
_start:
{
lean_object* v___x_4078_; uint8_t v___x_4079_; 
v___x_4078_ = lean_array_get_size(v_xs_4076_);
v___x_4079_ = lean_nat_dec_lt(v_i_4077_, v___x_4078_);
if (v___x_4079_ == 0)
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
lean_dec(v_i_4077_);
lean_dec_ref(v_xs_4076_);
v___x_4080_ = lean_obj_once(&l_Array_eraseIdx_x21___redArg___closed__2, &l_Array_eraseIdx_x21___redArg___closed__2_once, _init_l_Array_eraseIdx_x21___redArg___closed__2);
v___x_4081_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4080_);
return v___x_4081_;
}
else
{
lean_object* v___x_4082_; 
v___x_4082_ = l_Array_eraseIdx___redArg(v_xs_4076_, v_i_4077_);
return v___x_4082_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21(lean_object* v_00_u03b1_4083_, lean_object* v_xs_4084_, lean_object* v_i_4085_){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = l_Array_eraseIdx_x21___redArg(v_xs_4084_, v_i_4085_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Array_erase___redArg(lean_object* v_inst_4087_, lean_object* v_as_4088_, lean_object* v_a_4089_){
_start:
{
lean_object* v___x_4090_; 
v___x_4090_ = l_Array_finIdxOf_x3f___redArg(v_inst_4087_, v_as_4088_, v_a_4089_);
if (lean_obj_tag(v___x_4090_) == 0)
{
return v_as_4088_;
}
else
{
lean_object* v_val_4091_; lean_object* v___x_4092_; 
v_val_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_val_4091_);
lean_dec_ref(v___x_4090_);
v___x_4092_ = l_Array_eraseIdx___redArg(v_as_4088_, v_val_4091_);
return v___x_4092_;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase(lean_object* v_00_u03b1_4093_, lean_object* v_inst_4094_, lean_object* v_as_4095_, lean_object* v_a_4096_){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = l_Array_erase___redArg(v_inst_4094_, v_as_4095_, v_a_4096_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseP___redArg(lean_object* v_as_4098_, lean_object* v_p_4099_){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4100_ = lean_unsigned_to_nat(0u);
v___x_4101_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_4099_, v_as_4098_, v___x_4100_);
if (lean_obj_tag(v___x_4101_) == 0)
{
return v_as_4098_;
}
else
{
lean_object* v_val_4102_; lean_object* v___x_4103_; 
v_val_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_val_4102_);
lean_dec_ref(v___x_4101_);
v___x_4103_ = l_Array_eraseIdx___redArg(v_as_4098_, v_val_4102_);
return v___x_4103_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseP(lean_object* v_00_u03b1_4104_, lean_object* v_as_4105_, lean_object* v_p_4106_){
_start:
{
lean_object* v___x_4107_; 
v___x_4107_ = l_Array_eraseP___redArg(v_as_4105_, v_p_4106_);
return v___x_4107_;
}
}
static lean_object* _init_l_Array_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_4108_; 
v___x_4108_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(lean_object* v_i_4109_, lean_object* v_as_4110_, lean_object* v_j_4111_){
_start:
{
uint8_t v___x_4112_; 
v___x_4112_ = lean_nat_dec_lt(v_i_4109_, v_j_4111_);
if (v___x_4112_ == 0)
{
lean_dec(v_j_4111_);
return v_as_4110_;
}
else
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v_as_4115_; 
v___x_4113_ = lean_unsigned_to_nat(1u);
v___x_4114_ = lean_nat_sub(v_j_4111_, v___x_4113_);
v_as_4115_ = lean_array_fswap(v_as_4110_, v___x_4114_, v_j_4111_);
lean_dec(v_j_4111_);
v_as_4110_ = v_as_4115_;
v_j_4111_ = v___x_4114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg___boxed(lean_object* v_i_4117_, lean_object* v_as_4118_, lean_object* v_j_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4117_, v_as_4118_, v_j_4119_);
lean_dec(v_i_4117_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object* v_00_u03b1_4121_, lean_object* v_i_4122_, lean_object* v_as_4123_, lean_object* v_j_4124_){
_start:
{
lean_object* v___x_4125_; 
v___x_4125_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4122_, v_as_4123_, v_j_4124_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___boxed(lean_object* v_00_u03b1_4126_, lean_object* v_i_4127_, lean_object* v_as_4128_, lean_object* v_j_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(v_00_u03b1_4126_, v_i_4127_, v_as_4128_, v_j_4129_);
lean_dec(v_i_4127_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg(lean_object* v_as_4131_, lean_object* v_i_4132_, lean_object* v_a_4133_){
_start:
{
lean_object* v_j_4134_; lean_object* v_as_4135_; lean_object* v___x_4136_; 
v_j_4134_ = lean_array_get_size(v_as_4131_);
v_as_4135_ = lean_array_push(v_as_4131_, v_a_4133_);
v___x_4136_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4132_, v_as_4135_, v_j_4134_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg___boxed(lean_object* v_as_4137_, lean_object* v_i_4138_, lean_object* v_a_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Array_insertIdx___redArg(v_as_4137_, v_i_4138_, v_a_4139_);
lean_dec(v_i_4138_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx(lean_object* v_00_u03b1_4141_, lean_object* v_as_4142_, lean_object* v_i_4143_, lean_object* v_a_4144_, lean_object* v_x_4145_){
_start:
{
lean_object* v_j_4146_; lean_object* v_as_4147_; lean_object* v___x_4148_; 
v_j_4146_ = lean_array_get_size(v_as_4142_);
v_as_4147_ = lean_array_push(v_as_4142_, v_a_4144_);
v___x_4148_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4143_, v_as_4147_, v_j_4146_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___boxed(lean_object* v_00_u03b1_4149_, lean_object* v_as_4150_, lean_object* v_i_4151_, lean_object* v_a_4152_, lean_object* v_x_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_Array_insertIdx(v_00_u03b1_4149_, v_as_4150_, v_i_4151_, v_a_4152_, v_x_4153_);
lean_dec(v_i_4151_);
return v_res_4154_;
}
}
static lean_object* _init_l_Array_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4156_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4157_ = lean_unsigned_to_nat(7u);
v___x_4158_ = lean_unsigned_to_nat(1890u);
v___x_4159_ = ((lean_object*)(l_Array_insertIdx_x21___redArg___closed__0));
v___x_4160_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4161_ = l_mkPanicMessageWithDecl(v___x_4160_, v___x_4159_, v___x_4158_, v___x_4157_, v___x_4156_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg(lean_object* v_as_4162_, lean_object* v_i_4163_, lean_object* v_a_4164_){
_start:
{
lean_object* v___x_4165_; uint8_t v___x_4166_; 
v___x_4165_ = lean_array_get_size(v_as_4162_);
v___x_4166_ = lean_nat_dec_le(v_i_4163_, v___x_4165_);
if (v___x_4166_ == 0)
{
lean_object* v___x_4167_; lean_object* v___x_4168_; 
lean_dec(v_a_4164_);
lean_dec_ref(v_as_4162_);
v___x_4167_ = lean_obj_once(&l_Array_insertIdx_x21___redArg___closed__1, &l_Array_insertIdx_x21___redArg___closed__1_once, _init_l_Array_insertIdx_x21___redArg___closed__1);
v___x_4168_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4167_);
return v___x_4168_;
}
else
{
lean_object* v_as_4169_; lean_object* v___x_4170_; 
v_as_4169_ = lean_array_push(v_as_4162_, v_a_4164_);
v___x_4170_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4163_, v_as_4169_, v___x_4165_);
return v___x_4170_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg___boxed(lean_object* v_as_4171_, lean_object* v_i_4172_, lean_object* v_a_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Array_insertIdx_x21___redArg(v_as_4171_, v_i_4172_, v_a_4173_);
lean_dec(v_i_4172_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21(lean_object* v_00_u03b1_4175_, lean_object* v_as_4176_, lean_object* v_i_4177_, lean_object* v_a_4178_){
_start:
{
lean_object* v___x_4179_; 
v___x_4179_ = l_Array_insertIdx_x21___redArg(v_as_4176_, v_i_4177_, v_a_4178_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___boxed(lean_object* v_00_u03b1_4180_, lean_object* v_as_4181_, lean_object* v_i_4182_, lean_object* v_a_4183_){
_start:
{
lean_object* v_res_4184_; 
v_res_4184_ = l_Array_insertIdx_x21(v_00_u03b1_4180_, v_as_4181_, v_i_4182_, v_a_4183_);
lean_dec(v_i_4182_);
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg(lean_object* v_as_4185_, lean_object* v_i_4186_, lean_object* v_a_4187_){
_start:
{
lean_object* v___x_4188_; uint8_t v___x_4189_; 
v___x_4188_ = lean_array_get_size(v_as_4185_);
v___x_4189_ = lean_nat_dec_le(v_i_4186_, v___x_4188_);
if (v___x_4189_ == 0)
{
lean_dec(v_a_4187_);
return v_as_4185_;
}
else
{
lean_object* v_as_4190_; lean_object* v___x_4191_; 
v_as_4190_ = lean_array_push(v_as_4185_, v_a_4187_);
v___x_4191_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4186_, v_as_4190_, v___x_4188_);
return v___x_4191_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg___boxed(lean_object* v_as_4192_, lean_object* v_i_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Array_insertIdxIfInBounds___redArg(v_as_4192_, v_i_4193_, v_a_4194_);
lean_dec(v_i_4193_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds(lean_object* v_00_u03b1_4196_, lean_object* v_as_4197_, lean_object* v_i_4198_, lean_object* v_a_4199_){
_start:
{
lean_object* v___x_4200_; 
v___x_4200_ = l_Array_insertIdxIfInBounds___redArg(v_as_4197_, v_i_4198_, v_a_4199_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___boxed(lean_object* v_00_u03b1_4201_, lean_object* v_as_4202_, lean_object* v_i_4203_, lean_object* v_a_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l_Array_insertIdxIfInBounds(v_00_u03b1_4201_, v_as_4202_, v_i_4203_, v_a_4204_);
lean_dec(v_i_4203_);
return v_res_4205_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux___redArg(lean_object* v_inst_4206_, lean_object* v_as_4207_, lean_object* v_bs_4208_, lean_object* v_i_4209_){
_start:
{
lean_object* v___x_4210_; uint8_t v___x_4211_; 
v___x_4210_ = lean_array_get_size(v_as_4207_);
v___x_4211_ = lean_nat_dec_lt(v_i_4209_, v___x_4210_);
if (v___x_4211_ == 0)
{
uint8_t v___x_4212_; 
lean_dec(v_i_4209_);
lean_dec_ref(v_inst_4206_);
v___x_4212_ = 1;
return v___x_4212_;
}
else
{
lean_object* v_a_4213_; lean_object* v_b_4214_; lean_object* v___x_4215_; uint8_t v___x_4216_; 
v_a_4213_ = lean_array_fget_borrowed(v_as_4207_, v_i_4209_);
v_b_4214_ = lean_array_fget_borrowed(v_bs_4208_, v_i_4209_);
lean_inc_ref(v_inst_4206_);
lean_inc(v_b_4214_);
lean_inc(v_a_4213_);
v___x_4215_ = lean_apply_2(v_inst_4206_, v_a_4213_, v_b_4214_);
v___x_4216_ = lean_unbox(v___x_4215_);
if (v___x_4216_ == 0)
{
uint8_t v___x_4217_; 
lean_dec(v_i_4209_);
lean_dec_ref(v_inst_4206_);
v___x_4217_ = lean_unbox(v___x_4215_);
return v___x_4217_;
}
else
{
lean_object* v___x_4218_; lean_object* v___x_4219_; 
v___x_4218_ = lean_unsigned_to_nat(1u);
v___x_4219_ = lean_nat_add(v_i_4209_, v___x_4218_);
lean_dec(v_i_4209_);
v_i_4209_ = v___x_4219_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___redArg___boxed(lean_object* v_inst_4221_, lean_object* v_as_4222_, lean_object* v_bs_4223_, lean_object* v_i_4224_){
_start:
{
uint8_t v_res_4225_; lean_object* v_r_4226_; 
v_res_4225_ = l_Array_isPrefixOfAux___redArg(v_inst_4221_, v_as_4222_, v_bs_4223_, v_i_4224_);
lean_dec_ref(v_bs_4223_);
lean_dec_ref(v_as_4222_);
v_r_4226_ = lean_box(v_res_4225_);
return v_r_4226_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux(lean_object* v_00_u03b1_4227_, lean_object* v_inst_4228_, lean_object* v_as_4229_, lean_object* v_bs_4230_, lean_object* v_hle_4231_, lean_object* v_i_4232_){
_start:
{
uint8_t v___x_4233_; 
v___x_4233_ = l_Array_isPrefixOfAux___redArg(v_inst_4228_, v_as_4229_, v_bs_4230_, v_i_4232_);
return v___x_4233_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___boxed(lean_object* v_00_u03b1_4234_, lean_object* v_inst_4235_, lean_object* v_as_4236_, lean_object* v_bs_4237_, lean_object* v_hle_4238_, lean_object* v_i_4239_){
_start:
{
uint8_t v_res_4240_; lean_object* v_r_4241_; 
v_res_4240_ = l_Array_isPrefixOfAux(v_00_u03b1_4234_, v_inst_4235_, v_as_4236_, v_bs_4237_, v_hle_4238_, v_i_4239_);
lean_dec_ref(v_bs_4237_);
lean_dec_ref(v_as_4236_);
v_r_4241_ = lean_box(v_res_4240_);
return v_r_4241_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf___redArg(lean_object* v_inst_4242_, lean_object* v_as_4243_, lean_object* v_bs_4244_){
_start:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; uint8_t v___x_4247_; 
v___x_4245_ = lean_array_get_size(v_as_4243_);
v___x_4246_ = lean_array_get_size(v_bs_4244_);
v___x_4247_ = lean_nat_dec_le(v___x_4245_, v___x_4246_);
if (v___x_4247_ == 0)
{
lean_dec_ref(v_inst_4242_);
return v___x_4247_;
}
else
{
lean_object* v___x_4248_; uint8_t v___x_4249_; 
v___x_4248_ = lean_unsigned_to_nat(0u);
v___x_4249_ = l_Array_isPrefixOfAux___redArg(v_inst_4242_, v_as_4243_, v_bs_4244_, v___x_4248_);
return v___x_4249_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___redArg___boxed(lean_object* v_inst_4250_, lean_object* v_as_4251_, lean_object* v_bs_4252_){
_start:
{
uint8_t v_res_4253_; lean_object* v_r_4254_; 
v_res_4253_ = l_Array_isPrefixOf___redArg(v_inst_4250_, v_as_4251_, v_bs_4252_);
lean_dec_ref(v_bs_4252_);
lean_dec_ref(v_as_4251_);
v_r_4254_ = lean_box(v_res_4253_);
return v_r_4254_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf(lean_object* v_00_u03b1_4255_, lean_object* v_inst_4256_, lean_object* v_as_4257_, lean_object* v_bs_4258_){
_start:
{
uint8_t v___x_4259_; 
v___x_4259_ = l_Array_isPrefixOf___redArg(v_inst_4256_, v_as_4257_, v_bs_4258_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___boxed(lean_object* v_00_u03b1_4260_, lean_object* v_inst_4261_, lean_object* v_as_4262_, lean_object* v_bs_4263_){
_start:
{
uint8_t v_res_4264_; lean_object* v_r_4265_; 
v_res_4264_ = l_Array_isPrefixOf(v_00_u03b1_4260_, v_inst_4261_, v_as_4262_, v_bs_4263_);
lean_dec_ref(v_bs_4263_);
lean_dec_ref(v_as_4262_);
v_r_4265_ = lean_box(v_res_4264_);
return v_r_4265_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0___boxed(lean_object* v_i_4266_, lean_object* v_cs_4267_, lean_object* v_inst_4268_, lean_object* v_as_4269_, lean_object* v_bs_4270_, lean_object* v_f_4271_, lean_object* v_____do__lift_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l_Array_zipWithMAux___redArg___lam__0(v_i_4266_, v_cs_4267_, v_inst_4268_, v_as_4269_, v_bs_4270_, v_f_4271_, v_____do__lift_4272_);
lean_dec(v_i_4266_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg(lean_object* v_inst_4274_, lean_object* v_as_4275_, lean_object* v_bs_4276_, lean_object* v_f_4277_, lean_object* v_i_4278_, lean_object* v_cs_4279_){
_start:
{
lean_object* v___x_4280_; uint8_t v___x_4281_; 
v___x_4280_ = lean_array_get_size(v_as_4275_);
v___x_4281_ = lean_nat_dec_lt(v_i_4278_, v___x_4280_);
if (v___x_4281_ == 0)
{
lean_object* v_toApplicative_4282_; lean_object* v_toPure_4283_; lean_object* v___x_4284_; 
lean_dec(v_i_4278_);
lean_dec(v_f_4277_);
lean_dec_ref(v_bs_4276_);
lean_dec_ref(v_as_4275_);
v_toApplicative_4282_ = lean_ctor_get(v_inst_4274_, 0);
lean_inc_ref(v_toApplicative_4282_);
lean_dec_ref(v_inst_4274_);
v_toPure_4283_ = lean_ctor_get(v_toApplicative_4282_, 1);
lean_inc(v_toPure_4283_);
lean_dec_ref(v_toApplicative_4282_);
v___x_4284_ = lean_apply_2(v_toPure_4283_, lean_box(0), v_cs_4279_);
return v___x_4284_;
}
else
{
lean_object* v___x_4285_; uint8_t v___x_4286_; 
v___x_4285_ = lean_array_get_size(v_bs_4276_);
v___x_4286_ = lean_nat_dec_lt(v_i_4278_, v___x_4285_);
if (v___x_4286_ == 0)
{
lean_object* v_toApplicative_4287_; lean_object* v_toPure_4288_; lean_object* v___x_4289_; 
lean_dec(v_i_4278_);
lean_dec(v_f_4277_);
lean_dec_ref(v_bs_4276_);
lean_dec_ref(v_as_4275_);
v_toApplicative_4287_ = lean_ctor_get(v_inst_4274_, 0);
lean_inc_ref(v_toApplicative_4287_);
lean_dec_ref(v_inst_4274_);
v_toPure_4288_ = lean_ctor_get(v_toApplicative_4287_, 1);
lean_inc(v_toPure_4288_);
lean_dec_ref(v_toApplicative_4287_);
v___x_4289_ = lean_apply_2(v_toPure_4288_, lean_box(0), v_cs_4279_);
return v___x_4289_;
}
else
{
lean_object* v_toBind_4290_; lean_object* v___f_4291_; lean_object* v_a_4292_; lean_object* v_b_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v_toBind_4290_ = lean_ctor_get(v_inst_4274_, 1);
lean_inc(v_toBind_4290_);
lean_inc(v_f_4277_);
lean_inc_ref(v_bs_4276_);
lean_inc_ref(v_as_4275_);
lean_inc(v_i_4278_);
v___f_4291_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4291_, 0, v_i_4278_);
lean_closure_set(v___f_4291_, 1, v_cs_4279_);
lean_closure_set(v___f_4291_, 2, v_inst_4274_);
lean_closure_set(v___f_4291_, 3, v_as_4275_);
lean_closure_set(v___f_4291_, 4, v_bs_4276_);
lean_closure_set(v___f_4291_, 5, v_f_4277_);
v_a_4292_ = lean_array_fget(v_as_4275_, v_i_4278_);
lean_dec_ref(v_as_4275_);
v_b_4293_ = lean_array_fget(v_bs_4276_, v_i_4278_);
lean_dec(v_i_4278_);
lean_dec_ref(v_bs_4276_);
v___x_4294_ = lean_apply_2(v_f_4277_, v_a_4292_, v_b_4293_);
v___x_4295_ = lean_apply_4(v_toBind_4290_, lean_box(0), lean_box(0), v___x_4294_, v___f_4291_);
return v___x_4295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0(lean_object* v_i_4296_, lean_object* v_cs_4297_, lean_object* v_inst_4298_, lean_object* v_as_4299_, lean_object* v_bs_4300_, lean_object* v_f_4301_, lean_object* v_____do__lift_4302_){
_start:
{
lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4303_ = lean_unsigned_to_nat(1u);
v___x_4304_ = lean_nat_add(v_i_4296_, v___x_4303_);
v___x_4305_ = lean_array_push(v_cs_4297_, v_____do__lift_4302_);
v___x_4306_ = l_Array_zipWithMAux___redArg(v_inst_4298_, v_as_4299_, v_bs_4300_, v_f_4301_, v___x_4304_, v___x_4305_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux(lean_object* v_00_u03b1_4307_, lean_object* v_00_u03b2_4308_, lean_object* v_00_u03b3_4309_, lean_object* v_m_4310_, lean_object* v_inst_4311_, lean_object* v_as_4312_, lean_object* v_bs_4313_, lean_object* v_f_4314_, lean_object* v_i_4315_, lean_object* v_cs_4316_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Array_zipWithMAux___redArg(v_inst_4311_, v_as_4312_, v_bs_4313_, v_f_4314_, v_i_4315_, v_cs_4316_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith___redArg(lean_object* v_f_4318_, lean_object* v_as_4319_, lean_object* v_bs_4320_){
_start:
{
lean_object* v___f_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___f_4321_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4321_, 0, v_f_4318_);
v___x_4322_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4323_ = lean_unsigned_to_nat(0u);
v___x_4324_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4325_ = l_Array_zipWithMAux___redArg(v___x_4322_, v_as_4319_, v_bs_4320_, v___f_4321_, v___x_4323_, v___x_4324_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith(lean_object* v_00_u03b1_4326_, lean_object* v_00_u03b2_4327_, lean_object* v_00_u03b3_4328_, lean_object* v_f_4329_, lean_object* v_as_4330_, lean_object* v_bs_4331_){
_start:
{
lean_object* v___f_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___f_4332_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4332_, 0, v_f_4329_);
v___x_4333_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4334_ = lean_unsigned_to_nat(0u);
v___x_4335_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4336_ = l_Array_zipWithMAux___redArg(v___x_4333_, v_as_4330_, v_bs_4331_, v___f_4332_, v___x_4334_, v___x_4335_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(lean_object* v_as_4337_, lean_object* v_bs_4338_, lean_object* v_i_4339_, lean_object* v_cs_4340_){
_start:
{
lean_object* v___x_4341_; uint8_t v___x_4342_; 
v___x_4341_ = lean_array_get_size(v_as_4337_);
v___x_4342_ = lean_nat_dec_lt(v_i_4339_, v___x_4341_);
if (v___x_4342_ == 0)
{
lean_dec(v_i_4339_);
return v_cs_4340_;
}
else
{
lean_object* v___x_4343_; uint8_t v___x_4344_; 
v___x_4343_ = lean_array_get_size(v_bs_4338_);
v___x_4344_ = lean_nat_dec_lt(v_i_4339_, v___x_4343_);
if (v___x_4344_ == 0)
{
lean_dec(v_i_4339_);
return v_cs_4340_;
}
else
{
lean_object* v_a_4345_; lean_object* v_b_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v_a_4345_ = lean_array_fget_borrowed(v_as_4337_, v_i_4339_);
v_b_4346_ = lean_array_fget_borrowed(v_bs_4338_, v_i_4339_);
lean_inc(v_b_4346_);
lean_inc(v_a_4345_);
v___x_4347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4347_, 0, v_a_4345_);
lean_ctor_set(v___x_4347_, 1, v_b_4346_);
v___x_4348_ = lean_unsigned_to_nat(1u);
v___x_4349_ = lean_nat_add(v_i_4339_, v___x_4348_);
lean_dec(v_i_4339_);
v___x_4350_ = lean_array_push(v_cs_4340_, v___x_4347_);
v_i_4339_ = v___x_4349_;
v_cs_4340_ = v___x_4350_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg___boxed(lean_object* v_as_4352_, lean_object* v_bs_4353_, lean_object* v_i_4354_, lean_object* v_cs_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4352_, v_bs_4353_, v_i_4354_, v_cs_4355_);
lean_dec_ref(v_bs_4353_);
lean_dec_ref(v_as_4352_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg(lean_object* v_as_4359_, lean_object* v_bs_4360_){
_start:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4361_ = lean_unsigned_to_nat(0u);
v___x_4362_ = ((lean_object*)(l_Array_zip___redArg___closed__0));
v___x_4363_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4359_, v_bs_4360_, v___x_4361_, v___x_4362_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg___boxed(lean_object* v_as_4364_, lean_object* v_bs_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l_Array_zip___redArg(v_as_4364_, v_bs_4365_);
lean_dec_ref(v_bs_4365_);
lean_dec_ref(v_as_4364_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Array_zip(lean_object* v_00_u03b1_4367_, lean_object* v_00_u03b2_4368_, lean_object* v_as_4369_, lean_object* v_bs_4370_){
_start:
{
lean_object* v___x_4371_; 
v___x_4371_ = l_Array_zip___redArg(v_as_4369_, v_bs_4370_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___boxed(lean_object* v_00_u03b1_4372_, lean_object* v_00_u03b2_4373_, lean_object* v_as_4374_, lean_object* v_bs_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l_Array_zip(v_00_u03b1_4372_, v_00_u03b2_4373_, v_as_4374_, v_bs_4375_);
lean_dec_ref(v_bs_4375_);
lean_dec_ref(v_as_4374_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0(lean_object* v_00_u03b1_4377_, lean_object* v_00_u03b2_4378_, lean_object* v_as_4379_, lean_object* v_bs_4380_, lean_object* v_i_4381_, lean_object* v_cs_4382_){
_start:
{
lean_object* v___x_4383_; 
v___x_4383_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4379_, v_bs_4380_, v_i_4381_, v_cs_4382_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___boxed(lean_object* v_00_u03b1_4384_, lean_object* v_00_u03b2_4385_, lean_object* v_as_4386_, lean_object* v_bs_4387_, lean_object* v_i_4388_, lean_object* v_cs_4389_){
_start:
{
lean_object* v_res_4390_; 
v_res_4390_ = l_Array_zipWithMAux___at___00Array_zip_spec__0(v_00_u03b1_4384_, v_00_u03b2_4385_, v_as_4386_, v_bs_4387_, v_i_4388_, v_cs_4389_);
lean_dec_ref(v_bs_4387_);
lean_dec_ref(v_as_4386_);
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(lean_object* v_f_4391_, lean_object* v_as_4392_, lean_object* v_bs_4393_, lean_object* v_i_4394_, lean_object* v_cs_4395_){
_start:
{
lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4405_; lean_object* v___y_4412_; lean_object* v___x_4419_; lean_object* v___x_4420_; uint8_t v___x_4421_; 
v___x_4419_ = lean_array_get_size(v_as_4392_);
v___x_4420_ = lean_array_get_size(v_bs_4393_);
v___x_4421_ = lean_nat_dec_le(v___x_4419_, v___x_4420_);
if (v___x_4421_ == 0)
{
v___y_4412_ = v___x_4419_;
goto v___jp_4411_;
}
else
{
v___y_4412_ = v___x_4420_;
goto v___jp_4411_;
}
v___jp_4396_:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4399_ = lean_unsigned_to_nat(1u);
v___x_4400_ = lean_nat_add(v_i_4394_, v___x_4399_);
lean_dec(v_i_4394_);
lean_inc(v_f_4391_);
v___x_4401_ = lean_apply_2(v_f_4391_, v___y_4397_, v___y_4398_);
v___x_4402_ = lean_array_push(v_cs_4395_, v___x_4401_);
v_i_4394_ = v___x_4400_;
v_cs_4395_ = v___x_4402_;
goto _start;
}
v___jp_4404_:
{
lean_object* v___x_4406_; uint8_t v___x_4407_; 
v___x_4406_ = lean_array_get_size(v_bs_4393_);
v___x_4407_ = lean_nat_dec_lt(v_i_4394_, v___x_4406_);
if (v___x_4407_ == 0)
{
lean_object* v___x_4408_; 
v___x_4408_ = lean_box(0);
v___y_4397_ = v___y_4405_;
v___y_4398_ = v___x_4408_;
goto v___jp_4396_;
}
else
{
lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4409_ = lean_array_fget_borrowed(v_bs_4393_, v_i_4394_);
lean_inc(v___x_4409_);
v___x_4410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4409_);
v___y_4397_ = v___y_4405_;
v___y_4398_ = v___x_4410_;
goto v___jp_4396_;
}
}
v___jp_4411_:
{
uint8_t v___x_4413_; 
v___x_4413_ = lean_nat_dec_lt(v_i_4394_, v___y_4412_);
lean_dec(v___y_4412_);
if (v___x_4413_ == 0)
{
lean_dec(v_i_4394_);
lean_dec(v_f_4391_);
return v_cs_4395_;
}
else
{
lean_object* v___x_4414_; uint8_t v___x_4415_; 
v___x_4414_ = lean_array_get_size(v_as_4392_);
v___x_4415_ = lean_nat_dec_lt(v_i_4394_, v___x_4414_);
if (v___x_4415_ == 0)
{
lean_object* v___x_4416_; 
v___x_4416_ = lean_box(0);
v___y_4405_ = v___x_4416_;
goto v___jp_4404_;
}
else
{
lean_object* v___x_4417_; lean_object* v___x_4418_; 
v___x_4417_ = lean_array_fget_borrowed(v_as_4392_, v_i_4394_);
lean_inc(v___x_4417_);
v___x_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4417_);
v___y_4405_ = v___x_4418_;
goto v___jp_4404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg___boxed(lean_object* v_f_4422_, lean_object* v_as_4423_, lean_object* v_bs_4424_, lean_object* v_i_4425_, lean_object* v_cs_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4422_, v_as_4423_, v_bs_4424_, v_i_4425_, v_cs_4426_);
lean_dec_ref(v_bs_4424_);
lean_dec_ref(v_as_4423_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(lean_object* v_00_u03b1_4428_, lean_object* v_00_u03b2_4429_, lean_object* v_00_u03b3_4430_, lean_object* v_f_4431_, lean_object* v_as_4432_, lean_object* v_bs_4433_, lean_object* v_i_4434_, lean_object* v_cs_4435_){
_start:
{
lean_object* v___x_4436_; 
v___x_4436_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4431_, v_as_4432_, v_bs_4433_, v_i_4434_, v_cs_4435_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___boxed(lean_object* v_00_u03b1_4437_, lean_object* v_00_u03b2_4438_, lean_object* v_00_u03b3_4439_, lean_object* v_f_4440_, lean_object* v_as_4441_, lean_object* v_bs_4442_, lean_object* v_i_4443_, lean_object* v_cs_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(v_00_u03b1_4437_, v_00_u03b2_4438_, v_00_u03b3_4439_, v_f_4440_, v_as_4441_, v_bs_4442_, v_i_4443_, v_cs_4444_);
lean_dec_ref(v_bs_4442_);
lean_dec_ref(v_as_4441_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg(lean_object* v_f_4446_, lean_object* v_as_4447_, lean_object* v_bs_4448_){
_start:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4449_ = lean_unsigned_to_nat(0u);
v___x_4450_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4451_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4446_, v_as_4447_, v_bs_4448_, v___x_4449_, v___x_4450_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg___boxed(lean_object* v_f_4452_, lean_object* v_as_4453_, lean_object* v_bs_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Array_zipWithAll___redArg(v_f_4452_, v_as_4453_, v_bs_4454_);
lean_dec_ref(v_bs_4454_);
lean_dec_ref(v_as_4453_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll(lean_object* v_00_u03b1_4456_, lean_object* v_00_u03b2_4457_, lean_object* v_00_u03b3_4458_, lean_object* v_f_4459_, lean_object* v_as_4460_, lean_object* v_bs_4461_){
_start:
{
lean_object* v___x_4462_; 
v___x_4462_ = l_Array_zipWithAll___redArg(v_f_4459_, v_as_4460_, v_bs_4461_);
return v___x_4462_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___boxed(lean_object* v_00_u03b1_4463_, lean_object* v_00_u03b2_4464_, lean_object* v_00_u03b3_4465_, lean_object* v_f_4466_, lean_object* v_as_4467_, lean_object* v_bs_4468_){
_start:
{
lean_object* v_res_4469_; 
v_res_4469_ = l_Array_zipWithAll(v_00_u03b1_4463_, v_00_u03b2_4464_, v_00_u03b3_4465_, v_f_4466_, v_as_4467_, v_bs_4468_);
lean_dec_ref(v_bs_4468_);
lean_dec_ref(v_as_4467_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM___redArg(lean_object* v_inst_4470_, lean_object* v_f_4471_, lean_object* v_as_4472_, lean_object* v_bs_4473_){
_start:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4474_ = lean_unsigned_to_nat(0u);
v___x_4475_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4476_ = l_Array_zipWithMAux___redArg(v_inst_4470_, v_as_4472_, v_bs_4473_, v_f_4471_, v___x_4474_, v___x_4475_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM(lean_object* v_00_u03b1_4477_, lean_object* v_00_u03b2_4478_, lean_object* v_00_u03b3_4479_, lean_object* v_m_4480_, lean_object* v_inst_4481_, lean_object* v_f_4482_, lean_object* v_as_4483_, lean_object* v_bs_4484_){
_start:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4485_ = lean_unsigned_to_nat(0u);
v___x_4486_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4487_ = l_Array_zipWithMAux___redArg(v_inst_4481_, v_as_4483_, v_bs_4484_, v_f_4482_, v___x_4485_, v___x_4486_);
return v___x_4487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(lean_object* v_as_4488_, size_t v_i_4489_, size_t v_stop_4490_, lean_object* v_b_4491_){
_start:
{
uint8_t v___x_4492_; 
v___x_4492_ = lean_usize_dec_eq(v_i_4489_, v_stop_4490_);
if (v___x_4492_ == 0)
{
lean_object* v_fst_4493_; lean_object* v_snd_4494_; lean_object* v___x_4495_; lean_object* v_fst_4496_; lean_object* v_snd_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4509_; 
v_fst_4493_ = lean_ctor_get(v_b_4491_, 0);
lean_inc(v_fst_4493_);
v_snd_4494_ = lean_ctor_get(v_b_4491_, 1);
lean_inc(v_snd_4494_);
lean_dec_ref(v_b_4491_);
v___x_4495_ = lean_array_uget(v_as_4488_, v_i_4489_);
v_fst_4496_ = lean_ctor_get(v___x_4495_, 0);
v_snd_4497_ = lean_ctor_get(v___x_4495_, 1);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4499_ = v___x_4495_;
v_isShared_4500_ = v_isSharedCheck_4509_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_snd_4497_);
lean_inc(v_fst_4496_);
lean_dec(v___x_4495_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4509_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4504_; 
v___x_4501_ = lean_array_push(v_fst_4493_, v_fst_4496_);
v___x_4502_ = lean_array_push(v_snd_4494_, v_snd_4497_);
if (v_isShared_4500_ == 0)
{
lean_ctor_set(v___x_4499_, 1, v___x_4502_);
lean_ctor_set(v___x_4499_, 0, v___x_4501_);
v___x_4504_ = v___x_4499_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v___x_4501_);
lean_ctor_set(v_reuseFailAlloc_4508_, 1, v___x_4502_);
v___x_4504_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
size_t v___x_4505_; size_t v___x_4506_; 
v___x_4505_ = ((size_t)1ULL);
v___x_4506_ = lean_usize_add(v_i_4489_, v___x_4505_);
v_i_4489_ = v___x_4506_;
v_b_4491_ = v___x_4504_;
goto _start;
}
}
}
else
{
return v_b_4491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg___boxed(lean_object* v_as_4510_, lean_object* v_i_4511_, lean_object* v_stop_4512_, lean_object* v_b_4513_){
_start:
{
size_t v_i_boxed_4514_; size_t v_stop_boxed_4515_; lean_object* v_res_4516_; 
v_i_boxed_4514_ = lean_unbox_usize(v_i_4511_);
lean_dec(v_i_4511_);
v_stop_boxed_4515_ = lean_unbox_usize(v_stop_4512_);
lean_dec(v_stop_4512_);
v_res_4516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4510_, v_i_boxed_4514_, v_stop_boxed_4515_, v_b_4513_);
lean_dec_ref(v_as_4510_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg(lean_object* v_as_4517_){
_start:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4518_ = lean_unsigned_to_nat(0u);
v___x_4519_ = lean_obj_once(&l_Array_partition___redArg___closed__0, &l_Array_partition___redArg___closed__0_once, _init_l_Array_partition___redArg___closed__0);
v___x_4520_ = lean_array_get_size(v_as_4517_);
v___x_4521_ = lean_nat_dec_lt(v___x_4518_, v___x_4520_);
if (v___x_4521_ == 0)
{
return v___x_4519_;
}
else
{
uint8_t v___x_4522_; 
v___x_4522_ = lean_nat_dec_le(v___x_4520_, v___x_4520_);
if (v___x_4522_ == 0)
{
if (v___x_4521_ == 0)
{
return v___x_4519_;
}
else
{
size_t v___x_4523_; size_t v___x_4524_; lean_object* v___x_4525_; 
v___x_4523_ = ((size_t)0ULL);
v___x_4524_ = lean_usize_of_nat(v___x_4520_);
v___x_4525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4517_, v___x_4523_, v___x_4524_, v___x_4519_);
return v___x_4525_;
}
}
else
{
size_t v___x_4526_; size_t v___x_4527_; lean_object* v___x_4528_; 
v___x_4526_ = ((size_t)0ULL);
v___x_4527_ = lean_usize_of_nat(v___x_4520_);
v___x_4528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4517_, v___x_4526_, v___x_4527_, v___x_4519_);
return v___x_4528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg___boxed(lean_object* v_as_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l_Array_unzip___redArg(v_as_4529_);
lean_dec_ref(v_as_4529_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip(lean_object* v_00_u03b1_4531_, lean_object* v_00_u03b2_4532_, lean_object* v_as_4533_){
_start:
{
lean_object* v___x_4534_; 
v___x_4534_ = l_Array_unzip___redArg(v_as_4533_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___boxed(lean_object* v_00_u03b1_4535_, lean_object* v_00_u03b2_4536_, lean_object* v_as_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l_Array_unzip(v_00_u03b1_4535_, v_00_u03b2_4536_, v_as_4537_);
lean_dec_ref(v_as_4537_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(lean_object* v_00_u03b1_4539_, lean_object* v_00_u03b2_4540_, lean_object* v_as_4541_, size_t v_i_4542_, size_t v_stop_4543_, lean_object* v_b_4544_){
_start:
{
lean_object* v___x_4545_; 
v___x_4545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4541_, v_i_4542_, v_stop_4543_, v_b_4544_);
return v___x_4545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___boxed(lean_object* v_00_u03b1_4546_, lean_object* v_00_u03b2_4547_, lean_object* v_as_4548_, lean_object* v_i_4549_, lean_object* v_stop_4550_, lean_object* v_b_4551_){
_start:
{
size_t v_i_boxed_4552_; size_t v_stop_boxed_4553_; lean_object* v_res_4554_; 
v_i_boxed_4552_ = lean_unbox_usize(v_i_4549_);
lean_dec(v_i_4549_);
v_stop_boxed_4553_ = lean_unbox_usize(v_stop_4550_);
lean_dec(v_stop_4550_);
v_res_4554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(v_00_u03b1_4546_, v_00_u03b2_4547_, v_as_4548_, v_i_boxed_4552_, v_stop_boxed_4553_, v_b_4551_);
lean_dec_ref(v_as_4548_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l_Array_replace___redArg(lean_object* v_inst_4555_, lean_object* v_xs_4556_, lean_object* v_a_4557_, lean_object* v_b_4558_){
_start:
{
lean_object* v___x_4559_; 
v___x_4559_ = l_Array_finIdxOf_x3f___redArg(v_inst_4555_, v_xs_4556_, v_a_4557_);
if (lean_obj_tag(v___x_4559_) == 0)
{
lean_dec(v_b_4558_);
return v_xs_4556_;
}
else
{
lean_object* v_val_4560_; lean_object* v___x_4561_; 
v_val_4560_ = lean_ctor_get(v___x_4559_, 0);
lean_inc(v_val_4560_);
lean_dec_ref(v___x_4559_);
v___x_4561_ = lean_array_fset(v_xs_4556_, v_val_4560_, v_b_4558_);
lean_dec(v_val_4560_);
return v___x_4561_;
}
}
}
LEAN_EXPORT lean_object* l_Array_replace(lean_object* v_00_u03b1_4562_, lean_object* v_inst_4563_, lean_object* v_xs_4564_, lean_object* v_a_4565_, lean_object* v_b_4566_){
_start:
{
lean_object* v___x_4567_; 
v___x_4567_ = l_Array_replace___redArg(v_inst_4563_, v_xs_4564_, v_a_4565_, v_b_4566_);
return v___x_4567_;
}
}
LEAN_EXPORT lean_object* l_Array_instLT(lean_object* v_00_u03b1_4568_, lean_object* v_inst_4569_){
_start:
{
lean_object* v___x_4570_; 
v___x_4570_ = lean_box(0);
return v___x_4570_;
}
}
LEAN_EXPORT lean_object* l_Array_instLE(lean_object* v_00_u03b1_4571_, lean_object* v_inst_4572_){
_start:
{
lean_object* v___x_4573_; 
v___x_4573_ = lean_box(0);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg(lean_object* v_n_4574_, lean_object* v_a_4575_, lean_object* v_xs_4576_){
_start:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4577_ = lean_array_get_size(v_xs_4576_);
v___x_4578_ = lean_nat_sub(v_n_4574_, v___x_4577_);
v___x_4579_ = lean_mk_array(v___x_4578_, v_a_4575_);
v___x_4580_ = l_Array_append___redArg(v___x_4579_, v_xs_4576_);
return v___x_4580_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg___boxed(lean_object* v_n_4581_, lean_object* v_a_4582_, lean_object* v_xs_4583_){
_start:
{
lean_object* v_res_4584_; 
v_res_4584_ = l_Array_leftpad___redArg(v_n_4581_, v_a_4582_, v_xs_4583_);
lean_dec_ref(v_xs_4583_);
lean_dec(v_n_4581_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad(lean_object* v_00_u03b1_4585_, lean_object* v_n_4586_, lean_object* v_a_4587_, lean_object* v_xs_4588_){
_start:
{
lean_object* v___x_4589_; 
v___x_4589_ = l_Array_leftpad___redArg(v_n_4586_, v_a_4587_, v_xs_4588_);
return v___x_4589_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___boxed(lean_object* v_00_u03b1_4590_, lean_object* v_n_4591_, lean_object* v_a_4592_, lean_object* v_xs_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_Array_leftpad(v_00_u03b1_4590_, v_n_4591_, v_a_4592_, v_xs_4593_);
lean_dec_ref(v_xs_4593_);
lean_dec(v_n_4591_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg(lean_object* v_n_4595_, lean_object* v_a_4596_, lean_object* v_xs_4597_){
_start:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4598_ = lean_array_get_size(v_xs_4597_);
v___x_4599_ = lean_nat_sub(v_n_4595_, v___x_4598_);
v___x_4600_ = lean_mk_array(v___x_4599_, v_a_4596_);
v___x_4601_ = l_Array_append___redArg(v_xs_4597_, v___x_4600_);
lean_dec_ref(v___x_4600_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg___boxed(lean_object* v_n_4602_, lean_object* v_a_4603_, lean_object* v_xs_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_Array_rightpad___redArg(v_n_4602_, v_a_4603_, v_xs_4604_);
lean_dec(v_n_4602_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad(lean_object* v_00_u03b1_4606_, lean_object* v_n_4607_, lean_object* v_a_4608_, lean_object* v_xs_4609_){
_start:
{
lean_object* v___x_4610_; 
v___x_4610_ = l_Array_rightpad___redArg(v_n_4607_, v_a_4608_, v_xs_4609_);
return v___x_4610_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___boxed(lean_object* v_00_u03b1_4611_, lean_object* v_n_4612_, lean_object* v_a_4613_, lean_object* v_xs_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l_Array_rightpad(v_00_u03b1_4611_, v_n_4612_, v_a_4613_, v_xs_4614_);
lean_dec(v_n_4612_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0(lean_object* v_x_4616_){
_start:
{
lean_inc(v_x_4616_);
return v_x_4616_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0___boxed(lean_object* v_x_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l_Array_reduceOption___redArg___lam__0(v_x_4617_);
lean_dec(v_x_4617_);
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg(lean_object* v_as_4620_){
_start:
{
lean_object* v___f_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___f_4621_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4622_ = lean_unsigned_to_nat(0u);
v___x_4623_ = lean_array_get_size(v_as_4620_);
v___x_4624_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4625_ = l_Array_filterMapM___redArg(v___x_4624_, v___f_4621_, v_as_4620_, v___x_4622_, v___x_4623_);
return v___x_4625_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption(lean_object* v_00_u03b1_4626_, lean_object* v_as_4627_){
_start:
{
lean_object* v___f_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___f_4628_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4629_ = lean_unsigned_to_nat(0u);
v___x_4630_ = lean_array_get_size(v_as_4627_);
v___x_4631_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4632_ = l_Array_filterMapM___redArg(v___x_4631_, v___f_4628_, v_as_4627_, v___x_4629_, v___x_4630_);
return v___x_4632_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg___lam__0(lean_object* v_inst_4633_, lean_object* v_x1_4634_, lean_object* v_x2_4635_){
_start:
{
lean_object* v_fst_4636_; lean_object* v_snd_4637_; lean_object* v___x_4638_; uint8_t v___x_4639_; 
v_fst_4636_ = lean_ctor_get(v_x1_4634_, 0);
v_snd_4637_ = lean_ctor_get(v_x1_4634_, 1);
lean_inc(v_fst_4636_);
lean_inc(v_x2_4635_);
v___x_4638_ = lean_apply_2(v_inst_4633_, v_x2_4635_, v_fst_4636_);
v___x_4639_ = lean_unbox(v___x_4638_);
if (v___x_4639_ == 0)
{
lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4647_; 
lean_inc(v_snd_4637_);
lean_inc(v_fst_4636_);
v_isSharedCheck_4647_ = !lean_is_exclusive(v_x1_4634_);
if (v_isSharedCheck_4647_ == 0)
{
lean_object* v_unused_4648_; lean_object* v_unused_4649_; 
v_unused_4648_ = lean_ctor_get(v_x1_4634_, 1);
lean_dec(v_unused_4648_);
v_unused_4649_ = lean_ctor_get(v_x1_4634_, 0);
lean_dec(v_unused_4649_);
v___x_4641_ = v_x1_4634_;
v_isShared_4642_ = v_isSharedCheck_4647_;
goto v_resetjp_4640_;
}
else
{
lean_dec(v_x1_4634_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4647_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4643_; lean_object* v___x_4645_; 
v___x_4643_ = lean_array_push(v_snd_4637_, v_fst_4636_);
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 1, v___x_4643_);
lean_ctor_set(v___x_4641_, 0, v_x2_4635_);
v___x_4645_ = v___x_4641_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_x2_4635_);
lean_ctor_set(v_reuseFailAlloc_4646_, 1, v___x_4643_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
}
}
}
else
{
lean_dec(v_x2_4635_);
return v_x1_4634_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg(lean_object* v_inst_4650_, lean_object* v_as_4651_){
_start:
{
lean_object* v___y_4653_; lean_object* v___x_4657_; lean_object* v___x_4658_; uint8_t v___x_4659_; 
v___x_4657_ = lean_unsigned_to_nat(0u);
v___x_4658_ = lean_array_get_size(v_as_4651_);
v___x_4659_ = lean_nat_dec_lt(v___x_4657_, v___x_4658_);
if (v___x_4659_ == 0)
{
lean_object* v___x_4660_; 
lean_dec_ref(v_as_4651_);
lean_dec_ref(v_inst_4650_);
v___x_4660_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
return v___x_4660_;
}
else
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4661_ = lean_array_fget_borrowed(v_as_4651_, v___x_4657_);
v___x_4662_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4663_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
if (v___x_4659_ == 0)
{
lean_object* v___x_4664_; 
lean_inc(v___x_4661_);
lean_dec_ref(v_as_4651_);
lean_dec_ref(v_inst_4650_);
v___x_4664_ = lean_array_push(v___x_4662_, v___x_4661_);
return v___x_4664_;
}
else
{
lean_object* v___f_4665_; lean_object* v___x_4666_; uint8_t v___x_4667_; 
v___f_4665_ = lean_alloc_closure((void*)(l_Array_eraseReps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4665_, 0, v_inst_4650_);
lean_inc(v___x_4661_);
v___x_4666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4661_);
lean_ctor_set(v___x_4666_, 1, v___x_4662_);
v___x_4667_ = lean_nat_dec_le(v___x_4658_, v___x_4658_);
if (v___x_4667_ == 0)
{
if (v___x_4659_ == 0)
{
lean_object* v___x_4668_; 
lean_inc(v___x_4661_);
lean_dec_ref(v___x_4666_);
lean_dec_ref(v___f_4665_);
lean_dec_ref(v_as_4651_);
v___x_4668_ = lean_array_push(v___x_4662_, v___x_4661_);
return v___x_4668_;
}
else
{
size_t v___x_4669_; size_t v___x_4670_; lean_object* v___x_4671_; 
v___x_4669_ = ((size_t)0ULL);
v___x_4670_ = lean_usize_of_nat(v___x_4658_);
v___x_4671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4663_, v___f_4665_, v_as_4651_, v___x_4669_, v___x_4670_, v___x_4666_);
v___y_4653_ = v___x_4671_;
goto v___jp_4652_;
}
}
else
{
size_t v___x_4672_; size_t v___x_4673_; lean_object* v___x_4674_; 
v___x_4672_ = ((size_t)0ULL);
v___x_4673_ = lean_usize_of_nat(v___x_4658_);
v___x_4674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4663_, v___f_4665_, v_as_4651_, v___x_4672_, v___x_4673_, v___x_4666_);
v___y_4653_ = v___x_4674_;
goto v___jp_4652_;
}
}
}
v___jp_4652_:
{
lean_object* v_fst_4654_; lean_object* v_snd_4655_; lean_object* v___x_4656_; 
v_fst_4654_ = lean_ctor_get(v___y_4653_, 0);
lean_inc(v_fst_4654_);
v_snd_4655_ = lean_ctor_get(v___y_4653_, 1);
lean_inc(v_snd_4655_);
lean_dec_ref(v___y_4653_);
v___x_4656_ = lean_array_push(v_snd_4655_, v_fst_4654_);
return v___x_4656_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps(lean_object* v_00_u03b1_4675_, lean_object* v_inst_4676_, lean_object* v_as_4677_){
_start:
{
lean_object* v___x_4678_; 
v___x_4678_ = l_Array_eraseReps___redArg(v_inst_4676_, v_as_4677_);
return v___x_4678_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(lean_object* v_inst_4679_, lean_object* v_as_4680_, lean_object* v_a_4681_, lean_object* v_x_4682_){
_start:
{
lean_object* v_zero_4683_; uint8_t v_isZero_4684_; 
v_zero_4683_ = lean_unsigned_to_nat(0u);
v_isZero_4684_ = lean_nat_dec_eq(v_x_4682_, v_zero_4683_);
if (v_isZero_4684_ == 1)
{
lean_dec(v_x_4682_);
lean_dec(v_a_4681_);
lean_dec_ref(v_inst_4679_);
return v_isZero_4684_;
}
else
{
lean_object* v_one_4685_; lean_object* v_n_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; uint8_t v___x_4689_; 
v_one_4685_ = lean_unsigned_to_nat(1u);
v_n_4686_ = lean_nat_sub(v_x_4682_, v_one_4685_);
lean_dec(v_x_4682_);
v___x_4687_ = lean_array_fget_borrowed(v_as_4680_, v_n_4686_);
lean_inc_ref(v_inst_4679_);
lean_inc(v___x_4687_);
lean_inc(v_a_4681_);
v___x_4688_ = lean_apply_2(v_inst_4679_, v_a_4681_, v___x_4687_);
v___x_4689_ = lean_unbox(v___x_4688_);
if (v___x_4689_ == 0)
{
v_x_4682_ = v_n_4686_;
goto _start;
}
else
{
lean_dec(v_n_4686_);
lean_dec(v_a_4681_);
lean_dec_ref(v_inst_4679_);
return v_isZero_4684_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg___boxed(lean_object* v_inst_4691_, lean_object* v_as_4692_, lean_object* v_a_4693_, lean_object* v_x_4694_){
_start:
{
uint8_t v_res_4695_; lean_object* v_r_4696_; 
v_res_4695_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4691_, v_as_4692_, v_a_4693_, v_x_4694_);
lean_dec_ref(v_as_4692_);
v_r_4696_ = lean_box(v_res_4695_);
return v_r_4696_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(lean_object* v_00_u03b1_4697_, lean_object* v_inst_4698_, lean_object* v_as_4699_, lean_object* v_a_4700_, lean_object* v_x_4701_, lean_object* v_x_4702_){
_start:
{
uint8_t v___x_4703_; 
v___x_4703_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4698_, v_as_4699_, v_a_4700_, v_x_4701_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___boxed(lean_object* v_00_u03b1_4704_, lean_object* v_inst_4705_, lean_object* v_as_4706_, lean_object* v_a_4707_, lean_object* v_x_4708_, lean_object* v_x_4709_){
_start:
{
uint8_t v_res_4710_; lean_object* v_r_4711_; 
v_res_4710_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(v_00_u03b1_4704_, v_inst_4705_, v_as_4706_, v_a_4707_, v_x_4708_, v_x_4709_);
lean_dec_ref(v_as_4706_);
v_r_4711_ = lean_box(v_res_4710_);
return v_r_4711_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(lean_object* v_inst_4712_, lean_object* v_as_4713_, lean_object* v_i_4714_){
_start:
{
lean_object* v___x_4715_; uint8_t v___x_4716_; 
v___x_4715_ = lean_array_get_size(v_as_4713_);
v___x_4716_ = lean_nat_dec_lt(v_i_4714_, v___x_4715_);
if (v___x_4716_ == 0)
{
uint8_t v___x_4717_; 
lean_dec(v_i_4714_);
lean_dec_ref(v_inst_4712_);
v___x_4717_ = 1;
return v___x_4717_;
}
else
{
lean_object* v___x_4718_; uint8_t v___x_4719_; 
v___x_4718_ = lean_array_fget_borrowed(v_as_4713_, v_i_4714_);
lean_inc(v_i_4714_);
lean_inc(v___x_4718_);
lean_inc_ref(v_inst_4712_);
v___x_4719_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4712_, v_as_4713_, v___x_4718_, v_i_4714_);
if (v___x_4719_ == 0)
{
lean_dec(v_i_4714_);
lean_dec_ref(v_inst_4712_);
return v___x_4719_;
}
else
{
lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4720_ = lean_unsigned_to_nat(1u);
v___x_4721_ = lean_nat_add(v_i_4714_, v___x_4720_);
lean_dec(v_i_4714_);
v_i_4714_ = v___x_4721_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg___boxed(lean_object* v_inst_4723_, lean_object* v_as_4724_, lean_object* v_i_4725_){
_start:
{
uint8_t v_res_4726_; lean_object* v_r_4727_; 
v_res_4726_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4723_, v_as_4724_, v_i_4725_);
lean_dec_ref(v_as_4724_);
v_r_4727_ = lean_box(v_res_4726_);
return v_r_4727_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux(lean_object* v_00_u03b1_4728_, lean_object* v_inst_4729_, lean_object* v_as_4730_, lean_object* v_i_4731_){
_start:
{
uint8_t v___x_4732_; 
v___x_4732_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4729_, v_as_4730_, v_i_4731_);
return v___x_4732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___boxed(lean_object* v_00_u03b1_4733_, lean_object* v_inst_4734_, lean_object* v_as_4735_, lean_object* v_i_4736_){
_start:
{
uint8_t v_res_4737_; lean_object* v_r_4738_; 
v_res_4737_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux(v_00_u03b1_4733_, v_inst_4734_, v_as_4735_, v_i_4736_);
lean_dec_ref(v_as_4735_);
v_r_4738_ = lean_box(v_res_4737_);
return v_r_4738_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___redArg(lean_object* v_inst_4739_, lean_object* v_as_4740_){
_start:
{
lean_object* v___x_4741_; uint8_t v___x_4742_; 
v___x_4741_ = lean_unsigned_to_nat(0u);
v___x_4742_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4739_, v_as_4740_, v___x_4741_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___redArg___boxed(lean_object* v_inst_4743_, lean_object* v_as_4744_){
_start:
{
uint8_t v_res_4745_; lean_object* v_r_4746_; 
v_res_4745_ = l_Array_allDiff___redArg(v_inst_4743_, v_as_4744_);
lean_dec_ref(v_as_4744_);
v_r_4746_ = lean_box(v_res_4745_);
return v_r_4746_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff(lean_object* v_00_u03b1_4747_, lean_object* v_inst_4748_, lean_object* v_as_4749_){
_start:
{
uint8_t v___x_4750_; 
v___x_4750_ = l_Array_allDiff___redArg(v_inst_4748_, v_as_4749_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___boxed(lean_object* v_00_u03b1_4751_, lean_object* v_inst_4752_, lean_object* v_as_4753_){
_start:
{
uint8_t v_res_4754_; lean_object* v_r_4755_; 
v_res_4754_ = l_Array_allDiff(v_00_u03b1_4751_, v_inst_4752_, v_as_4753_);
lean_dec_ref(v_as_4753_);
v_r_4755_ = lean_box(v_res_4754_);
return v_r_4755_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0(uint8_t v___x_4756_, lean_object* v_x1_4757_, lean_object* v_x2_4758_){
_start:
{
lean_object* v_fst_4759_; uint8_t v___x_4760_; 
v_fst_4759_ = lean_ctor_get(v_x1_4757_, 0);
v___x_4760_ = lean_unbox(v_fst_4759_);
if (v___x_4760_ == 0)
{
lean_object* v_snd_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4769_; 
lean_dec(v_x2_4758_);
v_snd_4761_ = lean_ctor_get(v_x1_4757_, 1);
v_isSharedCheck_4769_ = !lean_is_exclusive(v_x1_4757_);
if (v_isSharedCheck_4769_ == 0)
{
lean_object* v_unused_4770_; 
v_unused_4770_ = lean_ctor_get(v_x1_4757_, 0);
lean_dec(v_unused_4770_);
v___x_4763_ = v_x1_4757_;
v_isShared_4764_ = v_isSharedCheck_4769_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_snd_4761_);
lean_dec(v_x1_4757_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4769_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4765_; lean_object* v___x_4767_; 
v___x_4765_ = lean_box(v___x_4756_);
if (v_isShared_4764_ == 0)
{
lean_ctor_set(v___x_4763_, 0, v___x_4765_);
v___x_4767_ = v___x_4763_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v___x_4765_);
lean_ctor_set(v_reuseFailAlloc_4768_, 1, v_snd_4761_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
else
{
lean_object* v_snd_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4781_; 
v_snd_4771_ = lean_ctor_get(v_x1_4757_, 1);
v_isSharedCheck_4781_ = !lean_is_exclusive(v_x1_4757_);
if (v_isSharedCheck_4781_ == 0)
{
lean_object* v_unused_4782_; 
v_unused_4782_ = lean_ctor_get(v_x1_4757_, 0);
lean_dec(v_unused_4782_);
v___x_4773_ = v_x1_4757_;
v_isShared_4774_ = v_isSharedCheck_4781_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_snd_4771_);
lean_dec(v_x1_4757_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4781_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
uint8_t v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4779_; 
v___x_4775_ = 0;
v___x_4776_ = lean_array_push(v_snd_4771_, v_x2_4758_);
v___x_4777_ = lean_box(v___x_4775_);
if (v_isShared_4774_ == 0)
{
lean_ctor_set(v___x_4773_, 1, v___x_4776_);
lean_ctor_set(v___x_4773_, 0, v___x_4777_);
v___x_4779_ = v___x_4773_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v___x_4777_);
lean_ctor_set(v_reuseFailAlloc_4780_, 1, v___x_4776_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0___boxed(lean_object* v___x_4783_, lean_object* v_x1_4784_, lean_object* v_x2_4785_){
_start:
{
uint8_t v___x_172__boxed_4786_; lean_object* v_res_4787_; 
v___x_172__boxed_4786_ = lean_unbox(v___x_4783_);
v_res_4787_ = l_Array_getEvenElems___redArg___lam__0(v___x_172__boxed_4786_, v_x1_4784_, v_x2_4785_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg(lean_object* v_as_4788_){
_start:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; uint8_t v___x_4793_; 
v___x_4789_ = lean_unsigned_to_nat(0u);
v___x_4790_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_4791_ = lean_array_get_size(v_as_4788_);
v___x_4792_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4793_ = lean_nat_dec_lt(v___x_4789_, v___x_4791_);
if (v___x_4793_ == 0)
{
lean_dec_ref(v_as_4788_);
return v___x_4790_;
}
else
{
lean_object* v___x_4794_; lean_object* v___f_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; uint8_t v___x_4798_; 
v___x_4794_ = lean_box(v___x_4793_);
v___f_4795_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4795_, 0, v___x_4794_);
v___x_4796_ = lean_box(v___x_4793_);
v___x_4797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4796_);
lean_ctor_set(v___x_4797_, 1, v___x_4790_);
v___x_4798_ = lean_nat_dec_le(v___x_4791_, v___x_4791_);
if (v___x_4798_ == 0)
{
if (v___x_4793_ == 0)
{
lean_dec_ref(v___x_4797_);
lean_dec_ref(v___f_4795_);
lean_dec_ref(v_as_4788_);
return v___x_4790_;
}
else
{
size_t v___x_4799_; size_t v___x_4800_; lean_object* v___x_4801_; lean_object* v_snd_4802_; 
v___x_4799_ = ((size_t)0ULL);
v___x_4800_ = lean_usize_of_nat(v___x_4791_);
v___x_4801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4792_, v___f_4795_, v_as_4788_, v___x_4799_, v___x_4800_, v___x_4797_);
v_snd_4802_ = lean_ctor_get(v___x_4801_, 1);
lean_inc(v_snd_4802_);
lean_dec(v___x_4801_);
return v_snd_4802_;
}
}
else
{
size_t v___x_4803_; size_t v___x_4804_; lean_object* v___x_4805_; lean_object* v_snd_4806_; 
v___x_4803_ = ((size_t)0ULL);
v___x_4804_ = lean_usize_of_nat(v___x_4791_);
v___x_4805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4792_, v___f_4795_, v_as_4788_, v___x_4803_, v___x_4804_, v___x_4797_);
v_snd_4806_ = lean_ctor_get(v___x_4805_, 1);
lean_inc(v_snd_4806_);
lean_dec(v___x_4805_);
return v_snd_4806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems(lean_object* v_00_u03b1_4807_, lean_object* v_as_4808_){
_start:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; uint8_t v___x_4813_; 
v___x_4809_ = lean_unsigned_to_nat(0u);
v___x_4810_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_4811_ = lean_array_get_size(v_as_4808_);
v___x_4812_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4813_ = lean_nat_dec_lt(v___x_4809_, v___x_4811_);
if (v___x_4813_ == 0)
{
lean_dec_ref(v_as_4808_);
return v___x_4810_;
}
else
{
lean_object* v___x_4814_; lean_object* v___f_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; uint8_t v___x_4818_; 
v___x_4814_ = lean_box(v___x_4813_);
v___f_4815_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4815_, 0, v___x_4814_);
v___x_4816_ = lean_box(v___x_4813_);
v___x_4817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4817_, 0, v___x_4816_);
lean_ctor_set(v___x_4817_, 1, v___x_4810_);
v___x_4818_ = lean_nat_dec_le(v___x_4811_, v___x_4811_);
if (v___x_4818_ == 0)
{
if (v___x_4813_ == 0)
{
lean_dec_ref(v___x_4817_);
lean_dec_ref(v___f_4815_);
lean_dec_ref(v_as_4808_);
return v___x_4810_;
}
else
{
size_t v___x_4819_; size_t v___x_4820_; lean_object* v___x_4821_; lean_object* v_snd_4822_; 
v___x_4819_ = ((size_t)0ULL);
v___x_4820_ = lean_usize_of_nat(v___x_4811_);
v___x_4821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4812_, v___f_4815_, v_as_4808_, v___x_4819_, v___x_4820_, v___x_4817_);
v_snd_4822_ = lean_ctor_get(v___x_4821_, 1);
lean_inc(v_snd_4822_);
lean_dec(v___x_4821_);
return v_snd_4822_;
}
}
else
{
size_t v___x_4823_; size_t v___x_4824_; lean_object* v___x_4825_; lean_object* v_snd_4826_; 
v___x_4823_ = ((size_t)0ULL);
v___x_4824_ = lean_usize_of_nat(v___x_4811_);
v___x_4825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4812_, v___f_4815_, v_as_4808_, v___x_4823_, v___x_4824_, v___x_4817_);
v_snd_4826_ = lean_ctor_get(v___x_4825_, 1);
lean_inc(v_snd_4826_);
lean_dec(v___x_4825_);
return v_snd_4826_;
}
}
}
}
static lean_object* _init_l_Array_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; 
v___x_4832_ = ((lean_object*)(l_term_x23_x5b___x2c_x5d___closed__4));
v___x_4833_ = lean_string_length(v___x_4832_);
return v___x_4833_;
}
}
static lean_object* _init_l_Array_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_4834_; lean_object* v___x_4835_; 
v___x_4834_ = lean_obj_once(&l_Array_repr___redArg___closed__2, &l_Array_repr___redArg___closed__2_once, _init_l_Array_repr___redArg___closed__2);
v___x_4835_ = lean_nat_to_int(v___x_4834_);
return v___x_4835_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___redArg(lean_object* v_inst_4843_, lean_object* v_xs_4844_){
_start:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; uint8_t v___x_4847_; 
v___x_4845_ = lean_array_get_size(v_xs_4844_);
v___x_4846_ = lean_unsigned_to_nat(0u);
v___x_4847_ = lean_nat_dec_eq(v___x_4845_, v___x_4846_);
if (v___x_4847_ == 0)
{
lean_object* v_x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
v_x_4848_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_4848_, 0, lean_box(0));
lean_closure_set(v_x_4848_, 1, v_inst_4843_);
v___x_4849_ = lean_array_to_list(v_xs_4844_);
v___x_4850_ = ((lean_object*)(l_Array_repr___redArg___closed__1));
v___x_4851_ = l_Std_Format_joinSep___redArg(v_x_4848_, v___x_4849_, v___x_4850_);
v___x_4852_ = lean_obj_once(&l_Array_repr___redArg___closed__3, &l_Array_repr___redArg___closed__3_once, _init_l_Array_repr___redArg___closed__3);
v___x_4853_ = ((lean_object*)(l_Array_repr___redArg___closed__4));
v___x_4854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4854_, 0, v___x_4853_);
lean_ctor_set(v___x_4854_, 1, v___x_4851_);
v___x_4855_ = ((lean_object*)(l_Array_repr___redArg___closed__5));
v___x_4856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4854_);
lean_ctor_set(v___x_4856_, 1, v___x_4855_);
v___x_4857_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4852_);
lean_ctor_set(v___x_4857_, 1, v___x_4856_);
v___x_4858_ = l_Std_Format_fill(v___x_4857_);
return v___x_4858_;
}
else
{
lean_object* v___x_4859_; 
lean_dec_ref(v_xs_4844_);
lean_dec_ref(v_inst_4843_);
v___x_4859_ = ((lean_object*)(l_Array_repr___redArg___closed__7));
return v___x_4859_;
}
}
}
LEAN_EXPORT lean_object* l_Array_repr(lean_object* v_00_u03b1_4860_, lean_object* v_inst_4861_, lean_object* v_xs_4862_){
_start:
{
lean_object* v___x_4863_; 
v___x_4863_ = l_Array_repr___redArg(v_inst_4861_, v_xs_4862_);
return v___x_4863_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0(lean_object* v_inst_4864_, lean_object* v_xs_4865_, lean_object* v_x_4866_){
_start:
{
lean_object* v___x_4867_; 
v___x_4867_ = l_Array_repr___redArg(v_inst_4864_, v_xs_4865_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object* v_inst_4868_, lean_object* v_xs_4869_, lean_object* v_x_4870_){
_start:
{
lean_object* v_res_4871_; 
v_res_4871_ = l_Array_instRepr___redArg___lam__0(v_inst_4868_, v_xs_4869_, v_x_4870_);
lean_dec(v_x_4870_);
return v_res_4871_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg(lean_object* v_inst_4872_){
_start:
{
lean_object* v___f_4873_; 
v___f_4873_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4873_, 0, v_inst_4872_);
return v___f_4873_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr(lean_object* v_00_u03b1_4874_, lean_object* v_inst_4875_){
_start:
{
lean_object* v___f_4876_; 
v___f_4876_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4876_, 0, v_inst_4875_);
return v___f_4876_;
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
