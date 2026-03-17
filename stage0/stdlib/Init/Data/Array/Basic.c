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
lean_object* v___x_126_; 
v___x_126_ = l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter___redArg(v_x_122_, v_x_123_, v_h__1_124_, v_h__2_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Array_instMembership(lean_object* v_00_u03b1_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_box(0);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter___redArg(lean_object* v_x_129_, lean_object* v_h__1_130_, lean_object* v_h__2_131_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_h__1_130_);
v___x_132_ = lean_box(0);
v___x_133_ = lean_apply_1(v_h__2_131_, v___x_132_);
return v___x_133_;
}
else
{
lean_object* v_val_134_; lean_object* v___x_135_; 
lean_dec(v_h__2_131_);
v_val_134_ = lean_ctor_get(v_x_129_, 0);
lean_inc(v_val_134_);
lean_dec_ref(v_x_129_);
v___x_135_ = lean_apply_1(v_h__1_130_, v_val_134_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_136_, lean_object* v_motive_137_, lean_object* v_x_138_, lean_object* v_h__1_139_, lean_object* v_h__2_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter___redArg(v_x_138_, v_h__1_139_, v_h__2_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Array_usize___boxed(lean_object* v_00_u03b1_144_, lean_object* v_xs_145_){
_start:
{
size_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = lean_array_size(v_xs_145_);
lean_dec_ref(v_xs_145_);
v_r_147_ = lean_box_usize(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_Array_uget___boxed(lean_object* v_00_u03b1_152_, lean_object* v_xs_153_, lean_object* v_i_154_, lean_object* v_h_155_){
_start:
{
size_t v_i_boxed_156_; lean_object* v_res_157_; 
v_i_boxed_156_ = lean_unbox_usize(v_i_154_);
lean_dec(v_i_154_);
v_res_157_ = lean_array_uget(v_xs_153_, v_i_boxed_156_);
lean_dec_ref(v_xs_153_);
return v_res_157_;
}
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
LEAN_EXPORT lean_object* l_Array_uset___boxed(lean_object* v_00_u03b1_173_, lean_object* v_xs_174_, lean_object* v_i_175_, lean_object* v_v_176_, lean_object* v_h_177_){
_start:
{
size_t v_i_boxed_178_; lean_object* v_res_179_; 
v_i_boxed_178_ = lean_unbox_usize(v_i_175_);
lean_dec(v_i_175_);
v_res_179_ = lean_array_uset(v_xs_174_, v_i_boxed_178_, v_v_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Array_pop___boxed(lean_object* v_00_u03b1_182_, lean_object* v_xs_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = lean_array_pop(v_xs_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Array_replicate___boxed(lean_object* v_00_u03b1_188_, lean_object* v_n_189_, lean_object* v_v_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = lean_mk_array(v_n_189_, v_v_190_);
return v_res_191_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__9(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l_Array_swap___auto__1___closed__8));
v___x_212_ = l_Lean_mkAtom(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__10(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_obj_once(&l_Array_swap___auto__1___closed__9, &l_Array_swap___auto__1___closed__9_once, _init_l_Array_swap___auto__1___closed__9);
v___x_214_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_215_ = lean_array_push(v___x_214_, v___x_213_);
return v___x_215_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__11(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_216_ = lean_obj_once(&l_Array_swap___auto__1___closed__10, &l_Array_swap___auto__1___closed__10_once, _init_l_Array_swap___auto__1___closed__10);
v___x_217_ = ((lean_object*)(l_Array_swap___auto__1___closed__7));
v___x_218_ = lean_box(2);
v___x_219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_217_);
lean_ctor_set(v___x_219_, 2, v___x_216_);
return v___x_219_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__12(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = lean_obj_once(&l_Array_swap___auto__1___closed__11, &l_Array_swap___auto__1___closed__11_once, _init_l_Array_swap___auto__1___closed__11);
v___x_221_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_222_ = lean_array_push(v___x_221_, v___x_220_);
return v___x_222_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__13(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_223_ = lean_obj_once(&l_Array_swap___auto__1___closed__12, &l_Array_swap___auto__1___closed__12_once, _init_l_Array_swap___auto__1___closed__12);
v___x_224_ = ((lean_object*)(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13));
v___x_225_ = lean_box(2);
v___x_226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_224_);
lean_ctor_set(v___x_226_, 2, v___x_223_);
return v___x_226_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__14(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_obj_once(&l_Array_swap___auto__1___closed__13, &l_Array_swap___auto__1___closed__13_once, _init_l_Array_swap___auto__1___closed__13);
v___x_228_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_229_ = lean_array_push(v___x_228_, v___x_227_);
return v___x_229_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__15(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_230_ = lean_obj_once(&l_Array_swap___auto__1___closed__14, &l_Array_swap___auto__1___closed__14_once, _init_l_Array_swap___auto__1___closed__14);
v___x_231_ = ((lean_object*)(l_Array_swap___auto__1___closed__5));
v___x_232_ = lean_box(2);
v___x_233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v___x_231_);
lean_ctor_set(v___x_233_, 2, v___x_230_);
return v___x_233_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__16(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_obj_once(&l_Array_swap___auto__1___closed__15, &l_Array_swap___auto__1___closed__15_once, _init_l_Array_swap___auto__1___closed__15);
v___x_235_ = ((lean_object*)(l_Array_swap___auto__1___closed__3));
v___x_236_ = lean_array_push(v___x_235_, v___x_234_);
return v___x_236_;
}
}
static lean_object* _init_l_Array_swap___auto__1___closed__17(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_237_ = lean_obj_once(&l_Array_swap___auto__1___closed__16, &l_Array_swap___auto__1___closed__16_once, _init_l_Array_swap___auto__1___closed__16);
v___x_238_ = ((lean_object*)(l_Array_swap___auto__1___closed__2));
v___x_239_ = lean_box(2);
v___x_240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
lean_ctor_set(v___x_240_, 2, v___x_237_);
return v___x_240_;
}
}
static lean_object* _init_l_Array_swap___auto__1(void){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_241_;
}
}
static lean_object* _init_l_Array_swap___auto__3(void){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Array_swap___boxed(lean_object* v_00_u03b1_249_, lean_object* v_xs_250_, lean_object* v_i_251_, lean_object* v_j_252_, lean_object* v_hi_253_, lean_object* v_hj_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = lean_array_fswap(v_xs_250_, v_i_251_, v_j_252_);
lean_dec(v_j_252_);
lean_dec(v_i_251_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Array_swapIfInBounds___boxed(lean_object* v_00_u03b1_260_, lean_object* v_xs_261_, lean_object* v_i_262_, lean_object* v_j_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = lean_array_swap(v_xs_261_, v_i_262_, v_j_263_);
lean_dec(v_j_263_);
lean_dec(v_i_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___lam__0(lean_object* v_xs_265_, size_t v_i_266_, lean_object* v_h_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_array_uget_borrowed(v_xs_265_, v_i_266_);
lean_inc(v___x_268_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize___lam__0___boxed(lean_object* v_xs_269_, lean_object* v_i_270_, lean_object* v_h_271_){
_start:
{
size_t v_i_boxed_272_; lean_object* v_res_273_; 
v_i_boxed_272_ = lean_unbox_usize(v_i_270_);
lean_dec(v_i_270_);
v_res_273_ = l_Array_instGetElemUSizeLtNatToNatSize___lam__0(v_xs_269_, v_i_boxed_272_, v_h_271_);
lean_dec_ref(v_xs_269_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize(lean_object* v_00_u03b1_275_){
_start:
{
lean_object* v___f_276_; 
v___f_276_ = ((lean_object*)(l_Array_instGetElemUSizeLtNatToNatSize___closed__0));
return v___f_276_;
}
}
LEAN_EXPORT lean_object* l_Array_instEmptyCollection(lean_object* v_00_u03b1_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Array_instInhabited(lean_object* v_00_u03b1_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
return v___x_282_;
}
}
LEAN_EXPORT uint8_t l_Array_isEmpty___redArg(lean_object* v_xs_283_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_284_ = lean_array_get_size(v_xs_283_);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_nat_dec_eq(v___x_284_, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Array_isEmpty___redArg___boxed(lean_object* v_xs_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Array_isEmpty___redArg(v_xs_287_);
lean_dec_ref(v_xs_287_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT uint8_t l_Array_isEmpty(lean_object* v_00_u03b1_290_, lean_object* v_xs_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_292_ = lean_array_get_size(v_xs_291_);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_nat_dec_eq(v___x_292_, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Array_isEmpty___boxed(lean_object* v_00_u03b1_295_, lean_object* v_xs_296_){
_start:
{
uint8_t v_res_297_; lean_object* v_r_298_; 
v_res_297_ = l_Array_isEmpty(v_00_u03b1_295_, v_xs_296_);
lean_dec_ref(v_xs_296_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___redArg(lean_object* v_xs_299_, lean_object* v_ys_300_, lean_object* v_p_301_, lean_object* v_x_302_){
_start:
{
lean_object* v_zero_303_; uint8_t v_isZero_304_; 
v_zero_303_ = lean_unsigned_to_nat(0u);
v_isZero_304_ = lean_nat_dec_eq(v_x_302_, v_zero_303_);
if (v_isZero_304_ == 1)
{
lean_dec(v_x_302_);
lean_dec_ref(v_p_301_);
return v_isZero_304_;
}
else
{
lean_object* v_one_305_; lean_object* v_n_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_one_305_ = lean_unsigned_to_nat(1u);
v_n_306_ = lean_nat_sub(v_x_302_, v_one_305_);
lean_dec(v_x_302_);
v___x_307_ = lean_array_fget_borrowed(v_xs_299_, v_n_306_);
v___x_308_ = lean_array_fget_borrowed(v_ys_300_, v_n_306_);
lean_inc_ref(v_p_301_);
lean_inc(v___x_308_);
lean_inc(v___x_307_);
v___x_309_ = lean_apply_2(v_p_301_, v___x_307_, v___x_308_);
v___x_310_ = lean_unbox(v___x_309_);
if (v___x_310_ == 0)
{
uint8_t v___x_311_; 
lean_dec(v_n_306_);
lean_dec_ref(v_p_301_);
v___x_311_ = lean_unbox(v___x_309_);
return v___x_311_;
}
else
{
v_x_302_ = v_n_306_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___redArg___boxed(lean_object* v_xs_313_, lean_object* v_ys_314_, lean_object* v_p_315_, lean_object* v_x_316_){
_start:
{
uint8_t v_res_317_; lean_object* v_r_318_; 
v_res_317_ = l_Array_isEqvAux___redArg(v_xs_313_, v_ys_314_, v_p_315_, v_x_316_);
lean_dec_ref(v_ys_314_);
lean_dec_ref(v_xs_313_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux(lean_object* v_00_u03b1_319_, lean_object* v_xs_320_, lean_object* v_ys_321_, lean_object* v_hsz_322_, lean_object* v_p_323_, lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = l_Array_isEqvAux___redArg(v_xs_320_, v_ys_321_, v_p_323_, v_x_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___boxed(lean_object* v_00_u03b1_327_, lean_object* v_xs_328_, lean_object* v_ys_329_, lean_object* v_hsz_330_, lean_object* v_p_331_, lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Array_isEqvAux(v_00_u03b1_327_, v_xs_328_, v_ys_329_, v_hsz_330_, v_p_331_, v_x_332_, v_x_333_);
lean_dec_ref(v_ys_329_);
lean_dec_ref(v_xs_328_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqv___redArg(lean_object* v_xs_336_, lean_object* v_ys_337_, lean_object* v_p_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_339_ = lean_array_get_size(v_xs_336_);
v___x_340_ = lean_array_get_size(v_ys_337_);
v___x_341_ = lean_nat_dec_eq(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
lean_dec_ref(v_p_338_);
return v___x_341_;
}
else
{
uint8_t v___x_342_; 
v___x_342_ = l_Array_isEqvAux___redArg(v_xs_336_, v_ys_337_, v_p_338_, v___x_339_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqv___redArg___boxed(lean_object* v_xs_343_, lean_object* v_ys_344_, lean_object* v_p_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Array_isEqv___redArg(v_xs_343_, v_ys_344_, v_p_345_);
lean_dec_ref(v_ys_344_);
lean_dec_ref(v_xs_343_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqv(lean_object* v_00_u03b1_348_, lean_object* v_xs_349_, lean_object* v_ys_350_, lean_object* v_p_351_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_352_ = lean_array_get_size(v_xs_349_);
v___x_353_ = lean_array_get_size(v_ys_350_);
v___x_354_ = lean_nat_dec_eq(v___x_352_, v___x_353_);
if (v___x_354_ == 0)
{
lean_dec_ref(v_p_351_);
return v___x_354_;
}
else
{
uint8_t v___x_355_; 
v___x_355_ = l_Array_isEqvAux___redArg(v_xs_349_, v_ys_350_, v_p_351_, v___x_352_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqv___boxed(lean_object* v_00_u03b1_356_, lean_object* v_xs_357_, lean_object* v_ys_358_, lean_object* v_p_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = l_Array_isEqv(v_00_u03b1_356_, v_xs_357_, v_ys_358_, v_p_359_);
lean_dec_ref(v_ys_358_);
lean_dec_ref(v_xs_357_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT uint8_t l_Array_instBEq___redArg___lam__0(lean_object* v_inst_362_, lean_object* v_xs_363_, lean_object* v_ys_364_){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_365_ = lean_array_get_size(v_xs_363_);
v___x_366_ = lean_array_get_size(v_ys_364_);
v___x_367_ = lean_nat_dec_eq(v___x_365_, v___x_366_);
if (v___x_367_ == 0)
{
lean_dec_ref(v_inst_362_);
return v___x_367_;
}
else
{
uint8_t v___x_368_; 
v___x_368_ = l_Array_isEqvAux___redArg(v_xs_363_, v_ys_364_, v_inst_362_, v___x_365_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instBEq___redArg___lam__0___boxed(lean_object* v_inst_369_, lean_object* v_xs_370_, lean_object* v_ys_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Array_instBEq___redArg___lam__0(v_inst_369_, v_xs_370_, v_ys_371_);
lean_dec_ref(v_ys_371_);
lean_dec_ref(v_xs_370_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l_Array_instBEq___redArg(lean_object* v_inst_374_){
_start:
{
lean_object* v___f_375_; 
v___f_375_ = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_375_, 0, v_inst_374_);
return v___f_375_;
}
}
LEAN_EXPORT lean_object* l_Array_instBEq(lean_object* v_00_u03b1_376_, lean_object* v_inst_377_){
_start:
{
lean_object* v___f_378_; 
v___f_378_ = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_378_, 0, v_inst_377_);
return v___f_378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(lean_object* v_n_379_, lean_object* v_f_380_, lean_object* v_acc_381_, lean_object* v_i_382_){
_start:
{
lean_object* v_zero_383_; uint8_t v_isZero_384_; 
v_zero_383_ = lean_unsigned_to_nat(0u);
v_isZero_384_ = lean_nat_dec_eq(v_i_382_, v_zero_383_);
if (v_isZero_384_ == 1)
{
lean_dec(v_i_382_);
lean_dec(v_f_380_);
return v_acc_381_;
}
else
{
lean_object* v_one_385_; lean_object* v_n_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_one_385_ = lean_unsigned_to_nat(1u);
v_n_386_ = lean_nat_sub(v_i_382_, v_one_385_);
lean_dec(v_i_382_);
v___x_387_ = lean_nat_sub(v_n_379_, v_n_386_);
v___x_388_ = lean_nat_sub(v___x_387_, v_one_385_);
lean_dec(v___x_387_);
lean_inc(v_f_380_);
v___x_389_ = lean_apply_1(v_f_380_, v___x_388_);
v___x_390_ = lean_array_push(v_acc_381_, v___x_389_);
v_acc_381_ = v___x_390_;
v_i_382_ = v_n_386_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg___boxed(lean_object* v_n_392_, lean_object* v_f_393_, lean_object* v_acc_394_, lean_object* v_i_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(v_n_392_, v_f_393_, v_acc_394_, v_i_395_);
lean_dec(v_n_392_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go(lean_object* v_00_u03b1_397_, lean_object* v_n_398_, lean_object* v_f_399_, lean_object* v_acc_400_, lean_object* v_i_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(v_n_398_, v_f_399_, v_acc_400_, v_i_401_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_ofFn_go___boxed(lean_object* v_00_u03b1_404_, lean_object* v_n_405_, lean_object* v_f_406_, lean_object* v_acc_407_, lean_object* v_i_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go(v_00_u03b1_404_, v_n_405_, v_f_406_, v_acc_407_, v_i_408_, v_a_409_);
lean_dec(v_n_405_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn___redArg(lean_object* v_n_411_, lean_object* v_f_412_){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_mk_empty_array_with_capacity(v_n_411_);
lean_inc(v_n_411_);
v___x_414_ = l___private_Init_Data_Array_Basic_0__Array_ofFn_go___redArg(v_n_411_, v_f_412_, v___x_413_, v_n_411_);
lean_dec(v_n_411_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn(lean_object* v_00_u03b1_415_, lean_object* v_n_416_, lean_object* v_f_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Array_ofFn___redArg(v_n_416_, v_f_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Array_range___lam__0(lean_object* v_i_419_){
_start:
{
lean_inc(v_i_419_);
return v_i_419_;
}
}
LEAN_EXPORT lean_object* l_Array_range___lam__0___boxed(lean_object* v_i_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Array_range___lam__0(v_i_420_);
lean_dec(v_i_420_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Array_range(lean_object* v_n_423_){
_start:
{
lean_object* v___f_424_; lean_object* v___x_425_; 
v___f_424_ = ((lean_object*)(l_Array_range___closed__0));
v___x_425_ = l_Array_ofFn___redArg(v_n_423_, v___f_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27___lam__0(lean_object* v_step_426_, lean_object* v_start_427_, lean_object* v_i_428_){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_nat_mul(v_step_426_, v_i_428_);
v___x_430_ = lean_nat_add(v_start_427_, v___x_429_);
lean_dec(v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27___lam__0___boxed(lean_object* v_step_431_, lean_object* v_start_432_, lean_object* v_i_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Array_range_x27___lam__0(v_step_431_, v_start_432_, v_i_433_);
lean_dec(v_i_433_);
lean_dec(v_start_432_);
lean_dec(v_step_431_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27(lean_object* v_start_435_, lean_object* v_size_436_, lean_object* v_step_437_){
_start:
{
lean_object* v___f_438_; lean_object* v___x_439_; 
v___f_438_ = lean_alloc_closure((void*)(l_Array_range_x27___lam__0___boxed), 3, 2);
lean_closure_set(v___f_438_, 0, v_step_437_);
lean_closure_set(v___f_438_, 1, v_start_435_);
v___x_439_ = l_Array_ofFn___redArg(v_size_436_, v___f_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Array_singleton___redArg(lean_object* v_v_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = lean_mk_empty_array_with_capacity(v___x_441_);
v___x_443_ = lean_array_push(v___x_442_, v_v_440_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Array_singleton(lean_object* v_00_u03b1_444_, lean_object* v_v_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_mk_empty_array_with_capacity(v___x_446_);
v___x_448_ = lean_array_push(v___x_447_, v_v_445_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___redArg(lean_object* v_inst_449_, lean_object* v_xs_450_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_451_ = lean_array_get_size(v_xs_450_);
v___x_452_ = lean_unsigned_to_nat(1u);
v___x_453_ = lean_nat_sub(v___x_451_, v___x_452_);
v___x_454_ = lean_array_get_borrowed(v_inst_449_, v_xs_450_, v___x_453_);
lean_dec(v___x_453_);
lean_inc(v___x_454_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___redArg___boxed(lean_object* v_inst_455_, lean_object* v_xs_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Array_back_x21___redArg(v_inst_455_, v_xs_456_);
lean_dec_ref(v_xs_456_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21(lean_object* v_00_u03b1_458_, lean_object* v_inst_459_, lean_object* v_xs_460_){
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
LEAN_EXPORT lean_object* l_Array_back_x21___boxed(lean_object* v_00_u03b1_465_, lean_object* v_inst_466_, lean_object* v_xs_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Array_back_x21(v_00_u03b1_465_, v_inst_466_, v_xs_467_);
lean_dec_ref(v_xs_467_);
return v_res_468_;
}
}
static lean_object* _init_l_Array_back___auto__1(void){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Array_back___redArg(lean_object* v_xs_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_471_ = lean_array_get_size(v_xs_470_);
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = lean_nat_sub(v___x_471_, v___x_472_);
v___x_474_ = lean_array_fget_borrowed(v_xs_470_, v___x_473_);
lean_dec(v___x_473_);
lean_inc(v___x_474_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Array_back___redArg___boxed(lean_object* v_xs_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Array_back___redArg(v_xs_475_);
lean_dec_ref(v_xs_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Array_back(lean_object* v_00_u03b1_477_, lean_object* v_xs_478_, lean_object* v_h_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_480_ = lean_array_get_size(v_xs_478_);
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = lean_nat_sub(v___x_480_, v___x_481_);
v___x_483_ = lean_array_fget_borrowed(v_xs_478_, v___x_482_);
lean_dec(v___x_482_);
lean_inc(v___x_483_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Array_back___boxed(lean_object* v_00_u03b1_484_, lean_object* v_xs_485_, lean_object* v_h_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Array_back(v_00_u03b1_484_, v_xs_485_, v_h_486_);
lean_dec_ref(v_xs_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___redArg(lean_object* v_xs_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_489_ = lean_array_get_size(v_xs_488_);
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_sub(v___x_489_, v___x_490_);
v___x_492_ = lean_nat_dec_lt(v___x_491_, v___x_489_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
lean_dec(v___x_491_);
v___x_493_ = lean_box(0);
return v___x_493_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_array_fget_borrowed(v_xs_488_, v___x_491_);
lean_dec(v___x_491_);
lean_inc(v___x_494_);
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___redArg___boxed(lean_object* v_xs_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Array_back_x3f___redArg(v_xs_496_);
lean_dec_ref(v_xs_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f(lean_object* v_00_u03b1_498_, lean_object* v_xs_499_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_500_ = lean_array_get_size(v_xs_499_);
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_sub(v___x_500_, v___x_501_);
v___x_503_ = lean_nat_dec_lt(v___x_502_, v___x_500_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
lean_dec(v___x_502_);
v___x_504_ = lean_box(0);
return v___x_504_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_array_fget_borrowed(v_xs_499_, v___x_502_);
lean_dec(v___x_502_);
lean_inc(v___x_505_);
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___boxed(lean_object* v_00_u03b1_507_, lean_object* v_xs_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Array_back_x3f(v_00_u03b1_507_, v_xs_508_);
lean_dec_ref(v_xs_508_);
return v_res_509_;
}
}
static lean_object* _init_l_Array_swapAt___auto__1(void){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___redArg(lean_object* v_xs_511_, lean_object* v_i_512_, lean_object* v_v_513_){
_start:
{
lean_object* v_e_514_; lean_object* v_xs_x27_515_; lean_object* v___x_516_; 
v_e_514_ = lean_array_fget(v_xs_511_, v_i_512_);
v_xs_x27_515_ = lean_array_fset(v_xs_511_, v_i_512_, v_v_513_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v_e_514_);
lean_ctor_set(v___x_516_, 1, v_xs_x27_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___redArg___boxed(lean_object* v_xs_517_, lean_object* v_i_518_, lean_object* v_v_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Array_swapAt___redArg(v_xs_517_, v_i_518_, v_v_519_);
lean_dec(v_i_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt(lean_object* v_00_u03b1_521_, lean_object* v_xs_522_, lean_object* v_i_523_, lean_object* v_v_524_, lean_object* v_hi_525_){
_start:
{
lean_object* v_e_526_; lean_object* v_xs_x27_527_; lean_object* v___x_528_; 
v_e_526_ = lean_array_fget(v_xs_522_, v_i_523_);
v_xs_x27_527_ = lean_array_fset(v_xs_522_, v_i_523_, v_v_524_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v_e_526_);
lean_ctor_set(v___x_528_, 1, v_xs_x27_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___boxed(lean_object* v_00_u03b1_529_, lean_object* v_xs_530_, lean_object* v_i_531_, lean_object* v_v_532_, lean_object* v_hi_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Array_swapAt(v_00_u03b1_529_, v_xs_530_, v_i_531_, v_v_532_, v_hi_533_);
lean_dec(v_i_531_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt_x21___redArg(lean_object* v_xs_539_, lean_object* v_i_540_, lean_object* v_v_541_){
_start:
{
lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = lean_array_get_size(v_xs_539_);
v___x_543_ = lean_nat_dec_lt(v_i_540_, v___x_542_);
if (v___x_543_ == 0)
{
lean_object* v_this_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_this_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_544_, 0, v_v_541_);
lean_ctor_set(v_this_544_, 1, v_xs_539_);
v___x_545_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_546_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__1));
v___x_547_ = lean_unsigned_to_nat(438u);
v___x_548_ = lean_unsigned_to_nat(4u);
v___x_549_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__2));
v___x_550_ = l_Nat_reprFast(v_i_540_);
v___x_551_ = lean_string_append(v___x_549_, v___x_550_);
lean_dec_ref(v___x_550_);
v___x_552_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__3));
v___x_553_ = lean_string_append(v___x_551_, v___x_552_);
v___x_554_ = l_mkPanicMessageWithDecl(v___x_545_, v___x_546_, v___x_547_, v___x_548_, v___x_553_);
lean_dec_ref(v___x_553_);
v___x_555_ = l_panic___redArg(v_this_544_, v___x_554_);
return v___x_555_;
}
else
{
lean_object* v_e_556_; lean_object* v_xs_x27_557_; lean_object* v___x_558_; 
v_e_556_ = lean_array_fget(v_xs_539_, v_i_540_);
v_xs_x27_557_ = lean_array_fset(v_xs_539_, v_i_540_, v_v_541_);
lean_dec(v_i_540_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v_e_556_);
lean_ctor_set(v___x_558_, 1, v_xs_x27_557_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_Array_swapAt_x21(lean_object* v_00_u03b1_559_, lean_object* v_xs_560_, lean_object* v_i_561_, lean_object* v_v_562_){
_start:
{
lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_563_ = lean_array_get_size(v_xs_560_);
v___x_564_ = lean_nat_dec_lt(v_i_561_, v___x_563_);
if (v___x_564_ == 0)
{
lean_object* v_this_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_this_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_565_, 0, v_v_562_);
lean_ctor_set(v_this_565_, 1, v_xs_560_);
v___x_566_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_567_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__1));
v___x_568_ = lean_unsigned_to_nat(438u);
v___x_569_ = lean_unsigned_to_nat(4u);
v___x_570_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__2));
v___x_571_ = l_Nat_reprFast(v_i_561_);
v___x_572_ = lean_string_append(v___x_570_, v___x_571_);
lean_dec_ref(v___x_571_);
v___x_573_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__3));
v___x_574_ = lean_string_append(v___x_572_, v___x_573_);
v___x_575_ = l_mkPanicMessageWithDecl(v___x_566_, v___x_567_, v___x_568_, v___x_569_, v___x_574_);
lean_dec_ref(v___x_574_);
v___x_576_ = l_panic___redArg(v_this_565_, v___x_575_);
return v___x_576_;
}
else
{
lean_object* v_e_577_; lean_object* v_xs_x27_578_; lean_object* v___x_579_; 
v_e_577_ = lean_array_fget(v_xs_560_, v_i_561_);
v_xs_x27_578_ = lean_array_fset(v_xs_560_, v_i_561_, v_v_562_);
lean_dec(v_i_561_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_e_577_);
lean_ctor_set(v___x_579_, 1, v_xs_x27_578_);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
lean_object* v_zero_582_; uint8_t v_isZero_583_; 
v_zero_582_ = lean_unsigned_to_nat(0u);
v_isZero_583_ = lean_nat_dec_eq(v_x_580_, v_zero_582_);
if (v_isZero_583_ == 1)
{
lean_dec(v_x_580_);
return v_x_581_;
}
else
{
lean_object* v_one_584_; lean_object* v_n_585_; lean_object* v___x_586_; 
v_one_584_ = lean_unsigned_to_nat(1u);
v_n_585_ = lean_nat_sub(v_x_580_, v_one_584_);
lean_dec(v_x_580_);
v___x_586_ = lean_array_pop(v_x_581_);
v_x_580_ = v_n_585_;
v_x_581_ = v___x_586_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_shrink_loop(lean_object* v_00_u03b1_588_, lean_object* v_x_589_, lean_object* v_x_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(v_x_589_, v_x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___redArg(lean_object* v_xs_592_, lean_object* v_n_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = lean_array_get_size(v_xs_592_);
v___x_595_ = lean_nat_sub(v___x_594_, v_n_593_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_shrink_loop___redArg(v___x_595_, v_xs_592_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___redArg___boxed(lean_object* v_xs_597_, lean_object* v_n_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Array_shrink___redArg(v_xs_597_, v_n_598_);
lean_dec(v_n_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink(lean_object* v_00_u03b1_600_, lean_object* v_xs_601_, lean_object* v_n_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Array_shrink___redArg(v_xs_601_, v_n_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___boxed(lean_object* v_00_u03b1_604_, lean_object* v_xs_605_, lean_object* v_n_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Array_shrink(v_00_u03b1_604_, v_xs_605_, v_n_606_);
lean_dec(v_n_606_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Array_take___redArg(lean_object* v_xs_608_, lean_object* v_i_609_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = l_Array_extract___redArg(v_xs_608_, v___x_610_, v_i_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Array_take___redArg___boxed(lean_object* v_xs_612_, lean_object* v_i_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Array_take___redArg(v_xs_612_, v_i_613_);
lean_dec_ref(v_xs_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Array_take(lean_object* v_00_u03b1_615_, lean_object* v_xs_616_, lean_object* v_i_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = l_Array_extract___redArg(v_xs_616_, v___x_618_, v_i_617_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Array_take___boxed(lean_object* v_00_u03b1_620_, lean_object* v_xs_621_, lean_object* v_i_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Array_take(v_00_u03b1_620_, v_xs_621_, v_i_622_);
lean_dec_ref(v_xs_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___redArg(lean_object* v_xs_624_, lean_object* v_i_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_array_get_size(v_xs_624_);
v___x_627_ = l_Array_extract___redArg(v_xs_624_, v_i_625_, v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___redArg___boxed(lean_object* v_xs_628_, lean_object* v_i_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Array_drop___redArg(v_xs_628_, v_i_629_);
lean_dec_ref(v_xs_628_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Array_drop(lean_object* v_00_u03b1_631_, lean_object* v_xs_632_, lean_object* v_i_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_array_get_size(v_xs_632_);
v___x_635_ = l_Array_extract___redArg(v_xs_632_, v_i_633_, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Array_drop___boxed(lean_object* v_00_u03b1_636_, lean_object* v_xs_637_, lean_object* v_i_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Array_drop(v_00_u03b1_636_, v_xs_637_, v_i_638_);
lean_dec_ref(v_xs_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0(lean_object* v_toApplicative_640_, lean_object* v_xs_x27_641_, lean_object* v_i_642_, lean_object* v_v_643_){
_start:
{
lean_object* v_toPure_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v_toPure_644_ = lean_ctor_get(v_toApplicative_640_, 1);
lean_inc(v_toPure_644_);
lean_dec_ref(v_toApplicative_640_);
v___x_645_ = lean_array_fset(v_xs_x27_641_, v_i_642_, v_v_643_);
v___x_646_ = lean_apply_2(v_toPure_644_, lean_box(0), v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg___lam__0___boxed(lean_object* v_toApplicative_647_, lean_object* v_xs_x27_648_, lean_object* v_i_649_, lean_object* v_v_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Array_modifyMUnsafe___redArg___lam__0(v_toApplicative_647_, v_xs_x27_648_, v_i_649_, v_v_650_);
lean_dec(v_i_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___redArg(lean_object* v_inst_652_, lean_object* v_xs_653_, lean_object* v_i_654_, lean_object* v_f_655_){
_start:
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = lean_array_get_size(v_xs_653_);
v___x_657_ = lean_nat_dec_lt(v_i_654_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v_toApplicative_658_; lean_object* v_toPure_659_; lean_object* v___x_660_; 
lean_dec(v_f_655_);
lean_dec(v_i_654_);
v_toApplicative_658_ = lean_ctor_get(v_inst_652_, 0);
lean_inc_ref(v_toApplicative_658_);
lean_dec_ref(v_inst_652_);
v_toPure_659_ = lean_ctor_get(v_toApplicative_658_, 1);
lean_inc(v_toPure_659_);
lean_dec_ref(v_toApplicative_658_);
v___x_660_ = lean_apply_2(v_toPure_659_, lean_box(0), v_xs_653_);
return v___x_660_;
}
else
{
lean_object* v_toApplicative_661_; lean_object* v_toBind_662_; lean_object* v_v_663_; lean_object* v___x_664_; lean_object* v_xs_x27_665_; lean_object* v___f_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_toApplicative_661_ = lean_ctor_get(v_inst_652_, 0);
lean_inc_ref(v_toApplicative_661_);
v_toBind_662_ = lean_ctor_get(v_inst_652_, 1);
lean_inc(v_toBind_662_);
lean_dec_ref(v_inst_652_);
v_v_663_ = lean_array_fget(v_xs_653_, v_i_654_);
v___x_664_ = lean_box(0);
v_xs_x27_665_ = lean_array_fset(v_xs_653_, v_i_654_, v___x_664_);
v___f_666_ = lean_alloc_closure((void*)(l_Array_modifyMUnsafe___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_666_, 0, v_toApplicative_661_);
lean_closure_set(v___f_666_, 1, v_xs_x27_665_);
lean_closure_set(v___f_666_, 2, v_i_654_);
v___x_667_ = lean_apply_1(v_f_655_, v_v_663_);
v___x_668_ = lean_apply_4(v_toBind_662_, lean_box(0), lean_box(0), v___x_667_, v___f_666_);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe(lean_object* v_00_u03b1_669_, lean_object* v_m_670_, lean_object* v_inst_671_, lean_object* v_xs_672_, lean_object* v_i_673_, lean_object* v_f_674_){
_start:
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_array_get_size(v_xs_672_);
v___x_676_ = lean_nat_dec_lt(v_i_673_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v_toApplicative_677_; lean_object* v_toPure_678_; lean_object* v___x_679_; 
lean_dec(v_f_674_);
lean_dec(v_i_673_);
v_toApplicative_677_ = lean_ctor_get(v_inst_671_, 0);
lean_inc_ref(v_toApplicative_677_);
lean_dec_ref(v_inst_671_);
v_toPure_678_ = lean_ctor_get(v_toApplicative_677_, 1);
lean_inc(v_toPure_678_);
lean_dec_ref(v_toApplicative_677_);
v___x_679_ = lean_apply_2(v_toPure_678_, lean_box(0), v_xs_672_);
return v___x_679_;
}
else
{
lean_object* v_toApplicative_680_; lean_object* v_toBind_681_; lean_object* v_v_682_; lean_object* v___x_683_; lean_object* v_xs_x27_684_; lean_object* v___f_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_toApplicative_680_ = lean_ctor_get(v_inst_671_, 0);
lean_inc_ref(v_toApplicative_680_);
v_toBind_681_ = lean_ctor_get(v_inst_671_, 1);
lean_inc(v_toBind_681_);
lean_dec_ref(v_inst_671_);
v_v_682_ = lean_array_fget(v_xs_672_, v_i_673_);
v___x_683_ = lean_box(0);
v_xs_x27_684_ = lean_array_fset(v_xs_672_, v_i_673_, v___x_683_);
v___f_685_ = lean_alloc_closure((void*)(l_Array_modifyMUnsafe___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_685_, 0, v_toApplicative_680_);
lean_closure_set(v___f_685_, 1, v_xs_x27_684_);
lean_closure_set(v___f_685_, 2, v_i_673_);
v___x_686_ = lean_apply_1(v_f_674_, v_v_682_);
v___x_687_ = lean_apply_4(v_toBind_681_, lean_box(0), lean_box(0), v___x_686_, v___f_685_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___redArg(lean_object* v_xs_688_, lean_object* v_i_689_, lean_object* v_f_690_){
_start:
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = lean_array_get_size(v_xs_688_);
v___x_692_ = lean_nat_dec_lt(v_i_689_, v___x_691_);
if (v___x_692_ == 0)
{
lean_dec(v_f_690_);
return v_xs_688_;
}
else
{
lean_object* v_v_693_; lean_object* v___x_694_; lean_object* v_xs_x27_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_v_693_ = lean_array_fget(v_xs_688_, v_i_689_);
v___x_694_ = lean_box(0);
v_xs_x27_695_ = lean_array_fset(v_xs_688_, v_i_689_, v___x_694_);
v___x_696_ = lean_apply_1(v_f_690_, v_v_693_);
v___x_697_ = lean_array_fset(v_xs_x27_695_, v_i_689_, v___x_696_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___redArg___boxed(lean_object* v_xs_698_, lean_object* v_i_699_, lean_object* v_f_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Array_modify___redArg(v_xs_698_, v_i_699_, v_f_700_);
lean_dec(v_i_699_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Array_modify(lean_object* v_00_u03b1_702_, lean_object* v_xs_703_, lean_object* v_i_704_, lean_object* v_f_705_){
_start:
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_array_get_size(v_xs_703_);
v___x_707_ = lean_nat_dec_lt(v_i_704_, v___x_706_);
if (v___x_707_ == 0)
{
lean_dec(v_f_705_);
return v_xs_703_;
}
else
{
lean_object* v_v_708_; lean_object* v___x_709_; lean_object* v_xs_x27_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_v_708_ = lean_array_fget(v_xs_703_, v_i_704_);
v___x_709_ = lean_box(0);
v_xs_x27_710_ = lean_array_fset(v_xs_703_, v_i_704_, v___x_709_);
v___x_711_ = lean_apply_1(v_f_705_, v_v_708_);
v___x_712_ = lean_array_fset(v_xs_x27_710_, v_i_704_, v___x_711_);
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify___boxed(lean_object* v_00_u03b1_713_, lean_object* v_xs_714_, lean_object* v_i_715_, lean_object* v_f_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Array_modify(v_00_u03b1_713_, v_xs_714_, v_i_715_, v_f_716_);
lean_dec(v_i_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg(lean_object* v_xs_718_, lean_object* v_idx_719_, lean_object* v_f_720_){
_start:
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = lean_array_get_size(v_xs_718_);
v___x_722_ = lean_nat_dec_lt(v_idx_719_, v___x_721_);
if (v___x_722_ == 0)
{
lean_dec(v_f_720_);
return v_xs_718_;
}
else
{
lean_object* v_v_723_; lean_object* v___x_724_; lean_object* v_xs_x27_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v_v_723_ = lean_array_fget(v_xs_718_, v_idx_719_);
v___x_724_ = lean_box(0);
v_xs_x27_725_ = lean_array_fset(v_xs_718_, v_idx_719_, v___x_724_);
v___x_726_ = lean_apply_1(v_f_720_, v_v_723_);
v___x_727_ = lean_array_fset(v_xs_x27_725_, v_idx_719_, v___x_726_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___redArg___boxed(lean_object* v_xs_728_, lean_object* v_idx_729_, lean_object* v_f_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Array_modifyOp___redArg(v_xs_728_, v_idx_729_, v_f_730_);
lean_dec(v_idx_729_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp(lean_object* v_00_u03b1_732_, lean_object* v_xs_733_, lean_object* v_idx_734_, lean_object* v_f_735_){
_start:
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_array_get_size(v_xs_733_);
v___x_737_ = lean_nat_dec_lt(v_idx_734_, v___x_736_);
if (v___x_737_ == 0)
{
lean_dec(v_f_735_);
return v_xs_733_;
}
else
{
lean_object* v_v_738_; lean_object* v___x_739_; lean_object* v_xs_x27_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_v_738_ = lean_array_fget(v_xs_733_, v_idx_734_);
v___x_739_ = lean_box(0);
v_xs_x27_740_ = lean_array_fset(v_xs_733_, v_idx_734_, v___x_739_);
v___x_741_ = lean_apply_1(v_f_735_, v_v_738_);
v___x_742_ = lean_array_fset(v_xs_x27_740_, v_idx_734_, v___x_741_);
return v___x_742_;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___boxed(lean_object* v_00_u03b1_743_, lean_object* v_xs_744_, lean_object* v_idx_745_, lean_object* v_f_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Array_modifyOp(v_00_u03b1_743_, v_xs_744_, v_idx_745_, v_f_746_);
lean_dec(v_idx_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed(lean_object* v_toApplicative_748_, lean_object* v_i_749_, lean_object* v_inst_750_, lean_object* v_as_751_, lean_object* v_f_752_, lean_object* v_sz_753_, lean_object* v_____do__lift_754_){
_start:
{
size_t v_i_boxed_755_; size_t v_sz_boxed_756_; lean_object* v_res_757_; 
v_i_boxed_755_ = lean_unbox_usize(v_i_749_);
lean_dec(v_i_749_);
v_sz_boxed_756_ = lean_unbox_usize(v_sz_753_);
lean_dec(v_sz_753_);
v_res_757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(v_toApplicative_748_, v_i_boxed_755_, v_inst_750_, v_as_751_, v_f_752_, v_sz_boxed_756_, v_____do__lift_754_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(lean_object* v_inst_758_, lean_object* v_as_759_, lean_object* v_f_760_, size_t v_sz_761_, size_t v_i_762_, lean_object* v_b_763_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = lean_usize_dec_lt(v_i_762_, v_sz_761_);
if (v___x_764_ == 0)
{
lean_object* v_toApplicative_765_; lean_object* v_toPure_766_; lean_object* v___x_767_; 
lean_dec(v_f_760_);
lean_dec_ref(v_as_759_);
v_toApplicative_765_ = lean_ctor_get(v_inst_758_, 0);
lean_inc_ref(v_toApplicative_765_);
lean_dec_ref(v_inst_758_);
v_toPure_766_ = lean_ctor_get(v_toApplicative_765_, 1);
lean_inc(v_toPure_766_);
lean_dec_ref(v_toApplicative_765_);
v___x_767_ = lean_apply_2(v_toPure_766_, lean_box(0), v_b_763_);
return v___x_767_;
}
else
{
lean_object* v_toApplicative_768_; lean_object* v_toBind_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___f_772_; lean_object* v_a_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_toApplicative_768_ = lean_ctor_get(v_inst_758_, 0);
lean_inc_ref(v_toApplicative_768_);
v_toBind_769_ = lean_ctor_get(v_inst_758_, 1);
lean_inc(v_toBind_769_);
v___x_770_ = lean_box_usize(v_i_762_);
v___x_771_ = lean_box_usize(v_sz_761_);
lean_inc(v_f_760_);
lean_inc_ref(v_as_759_);
v___f_772_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_772_, 0, v_toApplicative_768_);
lean_closure_set(v___f_772_, 1, v___x_770_);
lean_closure_set(v___f_772_, 2, v_inst_758_);
lean_closure_set(v___f_772_, 3, v_as_759_);
lean_closure_set(v___f_772_, 4, v_f_760_);
lean_closure_set(v___f_772_, 5, v___x_771_);
v_a_773_ = lean_array_uget(v_as_759_, v_i_762_);
lean_dec_ref(v_as_759_);
v___x_774_ = lean_apply_3(v_f_760_, v_a_773_, lean_box(0), v_b_763_);
v___x_775_ = lean_apply_4(v_toBind_769_, lean_box(0), lean_box(0), v___x_774_, v___f_772_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___lam__0(lean_object* v_toApplicative_776_, size_t v_i_777_, lean_object* v_inst_778_, lean_object* v_as_779_, lean_object* v_f_780_, size_t v_sz_781_, lean_object* v_____do__lift_782_){
_start:
{
if (lean_obj_tag(v_____do__lift_782_) == 0)
{
lean_object* v_a_783_; lean_object* v_toPure_784_; lean_object* v___x_785_; 
lean_dec(v_f_780_);
lean_dec_ref(v_as_779_);
lean_dec_ref(v_inst_778_);
v_a_783_ = lean_ctor_get(v_____do__lift_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref(v_____do__lift_782_);
v_toPure_784_ = lean_ctor_get(v_toApplicative_776_, 1);
lean_inc(v_toPure_784_);
lean_dec_ref(v_toApplicative_776_);
v___x_785_ = lean_apply_2(v_toPure_784_, lean_box(0), v_a_783_);
return v___x_785_;
}
else
{
lean_object* v_a_786_; size_t v___x_787_; size_t v___x_788_; lean_object* v___x_789_; 
lean_dec_ref(v_toApplicative_776_);
v_a_786_ = lean_ctor_get(v_____do__lift_782_, 0);
lean_inc(v_a_786_);
lean_dec_ref(v_____do__lift_782_);
v___x_787_ = ((size_t)1ULL);
v___x_788_ = lean_usize_add(v_i_777_, v___x_787_);
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_778_, v_as_779_, v_f_780_, v_sz_781_, v___x_788_, v_a_786_);
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg___boxed(lean_object* v_inst_790_, lean_object* v_as_791_, lean_object* v_f_792_, lean_object* v_sz_793_, lean_object* v_i_794_, lean_object* v_b_795_){
_start:
{
size_t v_sz_boxed_796_; size_t v_i_boxed_797_; lean_object* v_res_798_; 
v_sz_boxed_796_ = lean_unbox_usize(v_sz_793_);
lean_dec(v_sz_793_);
v_i_boxed_797_ = lean_unbox_usize(v_i_794_);
lean_dec(v_i_794_);
v_res_798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_790_, v_as_791_, v_f_792_, v_sz_boxed_796_, v_i_boxed_797_, v_b_795_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object* v_00_u03b1_799_, lean_object* v_00_u03b2_800_, lean_object* v_m_801_, lean_object* v_inst_802_, lean_object* v_as_803_, lean_object* v_f_804_, size_t v_sz_805_, size_t v_i_806_, lean_object* v_b_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_802_, v_as_803_, v_f_804_, v_sz_805_, v_i_806_, v_b_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___boxed(lean_object* v_00_u03b1_809_, lean_object* v_00_u03b2_810_, lean_object* v_m_811_, lean_object* v_inst_812_, lean_object* v_as_813_, lean_object* v_f_814_, lean_object* v_sz_815_, lean_object* v_i_816_, lean_object* v_b_817_){
_start:
{
size_t v_sz_boxed_818_; size_t v_i_boxed_819_; lean_object* v_res_820_; 
v_sz_boxed_818_ = lean_unbox_usize(v_sz_815_);
lean_dec(v_sz_815_);
v_i_boxed_819_ = lean_unbox_usize(v_i_816_);
lean_dec(v_i_816_);
v_res_820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(v_00_u03b1_809_, v_00_u03b2_810_, v_m_811_, v_inst_812_, v_as_813_, v_f_814_, v_sz_boxed_818_, v_i_boxed_819_, v_b_817_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe___redArg(lean_object* v_inst_821_, lean_object* v_as_822_, lean_object* v_b_823_, lean_object* v_f_824_){
_start:
{
size_t v_sz_825_; size_t v___x_826_; lean_object* v___x_827_; 
v_sz_825_ = lean_array_size(v_as_822_);
v___x_826_ = ((size_t)0ULL);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_821_, v_as_822_, v_f_824_, v_sz_825_, v___x_826_, v_b_823_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe(lean_object* v_00_u03b1_828_, lean_object* v_00_u03b2_829_, lean_object* v_m_830_, lean_object* v_inst_831_, lean_object* v_as_832_, lean_object* v_b_833_, lean_object* v_f_834_){
_start:
{
size_t v_sz_835_; size_t v___x_836_; lean_object* v___x_837_; 
v_sz_835_ = lean_array_size(v_as_832_);
v___x_836_ = ((size_t)0ULL);
v___x_837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_831_, v_as_832_, v_f_834_, v_sz_835_, v___x_836_, v_b_833_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0___boxed(lean_object* v_toPure_838_, lean_object* v_inst_839_, lean_object* v_as_840_, lean_object* v_f_841_, lean_object* v_n_842_, lean_object* v_____do__lift_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Array_forIn_x27_loop___redArg___lam__0(v_toPure_838_, v_inst_839_, v_as_840_, v_f_841_, v_n_842_, v_____do__lift_843_);
lean_dec(v_n_842_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg(lean_object* v_inst_845_, lean_object* v_as_846_, lean_object* v_f_847_, lean_object* v_i_848_, lean_object* v_b_849_){
_start:
{
lean_object* v_toApplicative_850_; lean_object* v_toBind_851_; lean_object* v_toPure_852_; lean_object* v_zero_853_; uint8_t v_isZero_854_; 
v_toApplicative_850_ = lean_ctor_get(v_inst_845_, 0);
v_toBind_851_ = lean_ctor_get(v_inst_845_, 1);
lean_inc(v_toBind_851_);
v_toPure_852_ = lean_ctor_get(v_toApplicative_850_, 1);
lean_inc(v_toPure_852_);
v_zero_853_ = lean_unsigned_to_nat(0u);
v_isZero_854_ = lean_nat_dec_eq(v_i_848_, v_zero_853_);
if (v_isZero_854_ == 1)
{
lean_object* v___x_855_; 
lean_dec(v_toBind_851_);
lean_dec(v_f_847_);
lean_dec_ref(v_as_846_);
lean_dec_ref(v_inst_845_);
v___x_855_ = lean_apply_2(v_toPure_852_, lean_box(0), v_b_849_);
return v___x_855_;
}
else
{
lean_object* v_one_856_; lean_object* v_n_857_; lean_object* v___f_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_one_856_ = lean_unsigned_to_nat(1u);
v_n_857_ = lean_nat_sub(v_i_848_, v_one_856_);
lean_inc(v_n_857_);
lean_inc(v_f_847_);
lean_inc_ref(v_as_846_);
v___f_858_ = lean_alloc_closure((void*)(l_Array_forIn_x27_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_858_, 0, v_toPure_852_);
lean_closure_set(v___f_858_, 1, v_inst_845_);
lean_closure_set(v___f_858_, 2, v_as_846_);
lean_closure_set(v___f_858_, 3, v_f_847_);
lean_closure_set(v___f_858_, 4, v_n_857_);
v___x_859_ = lean_array_get_size(v_as_846_);
v___x_860_ = lean_nat_sub(v___x_859_, v_one_856_);
v___x_861_ = lean_nat_sub(v___x_860_, v_n_857_);
lean_dec(v_n_857_);
lean_dec(v___x_860_);
v___x_862_ = lean_array_fget(v_as_846_, v___x_861_);
lean_dec(v___x_861_);
lean_dec_ref(v_as_846_);
v___x_863_ = lean_apply_3(v_f_847_, v___x_862_, lean_box(0), v_b_849_);
v___x_864_ = lean_apply_4(v_toBind_851_, lean_box(0), lean_box(0), v___x_863_, v___f_858_);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___lam__0(lean_object* v_toPure_865_, lean_object* v_inst_866_, lean_object* v_as_867_, lean_object* v_f_868_, lean_object* v_n_869_, lean_object* v_____do__lift_870_){
_start:
{
if (lean_obj_tag(v_____do__lift_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_872_; 
lean_dec(v_f_868_);
lean_dec_ref(v_as_867_);
lean_dec_ref(v_inst_866_);
v_a_871_ = lean_ctor_get(v_____do__lift_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref(v_____do__lift_870_);
v___x_872_ = lean_apply_2(v_toPure_865_, lean_box(0), v_a_871_);
return v___x_872_;
}
else
{
lean_object* v_a_873_; lean_object* v___x_874_; 
lean_dec(v_toPure_865_);
v_a_873_ = lean_ctor_get(v_____do__lift_870_, 0);
lean_inc(v_a_873_);
lean_dec_ref(v_____do__lift_870_);
v___x_874_ = l_Array_forIn_x27_loop___redArg(v_inst_866_, v_as_867_, v_f_868_, v_n_869_, v_a_873_);
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___redArg___boxed(lean_object* v_inst_875_, lean_object* v_as_876_, lean_object* v_f_877_, lean_object* v_i_878_, lean_object* v_b_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Array_forIn_x27_loop___redArg(v_inst_875_, v_as_876_, v_f_877_, v_i_878_, v_b_879_);
lean_dec(v_i_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_m_883_, lean_object* v_inst_884_, lean_object* v_as_885_, lean_object* v_f_886_, lean_object* v_i_887_, lean_object* v_h_888_, lean_object* v_b_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Array_forIn_x27_loop___redArg(v_inst_884_, v_as_885_, v_f_886_, v_i_887_, v_b_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___boxed(lean_object* v_00_u03b1_891_, lean_object* v_00_u03b2_892_, lean_object* v_m_893_, lean_object* v_inst_894_, lean_object* v_as_895_, lean_object* v_f_896_, lean_object* v_i_897_, lean_object* v_h_898_, lean_object* v_b_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Array_forIn_x27_loop(v_00_u03b1_891_, v_00_u03b2_892_, v_m_893_, v_inst_894_, v_as_895_, v_f_896_, v_i_897_, v_h_898_, v_b_899_);
lean_dec(v_i_897_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_inst_901_, lean_object* v_00_u03b2_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
size_t v_sz_906_; size_t v___x_907_; lean_object* v___x_908_; 
v_sz_906_ = lean_array_size(v___y_903_);
v___x_907_ = ((size_t)0ULL);
v___x_908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_901_, v___y_903_, v___y_905_, v_sz_906_, v___x_907_, v___y_904_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_909_){
_start:
{
lean_object* v___f_910_; 
v___f_910_ = lean_alloc_closure((void*)(l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_910_, 0, v_inst_909_);
return v___f_910_;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_00_u03b1_911_, lean_object* v_m_912_, lean_object* v_inst_913_){
_start:
{
lean_object* v___f_914_; 
v___f_914_ = lean_alloc_closure((void*)(l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_914_, 0, v_inst_913_);
return v___f_914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_i_915_, lean_object* v_inst_916_, lean_object* v_f_917_, lean_object* v_as_918_, lean_object* v_stop_919_, lean_object* v_____do__lift_920_){
_start:
{
size_t v_i_boxed_921_; size_t v_stop_boxed_922_; lean_object* v_res_923_; 
v_i_boxed_921_ = lean_unbox_usize(v_i_915_);
lean_dec(v_i_915_);
v_stop_boxed_922_ = lean_unbox_usize(v_stop_919_);
lean_dec(v_stop_919_);
v_res_923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(v_i_boxed_921_, v_inst_916_, v_f_917_, v_as_918_, v_stop_boxed_922_, v_____do__lift_920_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(lean_object* v_inst_924_, lean_object* v_f_925_, lean_object* v_as_926_, size_t v_i_927_, size_t v_stop_928_, lean_object* v_b_929_){
_start:
{
uint8_t v___x_930_; 
v___x_930_ = lean_usize_dec_eq(v_i_927_, v_stop_928_);
if (v___x_930_ == 0)
{
lean_object* v_toBind_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___f_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_toBind_931_ = lean_ctor_get(v_inst_924_, 1);
lean_inc(v_toBind_931_);
v___x_932_ = lean_box_usize(v_i_927_);
v___x_933_ = lean_box_usize(v_stop_928_);
lean_inc_ref(v_as_926_);
lean_inc(v_f_925_);
v___f_934_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_934_, 0, v___x_932_);
lean_closure_set(v___f_934_, 1, v_inst_924_);
lean_closure_set(v___f_934_, 2, v_f_925_);
lean_closure_set(v___f_934_, 3, v_as_926_);
lean_closure_set(v___f_934_, 4, v___x_933_);
v___x_935_ = lean_array_uget(v_as_926_, v_i_927_);
lean_dec_ref(v_as_926_);
v___x_936_ = lean_apply_2(v_f_925_, v_b_929_, v___x_935_);
v___x_937_ = lean_apply_4(v_toBind_931_, lean_box(0), lean_box(0), v___x_936_, v___f_934_);
return v___x_937_;
}
else
{
lean_object* v_toApplicative_938_; lean_object* v_toPure_939_; lean_object* v___x_940_; 
lean_dec_ref(v_as_926_);
lean_dec(v_f_925_);
v_toApplicative_938_ = lean_ctor_get(v_inst_924_, 0);
lean_inc_ref(v_toApplicative_938_);
lean_dec_ref(v_inst_924_);
v_toPure_939_ = lean_ctor_get(v_toApplicative_938_, 1);
lean_inc(v_toPure_939_);
lean_dec_ref(v_toApplicative_938_);
v___x_940_ = lean_apply_2(v_toPure_939_, lean_box(0), v_b_929_);
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___lam__0(size_t v_i_941_, lean_object* v_inst_942_, lean_object* v_f_943_, lean_object* v_as_944_, size_t v_stop_945_, lean_object* v_____do__lift_946_){
_start:
{
size_t v___x_947_; size_t v___x_948_; lean_object* v___x_949_; 
v___x_947_ = ((size_t)1ULL);
v___x_948_ = lean_usize_add(v_i_941_, v___x_947_);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_942_, v_f_943_, v_as_944_, v___x_948_, v_stop_945_, v_____do__lift_946_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg___boxed(lean_object* v_inst_950_, lean_object* v_f_951_, lean_object* v_as_952_, lean_object* v_i_953_, lean_object* v_stop_954_, lean_object* v_b_955_){
_start:
{
size_t v_i_boxed_956_; size_t v_stop_boxed_957_; lean_object* v_res_958_; 
v_i_boxed_956_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_stop_boxed_957_ = lean_unbox_usize(v_stop_954_);
lean_dec(v_stop_954_);
v_res_958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_950_, v_f_951_, v_as_952_, v_i_boxed_956_, v_stop_boxed_957_, v_b_955_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object* v_00_u03b1_959_, lean_object* v_00_u03b2_960_, lean_object* v_m_961_, lean_object* v_inst_962_, lean_object* v_f_963_, lean_object* v_as_964_, size_t v_i_965_, size_t v_stop_966_, lean_object* v_b_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_962_, v_f_963_, v_as_964_, v_i_965_, v_stop_966_, v_b_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___boxed(lean_object* v_00_u03b1_969_, lean_object* v_00_u03b2_970_, lean_object* v_m_971_, lean_object* v_inst_972_, lean_object* v_f_973_, lean_object* v_as_974_, lean_object* v_i_975_, lean_object* v_stop_976_, lean_object* v_b_977_){
_start:
{
size_t v_i_boxed_978_; size_t v_stop_boxed_979_; lean_object* v_res_980_; 
v_i_boxed_978_ = lean_unbox_usize(v_i_975_);
lean_dec(v_i_975_);
v_stop_boxed_979_ = lean_unbox_usize(v_stop_976_);
lean_dec(v_stop_976_);
v_res_980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(v_00_u03b1_969_, v_00_u03b2_970_, v_m_971_, v_inst_972_, v_f_973_, v_as_974_, v_i_boxed_978_, v_stop_boxed_979_, v_b_977_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg(lean_object* v_inst_981_, lean_object* v_f_982_, lean_object* v_init_983_, lean_object* v_as_984_, lean_object* v_start_985_, lean_object* v_stop_986_){
_start:
{
uint8_t v___x_987_; 
v___x_987_ = lean_nat_dec_lt(v_start_985_, v_stop_986_);
if (v___x_987_ == 0)
{
lean_object* v_toApplicative_988_; lean_object* v_toPure_989_; lean_object* v___x_990_; 
lean_dec_ref(v_as_984_);
lean_dec(v_f_982_);
v_toApplicative_988_ = lean_ctor_get(v_inst_981_, 0);
lean_inc_ref(v_toApplicative_988_);
lean_dec_ref(v_inst_981_);
v_toPure_989_ = lean_ctor_get(v_toApplicative_988_, 1);
lean_inc(v_toPure_989_);
lean_dec_ref(v_toApplicative_988_);
v___x_990_ = lean_apply_2(v_toPure_989_, lean_box(0), v_init_983_);
return v___x_990_;
}
else
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = lean_array_get_size(v_as_984_);
v___x_992_ = lean_nat_dec_le(v_stop_986_, v___x_991_);
if (v___x_992_ == 0)
{
uint8_t v___x_993_; 
v___x_993_ = lean_nat_dec_lt(v_start_985_, v___x_991_);
if (v___x_993_ == 0)
{
lean_object* v_toApplicative_994_; lean_object* v_toPure_995_; lean_object* v___x_996_; 
lean_dec_ref(v_as_984_);
lean_dec(v_f_982_);
v_toApplicative_994_ = lean_ctor_get(v_inst_981_, 0);
lean_inc_ref(v_toApplicative_994_);
lean_dec_ref(v_inst_981_);
v_toPure_995_ = lean_ctor_get(v_toApplicative_994_, 1);
lean_inc(v_toPure_995_);
lean_dec_ref(v_toApplicative_994_);
v___x_996_ = lean_apply_2(v_toPure_995_, lean_box(0), v_init_983_);
return v___x_996_;
}
else
{
size_t v___x_997_; size_t v___x_998_; lean_object* v___x_999_; 
v___x_997_ = lean_usize_of_nat(v_start_985_);
v___x_998_ = lean_usize_of_nat(v___x_991_);
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_981_, v_f_982_, v_as_984_, v___x_997_, v___x_998_, v_init_983_);
return v___x_999_;
}
}
else
{
size_t v___x_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_usize_of_nat(v_start_985_);
v___x_1001_ = lean_usize_of_nat(v_stop_986_);
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_981_, v_f_982_, v_as_984_, v___x_1000_, v___x_1001_, v_init_983_);
return v___x_1002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___redArg___boxed(lean_object* v_inst_1003_, lean_object* v_f_1004_, lean_object* v_init_1005_, lean_object* v_as_1006_, lean_object* v_start_1007_, lean_object* v_stop_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Array_foldlMUnsafe___redArg(v_inst_1003_, v_f_1004_, v_init_1005_, v_as_1006_, v_start_1007_, v_stop_1008_);
lean_dec(v_stop_1008_);
lean_dec(v_start_1007_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe(lean_object* v_00_u03b1_1010_, lean_object* v_00_u03b2_1011_, lean_object* v_m_1012_, lean_object* v_inst_1013_, lean_object* v_f_1014_, lean_object* v_init_1015_, lean_object* v_as_1016_, lean_object* v_start_1017_, lean_object* v_stop_1018_){
_start:
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_nat_dec_lt(v_start_1017_, v_stop_1018_);
if (v___x_1019_ == 0)
{
lean_object* v_toApplicative_1020_; lean_object* v_toPure_1021_; lean_object* v___x_1022_; 
lean_dec_ref(v_as_1016_);
lean_dec(v_f_1014_);
v_toApplicative_1020_ = lean_ctor_get(v_inst_1013_, 0);
lean_inc_ref(v_toApplicative_1020_);
lean_dec_ref(v_inst_1013_);
v_toPure_1021_ = lean_ctor_get(v_toApplicative_1020_, 1);
lean_inc(v_toPure_1021_);
lean_dec_ref(v_toApplicative_1020_);
v___x_1022_ = lean_apply_2(v_toPure_1021_, lean_box(0), v_init_1015_);
return v___x_1022_;
}
else
{
lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = lean_array_get_size(v_as_1016_);
v___x_1024_ = lean_nat_dec_le(v_stop_1018_, v___x_1023_);
if (v___x_1024_ == 0)
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_nat_dec_lt(v_start_1017_, v___x_1023_);
if (v___x_1025_ == 0)
{
lean_object* v_toApplicative_1026_; lean_object* v_toPure_1027_; lean_object* v___x_1028_; 
lean_dec_ref(v_as_1016_);
lean_dec(v_f_1014_);
v_toApplicative_1026_ = lean_ctor_get(v_inst_1013_, 0);
lean_inc_ref(v_toApplicative_1026_);
lean_dec_ref(v_inst_1013_);
v_toPure_1027_ = lean_ctor_get(v_toApplicative_1026_, 1);
lean_inc(v_toPure_1027_);
lean_dec_ref(v_toApplicative_1026_);
v___x_1028_ = lean_apply_2(v_toPure_1027_, lean_box(0), v_init_1015_);
return v___x_1028_;
}
else
{
size_t v___x_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_usize_of_nat(v_start_1017_);
v___x_1030_ = lean_usize_of_nat(v___x_1023_);
v___x_1031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1013_, v_f_1014_, v_as_1016_, v___x_1029_, v___x_1030_, v_init_1015_);
return v___x_1031_;
}
}
else
{
size_t v___x_1032_; size_t v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = lean_usize_of_nat(v_start_1017_);
v___x_1033_ = lean_usize_of_nat(v_stop_1018_);
v___x_1034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_1013_, v_f_1014_, v_as_1016_, v___x_1032_, v___x_1033_, v_init_1015_);
return v___x_1034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___boxed(lean_object* v_00_u03b1_1035_, lean_object* v_00_u03b2_1036_, lean_object* v_m_1037_, lean_object* v_inst_1038_, lean_object* v_f_1039_, lean_object* v_init_1040_, lean_object* v_as_1041_, lean_object* v_start_1042_, lean_object* v_stop_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Array_foldlMUnsafe(v_00_u03b1_1035_, v_00_u03b2_1036_, v_m_1037_, v_inst_1038_, v_f_1039_, v_init_1040_, v_as_1041_, v_start_1042_, v_stop_1043_);
lean_dec(v_stop_1043_);
lean_dec(v_start_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0___boxed(lean_object* v_j_1045_, lean_object* v_inst_1046_, lean_object* v_f_1047_, lean_object* v_as_1048_, lean_object* v_stop_1049_, lean_object* v_n_1050_, lean_object* v_____do__lift_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Array_foldlM_loop___redArg___lam__0(v_j_1045_, v_inst_1046_, v_f_1047_, v_as_1048_, v_stop_1049_, v_n_1050_, v_____do__lift_1051_);
lean_dec(v_n_1050_);
lean_dec(v_j_1045_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg(lean_object* v_inst_1053_, lean_object* v_f_1054_, lean_object* v_as_1055_, lean_object* v_stop_1056_, lean_object* v_i_1057_, lean_object* v_j_1058_, lean_object* v_b_1059_){
_start:
{
uint8_t v___x_1060_; 
v___x_1060_ = lean_nat_dec_lt(v_j_1058_, v_stop_1056_);
if (v___x_1060_ == 0)
{
lean_object* v_toApplicative_1061_; lean_object* v_toPure_1062_; lean_object* v___x_1063_; 
lean_dec(v_j_1058_);
lean_dec(v_stop_1056_);
lean_dec_ref(v_as_1055_);
lean_dec(v_f_1054_);
v_toApplicative_1061_ = lean_ctor_get(v_inst_1053_, 0);
lean_inc_ref(v_toApplicative_1061_);
lean_dec_ref(v_inst_1053_);
v_toPure_1062_ = lean_ctor_get(v_toApplicative_1061_, 1);
lean_inc(v_toPure_1062_);
lean_dec_ref(v_toApplicative_1061_);
v___x_1063_ = lean_apply_2(v_toPure_1062_, lean_box(0), v_b_1059_);
return v___x_1063_;
}
else
{
lean_object* v_zero_1064_; uint8_t v_isZero_1065_; 
v_zero_1064_ = lean_unsigned_to_nat(0u);
v_isZero_1065_ = lean_nat_dec_eq(v_i_1057_, v_zero_1064_);
if (v_isZero_1065_ == 1)
{
lean_object* v_toApplicative_1066_; lean_object* v_toPure_1067_; lean_object* v___x_1068_; 
lean_dec(v_j_1058_);
lean_dec(v_stop_1056_);
lean_dec_ref(v_as_1055_);
lean_dec(v_f_1054_);
v_toApplicative_1066_ = lean_ctor_get(v_inst_1053_, 0);
lean_inc_ref(v_toApplicative_1066_);
lean_dec_ref(v_inst_1053_);
v_toPure_1067_ = lean_ctor_get(v_toApplicative_1066_, 1);
lean_inc(v_toPure_1067_);
lean_dec_ref(v_toApplicative_1066_);
v___x_1068_ = lean_apply_2(v_toPure_1067_, lean_box(0), v_b_1059_);
return v___x_1068_;
}
else
{
lean_object* v_toBind_1069_; lean_object* v_one_1070_; lean_object* v_n_1071_; lean_object* v___f_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_toBind_1069_ = lean_ctor_get(v_inst_1053_, 1);
lean_inc(v_toBind_1069_);
v_one_1070_ = lean_unsigned_to_nat(1u);
v_n_1071_ = lean_nat_sub(v_i_1057_, v_one_1070_);
lean_inc_ref(v_as_1055_);
lean_inc(v_f_1054_);
lean_inc(v_j_1058_);
v___f_1072_ = lean_alloc_closure((void*)(l_Array_foldlM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1072_, 0, v_j_1058_);
lean_closure_set(v___f_1072_, 1, v_inst_1053_);
lean_closure_set(v___f_1072_, 2, v_f_1054_);
lean_closure_set(v___f_1072_, 3, v_as_1055_);
lean_closure_set(v___f_1072_, 4, v_stop_1056_);
lean_closure_set(v___f_1072_, 5, v_n_1071_);
v___x_1073_ = lean_array_fget(v_as_1055_, v_j_1058_);
lean_dec(v_j_1058_);
lean_dec_ref(v_as_1055_);
v___x_1074_ = lean_apply_2(v_f_1054_, v_b_1059_, v___x_1073_);
v___x_1075_ = lean_apply_4(v_toBind_1069_, lean_box(0), lean_box(0), v___x_1074_, v___f_1072_);
return v___x_1075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___lam__0(lean_object* v_j_1076_, lean_object* v_inst_1077_, lean_object* v_f_1078_, lean_object* v_as_1079_, lean_object* v_stop_1080_, lean_object* v_n_1081_, lean_object* v_____do__lift_1082_){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1083_ = lean_unsigned_to_nat(1u);
v___x_1084_ = lean_nat_add(v_j_1076_, v___x_1083_);
v___x_1085_ = l_Array_foldlM_loop___redArg(v_inst_1077_, v_f_1078_, v_as_1079_, v_stop_1080_, v_n_1081_, v___x_1084_, v_____do__lift_1082_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___redArg___boxed(lean_object* v_inst_1086_, lean_object* v_f_1087_, lean_object* v_as_1088_, lean_object* v_stop_1089_, lean_object* v_i_1090_, lean_object* v_j_1091_, lean_object* v_b_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Array_foldlM_loop___redArg(v_inst_1086_, v_f_1087_, v_as_1088_, v_stop_1089_, v_i_1090_, v_j_1091_, v_b_1092_);
lean_dec(v_i_1090_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop(lean_object* v_00_u03b1_1094_, lean_object* v_00_u03b2_1095_, lean_object* v_m_1096_, lean_object* v_inst_1097_, lean_object* v_f_1098_, lean_object* v_as_1099_, lean_object* v_stop_1100_, lean_object* v_h_1101_, lean_object* v_i_1102_, lean_object* v_j_1103_, lean_object* v_b_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Array_foldlM_loop___redArg(v_inst_1097_, v_f_1098_, v_as_1099_, v_stop_1100_, v_i_1102_, v_j_1103_, v_b_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___boxed(lean_object* v_00_u03b1_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_m_1108_, lean_object* v_inst_1109_, lean_object* v_f_1110_, lean_object* v_as_1111_, lean_object* v_stop_1112_, lean_object* v_h_1113_, lean_object* v_i_1114_, lean_object* v_j_1115_, lean_object* v_b_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Array_foldlM_loop(v_00_u03b1_1106_, v_00_u03b2_1107_, v_m_1108_, v_inst_1109_, v_f_1110_, v_as_1111_, v_stop_1112_, v_h_1113_, v_i_1114_, v_j_1115_, v_b_1116_);
lean_dec(v_i_1114_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed(lean_object* v_inst_1118_, lean_object* v_f_1119_, lean_object* v_as_1120_, lean_object* v___x_1121_, lean_object* v_stop_1122_, lean_object* v_____do__lift_1123_){
_start:
{
size_t v___x_94__boxed_1124_; size_t v_stop_boxed_1125_; lean_object* v_res_1126_; 
v___x_94__boxed_1124_ = lean_unbox_usize(v___x_1121_);
lean_dec(v___x_1121_);
v_stop_boxed_1125_ = lean_unbox_usize(v_stop_1122_);
lean_dec(v_stop_1122_);
v_res_1126_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(v_inst_1118_, v_f_1119_, v_as_1120_, v___x_94__boxed_1124_, v_stop_boxed_1125_, v_____do__lift_1123_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(lean_object* v_inst_1127_, lean_object* v_f_1128_, lean_object* v_as_1129_, size_t v_i_1130_, size_t v_stop_1131_, lean_object* v_b_1132_){
_start:
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_usize_dec_eq(v_i_1130_, v_stop_1131_);
if (v___x_1133_ == 0)
{
lean_object* v_toBind_1134_; size_t v___x_1135_; size_t v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___f_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_toBind_1134_ = lean_ctor_get(v_inst_1127_, 1);
lean_inc(v_toBind_1134_);
v___x_1135_ = ((size_t)1ULL);
v___x_1136_ = lean_usize_sub(v_i_1130_, v___x_1135_);
v___x_1137_ = lean_box_usize(v___x_1136_);
v___x_1138_ = lean_box_usize(v_stop_1131_);
lean_inc_ref(v_as_1129_);
lean_inc(v_f_1128_);
v___f_1139_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1139_, 0, v_inst_1127_);
lean_closure_set(v___f_1139_, 1, v_f_1128_);
lean_closure_set(v___f_1139_, 2, v_as_1129_);
lean_closure_set(v___f_1139_, 3, v___x_1137_);
lean_closure_set(v___f_1139_, 4, v___x_1138_);
v___x_1140_ = lean_array_uget(v_as_1129_, v___x_1136_);
lean_dec_ref(v_as_1129_);
v___x_1141_ = lean_apply_2(v_f_1128_, v___x_1140_, v_b_1132_);
v___x_1142_ = lean_apply_4(v_toBind_1134_, lean_box(0), lean_box(0), v___x_1141_, v___f_1139_);
return v___x_1142_;
}
else
{
lean_object* v_toApplicative_1143_; lean_object* v_toPure_1144_; lean_object* v___x_1145_; 
lean_dec_ref(v_as_1129_);
lean_dec(v_f_1128_);
v_toApplicative_1143_ = lean_ctor_get(v_inst_1127_, 0);
lean_inc_ref(v_toApplicative_1143_);
lean_dec_ref(v_inst_1127_);
v_toPure_1144_ = lean_ctor_get(v_toApplicative_1143_, 1);
lean_inc(v_toPure_1144_);
lean_dec_ref(v_toApplicative_1143_);
v___x_1145_ = lean_apply_2(v_toPure_1144_, lean_box(0), v_b_1132_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___lam__0(lean_object* v_inst_1146_, lean_object* v_f_1147_, lean_object* v_as_1148_, size_t v___x_1149_, size_t v_stop_1150_, lean_object* v_____do__lift_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1146_, v_f_1147_, v_as_1148_, v___x_1149_, v_stop_1150_, v_____do__lift_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg___boxed(lean_object* v_inst_1153_, lean_object* v_f_1154_, lean_object* v_as_1155_, lean_object* v_i_1156_, lean_object* v_stop_1157_, lean_object* v_b_1158_){
_start:
{
size_t v_i_boxed_1159_; size_t v_stop_boxed_1160_; lean_object* v_res_1161_; 
v_i_boxed_1159_ = lean_unbox_usize(v_i_1156_);
lean_dec(v_i_1156_);
v_stop_boxed_1160_ = lean_unbox_usize(v_stop_1157_);
lean_dec(v_stop_1157_);
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1153_, v_f_1154_, v_as_1155_, v_i_boxed_1159_, v_stop_boxed_1160_, v_b_1158_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object* v_00_u03b1_1162_, lean_object* v_00_u03b2_1163_, lean_object* v_m_1164_, lean_object* v_inst_1165_, lean_object* v_f_1166_, lean_object* v_as_1167_, size_t v_i_1168_, size_t v_stop_1169_, lean_object* v_b_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1165_, v_f_1166_, v_as_1167_, v_i_1168_, v_stop_1169_, v_b_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___boxed(lean_object* v_00_u03b1_1172_, lean_object* v_00_u03b2_1173_, lean_object* v_m_1174_, lean_object* v_inst_1175_, lean_object* v_f_1176_, lean_object* v_as_1177_, lean_object* v_i_1178_, lean_object* v_stop_1179_, lean_object* v_b_1180_){
_start:
{
size_t v_i_boxed_1181_; size_t v_stop_boxed_1182_; lean_object* v_res_1183_; 
v_i_boxed_1181_ = lean_unbox_usize(v_i_1178_);
lean_dec(v_i_1178_);
v_stop_boxed_1182_ = lean_unbox_usize(v_stop_1179_);
lean_dec(v_stop_1179_);
v_res_1183_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(v_00_u03b1_1172_, v_00_u03b2_1173_, v_m_1174_, v_inst_1175_, v_f_1176_, v_as_1177_, v_i_boxed_1181_, v_stop_boxed_1182_, v_b_1180_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg(lean_object* v_inst_1184_, lean_object* v_f_1185_, lean_object* v_init_1186_, lean_object* v_as_1187_, lean_object* v_start_1188_, lean_object* v_stop_1189_){
_start:
{
lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = lean_array_get_size(v_as_1187_);
v___x_1191_ = lean_nat_dec_le(v_start_1188_, v___x_1190_);
if (v___x_1191_ == 0)
{
uint8_t v___x_1192_; 
v___x_1192_ = lean_nat_dec_lt(v_stop_1189_, v___x_1190_);
if (v___x_1192_ == 0)
{
lean_object* v_toApplicative_1193_; lean_object* v_toPure_1194_; lean_object* v___x_1195_; 
lean_dec_ref(v_as_1187_);
lean_dec(v_f_1185_);
v_toApplicative_1193_ = lean_ctor_get(v_inst_1184_, 0);
lean_inc_ref(v_toApplicative_1193_);
lean_dec_ref(v_inst_1184_);
v_toPure_1194_ = lean_ctor_get(v_toApplicative_1193_, 1);
lean_inc(v_toPure_1194_);
lean_dec_ref(v_toApplicative_1193_);
v___x_1195_ = lean_apply_2(v_toPure_1194_, lean_box(0), v_init_1186_);
return v___x_1195_;
}
else
{
size_t v___x_1196_; size_t v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = lean_usize_of_nat(v___x_1190_);
v___x_1197_ = lean_usize_of_nat(v_stop_1189_);
v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1184_, v_f_1185_, v_as_1187_, v___x_1196_, v___x_1197_, v_init_1186_);
return v___x_1198_;
}
}
else
{
uint8_t v___x_1199_; 
v___x_1199_ = lean_nat_dec_lt(v_stop_1189_, v_start_1188_);
if (v___x_1199_ == 0)
{
lean_object* v_toApplicative_1200_; lean_object* v_toPure_1201_; lean_object* v___x_1202_; 
lean_dec_ref(v_as_1187_);
lean_dec(v_f_1185_);
v_toApplicative_1200_ = lean_ctor_get(v_inst_1184_, 0);
lean_inc_ref(v_toApplicative_1200_);
lean_dec_ref(v_inst_1184_);
v_toPure_1201_ = lean_ctor_get(v_toApplicative_1200_, 1);
lean_inc(v_toPure_1201_);
lean_dec_ref(v_toApplicative_1200_);
v___x_1202_ = lean_apply_2(v_toPure_1201_, lean_box(0), v_init_1186_);
return v___x_1202_;
}
else
{
size_t v___x_1203_; size_t v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = lean_usize_of_nat(v_start_1188_);
v___x_1204_ = lean_usize_of_nat(v_stop_1189_);
v___x_1205_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1184_, v_f_1185_, v_as_1187_, v___x_1203_, v___x_1204_, v_init_1186_);
return v___x_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___redArg___boxed(lean_object* v_inst_1206_, lean_object* v_f_1207_, lean_object* v_init_1208_, lean_object* v_as_1209_, lean_object* v_start_1210_, lean_object* v_stop_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Array_foldrMUnsafe___redArg(v_inst_1206_, v_f_1207_, v_init_1208_, v_as_1209_, v_start_1210_, v_stop_1211_);
lean_dec(v_stop_1211_);
lean_dec(v_start_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe(lean_object* v_00_u03b1_1213_, lean_object* v_00_u03b2_1214_, lean_object* v_m_1215_, lean_object* v_inst_1216_, lean_object* v_f_1217_, lean_object* v_init_1218_, lean_object* v_as_1219_, lean_object* v_start_1220_, lean_object* v_stop_1221_){
_start:
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = lean_array_get_size(v_as_1219_);
v___x_1223_ = lean_nat_dec_le(v_start_1220_, v___x_1222_);
if (v___x_1223_ == 0)
{
uint8_t v___x_1224_; 
v___x_1224_ = lean_nat_dec_lt(v_stop_1221_, v___x_1222_);
if (v___x_1224_ == 0)
{
lean_object* v_toApplicative_1225_; lean_object* v_toPure_1226_; lean_object* v___x_1227_; 
lean_dec_ref(v_as_1219_);
lean_dec(v_f_1217_);
v_toApplicative_1225_ = lean_ctor_get(v_inst_1216_, 0);
lean_inc_ref(v_toApplicative_1225_);
lean_dec_ref(v_inst_1216_);
v_toPure_1226_ = lean_ctor_get(v_toApplicative_1225_, 1);
lean_inc(v_toPure_1226_);
lean_dec_ref(v_toApplicative_1225_);
v___x_1227_ = lean_apply_2(v_toPure_1226_, lean_box(0), v_init_1218_);
return v___x_1227_;
}
else
{
size_t v___x_1228_; size_t v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = lean_usize_of_nat(v___x_1222_);
v___x_1229_ = lean_usize_of_nat(v_stop_1221_);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1216_, v_f_1217_, v_as_1219_, v___x_1228_, v___x_1229_, v_init_1218_);
return v___x_1230_;
}
}
else
{
uint8_t v___x_1231_; 
v___x_1231_ = lean_nat_dec_lt(v_stop_1221_, v_start_1220_);
if (v___x_1231_ == 0)
{
lean_object* v_toApplicative_1232_; lean_object* v_toPure_1233_; lean_object* v___x_1234_; 
lean_dec_ref(v_as_1219_);
lean_dec(v_f_1217_);
v_toApplicative_1232_ = lean_ctor_get(v_inst_1216_, 0);
lean_inc_ref(v_toApplicative_1232_);
lean_dec_ref(v_inst_1216_);
v_toPure_1233_ = lean_ctor_get(v_toApplicative_1232_, 1);
lean_inc(v_toPure_1233_);
lean_dec_ref(v_toApplicative_1232_);
v___x_1234_ = lean_apply_2(v_toPure_1233_, lean_box(0), v_init_1218_);
return v___x_1234_;
}
else
{
size_t v___x_1235_; size_t v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = lean_usize_of_nat(v_start_1220_);
v___x_1236_ = lean_usize_of_nat(v_stop_1221_);
v___x_1237_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_1216_, v_f_1217_, v_as_1219_, v___x_1235_, v___x_1236_, v_init_1218_);
return v___x_1237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___boxed(lean_object* v_00_u03b1_1238_, lean_object* v_00_u03b2_1239_, lean_object* v_m_1240_, lean_object* v_inst_1241_, lean_object* v_f_1242_, lean_object* v_init_1243_, lean_object* v_as_1244_, lean_object* v_start_1245_, lean_object* v_stop_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Array_foldrMUnsafe(v_00_u03b1_1238_, v_00_u03b2_1239_, v_m_1240_, v_inst_1241_, v_f_1242_, v_init_1243_, v_as_1244_, v_start_1245_, v_stop_1246_);
lean_dec(v_stop_1246_);
lean_dec(v_start_1245_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0___boxed(lean_object* v_inst_1248_, lean_object* v_f_1249_, lean_object* v_as_1250_, lean_object* v_stop_1251_, lean_object* v_n_1252_, lean_object* v_____do__lift_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Array_foldrM_fold___redArg___lam__0(v_inst_1248_, v_f_1249_, v_as_1250_, v_stop_1251_, v_n_1252_, v_____do__lift_1253_);
lean_dec(v_n_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg(lean_object* v_inst_1255_, lean_object* v_f_1256_, lean_object* v_as_1257_, lean_object* v_stop_1258_, lean_object* v_i_1259_, lean_object* v_b_1260_){
_start:
{
uint8_t v___x_1261_; 
v___x_1261_ = lean_nat_dec_eq(v_i_1259_, v_stop_1258_);
if (v___x_1261_ == 0)
{
lean_object* v_zero_1262_; uint8_t v_isZero_1263_; 
v_zero_1262_ = lean_unsigned_to_nat(0u);
v_isZero_1263_ = lean_nat_dec_eq(v_i_1259_, v_zero_1262_);
if (v_isZero_1263_ == 1)
{
lean_object* v_toApplicative_1264_; lean_object* v_toPure_1265_; lean_object* v___x_1266_; 
lean_dec(v_stop_1258_);
lean_dec_ref(v_as_1257_);
lean_dec(v_f_1256_);
v_toApplicative_1264_ = lean_ctor_get(v_inst_1255_, 0);
lean_inc_ref(v_toApplicative_1264_);
lean_dec_ref(v_inst_1255_);
v_toPure_1265_ = lean_ctor_get(v_toApplicative_1264_, 1);
lean_inc(v_toPure_1265_);
lean_dec_ref(v_toApplicative_1264_);
v___x_1266_ = lean_apply_2(v_toPure_1265_, lean_box(0), v_b_1260_);
return v___x_1266_;
}
else
{
lean_object* v_toBind_1267_; lean_object* v_one_1268_; lean_object* v_n_1269_; lean_object* v___f_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v_toBind_1267_ = lean_ctor_get(v_inst_1255_, 1);
lean_inc(v_toBind_1267_);
v_one_1268_ = lean_unsigned_to_nat(1u);
v_n_1269_ = lean_nat_sub(v_i_1259_, v_one_1268_);
lean_inc(v_n_1269_);
lean_inc_ref(v_as_1257_);
lean_inc(v_f_1256_);
v___f_1270_ = lean_alloc_closure((void*)(l_Array_foldrM_fold___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1270_, 0, v_inst_1255_);
lean_closure_set(v___f_1270_, 1, v_f_1256_);
lean_closure_set(v___f_1270_, 2, v_as_1257_);
lean_closure_set(v___f_1270_, 3, v_stop_1258_);
lean_closure_set(v___f_1270_, 4, v_n_1269_);
v___x_1271_ = lean_array_fget(v_as_1257_, v_n_1269_);
lean_dec(v_n_1269_);
lean_dec_ref(v_as_1257_);
v___x_1272_ = lean_apply_2(v_f_1256_, v___x_1271_, v_b_1260_);
v___x_1273_ = lean_apply_4(v_toBind_1267_, lean_box(0), lean_box(0), v___x_1272_, v___f_1270_);
return v___x_1273_;
}
}
else
{
lean_object* v_toApplicative_1274_; lean_object* v_toPure_1275_; lean_object* v___x_1276_; 
lean_dec(v_stop_1258_);
lean_dec_ref(v_as_1257_);
lean_dec(v_f_1256_);
v_toApplicative_1274_ = lean_ctor_get(v_inst_1255_, 0);
lean_inc_ref(v_toApplicative_1274_);
lean_dec_ref(v_inst_1255_);
v_toPure_1275_ = lean_ctor_get(v_toApplicative_1274_, 1);
lean_inc(v_toPure_1275_);
lean_dec_ref(v_toApplicative_1274_);
v___x_1276_ = lean_apply_2(v_toPure_1275_, lean_box(0), v_b_1260_);
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___lam__0(lean_object* v_inst_1277_, lean_object* v_f_1278_, lean_object* v_as_1279_, lean_object* v_stop_1280_, lean_object* v_n_1281_, lean_object* v_____do__lift_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Array_foldrM_fold___redArg(v_inst_1277_, v_f_1278_, v_as_1279_, v_stop_1280_, v_n_1281_, v_____do__lift_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___redArg___boxed(lean_object* v_inst_1284_, lean_object* v_f_1285_, lean_object* v_as_1286_, lean_object* v_stop_1287_, lean_object* v_i_1288_, lean_object* v_b_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Array_foldrM_fold___redArg(v_inst_1284_, v_f_1285_, v_as_1286_, v_stop_1287_, v_i_1288_, v_b_1289_);
lean_dec(v_i_1288_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold(lean_object* v_00_u03b1_1291_, lean_object* v_00_u03b2_1292_, lean_object* v_m_1293_, lean_object* v_inst_1294_, lean_object* v_f_1295_, lean_object* v_as_1296_, lean_object* v_stop_1297_, lean_object* v_i_1298_, lean_object* v_h_1299_, lean_object* v_b_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Array_foldrM_fold___redArg(v_inst_1294_, v_f_1295_, v_as_1296_, v_stop_1297_, v_i_1298_, v_b_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___boxed(lean_object* v_00_u03b1_1302_, lean_object* v_00_u03b2_1303_, lean_object* v_m_1304_, lean_object* v_inst_1305_, lean_object* v_f_1306_, lean_object* v_as_1307_, lean_object* v_stop_1308_, lean_object* v_i_1309_, lean_object* v_h_1310_, lean_object* v_b_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Array_foldrM_fold(v_00_u03b1_1302_, v_00_u03b2_1303_, v_m_1304_, v_inst_1305_, v_f_1306_, v_as_1307_, v_stop_1308_, v_i_1309_, v_h_1310_, v_b_1311_);
lean_dec(v_i_1309_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed(lean_object* v_i_1313_, lean_object* v_bs_x27_1314_, lean_object* v_inst_1315_, lean_object* v_f_1316_, lean_object* v_sz_1317_, lean_object* v_vNew_1318_){
_start:
{
size_t v_i_boxed_1319_; size_t v_sz_boxed_1320_; lean_object* v_res_1321_; 
v_i_boxed_1319_ = lean_unbox_usize(v_i_1313_);
lean_dec(v_i_1313_);
v_sz_boxed_1320_ = lean_unbox_usize(v_sz_1317_);
lean_dec(v_sz_1317_);
v_res_1321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(v_i_boxed_1319_, v_bs_x27_1314_, v_inst_1315_, v_f_1316_, v_sz_boxed_1320_, v_vNew_1318_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(lean_object* v_inst_1322_, lean_object* v_f_1323_, size_t v_sz_1324_, size_t v_i_1325_, lean_object* v_bs_1326_){
_start:
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_usize_dec_lt(v_i_1325_, v_sz_1324_);
if (v___x_1327_ == 0)
{
lean_object* v_toApplicative_1328_; lean_object* v_toPure_1329_; lean_object* v___x_1330_; 
lean_dec(v_f_1323_);
v_toApplicative_1328_ = lean_ctor_get(v_inst_1322_, 0);
lean_inc_ref(v_toApplicative_1328_);
lean_dec_ref(v_inst_1322_);
v_toPure_1329_ = lean_ctor_get(v_toApplicative_1328_, 1);
lean_inc(v_toPure_1329_);
lean_dec_ref(v_toApplicative_1328_);
v___x_1330_ = lean_apply_2(v_toPure_1329_, lean_box(0), v_bs_1326_);
return v___x_1330_;
}
else
{
lean_object* v_toBind_1331_; lean_object* v_v_1332_; lean_object* v___x_1333_; lean_object* v_bs_x27_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___f_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_toBind_1331_ = lean_ctor_get(v_inst_1322_, 1);
lean_inc(v_toBind_1331_);
v_v_1332_ = lean_array_uget(v_bs_1326_, v_i_1325_);
v___x_1333_ = lean_unsigned_to_nat(0u);
v_bs_x27_1334_ = lean_array_uset(v_bs_1326_, v_i_1325_, v___x_1333_);
v___x_1335_ = lean_box_usize(v_i_1325_);
v___x_1336_ = lean_box_usize(v_sz_1324_);
lean_inc(v_f_1323_);
v___f_1337_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1337_, 0, v___x_1335_);
lean_closure_set(v___f_1337_, 1, v_bs_x27_1334_);
lean_closure_set(v___f_1337_, 2, v_inst_1322_);
lean_closure_set(v___f_1337_, 3, v_f_1323_);
lean_closure_set(v___f_1337_, 4, v___x_1336_);
v___x_1338_ = lean_apply_1(v_f_1323_, v_v_1332_);
v___x_1339_ = lean_apply_4(v_toBind_1331_, lean_box(0), lean_box(0), v___x_1338_, v___f_1337_);
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___lam__0(size_t v_i_1340_, lean_object* v_bs_x27_1341_, lean_object* v_inst_1342_, lean_object* v_f_1343_, size_t v_sz_1344_, lean_object* v_vNew_1345_){
_start:
{
size_t v___x_1346_; size_t v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1346_ = ((size_t)1ULL);
v___x_1347_ = lean_usize_add(v_i_1340_, v___x_1346_);
v___x_1348_ = lean_array_uset(v_bs_x27_1341_, v_i_1340_, v_vNew_1345_);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1342_, v_f_1343_, v_sz_1344_, v___x_1347_, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg___boxed(lean_object* v_inst_1350_, lean_object* v_f_1351_, lean_object* v_sz_1352_, lean_object* v_i_1353_, lean_object* v_bs_1354_){
_start:
{
size_t v_sz_boxed_1355_; size_t v_i_boxed_1356_; lean_object* v_res_1357_; 
v_sz_boxed_1355_ = lean_unbox_usize(v_sz_1352_);
lean_dec(v_sz_1352_);
v_i_boxed_1356_ = lean_unbox_usize(v_i_1353_);
lean_dec(v_i_1353_);
v_res_1357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1350_, v_f_1351_, v_sz_boxed_1355_, v_i_boxed_1356_, v_bs_1354_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object* v_00_u03b1_1358_, lean_object* v_00_u03b2_1359_, lean_object* v_m_1360_, lean_object* v_inst_1361_, lean_object* v_f_1362_, size_t v_sz_1363_, size_t v_i_1364_, lean_object* v_bs_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1361_, v_f_1362_, v_sz_1363_, v_i_1364_, v_bs_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___boxed(lean_object* v_00_u03b1_1367_, lean_object* v_00_u03b2_1368_, lean_object* v_m_1369_, lean_object* v_inst_1370_, lean_object* v_f_1371_, lean_object* v_sz_1372_, lean_object* v_i_1373_, lean_object* v_bs_1374_){
_start:
{
size_t v_sz_boxed_1375_; size_t v_i_boxed_1376_; lean_object* v_res_1377_; 
v_sz_boxed_1375_ = lean_unbox_usize(v_sz_1372_);
lean_dec(v_sz_1372_);
v_i_boxed_1376_ = lean_unbox_usize(v_i_1373_);
lean_dec(v_i_1373_);
v_res_1377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(v_00_u03b1_1367_, v_00_u03b2_1368_, v_m_1369_, v_inst_1370_, v_f_1371_, v_sz_boxed_1375_, v_i_boxed_1376_, v_bs_1374_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe___redArg(lean_object* v_inst_1378_, lean_object* v_f_1379_, lean_object* v_as_1380_){
_start:
{
size_t v_sz_1381_; size_t v___x_1382_; lean_object* v___x_1383_; 
v_sz_1381_ = lean_array_size(v_as_1380_);
v___x_1382_ = ((size_t)0ULL);
v___x_1383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1378_, v_f_1379_, v_sz_1381_, v___x_1382_, v_as_1380_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe(lean_object* v_00_u03b1_1384_, lean_object* v_00_u03b2_1385_, lean_object* v_m_1386_, lean_object* v_inst_1387_, lean_object* v_f_1388_, lean_object* v_as_1389_){
_start:
{
size_t v_sz_1390_; size_t v___x_1391_; lean_object* v___x_1392_; 
v_sz_1390_ = lean_array_size(v_as_1389_);
v___x_1391_ = ((size_t)0ULL);
v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v_inst_1387_, v_f_1388_, v_sz_1390_, v___x_1391_, v_as_1389_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0___boxed(lean_object* v_i_1393_, lean_object* v_bs_1394_, lean_object* v_inst_1395_, lean_object* v_f_1396_, lean_object* v_as_1397_, lean_object* v_____do__lift_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0(v_i_1393_, v_bs_1394_, v_inst_1395_, v_f_1396_, v_as_1397_, v_____do__lift_1398_);
lean_dec(v_i_1393_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(lean_object* v_inst_1400_, lean_object* v_f_1401_, lean_object* v_as_1402_, lean_object* v_i_1403_, lean_object* v_bs_1404_){
_start:
{
lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1405_ = lean_array_get_size(v_as_1402_);
v___x_1406_ = lean_nat_dec_lt(v_i_1403_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v_toApplicative_1407_; lean_object* v_toPure_1408_; lean_object* v___x_1409_; 
lean_dec(v_i_1403_);
lean_dec_ref(v_as_1402_);
lean_dec(v_f_1401_);
v_toApplicative_1407_ = lean_ctor_get(v_inst_1400_, 0);
lean_inc_ref(v_toApplicative_1407_);
lean_dec_ref(v_inst_1400_);
v_toPure_1408_ = lean_ctor_get(v_toApplicative_1407_, 1);
lean_inc(v_toPure_1408_);
lean_dec_ref(v_toApplicative_1407_);
v___x_1409_ = lean_apply_2(v_toPure_1408_, lean_box(0), v_bs_1404_);
return v___x_1409_;
}
else
{
lean_object* v_toBind_1410_; lean_object* v___f_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_toBind_1410_ = lean_ctor_get(v_inst_1400_, 1);
lean_inc(v_toBind_1410_);
lean_inc_ref(v_as_1402_);
lean_inc(v_f_1401_);
lean_inc(v_i_1403_);
v___f_1411_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1411_, 0, v_i_1403_);
lean_closure_set(v___f_1411_, 1, v_bs_1404_);
lean_closure_set(v___f_1411_, 2, v_inst_1400_);
lean_closure_set(v___f_1411_, 3, v_f_1401_);
lean_closure_set(v___f_1411_, 4, v_as_1402_);
v___x_1412_ = lean_array_fget(v_as_1402_, v_i_1403_);
lean_dec(v_i_1403_);
lean_dec_ref(v_as_1402_);
v___x_1413_ = lean_apply_1(v_f_1401_, v___x_1412_);
v___x_1414_ = lean_apply_4(v_toBind_1410_, lean_box(0), lean_box(0), v___x_1413_, v___f_1411_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg___lam__0(lean_object* v_i_1415_, lean_object* v_bs_1416_, lean_object* v_inst_1417_, lean_object* v_f_1418_, lean_object* v_as_1419_, lean_object* v_____do__lift_1420_){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1421_ = lean_unsigned_to_nat(1u);
v___x_1422_ = lean_nat_add(v_i_1415_, v___x_1421_);
v___x_1423_ = lean_array_push(v_bs_1416_, v_____do__lift_1420_);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(v_inst_1417_, v_f_1418_, v_as_1419_, v___x_1422_, v___x_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapM_map(lean_object* v_00_u03b1_1425_, lean_object* v_00_u03b2_1426_, lean_object* v_m_1427_, lean_object* v_inst_1428_, lean_object* v_f_1429_, lean_object* v_as_1430_, lean_object* v_i_1431_, lean_object* v_bs_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l___private_Init_Data_Array_Basic_0__Array_mapM_map___redArg(v_inst_1428_, v_f_1429_, v_as_1430_, v_i_1431_, v_bs_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1434_, lean_object* v_bs_1435_, lean_object* v_inst_1436_, lean_object* v_as_1437_, lean_object* v_f_1438_, lean_object* v_n_1439_, lean_object* v_____do__lift_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Array_mapFinIdxM_map___redArg___lam__0(v_j_1434_, v_bs_1435_, v_inst_1436_, v_as_1437_, v_f_1438_, v_n_1439_, v_____do__lift_1440_);
lean_dec(v_n_1439_);
lean_dec(v_j_1434_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg(lean_object* v_inst_1442_, lean_object* v_as_1443_, lean_object* v_f_1444_, lean_object* v_i_1445_, lean_object* v_j_1446_, lean_object* v_bs_1447_){
_start:
{
lean_object* v_toApplicative_1448_; lean_object* v_toBind_1449_; lean_object* v_toPure_1450_; lean_object* v_zero_1451_; uint8_t v_isZero_1452_; 
v_toApplicative_1448_ = lean_ctor_get(v_inst_1442_, 0);
v_toBind_1449_ = lean_ctor_get(v_inst_1442_, 1);
lean_inc(v_toBind_1449_);
v_toPure_1450_ = lean_ctor_get(v_toApplicative_1448_, 1);
v_zero_1451_ = lean_unsigned_to_nat(0u);
v_isZero_1452_ = lean_nat_dec_eq(v_i_1445_, v_zero_1451_);
if (v_isZero_1452_ == 1)
{
lean_object* v___x_1453_; 
lean_inc(v_toPure_1450_);
lean_dec(v_toBind_1449_);
lean_dec(v_j_1446_);
lean_dec(v_f_1444_);
lean_dec_ref(v_as_1443_);
lean_dec_ref(v_inst_1442_);
v___x_1453_ = lean_apply_2(v_toPure_1450_, lean_box(0), v_bs_1447_);
return v___x_1453_;
}
else
{
lean_object* v_one_1454_; lean_object* v_n_1455_; lean_object* v___f_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_one_1454_ = lean_unsigned_to_nat(1u);
v_n_1455_ = lean_nat_sub(v_i_1445_, v_one_1454_);
lean_inc(v_f_1444_);
lean_inc_ref(v_as_1443_);
lean_inc(v_j_1446_);
v___f_1456_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1456_, 0, v_j_1446_);
lean_closure_set(v___f_1456_, 1, v_bs_1447_);
lean_closure_set(v___f_1456_, 2, v_inst_1442_);
lean_closure_set(v___f_1456_, 3, v_as_1443_);
lean_closure_set(v___f_1456_, 4, v_f_1444_);
lean_closure_set(v___f_1456_, 5, v_n_1455_);
v___x_1457_ = lean_array_fget(v_as_1443_, v_j_1446_);
lean_dec_ref(v_as_1443_);
v___x_1458_ = lean_apply_3(v_f_1444_, v_j_1446_, v___x_1457_, lean_box(0));
v___x_1459_ = lean_apply_4(v_toBind_1449_, lean_box(0), lean_box(0), v___x_1458_, v___f_1456_);
return v___x_1459_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1460_, lean_object* v_bs_1461_, lean_object* v_inst_1462_, lean_object* v_as_1463_, lean_object* v_f_1464_, lean_object* v_n_1465_, lean_object* v_____do__lift_1466_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1467_ = lean_unsigned_to_nat(1u);
v___x_1468_ = lean_nat_add(v_j_1460_, v___x_1467_);
v___x_1469_ = lean_array_push(v_bs_1461_, v_____do__lift_1466_);
v___x_1470_ = l_Array_mapFinIdxM_map___redArg(v_inst_1462_, v_as_1463_, v_f_1464_, v_n_1465_, v___x_1468_, v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1471_, lean_object* v_as_1472_, lean_object* v_f_1473_, lean_object* v_i_1474_, lean_object* v_j_1475_, lean_object* v_bs_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Array_mapFinIdxM_map___redArg(v_inst_1471_, v_as_1472_, v_f_1473_, v_i_1474_, v_j_1475_, v_bs_1476_);
lean_dec(v_i_1474_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map(lean_object* v_00_u03b1_1478_, lean_object* v_00_u03b2_1479_, lean_object* v_m_1480_, lean_object* v_inst_1481_, lean_object* v_as_1482_, lean_object* v_f_1483_, lean_object* v_i_1484_, lean_object* v_j_1485_, lean_object* v_inv_1486_, lean_object* v_bs_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Array_mapFinIdxM_map___redArg(v_inst_1481_, v_as_1482_, v_f_1483_, v_i_1484_, v_j_1485_, v_bs_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___boxed(lean_object* v_00_u03b1_1489_, lean_object* v_00_u03b2_1490_, lean_object* v_m_1491_, lean_object* v_inst_1492_, lean_object* v_as_1493_, lean_object* v_f_1494_, lean_object* v_i_1495_, lean_object* v_j_1496_, lean_object* v_inv_1497_, lean_object* v_bs_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Array_mapFinIdxM_map(v_00_u03b1_1489_, v_00_u03b2_1490_, v_m_1491_, v_inst_1492_, v_as_1493_, v_f_1494_, v_i_1495_, v_j_1496_, v_inv_1497_, v_bs_1498_);
lean_dec(v_i_1495_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM___redArg(lean_object* v_inst_1500_, lean_object* v_as_1501_, lean_object* v_f_1502_){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1503_ = lean_array_get_size(v_as_1501_);
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = lean_mk_empty_array_with_capacity(v___x_1503_);
v___x_1506_ = l_Array_mapFinIdxM_map___redArg(v_inst_1500_, v_as_1501_, v_f_1502_, v___x_1503_, v___x_1504_, v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM(lean_object* v_00_u03b1_1507_, lean_object* v_00_u03b2_1508_, lean_object* v_m_1509_, lean_object* v_inst_1510_, lean_object* v_as_1511_, lean_object* v_f_1512_){
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
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg___lam__0(lean_object* v_f_1517_, lean_object* v_i_1518_, lean_object* v_a_1519_, lean_object* v_x_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_apply_2(v_f_1517_, v_i_1518_, v_a_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___redArg(lean_object* v_inst_1522_, lean_object* v_f_1523_, lean_object* v_as_1524_){
_start:
{
lean_object* v___f_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___f_1525_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1525_, 0, v_f_1523_);
v___x_1526_ = lean_array_get_size(v_as_1524_);
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = lean_mk_empty_array_with_capacity(v___x_1526_);
v___x_1529_ = l_Array_mapFinIdxM_map___redArg(v_inst_1522_, v_as_1524_, v___f_1525_, v___x_1526_, v___x_1527_, v___x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM(lean_object* v_00_u03b1_1530_, lean_object* v_00_u03b2_1531_, lean_object* v_m_1532_, lean_object* v_inst_1533_, lean_object* v_f_1534_, lean_object* v_as_1535_){
_start:
{
lean_object* v___f_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___f_1536_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1536_, 0, v_f_1534_);
v___x_1537_ = lean_array_get_size(v_as_1535_);
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = lean_mk_empty_array_with_capacity(v___x_1537_);
v___x_1540_ = l_Array_mapFinIdxM_map___redArg(v_inst_1533_, v_as_1535_, v___f_1536_, v___x_1537_, v___x_1538_, v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed(lean_object* v_i_1541_, lean_object* v_inst_1542_, lean_object* v_f_1543_, lean_object* v_as_1544_, lean_object* v_x_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(v_i_1541_, v_inst_1542_, v_f_1543_, v_as_1544_, v_x_1545_);
lean_dec(v_i_1541_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(lean_object* v_inst_1547_, lean_object* v_f_1548_, lean_object* v_as_1549_, lean_object* v_i_1550_){
_start:
{
lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = lean_array_get_size(v_as_1549_);
v___x_1552_ = lean_nat_dec_lt(v_i_1550_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v_failure_1553_; lean_object* v___x_1554_; 
lean_dec(v_i_1550_);
lean_dec_ref(v_as_1549_);
lean_dec(v_f_1548_);
v_failure_1553_ = lean_ctor_get(v_inst_1547_, 1);
lean_inc(v_failure_1553_);
lean_dec_ref(v_inst_1547_);
v___x_1554_ = lean_apply_1(v_failure_1553_, lean_box(0));
return v___x_1554_;
}
else
{
lean_object* v_orElse_1555_; lean_object* v___f_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_orElse_1555_ = lean_ctor_get(v_inst_1547_, 2);
lean_inc(v_orElse_1555_);
lean_inc_ref(v_as_1549_);
lean_inc(v_f_1548_);
lean_inc(v_i_1550_);
v___f_1556_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1556_, 0, v_i_1550_);
lean_closure_set(v___f_1556_, 1, v_inst_1547_);
lean_closure_set(v___f_1556_, 2, v_f_1548_);
lean_closure_set(v___f_1556_, 3, v_as_1549_);
v___x_1557_ = lean_array_fget(v_as_1549_, v_i_1550_);
lean_dec(v_i_1550_);
lean_dec_ref(v_as_1549_);
v___x_1558_ = lean_apply_1(v_f_1548_, v___x_1557_);
v___x_1559_ = lean_apply_3(v_orElse_1555_, lean_box(0), v___x_1558_, v___f_1556_);
return v___x_1559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg___lam__0(lean_object* v_i_1560_, lean_object* v_inst_1561_, lean_object* v_f_1562_, lean_object* v_as_1563_, lean_object* v_x_1564_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = lean_nat_add(v_i_1560_, v___x_1565_);
v___x_1567_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1561_, v_f_1562_, v_as_1563_, v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_object* v_00_u03b2_1568_, lean_object* v_00_u03b1_1569_, lean_object* v_m_1570_, lean_object* v_inst_1571_, lean_object* v_f_1572_, lean_object* v_as_1573_, lean_object* v_i_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1571_, v_f_1572_, v_as_1573_, v_i_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM___redArg(lean_object* v_inst_1576_, lean_object* v_f_1577_, lean_object* v_as_1578_){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1580_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1576_, v_f_1577_, v_as_1578_, v___x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Array_firstM(lean_object* v_00_u03b2_1581_, lean_object* v_00_u03b1_1582_, lean_object* v_m_1583_, lean_object* v_inst_1584_, lean_object* v_f_1585_, lean_object* v_as_1586_){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = lean_unsigned_to_nat(0u);
v___x_1588_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___redArg(v_inst_1584_, v_f_1585_, v_as_1586_, v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__0(lean_object* v___x_1589_, lean_object* v_toPure_1590_, lean_object* v___x_1591_, lean_object* v_____do__lift_1592_){
_start:
{
if (lean_obj_tag(v_____do__lift_1592_) == 1)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec_ref(v___x_1591_);
v___x_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1593_, 0, v_____do__lift_1592_);
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v___x_1589_);
v___x_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
v___x_1596_ = lean_apply_2(v_toPure_1590_, lean_box(0), v___x_1595_);
return v___x_1596_;
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec(v_____do__lift_1592_);
v___x_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1591_);
v___x_1598_ = lean_apply_2(v_toPure_1590_, lean_box(0), v___x_1597_);
return v___x_1598_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1(lean_object* v_f_1599_, lean_object* v_toBind_1600_, lean_object* v___f_1601_, lean_object* v_a_1602_, lean_object* v_x_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_apply_1(v_f_1599_, v_a_1602_);
v___x_1606_ = lean_apply_4(v_toBind_1600_, lean_box(0), lean_box(0), v___x_1605_, v___f_1601_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__1___boxed(lean_object* v_f_1607_, lean_object* v_toBind_1608_, lean_object* v___f_1609_, lean_object* v_a_1610_, lean_object* v_x_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Array_findSomeM_x3f___redArg___lam__1(v_f_1607_, v_toBind_1608_, v___f_1609_, v_a_1610_, v_x_1611_, v___y_1612_);
lean_dec_ref(v___y_1612_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg___lam__2(lean_object* v_toPure_1614_, lean_object* v_____s_1615_){
_start:
{
lean_object* v_fst_1616_; 
v_fst_1616_ = lean_ctor_get(v_____s_1615_, 0);
lean_inc(v_fst_1616_);
lean_dec_ref(v_____s_1615_);
if (lean_obj_tag(v_fst_1616_) == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_box(0);
v___x_1618_ = lean_apply_2(v_toPure_1614_, lean_box(0), v___x_1617_);
return v___x_1618_;
}
else
{
lean_object* v_val_1619_; lean_object* v___x_1620_; 
v_val_1619_ = lean_ctor_get(v_fst_1616_, 0);
lean_inc(v_val_1619_);
lean_dec_ref(v_fst_1616_);
v___x_1620_ = lean_apply_2(v_toPure_1614_, lean_box(0), v_val_1619_);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___redArg(lean_object* v_inst_1624_, lean_object* v_f_1625_, lean_object* v_as_1626_){
_start:
{
lean_object* v_toApplicative_1627_; lean_object* v_toBind_1628_; lean_object* v_toPure_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___f_1632_; lean_object* v___f_1633_; lean_object* v___f_1634_; size_t v_sz_1635_; size_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_toApplicative_1627_ = lean_ctor_get(v_inst_1624_, 0);
v_toBind_1628_ = lean_ctor_get(v_inst_1624_, 1);
lean_inc(v_toBind_1628_);
v_toPure_1629_ = lean_ctor_get(v_toApplicative_1627_, 1);
v___x_1630_ = lean_box(0);
v___x_1631_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc(v_toPure_1629_);
v___f_1632_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1632_, 0, v___x_1630_);
lean_closure_set(v___f_1632_, 1, v_toPure_1629_);
lean_closure_set(v___f_1632_, 2, v___x_1631_);
lean_inc(v_toBind_1628_);
v___f_1633_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1633_, 0, v_f_1625_);
lean_closure_set(v___f_1633_, 1, v_toBind_1628_);
lean_closure_set(v___f_1633_, 2, v___f_1632_);
lean_inc(v_toPure_1629_);
v___f_1634_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1634_, 0, v_toPure_1629_);
v_sz_1635_ = lean_array_size(v_as_1626_);
v___x_1636_ = ((size_t)0ULL);
v___x_1637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1624_, v_as_1626_, v___f_1633_, v_sz_1635_, v___x_1636_, v___x_1631_);
v___x_1638_ = lean_apply_4(v_toBind_1628_, lean_box(0), lean_box(0), v___x_1637_, v___f_1634_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f(lean_object* v_00_u03b1_1639_, lean_object* v_00_u03b2_1640_, lean_object* v_m_1641_, lean_object* v_inst_1642_, lean_object* v_f_1643_, lean_object* v_as_1644_){
_start:
{
lean_object* v_toApplicative_1645_; lean_object* v_toBind_1646_; lean_object* v_toPure_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___f_1650_; lean_object* v___f_1651_; lean_object* v___f_1652_; size_t v_sz_1653_; size_t v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_toApplicative_1645_ = lean_ctor_get(v_inst_1642_, 0);
v_toBind_1646_ = lean_ctor_get(v_inst_1642_, 1);
lean_inc(v_toBind_1646_);
v_toPure_1647_ = lean_ctor_get(v_toApplicative_1645_, 1);
v___x_1648_ = lean_box(0);
v___x_1649_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc(v_toPure_1647_);
v___f_1650_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1650_, 0, v___x_1648_);
lean_closure_set(v___f_1650_, 1, v_toPure_1647_);
lean_closure_set(v___f_1650_, 2, v___x_1649_);
lean_inc(v_toBind_1646_);
v___f_1651_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1651_, 0, v_f_1643_);
lean_closure_set(v___f_1651_, 1, v_toBind_1646_);
lean_closure_set(v___f_1651_, 2, v___f_1650_);
lean_inc(v_toPure_1647_);
v___f_1652_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1652_, 0, v_toPure_1647_);
v_sz_1653_ = lean_array_size(v_as_1644_);
v___x_1654_ = ((size_t)0ULL);
v___x_1655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1642_, v_as_1644_, v___f_1651_, v_sz_1653_, v___x_1654_, v___x_1649_);
v___x_1656_ = lean_apply_4(v_toBind_1646_, lean_box(0), lean_box(0), v___x_1655_, v___f_1652_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0(lean_object* v___x_1657_, lean_object* v_toPure_1658_, lean_object* v_a_1659_, lean_object* v___x_1660_, uint8_t v_____do__lift_1661_){
_start:
{
if (v_____do__lift_1661_ == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_dec(v_a_1659_);
v___x_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1657_);
v___x_1663_ = lean_apply_2(v_toPure_1658_, lean_box(0), v___x_1662_);
return v___x_1663_;
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_dec_ref(v___x_1657_);
v___x_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1664_, 0, v_a_1659_);
v___x_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
v___x_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
lean_ctor_set(v___x_1666_, 1, v___x_1660_);
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
v___x_1668_ = lean_apply_2(v_toPure_1658_, lean_box(0), v___x_1667_);
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__0___boxed(lean_object* v___x_1669_, lean_object* v_toPure_1670_, lean_object* v_a_1671_, lean_object* v___x_1672_, lean_object* v_____do__lift_1673_){
_start:
{
uint8_t v_____do__lift_214__boxed_1674_; lean_object* v_res_1675_; 
v_____do__lift_214__boxed_1674_ = lean_unbox(v_____do__lift_1673_);
v_res_1675_ = l_Array_findM_x3f___redArg___lam__0(v___x_1669_, v_toPure_1670_, v_a_1671_, v___x_1672_, v_____do__lift_214__boxed_1674_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1(lean_object* v___x_1676_, lean_object* v_toPure_1677_, lean_object* v___x_1678_, lean_object* v_p_1679_, lean_object* v_toBind_1680_, lean_object* v_a_1681_, lean_object* v_x_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___f_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_inc(v_a_1681_);
v___f_1684_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1684_, 0, v___x_1676_);
lean_closure_set(v___f_1684_, 1, v_toPure_1677_);
lean_closure_set(v___f_1684_, 2, v_a_1681_);
lean_closure_set(v___f_1684_, 3, v___x_1678_);
v___x_1685_ = lean_apply_1(v_p_1679_, v_a_1681_);
v___x_1686_ = lean_apply_4(v_toBind_1680_, lean_box(0), lean_box(0), v___x_1685_, v___f_1684_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_1687_, lean_object* v_toPure_1688_, lean_object* v___x_1689_, lean_object* v_p_1690_, lean_object* v_toBind_1691_, lean_object* v_a_1692_, lean_object* v_x_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Array_findM_x3f___redArg___lam__1(v___x_1687_, v_toPure_1688_, v___x_1689_, v_p_1690_, v_toBind_1691_, v_a_1692_, v_x_1693_, v___y_1694_);
lean_dec_ref(v___y_1694_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___redArg(lean_object* v_inst_1696_, lean_object* v_p_1697_, lean_object* v_as_1698_){
_start:
{
lean_object* v_toApplicative_1699_; lean_object* v_toBind_1700_; lean_object* v_toPure_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___f_1704_; lean_object* v___f_1705_; size_t v_sz_1706_; size_t v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_toApplicative_1699_ = lean_ctor_get(v_inst_1696_, 0);
v_toBind_1700_ = lean_ctor_get(v_inst_1696_, 1);
lean_inc(v_toBind_1700_);
v_toPure_1701_ = lean_ctor_get(v_toApplicative_1699_, 1);
v___x_1702_ = lean_box(0);
v___x_1703_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc(v_toBind_1700_);
lean_inc(v_toPure_1701_);
v___f_1704_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1704_, 0, v___x_1703_);
lean_closure_set(v___f_1704_, 1, v_toPure_1701_);
lean_closure_set(v___f_1704_, 2, v___x_1702_);
lean_closure_set(v___f_1704_, 3, v_p_1697_);
lean_closure_set(v___f_1704_, 4, v_toBind_1700_);
lean_inc(v_toPure_1701_);
v___f_1705_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1705_, 0, v_toPure_1701_);
v_sz_1706_ = lean_array_size(v_as_1698_);
v___x_1707_ = ((size_t)0ULL);
v___x_1708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1696_, v_as_1698_, v___f_1704_, v_sz_1706_, v___x_1707_, v___x_1703_);
v___x_1709_ = lean_apply_4(v_toBind_1700_, lean_box(0), lean_box(0), v___x_1708_, v___f_1705_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f(lean_object* v_m_1710_, lean_object* v_00_u03b1_1711_, lean_object* v_inst_1712_, lean_object* v_p_1713_, lean_object* v_as_1714_){
_start:
{
lean_object* v_toApplicative_1715_; lean_object* v_toBind_1716_; lean_object* v_toPure_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___f_1720_; lean_object* v___f_1721_; size_t v_sz_1722_; size_t v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v_toApplicative_1715_ = lean_ctor_get(v_inst_1712_, 0);
v_toBind_1716_ = lean_ctor_get(v_inst_1712_, 1);
lean_inc(v_toBind_1716_);
v_toPure_1717_ = lean_ctor_get(v_toApplicative_1715_, 1);
v___x_1718_ = lean_box(0);
v___x_1719_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
lean_inc(v_toBind_1716_);
lean_inc(v_toPure_1717_);
v___f_1720_ = lean_alloc_closure((void*)(l_Array_findM_x3f___redArg___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1720_, 0, v___x_1719_);
lean_closure_set(v___f_1720_, 1, v_toPure_1717_);
lean_closure_set(v___f_1720_, 2, v___x_1718_);
lean_closure_set(v___f_1720_, 3, v_p_1713_);
lean_closure_set(v___f_1720_, 4, v_toBind_1716_);
lean_inc(v_toPure_1717_);
v___f_1721_ = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1721_, 0, v_toPure_1717_);
v_sz_1722_ = lean_array_size(v_as_1714_);
v___x_1723_ = ((size_t)0ULL);
v___x_1724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1712_, v_as_1714_, v___f_1720_, v_sz_1722_, v___x_1723_, v___x_1719_);
v___x_1725_ = lean_apply_4(v_toBind_1716_, lean_box(0), lean_box(0), v___x_1724_, v___f_1721_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0(lean_object* v_snd_1726_, lean_object* v___x_1727_, lean_object* v_toPure_1728_, uint8_t v_____do__lift_1729_){
_start:
{
if (v_____do__lift_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1730_ = lean_unsigned_to_nat(1u);
v___x_1731_ = lean_nat_add(v_snd_1726_, v___x_1730_);
lean_dec(v_snd_1726_);
v___x_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1727_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
v___x_1734_ = lean_apply_2(v_toPure_1728_, lean_box(0), v___x_1733_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v___x_1727_);
lean_inc(v_snd_1726_);
v___x_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1735_, 0, v_snd_1726_);
v___x_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
lean_ctor_set(v___x_1737_, 1, v_snd_1726_);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
v___x_1739_ = lean_apply_2(v_toPure_1728_, lean_box(0), v___x_1738_);
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__0___boxed(lean_object* v_snd_1740_, lean_object* v___x_1741_, lean_object* v_toPure_1742_, lean_object* v_____do__lift_1743_){
_start:
{
uint8_t v_____do__lift_249__boxed_1744_; lean_object* v_res_1745_; 
v_____do__lift_249__boxed_1744_ = lean_unbox(v_____do__lift_1743_);
v_res_1745_ = l_Array_findIdxM_x3f___redArg___lam__0(v_snd_1740_, v___x_1741_, v_toPure_1742_, v_____do__lift_249__boxed_1744_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__1(lean_object* v___x_1746_, lean_object* v_toPure_1747_, lean_object* v_p_1748_, lean_object* v_toBind_1749_, lean_object* v_a_1750_, lean_object* v_x_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_snd_1753_; lean_object* v___f_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v_snd_1753_ = lean_ctor_get(v___y_1752_, 1);
lean_inc(v_snd_1753_);
lean_dec_ref(v___y_1752_);
v___f_1754_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1754_, 0, v_snd_1753_);
lean_closure_set(v___f_1754_, 1, v___x_1746_);
lean_closure_set(v___f_1754_, 2, v_toPure_1747_);
v___x_1755_ = lean_apply_1(v_p_1748_, v_a_1750_);
v___x_1756_ = lean_apply_4(v_toBind_1749_, lean_box(0), lean_box(0), v___x_1755_, v___f_1754_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg___lam__2(lean_object* v_toPure_1757_, lean_object* v_____s_1758_){
_start:
{
lean_object* v_fst_1759_; 
v_fst_1759_ = lean_ctor_get(v_____s_1758_, 0);
lean_inc(v_fst_1759_);
lean_dec_ref(v_____s_1758_);
if (lean_obj_tag(v_fst_1759_) == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_box(0);
v___x_1761_ = lean_apply_2(v_toPure_1757_, lean_box(0), v___x_1760_);
return v___x_1761_;
}
else
{
lean_object* v_val_1762_; lean_object* v___x_1763_; 
v_val_1762_ = lean_ctor_get(v_fst_1759_, 0);
lean_inc(v_val_1762_);
lean_dec_ref(v_fst_1759_);
v___x_1763_ = lean_apply_2(v_toPure_1757_, lean_box(0), v_val_1762_);
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___redArg(lean_object* v_inst_1767_, lean_object* v_p_1768_, lean_object* v_as_1769_){
_start:
{
lean_object* v_toApplicative_1770_; lean_object* v_toBind_1771_; lean_object* v_toPure_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___f_1775_; lean_object* v___f_1776_; size_t v_sz_1777_; size_t v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v_toApplicative_1770_ = lean_ctor_get(v_inst_1767_, 0);
v_toBind_1771_ = lean_ctor_get(v_inst_1767_, 1);
lean_inc(v_toBind_1771_);
v_toPure_1772_ = lean_ctor_get(v_toApplicative_1770_, 1);
v___x_1773_ = lean_box(0);
v___x_1774_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc(v_toBind_1771_);
lean_inc(v_toPure_1772_);
v___f_1775_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1775_, 0, v___x_1773_);
lean_closure_set(v___f_1775_, 1, v_toPure_1772_);
lean_closure_set(v___f_1775_, 2, v_p_1768_);
lean_closure_set(v___f_1775_, 3, v_toBind_1771_);
lean_inc(v_toPure_1772_);
v___f_1776_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1776_, 0, v_toPure_1772_);
v_sz_1777_ = lean_array_size(v_as_1769_);
v___x_1778_ = ((size_t)0ULL);
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1767_, v_as_1769_, v___f_1775_, v_sz_1777_, v___x_1778_, v___x_1774_);
v___x_1780_ = lean_apply_4(v_toBind_1771_, lean_box(0), lean_box(0), v___x_1779_, v___f_1776_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f(lean_object* v_00_u03b1_1781_, lean_object* v_m_1782_, lean_object* v_inst_1783_, lean_object* v_p_1784_, lean_object* v_as_1785_){
_start:
{
lean_object* v_toApplicative_1786_; lean_object* v_toBind_1787_; lean_object* v_toPure_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___f_1791_; lean_object* v___f_1792_; size_t v_sz_1793_; size_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_toApplicative_1786_ = lean_ctor_get(v_inst_1783_, 0);
v_toBind_1787_ = lean_ctor_get(v_inst_1783_, 1);
lean_inc(v_toBind_1787_);
v_toPure_1788_ = lean_ctor_get(v_toApplicative_1786_, 1);
v___x_1789_ = lean_box(0);
v___x_1790_ = ((lean_object*)(l_Array_findIdxM_x3f___redArg___closed__0));
lean_inc(v_toBind_1787_);
lean_inc(v_toPure_1788_);
v___f_1791_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__1), 7, 4);
lean_closure_set(v___f_1791_, 0, v___x_1789_);
lean_closure_set(v___f_1791_, 1, v_toPure_1788_);
lean_closure_set(v___f_1791_, 2, v_p_1784_);
lean_closure_set(v___f_1791_, 3, v_toBind_1787_);
lean_inc(v_toPure_1788_);
v___f_1792_ = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1792_, 0, v_toPure_1788_);
v_sz_1793_ = lean_array_size(v_as_1785_);
v___x_1794_ = ((size_t)0ULL);
v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v_inst_1783_, v_as_1785_, v___f_1791_, v_sz_1793_, v___x_1794_, v___x_1790_);
v___x_1796_ = lean_apply_4(v_toBind_1787_, lean_box(0), lean_box(0), v___x_1795_, v___f_1792_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed(lean_object* v_i_1797_, lean_object* v_inst_1798_, lean_object* v_p_1799_, lean_object* v_as_1800_, lean_object* v_stop_1801_, lean_object* v_toApplicative_1802_, lean_object* v___x_1803_, lean_object* v_____do__lift_1804_){
_start:
{
size_t v_i_boxed_1805_; size_t v_stop_boxed_1806_; uint8_t v___x_153__boxed_1807_; uint8_t v_____do__lift_154__boxed_1808_; lean_object* v_res_1809_; 
v_i_boxed_1805_ = lean_unbox_usize(v_i_1797_);
lean_dec(v_i_1797_);
v_stop_boxed_1806_ = lean_unbox_usize(v_stop_1801_);
lean_dec(v_stop_1801_);
v___x_153__boxed_1807_ = lean_unbox(v___x_1803_);
v_____do__lift_154__boxed_1808_ = lean_unbox(v_____do__lift_1804_);
v_res_1809_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(v_i_boxed_1805_, v_inst_1798_, v_p_1799_, v_as_1800_, v_stop_boxed_1806_, v_toApplicative_1802_, v___x_153__boxed_1807_, v_____do__lift_154__boxed_1808_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(lean_object* v_inst_1810_, lean_object* v_p_1811_, lean_object* v_as_1812_, size_t v_i_1813_, size_t v_stop_1814_){
_start:
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_usize_dec_eq(v_i_1813_, v_stop_1814_);
if (v___x_1815_ == 0)
{
lean_object* v_toApplicative_1816_; lean_object* v_toBind_1817_; uint8_t v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___f_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_toApplicative_1816_ = lean_ctor_get(v_inst_1810_, 0);
lean_inc_ref(v_toApplicative_1816_);
v_toBind_1817_ = lean_ctor_get(v_inst_1810_, 1);
lean_inc(v_toBind_1817_);
v___x_1818_ = 1;
v___x_1819_ = lean_box_usize(v_i_1813_);
v___x_1820_ = lean_box_usize(v_stop_1814_);
v___x_1821_ = lean_box(v___x_1818_);
lean_inc_ref(v_as_1812_);
lean_inc(v_p_1811_);
v___f_1822_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1822_, 0, v___x_1819_);
lean_closure_set(v___f_1822_, 1, v_inst_1810_);
lean_closure_set(v___f_1822_, 2, v_p_1811_);
lean_closure_set(v___f_1822_, 3, v_as_1812_);
lean_closure_set(v___f_1822_, 4, v___x_1820_);
lean_closure_set(v___f_1822_, 5, v_toApplicative_1816_);
lean_closure_set(v___f_1822_, 6, v___x_1821_);
v___x_1823_ = lean_array_uget(v_as_1812_, v_i_1813_);
lean_dec_ref(v_as_1812_);
v___x_1824_ = lean_apply_1(v_p_1811_, v___x_1823_);
v___x_1825_ = lean_apply_4(v_toBind_1817_, lean_box(0), lean_box(0), v___x_1824_, v___f_1822_);
return v___x_1825_;
}
else
{
lean_object* v_toApplicative_1826_; lean_object* v_toPure_1827_; uint8_t v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec_ref(v_as_1812_);
lean_dec(v_p_1811_);
v_toApplicative_1826_ = lean_ctor_get(v_inst_1810_, 0);
lean_inc_ref(v_toApplicative_1826_);
lean_dec_ref(v_inst_1810_);
v_toPure_1827_ = lean_ctor_get(v_toApplicative_1826_, 1);
lean_inc(v_toPure_1827_);
lean_dec_ref(v_toApplicative_1826_);
v___x_1828_ = 0;
v___x_1829_ = lean_box(v___x_1828_);
v___x_1830_ = lean_apply_2(v_toPure_1827_, lean_box(0), v___x_1829_);
return v___x_1830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___lam__0(size_t v_i_1831_, lean_object* v_inst_1832_, lean_object* v_p_1833_, lean_object* v_as_1834_, size_t v_stop_1835_, lean_object* v_toApplicative_1836_, uint8_t v___x_1837_, uint8_t v_____do__lift_1838_){
_start:
{
if (v_____do__lift_1838_ == 0)
{
size_t v___x_1839_; size_t v___x_1840_; lean_object* v___x_1841_; 
lean_dec_ref(v_toApplicative_1836_);
v___x_1839_ = ((size_t)1ULL);
v___x_1840_ = lean_usize_add(v_i_1831_, v___x_1839_);
v___x_1841_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1832_, v_p_1833_, v_as_1834_, v___x_1840_, v_stop_1835_);
return v___x_1841_;
}
else
{
lean_object* v_toPure_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec_ref(v_as_1834_);
lean_dec(v_p_1833_);
lean_dec_ref(v_inst_1832_);
v_toPure_1842_ = lean_ctor_get(v_toApplicative_1836_, 1);
lean_inc(v_toPure_1842_);
lean_dec_ref(v_toApplicative_1836_);
v___x_1843_ = lean_box(v___x_1837_);
v___x_1844_ = lean_apply_2(v_toPure_1842_, lean_box(0), v___x_1843_);
return v___x_1844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg___boxed(lean_object* v_inst_1845_, lean_object* v_p_1846_, lean_object* v_as_1847_, lean_object* v_i_1848_, lean_object* v_stop_1849_){
_start:
{
size_t v_i_boxed_1850_; size_t v_stop_boxed_1851_; lean_object* v_res_1852_; 
v_i_boxed_1850_ = lean_unbox_usize(v_i_1848_);
lean_dec(v_i_1848_);
v_stop_boxed_1851_ = lean_unbox_usize(v_stop_1849_);
lean_dec(v_stop_1849_);
v_res_1852_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1845_, v_p_1846_, v_as_1847_, v_i_boxed_1850_, v_stop_boxed_1851_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object* v_00_u03b1_1853_, lean_object* v_m_1854_, lean_object* v_inst_1855_, lean_object* v_p_1856_, lean_object* v_as_1857_, size_t v_i_1858_, size_t v_stop_1859_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1855_, v_p_1856_, v_as_1857_, v_i_1858_, v_stop_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___boxed(lean_object* v_00_u03b1_1861_, lean_object* v_m_1862_, lean_object* v_inst_1863_, lean_object* v_p_1864_, lean_object* v_as_1865_, lean_object* v_i_1866_, lean_object* v_stop_1867_){
_start:
{
size_t v_i_boxed_1868_; size_t v_stop_boxed_1869_; lean_object* v_res_1870_; 
v_i_boxed_1868_ = lean_unbox_usize(v_i_1866_);
lean_dec(v_i_1866_);
v_stop_boxed_1869_ = lean_unbox_usize(v_stop_1867_);
lean_dec(v_stop_1867_);
v_res_1870_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(v_00_u03b1_1861_, v_m_1862_, v_inst_1863_, v_p_1864_, v_as_1865_, v_i_boxed_1868_, v_stop_boxed_1869_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg(lean_object* v_inst_1871_, lean_object* v_p_1872_, lean_object* v_as_1873_, lean_object* v_start_1874_, lean_object* v_stop_1875_){
_start:
{
lean_object* v___y_1877_; uint8_t v___x_1886_; 
v___x_1886_ = lean_nat_dec_lt(v_start_1874_, v_stop_1875_);
if (v___x_1886_ == 0)
{
lean_object* v_toApplicative_1887_; lean_object* v_toPure_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_dec(v_stop_1875_);
lean_dec_ref(v_as_1873_);
lean_dec(v_p_1872_);
v_toApplicative_1887_ = lean_ctor_get(v_inst_1871_, 0);
lean_inc_ref(v_toApplicative_1887_);
lean_dec_ref(v_inst_1871_);
v_toPure_1888_ = lean_ctor_get(v_toApplicative_1887_, 1);
lean_inc(v_toPure_1888_);
lean_dec_ref(v_toApplicative_1887_);
v___x_1889_ = lean_box(v___x_1886_);
v___x_1890_ = lean_apply_2(v_toPure_1888_, lean_box(0), v___x_1889_);
return v___x_1890_;
}
else
{
lean_object* v___x_1891_; uint8_t v___x_1892_; 
v___x_1891_ = lean_array_get_size(v_as_1873_);
v___x_1892_ = lean_nat_dec_le(v_stop_1875_, v___x_1891_);
if (v___x_1892_ == 0)
{
lean_dec(v_stop_1875_);
v___y_1877_ = v___x_1891_;
goto v___jp_1876_;
}
else
{
v___y_1877_ = v_stop_1875_;
goto v___jp_1876_;
}
}
v___jp_1876_:
{
uint8_t v___x_1878_; 
v___x_1878_ = lean_nat_dec_lt(v_start_1874_, v___y_1877_);
if (v___x_1878_ == 0)
{
lean_object* v_toApplicative_1879_; lean_object* v_toPure_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_dec(v___y_1877_);
lean_dec_ref(v_as_1873_);
lean_dec(v_p_1872_);
v_toApplicative_1879_ = lean_ctor_get(v_inst_1871_, 0);
lean_inc_ref(v_toApplicative_1879_);
lean_dec_ref(v_inst_1871_);
v_toPure_1880_ = lean_ctor_get(v_toApplicative_1879_, 1);
lean_inc(v_toPure_1880_);
lean_dec_ref(v_toApplicative_1879_);
v___x_1881_ = lean_box(v___x_1878_);
v___x_1882_ = lean_apply_2(v_toPure_1880_, lean_box(0), v___x_1881_);
return v___x_1882_;
}
else
{
size_t v___x_1883_; size_t v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = lean_usize_of_nat(v_start_1874_);
v___x_1884_ = lean_usize_of_nat(v___y_1877_);
lean_dec(v___y_1877_);
v___x_1885_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1871_, v_p_1872_, v_as_1873_, v___x_1883_, v___x_1884_);
return v___x_1885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___redArg___boxed(lean_object* v_inst_1893_, lean_object* v_p_1894_, lean_object* v_as_1895_, lean_object* v_start_1896_, lean_object* v_stop_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Array_anyMUnsafe___redArg(v_inst_1893_, v_p_1894_, v_as_1895_, v_start_1896_, v_stop_1897_);
lean_dec(v_start_1896_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe(lean_object* v_00_u03b1_1899_, lean_object* v_m_1900_, lean_object* v_inst_1901_, lean_object* v_p_1902_, lean_object* v_as_1903_, lean_object* v_start_1904_, lean_object* v_stop_1905_){
_start:
{
lean_object* v___y_1907_; uint8_t v___x_1916_; 
v___x_1916_ = lean_nat_dec_lt(v_start_1904_, v_stop_1905_);
if (v___x_1916_ == 0)
{
lean_object* v_toApplicative_1917_; lean_object* v_toPure_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_dec(v_stop_1905_);
lean_dec_ref(v_as_1903_);
lean_dec(v_p_1902_);
v_toApplicative_1917_ = lean_ctor_get(v_inst_1901_, 0);
lean_inc_ref(v_toApplicative_1917_);
lean_dec_ref(v_inst_1901_);
v_toPure_1918_ = lean_ctor_get(v_toApplicative_1917_, 1);
lean_inc(v_toPure_1918_);
lean_dec_ref(v_toApplicative_1917_);
v___x_1919_ = lean_box(v___x_1916_);
v___x_1920_ = lean_apply_2(v_toPure_1918_, lean_box(0), v___x_1919_);
return v___x_1920_;
}
else
{
lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1921_ = lean_array_get_size(v_as_1903_);
v___x_1922_ = lean_nat_dec_le(v_stop_1905_, v___x_1921_);
if (v___x_1922_ == 0)
{
lean_dec(v_stop_1905_);
v___y_1907_ = v___x_1921_;
goto v___jp_1906_;
}
else
{
v___y_1907_ = v_stop_1905_;
goto v___jp_1906_;
}
}
v___jp_1906_:
{
uint8_t v___x_1908_; 
v___x_1908_ = lean_nat_dec_lt(v_start_1904_, v___y_1907_);
if (v___x_1908_ == 0)
{
lean_object* v_toApplicative_1909_; lean_object* v_toPure_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_dec(v___y_1907_);
lean_dec_ref(v_as_1903_);
lean_dec(v_p_1902_);
v_toApplicative_1909_ = lean_ctor_get(v_inst_1901_, 0);
lean_inc_ref(v_toApplicative_1909_);
lean_dec_ref(v_inst_1901_);
v_toPure_1910_ = lean_ctor_get(v_toApplicative_1909_, 1);
lean_inc(v_toPure_1910_);
lean_dec_ref(v_toApplicative_1909_);
v___x_1911_ = lean_box(v___x_1908_);
v___x_1912_ = lean_apply_2(v_toPure_1910_, lean_box(0), v___x_1911_);
return v___x_1912_;
}
else
{
size_t v___x_1913_; size_t v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = lean_usize_of_nat(v_start_1904_);
v___x_1914_ = lean_usize_of_nat(v___y_1907_);
lean_dec(v___y_1907_);
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_1901_, v_p_1902_, v_as_1903_, v___x_1913_, v___x_1914_);
return v___x_1915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___boxed(lean_object* v_00_u03b1_1923_, lean_object* v_m_1924_, lean_object* v_inst_1925_, lean_object* v_p_1926_, lean_object* v_as_1927_, lean_object* v_start_1928_, lean_object* v_stop_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Array_anyMUnsafe(v_00_u03b1_1923_, v_m_1924_, v_inst_1925_, v_p_1926_, v_as_1927_, v_start_1928_, v_stop_1929_);
lean_dec(v_start_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0___boxed(lean_object* v_j_1931_, lean_object* v_inst_1932_, lean_object* v_p_1933_, lean_object* v_as_1934_, lean_object* v_stop_1935_, lean_object* v_toApplicative_1936_, lean_object* v_____do__lift_1937_){
_start:
{
uint8_t v_____do__lift_82__boxed_1938_; lean_object* v_res_1939_; 
v_____do__lift_82__boxed_1938_ = lean_unbox(v_____do__lift_1937_);
v_res_1939_ = l_Array_anyM_loop___redArg___lam__0(v_j_1931_, v_inst_1932_, v_p_1933_, v_as_1934_, v_stop_1935_, v_toApplicative_1936_, v_____do__lift_82__boxed_1938_);
lean_dec(v_j_1931_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg(lean_object* v_inst_1940_, lean_object* v_p_1941_, lean_object* v_as_1942_, lean_object* v_stop_1943_, lean_object* v_j_1944_){
_start:
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_nat_dec_lt(v_j_1944_, v_stop_1943_);
if (v___x_1945_ == 0)
{
lean_object* v_toApplicative_1946_; lean_object* v_toPure_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec(v_j_1944_);
lean_dec(v_stop_1943_);
lean_dec_ref(v_as_1942_);
lean_dec(v_p_1941_);
v_toApplicative_1946_ = lean_ctor_get(v_inst_1940_, 0);
lean_inc_ref(v_toApplicative_1946_);
lean_dec_ref(v_inst_1940_);
v_toPure_1947_ = lean_ctor_get(v_toApplicative_1946_, 1);
lean_inc(v_toPure_1947_);
lean_dec_ref(v_toApplicative_1946_);
v___x_1948_ = lean_box(v___x_1945_);
v___x_1949_ = lean_apply_2(v_toPure_1947_, lean_box(0), v___x_1948_);
return v___x_1949_;
}
else
{
lean_object* v_toApplicative_1950_; lean_object* v_toBind_1951_; lean_object* v___f_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v_toApplicative_1950_ = lean_ctor_get(v_inst_1940_, 0);
lean_inc_ref(v_toApplicative_1950_);
v_toBind_1951_ = lean_ctor_get(v_inst_1940_, 1);
lean_inc(v_toBind_1951_);
lean_inc_ref(v_as_1942_);
lean_inc(v_p_1941_);
lean_inc(v_j_1944_);
v___f_1952_ = lean_alloc_closure((void*)(l_Array_anyM_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1952_, 0, v_j_1944_);
lean_closure_set(v___f_1952_, 1, v_inst_1940_);
lean_closure_set(v___f_1952_, 2, v_p_1941_);
lean_closure_set(v___f_1952_, 3, v_as_1942_);
lean_closure_set(v___f_1952_, 4, v_stop_1943_);
lean_closure_set(v___f_1952_, 5, v_toApplicative_1950_);
v___x_1953_ = lean_array_fget(v_as_1942_, v_j_1944_);
lean_dec(v_j_1944_);
lean_dec_ref(v_as_1942_);
v___x_1954_ = lean_apply_1(v_p_1941_, v___x_1953_);
v___x_1955_ = lean_apply_4(v_toBind_1951_, lean_box(0), lean_box(0), v___x_1954_, v___f_1952_);
return v___x_1955_;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___redArg___lam__0(lean_object* v_j_1956_, lean_object* v_inst_1957_, lean_object* v_p_1958_, lean_object* v_as_1959_, lean_object* v_stop_1960_, lean_object* v_toApplicative_1961_, uint8_t v_____do__lift_1962_){
_start:
{
if (v_____do__lift_1962_ == 0)
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_dec_ref(v_toApplicative_1961_);
v___x_1963_ = lean_unsigned_to_nat(1u);
v___x_1964_ = lean_nat_add(v_j_1956_, v___x_1963_);
v___x_1965_ = l_Array_anyM_loop___redArg(v_inst_1957_, v_p_1958_, v_as_1959_, v_stop_1960_, v___x_1964_);
return v___x_1965_;
}
else
{
lean_object* v_toPure_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_dec(v_stop_1960_);
lean_dec_ref(v_as_1959_);
lean_dec(v_p_1958_);
lean_dec_ref(v_inst_1957_);
v_toPure_1966_ = lean_ctor_get(v_toApplicative_1961_, 1);
lean_inc(v_toPure_1966_);
lean_dec_ref(v_toApplicative_1961_);
v___x_1967_ = lean_box(v_____do__lift_1962_);
v___x_1968_ = lean_apply_2(v_toPure_1966_, lean_box(0), v___x_1967_);
return v___x_1968_;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop(lean_object* v_00_u03b1_1969_, lean_object* v_m_1970_, lean_object* v_inst_1971_, lean_object* v_p_1972_, lean_object* v_as_1973_, lean_object* v_stop_1974_, lean_object* v_h_1975_, lean_object* v_j_1976_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Array_anyM_loop___redArg(v_inst_1971_, v_p_1972_, v_as_1973_, v_stop_1974_, v_j_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0(lean_object* v_toPure_1978_, uint8_t v_____do__lift_1979_){
_start:
{
if (v_____do__lift_1979_ == 0)
{
uint8_t v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = 1;
v___x_1981_ = lean_box(v___x_1980_);
v___x_1982_ = lean_apply_2(v_toPure_1978_, lean_box(0), v___x_1981_);
return v___x_1982_;
}
else
{
uint8_t v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = 0;
v___x_1984_ = lean_box(v___x_1983_);
v___x_1985_ = lean_apply_2(v_toPure_1978_, lean_box(0), v___x_1984_);
return v___x_1985_;
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__0___boxed(lean_object* v_toPure_1986_, lean_object* v_____do__lift_1987_){
_start:
{
uint8_t v_____do__lift_123__boxed_1988_; lean_object* v_res_1989_; 
v_____do__lift_123__boxed_1988_ = lean_unbox(v_____do__lift_1987_);
v_res_1989_ = l_Array_allM___redArg___lam__0(v_toPure_1986_, v_____do__lift_123__boxed_1988_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1(lean_object* v_toPure_1990_, uint8_t v___x_1991_, uint8_t v_____do__lift_1992_){
_start:
{
if (v_____do__lift_1992_ == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = lean_box(v___x_1991_);
v___x_1994_ = lean_apply_2(v_toPure_1990_, lean_box(0), v___x_1993_);
return v___x_1994_;
}
else
{
uint8_t v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = 0;
v___x_1996_ = lean_box(v___x_1995_);
v___x_1997_ = lean_apply_2(v_toPure_1990_, lean_box(0), v___x_1996_);
return v___x_1997_;
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__1___boxed(lean_object* v_toPure_1998_, lean_object* v___x_1999_, lean_object* v_____do__lift_2000_){
_start:
{
uint8_t v___x_138__boxed_2001_; uint8_t v_____do__lift_139__boxed_2002_; lean_object* v_res_2003_; 
v___x_138__boxed_2001_ = lean_unbox(v___x_1999_);
v_____do__lift_139__boxed_2002_ = lean_unbox(v_____do__lift_2000_);
v_res_2003_ = l_Array_allM___redArg___lam__1(v_toPure_1998_, v___x_138__boxed_2001_, v_____do__lift_139__boxed_2002_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___lam__2(lean_object* v_p_2004_, lean_object* v_toBind_2005_, lean_object* v___f_2006_, lean_object* v_v_2007_){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_apply_1(v_p_2004_, v_v_2007_);
v___x_2009_ = lean_apply_4(v_toBind_2005_, lean_box(0), lean_box(0), v___x_2008_, v___f_2006_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg(lean_object* v_inst_2010_, lean_object* v_p_2011_, lean_object* v_as_2012_, lean_object* v_start_2013_, lean_object* v_stop_2014_){
_start:
{
lean_object* v_toApplicative_2015_; lean_object* v_toBind_2016_; lean_object* v_toPure_2017_; lean_object* v___f_2018_; uint8_t v___x_2019_; 
v_toApplicative_2015_ = lean_ctor_get(v_inst_2010_, 0);
v_toBind_2016_ = lean_ctor_get(v_inst_2010_, 1);
lean_inc(v_toBind_2016_);
v_toPure_2017_ = lean_ctor_get(v_toApplicative_2015_, 1);
lean_inc(v_toPure_2017_);
v___f_2018_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2018_, 0, v_toPure_2017_);
v___x_2019_ = lean_nat_dec_lt(v_start_2013_, v_stop_2014_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_inc(v_toPure_2017_);
lean_dec(v_stop_2014_);
lean_dec_ref(v_as_2012_);
lean_dec(v_p_2011_);
lean_dec_ref(v_inst_2010_);
v___x_2020_ = lean_box(v___x_2019_);
v___x_2021_ = lean_apply_2(v_toPure_2017_, lean_box(0), v___x_2020_);
v___x_2022_ = lean_apply_4(v_toBind_2016_, lean_box(0), lean_box(0), v___x_2021_, v___f_2018_);
return v___x_2022_;
}
else
{
lean_object* v___x_2023_; lean_object* v___f_2024_; lean_object* v___f_2025_; lean_object* v___y_2027_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2023_ = lean_box(v___x_2019_);
lean_inc(v_toPure_2017_);
v___f_2024_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2024_, 0, v_toPure_2017_);
lean_closure_set(v___f_2024_, 1, v___x_2023_);
lean_inc(v_toBind_2016_);
v___f_2025_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2025_, 0, v_p_2011_);
lean_closure_set(v___f_2025_, 1, v_toBind_2016_);
lean_closure_set(v___f_2025_, 2, v___f_2024_);
v___x_2036_ = lean_array_get_size(v_as_2012_);
v___x_2037_ = lean_nat_dec_le(v_stop_2014_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_dec(v_stop_2014_);
v___y_2027_ = v___x_2036_;
goto v___jp_2026_;
}
else
{
v___y_2027_ = v_stop_2014_;
goto v___jp_2026_;
}
v___jp_2026_:
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_nat_dec_lt(v_start_2013_, v___y_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
lean_inc(v_toPure_2017_);
lean_dec(v___y_2027_);
lean_dec_ref(v___f_2025_);
lean_dec_ref(v_as_2012_);
lean_dec_ref(v_inst_2010_);
v___x_2029_ = lean_box(v___x_2028_);
v___x_2030_ = lean_apply_2(v_toPure_2017_, lean_box(0), v___x_2029_);
v___x_2031_ = lean_apply_4(v_toBind_2016_, lean_box(0), lean_box(0), v___x_2030_, v___f_2018_);
return v___x_2031_;
}
else
{
size_t v___x_2032_; size_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2032_ = lean_usize_of_nat(v_start_2013_);
v___x_2033_ = lean_usize_of_nat(v___y_2027_);
lean_dec(v___y_2027_);
v___x_2034_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2010_, v___f_2025_, v_as_2012_, v___x_2032_, v___x_2033_);
v___x_2035_ = lean_apply_4(v_toBind_2016_, lean_box(0), lean_box(0), v___x_2034_, v___f_2018_);
return v___x_2035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___redArg___boxed(lean_object* v_inst_2038_, lean_object* v_p_2039_, lean_object* v_as_2040_, lean_object* v_start_2041_, lean_object* v_stop_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Array_allM___redArg(v_inst_2038_, v_p_2039_, v_as_2040_, v_start_2041_, v_stop_2042_);
lean_dec(v_start_2041_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Array_allM(lean_object* v_00_u03b1_2044_, lean_object* v_m_2045_, lean_object* v_inst_2046_, lean_object* v_p_2047_, lean_object* v_as_2048_, lean_object* v_start_2049_, lean_object* v_stop_2050_){
_start:
{
lean_object* v_toApplicative_2051_; lean_object* v_toBind_2052_; lean_object* v_toPure_2053_; lean_object* v___f_2054_; uint8_t v___x_2055_; 
v_toApplicative_2051_ = lean_ctor_get(v_inst_2046_, 0);
v_toBind_2052_ = lean_ctor_get(v_inst_2046_, 1);
lean_inc(v_toBind_2052_);
v_toPure_2053_ = lean_ctor_get(v_toApplicative_2051_, 1);
lean_inc(v_toPure_2053_);
v___f_2054_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2054_, 0, v_toPure_2053_);
v___x_2055_ = lean_nat_dec_lt(v_start_2049_, v_stop_2050_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_inc(v_toPure_2053_);
lean_dec(v_stop_2050_);
lean_dec_ref(v_as_2048_);
lean_dec(v_p_2047_);
lean_dec_ref(v_inst_2046_);
v___x_2056_ = lean_box(v___x_2055_);
v___x_2057_ = lean_apply_2(v_toPure_2053_, lean_box(0), v___x_2056_);
v___x_2058_ = lean_apply_4(v_toBind_2052_, lean_box(0), lean_box(0), v___x_2057_, v___f_2054_);
return v___x_2058_;
}
else
{
lean_object* v___x_2059_; lean_object* v___f_2060_; lean_object* v___f_2061_; lean_object* v___y_2063_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v___x_2059_ = lean_box(v___x_2055_);
lean_inc(v_toPure_2053_);
v___f_2060_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2060_, 0, v_toPure_2053_);
lean_closure_set(v___f_2060_, 1, v___x_2059_);
lean_inc(v_toBind_2052_);
v___f_2061_ = lean_alloc_closure((void*)(l_Array_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2061_, 0, v_p_2047_);
lean_closure_set(v___f_2061_, 1, v_toBind_2052_);
lean_closure_set(v___f_2061_, 2, v___f_2060_);
v___x_2072_ = lean_array_get_size(v_as_2048_);
v___x_2073_ = lean_nat_dec_le(v_stop_2050_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_dec(v_stop_2050_);
v___y_2063_ = v___x_2072_;
goto v___jp_2062_;
}
else
{
v___y_2063_ = v_stop_2050_;
goto v___jp_2062_;
}
v___jp_2062_:
{
uint8_t v___x_2064_; 
v___x_2064_ = lean_nat_dec_lt(v_start_2049_, v___y_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
lean_inc(v_toPure_2053_);
lean_dec(v___y_2063_);
lean_dec_ref(v___f_2061_);
lean_dec_ref(v_as_2048_);
lean_dec_ref(v_inst_2046_);
v___x_2065_ = lean_box(v___x_2064_);
v___x_2066_ = lean_apply_2(v_toPure_2053_, lean_box(0), v___x_2065_);
v___x_2067_ = lean_apply_4(v_toBind_2052_, lean_box(0), lean_box(0), v___x_2066_, v___f_2054_);
return v___x_2067_;
}
else
{
size_t v___x_2068_; size_t v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2068_ = lean_usize_of_nat(v_start_2049_);
v___x_2069_ = lean_usize_of_nat(v___y_2063_);
lean_dec(v___y_2063_);
v___x_2070_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v_inst_2046_, v___f_2061_, v_as_2048_, v___x_2068_, v___x_2069_);
v___x_2071_ = lean_apply_4(v_toBind_2052_, lean_box(0), lean_box(0), v___x_2070_, v___f_2054_);
return v___x_2071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM___boxed(lean_object* v_00_u03b1_2074_, lean_object* v_m_2075_, lean_object* v_inst_2076_, lean_object* v_p_2077_, lean_object* v_as_2078_, lean_object* v_start_2079_, lean_object* v_stop_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Array_allM(v_00_u03b1_2074_, v_m_2075_, v_inst_2076_, v_p_2077_, v_as_2078_, v_start_2079_, v_stop_2080_);
lean_dec(v_start_2079_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed(lean_object* v_inst_2082_, lean_object* v_f_2083_, lean_object* v_as_2084_, lean_object* v_n_2085_, lean_object* v_toPure_2086_, lean_object* v_r_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(v_inst_2082_, v_f_2083_, v_as_2084_, v_n_2085_, v_toPure_2086_, v_r_2087_);
lean_dec(v_n_2085_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(lean_object* v_inst_2089_, lean_object* v_f_2090_, lean_object* v_as_2091_, lean_object* v_i_2092_){
_start:
{
lean_object* v_toApplicative_2093_; lean_object* v_toBind_2094_; lean_object* v_toPure_2095_; lean_object* v_zero_2096_; uint8_t v_isZero_2097_; 
v_toApplicative_2093_ = lean_ctor_get(v_inst_2089_, 0);
v_toBind_2094_ = lean_ctor_get(v_inst_2089_, 1);
lean_inc(v_toBind_2094_);
v_toPure_2095_ = lean_ctor_get(v_toApplicative_2093_, 1);
lean_inc(v_toPure_2095_);
v_zero_2096_ = lean_unsigned_to_nat(0u);
v_isZero_2097_ = lean_nat_dec_eq(v_i_2092_, v_zero_2096_);
if (v_isZero_2097_ == 1)
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_dec(v_toBind_2094_);
lean_dec_ref(v_as_2091_);
lean_dec(v_f_2090_);
lean_dec_ref(v_inst_2089_);
v___x_2098_ = lean_box(0);
v___x_2099_ = lean_apply_2(v_toPure_2095_, lean_box(0), v___x_2098_);
return v___x_2099_;
}
else
{
lean_object* v_one_2100_; lean_object* v_n_2101_; lean_object* v___f_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v_one_2100_ = lean_unsigned_to_nat(1u);
v_n_2101_ = lean_nat_sub(v_i_2092_, v_one_2100_);
lean_inc(v_n_2101_);
lean_inc_ref(v_as_2091_);
lean_inc(v_f_2090_);
v___f_2102_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2102_, 0, v_inst_2089_);
lean_closure_set(v___f_2102_, 1, v_f_2090_);
lean_closure_set(v___f_2102_, 2, v_as_2091_);
lean_closure_set(v___f_2102_, 3, v_n_2101_);
lean_closure_set(v___f_2102_, 4, v_toPure_2095_);
v___x_2103_ = lean_array_fget(v_as_2091_, v_n_2101_);
lean_dec(v_n_2101_);
lean_dec_ref(v_as_2091_);
v___x_2104_ = lean_apply_1(v_f_2090_, v___x_2103_);
v___x_2105_ = lean_apply_4(v_toBind_2094_, lean_box(0), lean_box(0), v___x_2104_, v___f_2102_);
return v___x_2105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___lam__0(lean_object* v_inst_2106_, lean_object* v_f_2107_, lean_object* v_as_2108_, lean_object* v_n_2109_, lean_object* v_toPure_2110_, lean_object* v_r_2111_){
_start:
{
if (lean_obj_tag(v_r_2111_) == 0)
{
lean_object* v___x_2112_; 
lean_dec(v_toPure_2110_);
v___x_2112_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2106_, v_f_2107_, v_as_2108_, v_n_2109_);
return v___x_2112_;
}
else
{
lean_object* v___x_2113_; 
lean_dec_ref(v_as_2108_);
lean_dec(v_f_2107_);
lean_dec_ref(v_inst_2106_);
v___x_2113_ = lean_apply_2(v_toPure_2110_, lean_box(0), v_r_2111_);
return v___x_2113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg___boxed(lean_object* v_inst_2114_, lean_object* v_f_2115_, lean_object* v_as_2116_, lean_object* v_i_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2114_, v_f_2115_, v_as_2116_, v_i_2117_);
lean_dec(v_i_2117_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_object* v_00_u03b1_2119_, lean_object* v_00_u03b2_2120_, lean_object* v_m_2121_, lean_object* v_inst_2122_, lean_object* v_f_2123_, lean_object* v_as_2124_, lean_object* v_i_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2122_, v_f_2123_, v_as_2124_, v_i_2125_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___boxed(lean_object* v_00_u03b1_2128_, lean_object* v_00_u03b2_2129_, lean_object* v_m_2130_, lean_object* v_inst_2131_, lean_object* v_f_2132_, lean_object* v_as_2133_, lean_object* v_i_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(v_00_u03b1_2128_, v_00_u03b2_2129_, v_m_2130_, v_inst_2131_, v_f_2132_, v_as_2133_, v_i_2134_, v_a_2135_);
lean_dec(v_i_2134_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f___redArg(lean_object* v_inst_2137_, lean_object* v_f_2138_, lean_object* v_as_2139_){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = lean_array_get_size(v_as_2139_);
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2137_, v_f_2138_, v_as_2139_, v___x_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f(lean_object* v_00_u03b1_2142_, lean_object* v_00_u03b2_2143_, lean_object* v_m_2144_, lean_object* v_inst_2145_, lean_object* v_f_2146_, lean_object* v_as_2147_){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = lean_array_get_size(v_as_2147_);
v___x_2149_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2145_, v_f_2146_, v_as_2147_, v___x_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2150_, lean_object* v_a_2151_, uint8_t v_____do__lift_2152_){
_start:
{
if (v_____do__lift_2152_ == 0)
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_dec(v_a_2151_);
v___x_2153_ = lean_box(0);
v___x_2154_ = lean_apply_2(v_toPure_2150_, lean_box(0), v___x_2153_);
return v___x_2154_;
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2155_, 0, v_a_2151_);
v___x_2156_ = lean_apply_2(v_toPure_2150_, lean_box(0), v___x_2155_);
return v___x_2156_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2157_, lean_object* v_a_2158_, lean_object* v_____do__lift_2159_){
_start:
{
uint8_t v_____do__lift_74__boxed_2160_; lean_object* v_res_2161_; 
v_____do__lift_74__boxed_2160_ = lean_unbox(v_____do__lift_2159_);
v_res_2161_ = l_Array_findRevM_x3f___redArg___lam__0(v_toPure_2157_, v_a_2158_, v_____do__lift_74__boxed_2160_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2162_, lean_object* v_p_2163_, lean_object* v_toBind_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v___f_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_inc(v_a_2165_);
v___f_2166_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2166_, 0, v_toPure_2162_);
lean_closure_set(v___f_2166_, 1, v_a_2165_);
v___x_2167_ = lean_apply_1(v_p_2163_, v_a_2165_);
v___x_2168_ = lean_apply_4(v_toBind_2164_, lean_box(0), lean_box(0), v___x_2167_, v___f_2166_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___redArg(lean_object* v_inst_2169_, lean_object* v_p_2170_, lean_object* v_as_2171_){
_start:
{
lean_object* v_toApplicative_2172_; lean_object* v_toBind_2173_; lean_object* v_toPure_2174_; lean_object* v___f_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v_toApplicative_2172_ = lean_ctor_get(v_inst_2169_, 0);
v_toBind_2173_ = lean_ctor_get(v_inst_2169_, 1);
v_toPure_2174_ = lean_ctor_get(v_toApplicative_2172_, 1);
lean_inc(v_toBind_2173_);
lean_inc(v_toPure_2174_);
v___f_2175_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2175_, 0, v_toPure_2174_);
lean_closure_set(v___f_2175_, 1, v_p_2170_);
lean_closure_set(v___f_2175_, 2, v_toBind_2173_);
v___x_2176_ = lean_array_get_size(v_as_2171_);
v___x_2177_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2169_, v___f_2175_, v_as_2171_, v___x_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f(lean_object* v_00_u03b1_2178_, lean_object* v_m_2179_, lean_object* v_inst_2180_, lean_object* v_p_2181_, lean_object* v_as_2182_){
_start:
{
lean_object* v_toApplicative_2183_; lean_object* v_toBind_2184_; lean_object* v_toPure_2185_; lean_object* v___f_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v_toApplicative_2183_ = lean_ctor_get(v_inst_2180_, 0);
v_toBind_2184_ = lean_ctor_get(v_inst_2180_, 1);
v_toPure_2185_ = lean_ctor_get(v_toApplicative_2183_, 1);
lean_inc(v_toBind_2184_);
lean_inc(v_toPure_2185_);
v___f_2186_ = lean_alloc_closure((void*)(l_Array_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2186_, 0, v_toPure_2185_);
lean_closure_set(v___f_2186_, 1, v_p_2181_);
lean_closure_set(v___f_2186_, 2, v_toBind_2184_);
v___x_2187_ = lean_array_get_size(v_as_2182_);
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v_inst_2180_, v___f_2186_, v_as_2182_, v___x_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___lam__0(lean_object* v_f_2189_, lean_object* v_x_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = lean_apply_1(v_f_2189_, v___y_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg(lean_object* v_inst_2193_, lean_object* v_f_2194_, lean_object* v_as_2195_, lean_object* v_start_2196_, lean_object* v_stop_2197_){
_start:
{
lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2198_ = lean_box(0);
v___x_2199_ = lean_nat_dec_lt(v_start_2196_, v_stop_2197_);
if (v___x_2199_ == 0)
{
lean_object* v_toApplicative_2200_; lean_object* v_toPure_2201_; lean_object* v___x_2202_; 
lean_dec_ref(v_as_2195_);
lean_dec(v_f_2194_);
v_toApplicative_2200_ = lean_ctor_get(v_inst_2193_, 0);
lean_inc_ref(v_toApplicative_2200_);
lean_dec_ref(v_inst_2193_);
v_toPure_2201_ = lean_ctor_get(v_toApplicative_2200_, 1);
lean_inc(v_toPure_2201_);
lean_dec_ref(v_toApplicative_2200_);
v___x_2202_ = lean_apply_2(v_toPure_2201_, lean_box(0), v___x_2198_);
return v___x_2202_;
}
else
{
lean_object* v___f_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___f_2203_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2203_, 0, v_f_2194_);
v___x_2204_ = lean_array_get_size(v_as_2195_);
v___x_2205_ = lean_nat_dec_le(v_stop_2197_, v___x_2204_);
if (v___x_2205_ == 0)
{
uint8_t v___x_2206_; 
v___x_2206_ = lean_nat_dec_lt(v_start_2196_, v___x_2204_);
if (v___x_2206_ == 0)
{
lean_object* v_toApplicative_2207_; lean_object* v_toPure_2208_; lean_object* v___x_2209_; 
lean_dec_ref(v___f_2203_);
lean_dec_ref(v_as_2195_);
v_toApplicative_2207_ = lean_ctor_get(v_inst_2193_, 0);
lean_inc_ref(v_toApplicative_2207_);
lean_dec_ref(v_inst_2193_);
v_toPure_2208_ = lean_ctor_get(v_toApplicative_2207_, 1);
lean_inc(v_toPure_2208_);
lean_dec_ref(v_toApplicative_2207_);
v___x_2209_ = lean_apply_2(v_toPure_2208_, lean_box(0), v___x_2198_);
return v___x_2209_;
}
else
{
size_t v___x_2210_; size_t v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_usize_of_nat(v_start_2196_);
v___x_2211_ = lean_usize_of_nat(v___x_2204_);
v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2193_, v___f_2203_, v_as_2195_, v___x_2210_, v___x_2211_, v___x_2198_);
return v___x_2212_;
}
}
else
{
size_t v___x_2213_; size_t v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = lean_usize_of_nat(v_start_2196_);
v___x_2214_ = lean_usize_of_nat(v_stop_2197_);
v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2193_, v___f_2203_, v_as_2195_, v___x_2213_, v___x_2214_, v___x_2198_);
return v___x_2215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___redArg___boxed(lean_object* v_inst_2216_, lean_object* v_f_2217_, lean_object* v_as_2218_, lean_object* v_start_2219_, lean_object* v_stop_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Array_forM___redArg(v_inst_2216_, v_f_2217_, v_as_2218_, v_start_2219_, v_stop_2220_);
lean_dec(v_stop_2220_);
lean_dec(v_start_2219_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Array_forM(lean_object* v_00_u03b1_2222_, lean_object* v_m_2223_, lean_object* v_inst_2224_, lean_object* v_f_2225_, lean_object* v_as_2226_, lean_object* v_start_2227_, lean_object* v_stop_2228_){
_start:
{
lean_object* v___x_2229_; uint8_t v___x_2230_; 
v___x_2229_ = lean_box(0);
v___x_2230_ = lean_nat_dec_lt(v_start_2227_, v_stop_2228_);
if (v___x_2230_ == 0)
{
lean_object* v_toApplicative_2231_; lean_object* v_toPure_2232_; lean_object* v___x_2233_; 
lean_dec_ref(v_as_2226_);
lean_dec(v_f_2225_);
v_toApplicative_2231_ = lean_ctor_get(v_inst_2224_, 0);
lean_inc_ref(v_toApplicative_2231_);
lean_dec_ref(v_inst_2224_);
v_toPure_2232_ = lean_ctor_get(v_toApplicative_2231_, 1);
lean_inc(v_toPure_2232_);
lean_dec_ref(v_toApplicative_2231_);
v___x_2233_ = lean_apply_2(v_toPure_2232_, lean_box(0), v___x_2229_);
return v___x_2233_;
}
else
{
lean_object* v___f_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; 
v___f_2234_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2234_, 0, v_f_2225_);
v___x_2235_ = lean_array_get_size(v_as_2226_);
v___x_2236_ = lean_nat_dec_le(v_stop_2228_, v___x_2235_);
if (v___x_2236_ == 0)
{
uint8_t v___x_2237_; 
v___x_2237_ = lean_nat_dec_lt(v_start_2227_, v___x_2235_);
if (v___x_2237_ == 0)
{
lean_object* v_toApplicative_2238_; lean_object* v_toPure_2239_; lean_object* v___x_2240_; 
lean_dec_ref(v___f_2234_);
lean_dec_ref(v_as_2226_);
v_toApplicative_2238_ = lean_ctor_get(v_inst_2224_, 0);
lean_inc_ref(v_toApplicative_2238_);
lean_dec_ref(v_inst_2224_);
v_toPure_2239_ = lean_ctor_get(v_toApplicative_2238_, 1);
lean_inc(v_toPure_2239_);
lean_dec_ref(v_toApplicative_2238_);
v___x_2240_ = lean_apply_2(v_toPure_2239_, lean_box(0), v___x_2229_);
return v___x_2240_;
}
else
{
size_t v___x_2241_; size_t v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = lean_usize_of_nat(v_start_2227_);
v___x_2242_ = lean_usize_of_nat(v___x_2235_);
v___x_2243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2224_, v___f_2234_, v_as_2226_, v___x_2241_, v___x_2242_, v___x_2229_);
return v___x_2243_;
}
}
else
{
size_t v___x_2244_; size_t v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = lean_usize_of_nat(v_start_2227_);
v___x_2245_ = lean_usize_of_nat(v_stop_2228_);
v___x_2246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2224_, v___f_2234_, v_as_2226_, v___x_2244_, v___x_2245_, v___x_2229_);
return v___x_2246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM___boxed(lean_object* v_00_u03b1_2247_, lean_object* v_m_2248_, lean_object* v_inst_2249_, lean_object* v_f_2250_, lean_object* v_as_2251_, lean_object* v_start_2252_, lean_object* v_stop_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Array_forM(v_00_u03b1_2247_, v_m_2248_, v_inst_2249_, v_f_2250_, v_as_2251_, v_start_2252_, v_stop_2253_);
lean_dec(v_stop_2253_);
lean_dec(v_start_2252_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg___lam__1(lean_object* v_inst_2255_, lean_object* v_xs_2256_, lean_object* v_f_2257_){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
v___x_2258_ = lean_unsigned_to_nat(0u);
v___x_2259_ = lean_array_get_size(v_xs_2256_);
v___x_2260_ = lean_box(0);
v___x_2261_ = lean_nat_dec_lt(v___x_2258_, v___x_2259_);
if (v___x_2261_ == 0)
{
lean_object* v_toApplicative_2262_; lean_object* v_toPure_2263_; lean_object* v___x_2264_; 
lean_dec(v_f_2257_);
lean_dec_ref(v_xs_2256_);
v_toApplicative_2262_ = lean_ctor_get(v_inst_2255_, 0);
lean_inc_ref(v_toApplicative_2262_);
lean_dec_ref(v_inst_2255_);
v_toPure_2263_ = lean_ctor_get(v_toApplicative_2262_, 1);
lean_inc(v_toPure_2263_);
lean_dec_ref(v_toApplicative_2262_);
v___x_2264_ = lean_apply_2(v_toPure_2263_, lean_box(0), v___x_2260_);
return v___x_2264_;
}
else
{
lean_object* v___f_2265_; uint8_t v___x_2266_; 
v___f_2265_ = lean_alloc_closure((void*)(l_Array_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2265_, 0, v_f_2257_);
v___x_2266_ = lean_nat_dec_le(v___x_2259_, v___x_2259_);
if (v___x_2266_ == 0)
{
if (v___x_2261_ == 0)
{
lean_object* v_toApplicative_2267_; lean_object* v_toPure_2268_; lean_object* v___x_2269_; 
lean_dec_ref(v___f_2265_);
lean_dec_ref(v_xs_2256_);
v_toApplicative_2267_ = lean_ctor_get(v_inst_2255_, 0);
lean_inc_ref(v_toApplicative_2267_);
lean_dec_ref(v_inst_2255_);
v_toPure_2268_ = lean_ctor_get(v_toApplicative_2267_, 1);
lean_inc(v_toPure_2268_);
lean_dec_ref(v_toApplicative_2267_);
v___x_2269_ = lean_apply_2(v_toPure_2268_, lean_box(0), v___x_2260_);
return v___x_2269_;
}
else
{
size_t v___x_2270_; size_t v___x_2271_; lean_object* v___x_2272_; 
v___x_2270_ = ((size_t)0ULL);
v___x_2271_ = lean_usize_of_nat(v___x_2259_);
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2255_, v___f_2265_, v_xs_2256_, v___x_2270_, v___x_2271_, v___x_2260_);
return v___x_2272_;
}
}
else
{
size_t v___x_2273_; size_t v___x_2274_; lean_object* v___x_2275_; 
v___x_2273_ = ((size_t)0ULL);
v___x_2274_ = lean_usize_of_nat(v___x_2259_);
v___x_2275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_2255_, v___f_2265_, v_xs_2256_, v___x_2273_, v___x_2274_, v___x_2260_);
return v___x_2275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad___redArg(lean_object* v_inst_2276_){
_start:
{
lean_object* v___f_2277_; 
v___f_2277_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2277_, 0, v_inst_2276_);
return v___f_2277_;
}
}
LEAN_EXPORT lean_object* l_Array_instForMOfMonad(lean_object* v_00_u03b1_2278_, lean_object* v_m_2279_, lean_object* v_inst_2280_){
_start:
{
lean_object* v___f_2281_; 
v___f_2281_ = lean_alloc_closure((void*)(l_Array_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2281_, 0, v_inst_2280_);
return v___f_2281_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___lam__0(lean_object* v_f_2282_, lean_object* v_a_2283_, lean_object* v_x_2284_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = lean_apply_1(v_f_2282_, v_a_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg(lean_object* v_inst_2286_, lean_object* v_f_2287_, lean_object* v_as_2288_, lean_object* v_start_2289_, lean_object* v_stop_2290_){
_start:
{
lean_object* v___f_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___f_2291_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2291_, 0, v_f_2287_);
v___x_2292_ = lean_box(0);
v___x_2293_ = lean_array_get_size(v_as_2288_);
v___x_2294_ = lean_nat_dec_le(v_start_2289_, v___x_2293_);
if (v___x_2294_ == 0)
{
uint8_t v___x_2295_; 
v___x_2295_ = lean_nat_dec_lt(v_stop_2290_, v___x_2293_);
if (v___x_2295_ == 0)
{
lean_object* v_toApplicative_2296_; lean_object* v_toPure_2297_; lean_object* v___x_2298_; 
lean_dec_ref(v___f_2291_);
lean_dec_ref(v_as_2288_);
v_toApplicative_2296_ = lean_ctor_get(v_inst_2286_, 0);
lean_inc_ref(v_toApplicative_2296_);
lean_dec_ref(v_inst_2286_);
v_toPure_2297_ = lean_ctor_get(v_toApplicative_2296_, 1);
lean_inc(v_toPure_2297_);
lean_dec_ref(v_toApplicative_2296_);
v___x_2298_ = lean_apply_2(v_toPure_2297_, lean_box(0), v___x_2292_);
return v___x_2298_;
}
else
{
size_t v___x_2299_; size_t v___x_2300_; lean_object* v___x_2301_; 
v___x_2299_ = lean_usize_of_nat(v___x_2293_);
v___x_2300_ = lean_usize_of_nat(v_stop_2290_);
v___x_2301_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2286_, v___f_2291_, v_as_2288_, v___x_2299_, v___x_2300_, v___x_2292_);
return v___x_2301_;
}
}
else
{
uint8_t v___x_2302_; 
v___x_2302_ = lean_nat_dec_lt(v_stop_2290_, v_start_2289_);
if (v___x_2302_ == 0)
{
lean_object* v_toApplicative_2303_; lean_object* v_toPure_2304_; lean_object* v___x_2305_; 
lean_dec_ref(v___f_2291_);
lean_dec_ref(v_as_2288_);
v_toApplicative_2303_ = lean_ctor_get(v_inst_2286_, 0);
lean_inc_ref(v_toApplicative_2303_);
lean_dec_ref(v_inst_2286_);
v_toPure_2304_ = lean_ctor_get(v_toApplicative_2303_, 1);
lean_inc(v_toPure_2304_);
lean_dec_ref(v_toApplicative_2303_);
v___x_2305_ = lean_apply_2(v_toPure_2304_, lean_box(0), v___x_2292_);
return v___x_2305_;
}
else
{
size_t v___x_2306_; size_t v___x_2307_; lean_object* v___x_2308_; 
v___x_2306_ = lean_usize_of_nat(v_start_2289_);
v___x_2307_ = lean_usize_of_nat(v_stop_2290_);
v___x_2308_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2286_, v___f_2291_, v_as_2288_, v___x_2306_, v___x_2307_, v___x_2292_);
return v___x_2308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___redArg___boxed(lean_object* v_inst_2309_, lean_object* v_f_2310_, lean_object* v_as_2311_, lean_object* v_start_2312_, lean_object* v_stop_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Array_forRevM___redArg(v_inst_2309_, v_f_2310_, v_as_2311_, v_start_2312_, v_stop_2313_);
lean_dec(v_stop_2313_);
lean_dec(v_start_2312_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM(lean_object* v_00_u03b1_2315_, lean_object* v_m_2316_, lean_object* v_inst_2317_, lean_object* v_f_2318_, lean_object* v_as_2319_, lean_object* v_start_2320_, lean_object* v_stop_2321_){
_start:
{
lean_object* v___f_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___f_2322_ = lean_alloc_closure((void*)(l_Array_forRevM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2322_, 0, v_f_2318_);
v___x_2323_ = lean_box(0);
v___x_2324_ = lean_array_get_size(v_as_2319_);
v___x_2325_ = lean_nat_dec_le(v_start_2320_, v___x_2324_);
if (v___x_2325_ == 0)
{
uint8_t v___x_2326_; 
v___x_2326_ = lean_nat_dec_lt(v_stop_2321_, v___x_2324_);
if (v___x_2326_ == 0)
{
lean_object* v_toApplicative_2327_; lean_object* v_toPure_2328_; lean_object* v___x_2329_; 
lean_dec_ref(v___f_2322_);
lean_dec_ref(v_as_2319_);
v_toApplicative_2327_ = lean_ctor_get(v_inst_2317_, 0);
lean_inc_ref(v_toApplicative_2327_);
lean_dec_ref(v_inst_2317_);
v_toPure_2328_ = lean_ctor_get(v_toApplicative_2327_, 1);
lean_inc(v_toPure_2328_);
lean_dec_ref(v_toApplicative_2327_);
v___x_2329_ = lean_apply_2(v_toPure_2328_, lean_box(0), v___x_2323_);
return v___x_2329_;
}
else
{
size_t v___x_2330_; size_t v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = lean_usize_of_nat(v___x_2324_);
v___x_2331_ = lean_usize_of_nat(v_stop_2321_);
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2317_, v___f_2322_, v_as_2319_, v___x_2330_, v___x_2331_, v___x_2323_);
return v___x_2332_;
}
}
else
{
uint8_t v___x_2333_; 
v___x_2333_ = lean_nat_dec_lt(v_stop_2321_, v_start_2320_);
if (v___x_2333_ == 0)
{
lean_object* v_toApplicative_2334_; lean_object* v_toPure_2335_; lean_object* v___x_2336_; 
lean_dec_ref(v___f_2322_);
lean_dec_ref(v_as_2319_);
v_toApplicative_2334_ = lean_ctor_get(v_inst_2317_, 0);
lean_inc_ref(v_toApplicative_2334_);
lean_dec_ref(v_inst_2317_);
v_toPure_2335_ = lean_ctor_get(v_toApplicative_2334_, 1);
lean_inc(v_toPure_2335_);
lean_dec_ref(v_toApplicative_2334_);
v___x_2336_ = lean_apply_2(v_toPure_2335_, lean_box(0), v___x_2323_);
return v___x_2336_;
}
else
{
size_t v___x_2337_; size_t v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = lean_usize_of_nat(v_start_2320_);
v___x_2338_ = lean_usize_of_nat(v_stop_2321_);
v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_2317_, v___f_2322_, v_as_2319_, v___x_2337_, v___x_2338_, v___x_2323_);
return v___x_2339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___boxed(lean_object* v_00_u03b1_2340_, lean_object* v_m_2341_, lean_object* v_inst_2342_, lean_object* v_f_2343_, lean_object* v_as_2344_, lean_object* v_start_2345_, lean_object* v_stop_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Array_forRevM(v_00_u03b1_2340_, v_m_2341_, v_inst_2342_, v_f_2343_, v_as_2344_, v_start_2345_, v_stop_2346_);
lean_dec(v_stop_2346_);
lean_dec(v_start_2345_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___lam__0(lean_object* v_f_2348_, lean_object* v_x1_2349_, lean_object* v_x2_2350_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = lean_apply_2(v_f_2348_, v_x1_2349_, v_x2_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg(lean_object* v_f_2371_, lean_object* v_init_2372_, lean_object* v_as_2373_, lean_object* v_start_2374_, lean_object* v_stop_2375_){
_start:
{
lean_object* v___x_2376_; uint8_t v___x_2377_; 
v___x_2376_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2377_ = lean_nat_dec_lt(v_start_2374_, v_stop_2375_);
if (v___x_2377_ == 0)
{
lean_dec_ref(v_as_2373_);
lean_dec(v_f_2371_);
return v_init_2372_;
}
else
{
lean_object* v___f_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___f_2378_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2378_, 0, v_f_2371_);
v___x_2379_ = lean_array_get_size(v_as_2373_);
v___x_2380_ = lean_nat_dec_le(v_stop_2375_, v___x_2379_);
if (v___x_2380_ == 0)
{
uint8_t v___x_2381_; 
v___x_2381_ = lean_nat_dec_lt(v_start_2374_, v___x_2379_);
if (v___x_2381_ == 0)
{
lean_dec_ref(v___f_2378_);
lean_dec_ref(v_as_2373_);
return v_init_2372_;
}
else
{
size_t v___x_2382_; size_t v___x_2383_; lean_object* v___x_2384_; 
v___x_2382_ = lean_usize_of_nat(v_start_2374_);
v___x_2383_ = lean_usize_of_nat(v___x_2379_);
v___x_2384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2376_, v___f_2378_, v_as_2373_, v___x_2382_, v___x_2383_, v_init_2372_);
return v___x_2384_;
}
}
else
{
size_t v___x_2385_; size_t v___x_2386_; lean_object* v___x_2387_; 
v___x_2385_ = lean_usize_of_nat(v_start_2374_);
v___x_2386_ = lean_usize_of_nat(v_stop_2375_);
v___x_2387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2376_, v___f_2378_, v_as_2373_, v___x_2385_, v___x_2386_, v_init_2372_);
return v___x_2387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___redArg___boxed(lean_object* v_f_2388_, lean_object* v_init_2389_, lean_object* v_as_2390_, lean_object* v_start_2391_, lean_object* v_stop_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Array_foldl___redArg(v_f_2388_, v_init_2389_, v_as_2390_, v_start_2391_, v_stop_2392_);
lean_dec(v_stop_2392_);
lean_dec(v_start_2391_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Array_foldl(lean_object* v_00_u03b1_2394_, lean_object* v_00_u03b2_2395_, lean_object* v_f_2396_, lean_object* v_init_2397_, lean_object* v_as_2398_, lean_object* v_start_2399_, lean_object* v_stop_2400_){
_start:
{
lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2401_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2402_ = lean_nat_dec_lt(v_start_2399_, v_stop_2400_);
if (v___x_2402_ == 0)
{
lean_dec_ref(v_as_2398_);
lean_dec(v_f_2396_);
return v_init_2397_;
}
else
{
lean_object* v___f_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___f_2403_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2403_, 0, v_f_2396_);
v___x_2404_ = lean_array_get_size(v_as_2398_);
v___x_2405_ = lean_nat_dec_le(v_stop_2400_, v___x_2404_);
if (v___x_2405_ == 0)
{
uint8_t v___x_2406_; 
v___x_2406_ = lean_nat_dec_lt(v_start_2399_, v___x_2404_);
if (v___x_2406_ == 0)
{
lean_dec_ref(v___f_2403_);
lean_dec_ref(v_as_2398_);
return v_init_2397_;
}
else
{
size_t v___x_2407_; size_t v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = lean_usize_of_nat(v_start_2399_);
v___x_2408_ = lean_usize_of_nat(v___x_2404_);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2401_, v___f_2403_, v_as_2398_, v___x_2407_, v___x_2408_, v_init_2397_);
return v___x_2409_;
}
}
else
{
size_t v___x_2410_; size_t v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = lean_usize_of_nat(v_start_2399_);
v___x_2411_ = lean_usize_of_nat(v_stop_2400_);
v___x_2412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_2401_, v___f_2403_, v_as_2398_, v___x_2410_, v___x_2411_, v_init_2397_);
return v___x_2412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl___boxed(lean_object* v_00_u03b1_2413_, lean_object* v_00_u03b2_2414_, lean_object* v_f_2415_, lean_object* v_init_2416_, lean_object* v_as_2417_, lean_object* v_start_2418_, lean_object* v_stop_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Array_foldl(v_00_u03b1_2413_, v_00_u03b2_2414_, v_f_2415_, v_init_2416_, v_as_2417_, v_start_2418_, v_stop_2419_);
lean_dec(v_stop_2419_);
lean_dec(v_start_2418_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg(lean_object* v_f_2421_, lean_object* v_init_2422_, lean_object* v_as_2423_, lean_object* v_start_2424_, lean_object* v_stop_2425_){
_start:
{
lean_object* v___f_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; 
v___f_2426_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2426_, 0, v_f_2421_);
v___x_2427_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2428_ = lean_array_get_size(v_as_2423_);
v___x_2429_ = lean_nat_dec_le(v_start_2424_, v___x_2428_);
if (v___x_2429_ == 0)
{
uint8_t v___x_2430_; 
v___x_2430_ = lean_nat_dec_lt(v_stop_2425_, v___x_2428_);
if (v___x_2430_ == 0)
{
lean_dec_ref(v___f_2426_);
lean_dec_ref(v_as_2423_);
return v_init_2422_;
}
else
{
size_t v___x_2431_; size_t v___x_2432_; lean_object* v___x_2433_; 
v___x_2431_ = lean_usize_of_nat(v___x_2428_);
v___x_2432_ = lean_usize_of_nat(v_stop_2425_);
v___x_2433_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2427_, v___f_2426_, v_as_2423_, v___x_2431_, v___x_2432_, v_init_2422_);
return v___x_2433_;
}
}
else
{
uint8_t v___x_2434_; 
v___x_2434_ = lean_nat_dec_lt(v_stop_2425_, v_start_2424_);
if (v___x_2434_ == 0)
{
lean_dec_ref(v___f_2426_);
lean_dec_ref(v_as_2423_);
return v_init_2422_;
}
else
{
size_t v___x_2435_; size_t v___x_2436_; lean_object* v___x_2437_; 
v___x_2435_ = lean_usize_of_nat(v_start_2424_);
v___x_2436_ = lean_usize_of_nat(v_stop_2425_);
v___x_2437_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2427_, v___f_2426_, v_as_2423_, v___x_2435_, v___x_2436_, v_init_2422_);
return v___x_2437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___redArg___boxed(lean_object* v_f_2438_, lean_object* v_init_2439_, lean_object* v_as_2440_, lean_object* v_start_2441_, lean_object* v_stop_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Array_foldr___redArg(v_f_2438_, v_init_2439_, v_as_2440_, v_start_2441_, v_stop_2442_);
lean_dec(v_stop_2442_);
lean_dec(v_start_2441_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Array_foldr(lean_object* v_00_u03b1_2444_, lean_object* v_00_u03b2_2445_, lean_object* v_f_2446_, lean_object* v_init_2447_, lean_object* v_as_2448_, lean_object* v_start_2449_, lean_object* v_stop_2450_){
_start:
{
lean_object* v___f_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___f_2451_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2451_, 0, v_f_2446_);
v___x_2452_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2453_ = lean_array_get_size(v_as_2448_);
v___x_2454_ = lean_nat_dec_le(v_start_2449_, v___x_2453_);
if (v___x_2454_ == 0)
{
uint8_t v___x_2455_; 
v___x_2455_ = lean_nat_dec_lt(v_stop_2450_, v___x_2453_);
if (v___x_2455_ == 0)
{
lean_dec_ref(v___f_2451_);
lean_dec_ref(v_as_2448_);
return v_init_2447_;
}
else
{
size_t v___x_2456_; size_t v___x_2457_; lean_object* v___x_2458_; 
v___x_2456_ = lean_usize_of_nat(v___x_2453_);
v___x_2457_ = lean_usize_of_nat(v_stop_2450_);
v___x_2458_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2452_, v___f_2451_, v_as_2448_, v___x_2456_, v___x_2457_, v_init_2447_);
return v___x_2458_;
}
}
else
{
uint8_t v___x_2459_; 
v___x_2459_ = lean_nat_dec_lt(v_stop_2450_, v_start_2449_);
if (v___x_2459_ == 0)
{
lean_dec_ref(v___f_2451_);
lean_dec_ref(v_as_2448_);
return v_init_2447_;
}
else
{
size_t v___x_2460_; size_t v___x_2461_; lean_object* v___x_2462_; 
v___x_2460_ = lean_usize_of_nat(v_start_2449_);
v___x_2461_ = lean_usize_of_nat(v_stop_2450_);
v___x_2462_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2452_, v___f_2451_, v_as_2448_, v___x_2460_, v___x_2461_, v_init_2447_);
return v___x_2462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr___boxed(lean_object* v_00_u03b1_2463_, lean_object* v_00_u03b2_2464_, lean_object* v_f_2465_, lean_object* v_init_2466_, lean_object* v_as_2467_, lean_object* v_start_2468_, lean_object* v_stop_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Array_foldr(v_00_u03b1_2463_, v_00_u03b2_2464_, v_f_2465_, v_init_2466_, v_as_2467_, v_start_2468_, v_stop_2469_);
lean_dec(v_stop_2469_);
lean_dec(v_start_2468_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg___lam__0(lean_object* v_inst_2471_, lean_object* v_x1_2472_, lean_object* v_x2_2473_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_apply_2(v_inst_2471_, v_x1_2472_, v_x2_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Array_sum___redArg(lean_object* v_inst_2475_, lean_object* v_inst_2476_, lean_object* v_as_2477_){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v___x_2478_ = lean_array_get_size(v_as_2477_);
v___x_2479_ = lean_unsigned_to_nat(0u);
v___x_2480_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2481_ = lean_nat_dec_lt(v___x_2479_, v___x_2478_);
if (v___x_2481_ == 0)
{
lean_dec_ref(v_as_2477_);
lean_dec(v_inst_2475_);
return v_inst_2476_;
}
else
{
lean_object* v___f_2482_; size_t v___x_2483_; size_t v___x_2484_; lean_object* v___x_2485_; 
v___f_2482_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2482_, 0, v_inst_2475_);
v___x_2483_ = lean_usize_of_nat(v___x_2478_);
v___x_2484_ = ((size_t)0ULL);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2480_, v___f_2482_, v_as_2477_, v___x_2483_, v___x_2484_, v_inst_2476_);
return v___x_2485_;
}
}
}
LEAN_EXPORT lean_object* l_Array_sum(lean_object* v_00_u03b1_2486_, lean_object* v_inst_2487_, lean_object* v_inst_2488_, lean_object* v_as_2489_){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2490_ = lean_array_get_size(v_as_2489_);
v___x_2491_ = lean_unsigned_to_nat(0u);
v___x_2492_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2493_ = lean_nat_dec_lt(v___x_2491_, v___x_2490_);
if (v___x_2493_ == 0)
{
lean_dec_ref(v_as_2489_);
lean_dec(v_inst_2487_);
return v_inst_2488_;
}
else
{
lean_object* v___f_2494_; size_t v___x_2495_; size_t v___x_2496_; lean_object* v___x_2497_; 
v___f_2494_ = lean_alloc_closure((void*)(l_Array_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2494_, 0, v_inst_2487_);
v___x_2495_ = lean_usize_of_nat(v___x_2490_);
v___x_2496_ = ((size_t)0ULL);
v___x_2497_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2492_, v___f_2494_, v_as_2489_, v___x_2495_, v___x_2496_, v_inst_2488_);
return v___x_2497_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0(lean_object* v_p_2498_, lean_object* v_x1_2499_, lean_object* v_x2_2500_){
_start:
{
lean_object* v___x_2501_; uint8_t v___x_2502_; 
v___x_2501_ = lean_apply_1(v_p_2498_, v_x1_2499_);
v___x_2502_ = lean_unbox(v___x_2501_);
if (v___x_2502_ == 0)
{
lean_inc(v_x2_2500_);
return v_x2_2500_;
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = lean_unsigned_to_nat(1u);
v___x_2504_ = lean_nat_add(v_x2_2500_, v___x_2503_);
return v___x_2504_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg___lam__0___boxed(lean_object* v_p_2505_, lean_object* v_x1_2506_, lean_object* v_x2_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Array_countP___redArg___lam__0(v_p_2505_, v_x1_2506_, v_x2_2507_);
lean_dec(v_x2_2507_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Array_countP___redArg(lean_object* v_p_2509_, lean_object* v_as_2510_){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2511_ = lean_unsigned_to_nat(0u);
v___x_2512_ = lean_array_get_size(v_as_2510_);
v___x_2513_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2514_ = lean_nat_dec_lt(v___x_2511_, v___x_2512_);
if (v___x_2514_ == 0)
{
lean_dec_ref(v_as_2510_);
lean_dec_ref(v_p_2509_);
return v___x_2511_;
}
else
{
lean_object* v___f_2515_; size_t v___x_2516_; size_t v___x_2517_; lean_object* v___x_2518_; 
v___f_2515_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2515_, 0, v_p_2509_);
v___x_2516_ = lean_usize_of_nat(v___x_2512_);
v___x_2517_ = ((size_t)0ULL);
v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2513_, v___f_2515_, v_as_2510_, v___x_2516_, v___x_2517_, v___x_2511_);
return v___x_2518_;
}
}
}
LEAN_EXPORT lean_object* l_Array_countP(lean_object* v_00_u03b1_2519_, lean_object* v_p_2520_, lean_object* v_as_2521_){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
v___x_2522_ = lean_unsigned_to_nat(0u);
v___x_2523_ = lean_array_get_size(v_as_2521_);
v___x_2524_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2525_ = lean_nat_dec_lt(v___x_2522_, v___x_2523_);
if (v___x_2525_ == 0)
{
lean_dec_ref(v_as_2521_);
lean_dec_ref(v_p_2520_);
return v___x_2522_;
}
else
{
lean_object* v___f_2526_; size_t v___x_2527_; size_t v___x_2528_; lean_object* v___x_2529_; 
v___f_2526_ = lean_alloc_closure((void*)(l_Array_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2526_, 0, v_p_2520_);
v___x_2527_ = lean_usize_of_nat(v___x_2523_);
v___x_2528_ = ((size_t)0ULL);
v___x_2529_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2524_, v___f_2526_, v_as_2521_, v___x_2527_, v___x_2528_, v___x_2522_);
return v___x_2529_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0(lean_object* v_inst_2530_, lean_object* v_a_2531_, lean_object* v_x1_2532_, lean_object* v_x2_2533_){
_start:
{
lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2534_ = lean_apply_2(v_inst_2530_, v_x1_2532_, v_a_2531_);
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
LEAN_EXPORT lean_object* l_Array_count___redArg___lam__0___boxed(lean_object* v_inst_2538_, lean_object* v_a_2539_, lean_object* v_x1_2540_, lean_object* v_x2_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Array_count___redArg___lam__0(v_inst_2538_, v_a_2539_, v_x1_2540_, v_x2_2541_);
lean_dec(v_x2_2541_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Array_count___redArg(lean_object* v_inst_2543_, lean_object* v_a_2544_, lean_object* v_as_2545_){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v___x_2546_ = lean_unsigned_to_nat(0u);
v___x_2547_ = lean_array_get_size(v_as_2545_);
v___x_2548_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2549_ = lean_nat_dec_lt(v___x_2546_, v___x_2547_);
if (v___x_2549_ == 0)
{
lean_dec_ref(v_as_2545_);
lean_dec(v_a_2544_);
lean_dec_ref(v_inst_2543_);
return v___x_2546_;
}
else
{
lean_object* v___f_2550_; size_t v___x_2551_; size_t v___x_2552_; lean_object* v___x_2553_; 
v___f_2550_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2550_, 0, v_inst_2543_);
lean_closure_set(v___f_2550_, 1, v_a_2544_);
v___x_2551_ = lean_usize_of_nat(v___x_2547_);
v___x_2552_ = ((size_t)0ULL);
v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2548_, v___f_2550_, v_as_2545_, v___x_2551_, v___x_2552_, v___x_2546_);
return v___x_2553_;
}
}
}
LEAN_EXPORT lean_object* l_Array_count(lean_object* v_00_u03b1_2554_, lean_object* v_inst_2555_, lean_object* v_a_2556_, lean_object* v_as_2557_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2558_ = lean_unsigned_to_nat(0u);
v___x_2559_ = lean_array_get_size(v_as_2557_);
v___x_2560_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2561_ = lean_nat_dec_lt(v___x_2558_, v___x_2559_);
if (v___x_2561_ == 0)
{
lean_dec_ref(v_as_2557_);
lean_dec(v_a_2556_);
lean_dec_ref(v_inst_2555_);
return v___x_2558_;
}
else
{
lean_object* v___f_2562_; size_t v___x_2563_; size_t v___x_2564_; lean_object* v___x_2565_; 
v___f_2562_ = lean_alloc_closure((void*)(l_Array_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2562_, 0, v_inst_2555_);
lean_closure_set(v___f_2562_, 1, v_a_2556_);
v___x_2563_ = lean_usize_of_nat(v___x_2559_);
v___x_2564_ = ((size_t)0ULL);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_2560_, v___f_2562_, v_as_2557_, v___x_2563_, v___x_2564_, v___x_2558_);
return v___x_2565_;
}
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg___lam__0(lean_object* v_f_2566_, lean_object* v_x_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = lean_apply_1(v_f_2566_, v_x_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Array_map___redArg(lean_object* v_f_2569_, lean_object* v_as_2570_){
_start:
{
lean_object* v___f_2571_; lean_object* v___x_2572_; size_t v_sz_2573_; size_t v___x_2574_; lean_object* v___x_2575_; 
v___f_2571_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2571_, 0, v_f_2569_);
v___x_2572_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2573_ = lean_array_size(v_as_2570_);
v___x_2574_ = ((size_t)0ULL);
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2572_, v___f_2571_, v_sz_2573_, v___x_2574_, v_as_2570_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Array_map(lean_object* v_00_u03b1_2576_, lean_object* v_00_u03b2_2577_, lean_object* v_f_2578_, lean_object* v_as_2579_){
_start:
{
lean_object* v___f_2580_; lean_object* v___x_2581_; size_t v_sz_2582_; size_t v___x_2583_; lean_object* v___x_2584_; 
v___f_2580_ = lean_alloc_closure((void*)(l_Array_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2580_, 0, v_f_2578_);
v___x_2581_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2582_ = lean_array_size(v_as_2579_);
v___x_2583_ = ((size_t)0ULL);
v___x_2584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2581_, v___f_2580_, v_sz_2582_, v___x_2583_, v_as_2579_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0(lean_object* v___y_2585_, lean_object* v_x_2586_){
_start:
{
lean_inc(v___y_2585_);
return v___y_2585_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__0___boxed(lean_object* v___y_2587_, lean_object* v_x_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Array_instFunctor___lam__0(v___y_2587_, v_x_2588_);
lean_dec(v_x_2588_);
lean_dec(v___y_2587_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lam__1(lean_object* v_00_u03b1_2590_, lean_object* v_00_u03b2_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v___f_2594_; lean_object* v___x_2595_; size_t v_sz_2596_; size_t v___x_2597_; lean_object* v___x_2598_; 
v___f_2594_ = lean_alloc_closure((void*)(l_Array_instFunctor___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2594_, 0, v___y_2592_);
v___x_2595_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v_sz_2596_ = lean_array_size(v___y_2593_);
v___x_2597_ = ((size_t)0ULL);
v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___redArg(v___x_2595_, v___f_2594_, v_sz_2596_, v___x_2597_, v___y_2593_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg___lam__0(lean_object* v_f_2605_, lean_object* v_x1_2606_, lean_object* v_x2_2607_, lean_object* v_x3_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = lean_apply_3(v_f_2605_, v_x1_2606_, v_x2_2607_, lean_box(0));
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___redArg(lean_object* v_as_2610_, lean_object* v_f_2611_){
_start:
{
lean_object* v___f_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___f_2612_ = lean_alloc_closure((void*)(l_Array_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2612_, 0, v_f_2611_);
v___x_2613_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2614_ = lean_array_get_size(v_as_2610_);
v___x_2615_ = lean_unsigned_to_nat(0u);
v___x_2616_ = lean_mk_empty_array_with_capacity(v___x_2614_);
v___x_2617_ = l_Array_mapFinIdxM_map___redArg(v___x_2613_, v_as_2610_, v___f_2612_, v___x_2614_, v___x_2615_, v___x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx(lean_object* v_00_u03b1_2618_, lean_object* v_00_u03b2_2619_, lean_object* v_as_2620_, lean_object* v_f_2621_){
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
LEAN_EXPORT lean_object* l_Array_mapIdx___redArg(lean_object* v_f_2628_, lean_object* v_as_2629_){
_start:
{
lean_object* v___f_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___f_2630_ = lean_alloc_closure((void*)(l_Array_mapIdxM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2630_, 0, v_f_2628_);
v___x_2631_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2632_ = lean_array_get_size(v_as_2629_);
v___x_2633_ = lean_unsigned_to_nat(0u);
v___x_2634_ = lean_mk_empty_array_with_capacity(v___x_2632_);
v___x_2635_ = l_Array_mapFinIdxM_map___redArg(v___x_2631_, v_as_2629_, v___f_2630_, v___x_2632_, v___x_2633_, v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx(lean_object* v_00_u03b1_2636_, lean_object* v_00_u03b2_2637_, lean_object* v_f_2638_, lean_object* v_as_2639_){
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(lean_object* v_start_2646_, lean_object* v_as_2647_, lean_object* v_i_2648_, lean_object* v_j_2649_, lean_object* v_bs_2650_){
_start:
{
lean_object* v_zero_2651_; uint8_t v_isZero_2652_; 
v_zero_2651_ = lean_unsigned_to_nat(0u);
v_isZero_2652_ = lean_nat_dec_eq(v_i_2648_, v_zero_2651_);
if (v_isZero_2652_ == 1)
{
lean_dec(v_j_2649_);
lean_dec(v_i_2648_);
return v_bs_2650_;
}
else
{
lean_object* v_one_2653_; lean_object* v_n_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_one_2653_ = lean_unsigned_to_nat(1u);
v_n_2654_ = lean_nat_sub(v_i_2648_, v_one_2653_);
lean_dec(v_i_2648_);
v___x_2655_ = lean_array_fget_borrowed(v_as_2647_, v_j_2649_);
v___x_2656_ = lean_nat_add(v_start_2646_, v_j_2649_);
lean_inc(v___x_2655_);
v___x_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2655_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = lean_nat_add(v_j_2649_, v_one_2653_);
lean_dec(v_j_2649_);
v___x_2659_ = lean_array_push(v_bs_2650_, v___x_2657_);
v_i_2648_ = v_n_2654_;
v_j_2649_ = v___x_2658_;
v_bs_2650_ = v___x_2659_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg___boxed(lean_object* v_start_2661_, lean_object* v_as_2662_, lean_object* v_i_2663_, lean_object* v_j_2664_, lean_object* v_bs_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(v_start_2661_, v_as_2662_, v_i_2663_, v_j_2664_, v_bs_2665_);
lean_dec_ref(v_as_2662_);
lean_dec(v_start_2661_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg(lean_object* v_xs_2667_, lean_object* v_start_2668_){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2669_ = lean_array_get_size(v_xs_2667_);
v___x_2670_ = lean_unsigned_to_nat(0u);
v___x_2671_ = lean_mk_empty_array_with_capacity(v___x_2669_);
v___x_2672_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(v_start_2668_, v_xs_2667_, v___x_2669_, v___x_2670_, v___x_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___redArg___boxed(lean_object* v_xs_2673_, lean_object* v_start_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Array_zipIdx___redArg(v_xs_2673_, v_start_2674_);
lean_dec(v_start_2674_);
lean_dec_ref(v_xs_2673_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx(lean_object* v_00_u03b1_2676_, lean_object* v_xs_2677_, lean_object* v_start_2678_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Array_zipIdx___redArg(v_xs_2677_, v_start_2678_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___boxed(lean_object* v_00_u03b1_2680_, lean_object* v_xs_2681_, lean_object* v_start_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Array_zipIdx(v_00_u03b1_2680_, v_xs_2681_, v_start_2682_);
lean_dec(v_start_2682_);
lean_dec_ref(v_xs_2681_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0(lean_object* v_00_u03b1_2684_, lean_object* v_start_2685_, lean_object* v_as_2686_, lean_object* v_i_2687_, lean_object* v_j_2688_, lean_object* v_inv_2689_, lean_object* v_bs_2690_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___redArg(v_start_2685_, v_as_2686_, v_i_2687_, v_j_2688_, v_bs_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0___boxed(lean_object* v_00_u03b1_2692_, lean_object* v_start_2693_, lean_object* v_as_2694_, lean_object* v_i_2695_, lean_object* v_j_2696_, lean_object* v_inv_2697_, lean_object* v_bs_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Array_mapFinIdxM_map___at___00Array_zipIdx_spec__0(v_00_u03b1_2692_, v_start_2693_, v_as_2694_, v_i_2695_, v_j_2696_, v_inv_2697_, v_bs_2698_);
lean_dec_ref(v_as_2694_);
lean_dec(v_start_2693_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0(lean_object* v_p_2700_, lean_object* v___x_2701_, lean_object* v___x_2702_, lean_object* v_a_2703_, lean_object* v_x_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v___x_2706_; uint8_t v___x_2707_; 
lean_inc(v_a_2703_);
v___x_2706_ = lean_apply_1(v_p_2700_, v_a_2703_);
v___x_2707_ = lean_unbox(v___x_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; 
lean_dec(v_a_2703_);
v___x_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2701_);
return v___x_2708_;
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
lean_dec_ref(v___x_2701_);
v___x_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2709_, 0, v_a_2703_);
v___x_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
v___x_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
lean_ctor_set(v___x_2711_, 1, v___x_2702_);
v___x_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
return v___x_2712_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg___lam__0___boxed(lean_object* v_p_2713_, lean_object* v___x_2714_, lean_object* v___x_2715_, lean_object* v_a_2716_, lean_object* v_x_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Array_find_x3f___redArg___lam__0(v_p_2713_, v___x_2714_, v___x_2715_, v_a_2716_, v_x_2717_, v___y_2718_);
lean_dec_ref(v___y_2718_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___redArg(lean_object* v_p_2720_, lean_object* v_as_2721_){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___f_2726_; size_t v_sz_2727_; size_t v___x_2728_; lean_object* v___x_2729_; lean_object* v_fst_2730_; 
v___x_2722_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2723_ = lean_box(0);
v___x_2724_ = lean_box(0);
v___x_2725_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2726_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2726_, 0, v_p_2720_);
lean_closure_set(v___f_2726_, 1, v___x_2725_);
lean_closure_set(v___f_2726_, 2, v___x_2724_);
v_sz_2727_ = lean_array_size(v_as_2721_);
v___x_2728_ = ((size_t)0ULL);
v___x_2729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2722_, v_as_2721_, v___f_2726_, v_sz_2727_, v___x_2728_, v___x_2725_);
v_fst_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_fst_2730_);
lean_dec(v___x_2729_);
if (lean_obj_tag(v_fst_2730_) == 0)
{
return v___x_2723_;
}
else
{
lean_object* v_val_2731_; 
v_val_2731_ = lean_ctor_get(v_fst_2730_, 0);
lean_inc(v_val_2731_);
lean_dec_ref(v_fst_2730_);
return v_val_2731_;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f(lean_object* v_00_u03b1_2732_, lean_object* v_p_2733_, lean_object* v_as_2734_){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___f_2739_; size_t v_sz_2740_; size_t v___x_2741_; lean_object* v___x_2742_; lean_object* v_fst_2743_; 
v___x_2735_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2736_ = lean_box(0);
v___x_2737_ = lean_box(0);
v___x_2738_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2739_ = lean_alloc_closure((void*)(l_Array_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2739_, 0, v_p_2733_);
lean_closure_set(v___f_2739_, 1, v___x_2738_);
lean_closure_set(v___f_2739_, 2, v___x_2737_);
v_sz_2740_ = lean_array_size(v_as_2734_);
v___x_2741_ = ((size_t)0ULL);
v___x_2742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2735_, v_as_2734_, v___f_2739_, v_sz_2740_, v___x_2741_, v___x_2738_);
v_fst_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_fst_2743_);
lean_dec(v___x_2742_);
if (lean_obj_tag(v_fst_2743_) == 0)
{
return v___x_2736_;
}
else
{
lean_object* v_val_2744_; 
v_val_2744_ = lean_ctor_get(v_fst_2743_, 0);
lean_inc(v_val_2744_);
lean_dec_ref(v_fst_2743_);
return v_val_2744_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0(lean_object* v_f_2745_, lean_object* v___x_2746_, lean_object* v___x_2747_, lean_object* v_a_2748_, lean_object* v_x_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_apply_1(v_f_2745_, v_a_2748_);
if (lean_obj_tag(v___x_2751_) == 1)
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
lean_dec_ref(v___x_2747_);
v___x_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
lean_ctor_set(v___x_2753_, 1, v___x_2746_);
v___x_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
return v___x_2754_;
}
else
{
lean_object* v___x_2755_; 
lean_dec(v___x_2751_);
v___x_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2747_);
return v___x_2755_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2756_, lean_object* v___x_2757_, lean_object* v___x_2758_, lean_object* v_a_2759_, lean_object* v_x_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Array_findSome_x3f___redArg___lam__0(v_f_2756_, v___x_2757_, v___x_2758_, v_a_2759_, v_x_2760_, v___y_2761_);
lean_dec_ref(v___y_2761_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___redArg(lean_object* v_f_2763_, lean_object* v_as_2764_){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___f_2769_; size_t v_sz_2770_; size_t v___x_2771_; lean_object* v___x_2772_; lean_object* v_fst_2773_; 
v___x_2765_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2766_ = lean_box(0);
v___x_2767_ = lean_box(0);
v___x_2768_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2769_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2769_, 0, v_f_2763_);
lean_closure_set(v___f_2769_, 1, v___x_2767_);
lean_closure_set(v___f_2769_, 2, v___x_2768_);
v_sz_2770_ = lean_array_size(v_as_2764_);
v___x_2771_ = ((size_t)0ULL);
v___x_2772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2765_, v_as_2764_, v___f_2769_, v_sz_2770_, v___x_2771_, v___x_2768_);
v_fst_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_fst_2773_);
lean_dec(v___x_2772_);
if (lean_obj_tag(v_fst_2773_) == 0)
{
return v___x_2766_;
}
else
{
lean_object* v_val_2774_; 
v_val_2774_ = lean_ctor_get(v_fst_2773_, 0);
lean_inc(v_val_2774_);
lean_dec_ref(v_fst_2773_);
return v_val_2774_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f(lean_object* v_00_u03b1_2775_, lean_object* v_00_u03b2_2776_, lean_object* v_f_2777_, lean_object* v_as_2778_){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___f_2783_; size_t v_sz_2784_; size_t v___x_2785_; lean_object* v___x_2786_; lean_object* v_fst_2787_; 
v___x_2779_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2780_ = lean_box(0);
v___x_2781_ = lean_box(0);
v___x_2782_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2783_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2783_, 0, v_f_2777_);
lean_closure_set(v___f_2783_, 1, v___x_2781_);
lean_closure_set(v___f_2783_, 2, v___x_2782_);
v_sz_2784_ = lean_array_size(v_as_2778_);
v___x_2785_ = ((size_t)0ULL);
v___x_2786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2779_, v_as_2778_, v___f_2783_, v_sz_2784_, v___x_2785_, v___x_2782_);
v_fst_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_fst_2787_);
lean_dec(v___x_2786_);
if (lean_obj_tag(v_fst_2787_) == 0)
{
return v___x_2780_;
}
else
{
lean_object* v_val_2788_; 
v_val_2788_ = lean_ctor_get(v_fst_2787_, 0);
lean_inc(v_val_2788_);
lean_dec_ref(v_fst_2787_);
return v_val_2788_;
}
}
}
static lean_object* _init_l_Array_findSome_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2791_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__1));
v___x_2792_ = lean_unsigned_to_nat(14u);
v___x_2793_ = lean_unsigned_to_nat(1220u);
v___x_2794_ = ((lean_object*)(l_Array_findSome_x21___redArg___closed__0));
v___x_2795_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_2796_ = l_mkPanicMessageWithDecl(v___x_2795_, v___x_2794_, v___x_2793_, v___x_2792_, v___x_2791_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___redArg(lean_object* v_inst_2797_, lean_object* v_f_2798_, lean_object* v_xs_2799_){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___f_2806_; size_t v_sz_2807_; size_t v___x_2808_; lean_object* v___x_2809_; lean_object* v_fst_2810_; 
v___x_2803_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2804_ = lean_box(0);
v___x_2805_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2806_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2806_, 0, v_f_2798_);
lean_closure_set(v___f_2806_, 1, v___x_2804_);
lean_closure_set(v___f_2806_, 2, v___x_2805_);
v_sz_2807_ = lean_array_size(v_xs_2799_);
v___x_2808_ = ((size_t)0ULL);
v___x_2809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2803_, v_xs_2799_, v___f_2806_, v_sz_2807_, v___x_2808_, v___x_2805_);
v_fst_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_fst_2810_);
lean_dec(v___x_2809_);
if (lean_obj_tag(v_fst_2810_) == 0)
{
goto v___jp_2800_;
}
else
{
lean_object* v_val_2811_; 
v_val_2811_ = lean_ctor_get(v_fst_2810_, 0);
lean_inc(v_val_2811_);
lean_dec_ref(v_fst_2810_);
if (lean_obj_tag(v_val_2811_) == 0)
{
goto v___jp_2800_;
}
else
{
lean_object* v_val_2812_; 
lean_dec(v_inst_2797_);
v_val_2812_ = lean_ctor_get(v_val_2811_, 0);
lean_inc(v_val_2812_);
lean_dec_ref(v_val_2811_);
return v_val_2812_;
}
}
v___jp_2800_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2802_ = l_panic___redArg(v_inst_2797_, v___x_2801_);
return v___x_2802_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21(lean_object* v_00_u03b1_2813_, lean_object* v_00_u03b2_2814_, lean_object* v_inst_2815_, lean_object* v_f_2816_, lean_object* v_xs_2817_){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___f_2824_; size_t v_sz_2825_; size_t v___x_2826_; lean_object* v___x_2827_; lean_object* v_fst_2828_; 
v___x_2821_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2822_ = lean_box(0);
v___x_2823_ = ((lean_object*)(l_Array_findSomeM_x3f___redArg___closed__0));
v___f_2824_ = lean_alloc_closure((void*)(l_Array_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2824_, 0, v_f_2816_);
lean_closure_set(v___f_2824_, 1, v___x_2822_);
lean_closure_set(v___f_2824_, 2, v___x_2823_);
v_sz_2825_ = lean_array_size(v_xs_2817_);
v___x_2826_ = ((size_t)0ULL);
v___x_2827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_2821_, v_xs_2817_, v___f_2824_, v_sz_2825_, v___x_2826_, v___x_2823_);
v_fst_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_fst_2828_);
lean_dec(v___x_2827_);
if (lean_obj_tag(v_fst_2828_) == 0)
{
goto v___jp_2818_;
}
else
{
lean_object* v_val_2829_; 
v_val_2829_ = lean_ctor_get(v_fst_2828_, 0);
lean_inc(v_val_2829_);
lean_dec_ref(v_fst_2828_);
if (lean_obj_tag(v_val_2829_) == 0)
{
goto v___jp_2818_;
}
else
{
lean_object* v_val_2830_; 
lean_dec(v_inst_2815_);
v_val_2830_ = lean_ctor_get(v_val_2829_, 0);
lean_inc(v_val_2830_);
lean_dec_ref(v_val_2829_);
return v_val_2830_;
}
}
v___jp_2818_:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = lean_obj_once(&l_Array_findSome_x21___redArg___closed__2, &l_Array_findSome_x21___redArg___closed__2_once, _init_l_Array_findSome_x21___redArg___closed__2);
v___x_2820_ = l_panic___redArg(v_inst_2815_, v___x_2819_);
return v___x_2820_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2831_, lean_object* v_x_2832_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = lean_apply_1(v_f_2831_, v_x_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___redArg(lean_object* v_f_2834_, lean_object* v_as_2835_){
_start:
{
lean_object* v___f_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___f_2836_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2836_, 0, v_f_2834_);
v___x_2837_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2838_ = lean_array_get_size(v_as_2835_);
v___x_2839_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2837_, v___f_2836_, v_as_2835_, v___x_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f(lean_object* v_00_u03b1_2840_, lean_object* v_00_u03b2_2841_, lean_object* v_f_2842_, lean_object* v_as_2843_){
_start:
{
lean_object* v___f_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___f_2844_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2844_, 0, v_f_2842_);
v___x_2845_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2846_ = lean_array_get_size(v_as_2843_);
v___x_2847_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2845_, v___f_2844_, v_as_2843_, v___x_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg___lam__0(lean_object* v_p_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v___x_2850_; uint8_t v___x_2851_; 
lean_inc(v_a_2849_);
v___x_2850_ = lean_apply_1(v_p_2848_, v_a_2849_);
v___x_2851_ = lean_unbox(v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; 
lean_dec(v_a_2849_);
v___x_2852_ = lean_box(0);
return v___x_2852_;
}
else
{
lean_object* v___x_2853_; 
v___x_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2853_, 0, v_a_2849_);
return v___x_2853_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___redArg(lean_object* v_p_2854_, lean_object* v_as_2855_){
_start:
{
lean_object* v___f_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___f_2856_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2856_, 0, v_p_2854_);
v___x_2857_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2858_ = lean_array_get_size(v_as_2855_);
v___x_2859_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2857_, v___f_2856_, v_as_2855_, v___x_2858_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f(lean_object* v_00_u03b1_2860_, lean_object* v_p_2861_, lean_object* v_as_2862_){
_start:
{
lean_object* v___f_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___f_2863_ = lean_alloc_closure((void*)(l_Array_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2863_, 0, v_p_2861_);
v___x_2864_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_2865_ = lean_array_get_size(v_as_2862_);
v___x_2866_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___redArg(v___x_2864_, v___f_2863_, v_as_2862_, v___x_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object* v_p_2867_, lean_object* v_as_2868_, lean_object* v_j_2869_){
_start:
{
lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2870_ = lean_array_get_size(v_as_2868_);
v___x_2871_ = lean_nat_dec_lt(v_j_2869_, v___x_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; 
lean_dec(v_j_2869_);
lean_dec_ref(v_p_2867_);
v___x_2872_ = lean_box(0);
return v___x_2872_;
}
else
{
lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2873_ = lean_array_fget_borrowed(v_as_2868_, v_j_2869_);
lean_inc_ref(v_p_2867_);
lean_inc(v___x_2873_);
v___x_2874_ = lean_apply_1(v_p_2867_, v___x_2873_);
v___x_2875_ = lean_unbox(v___x_2874_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2876_ = lean_unsigned_to_nat(1u);
v___x_2877_ = lean_nat_add(v_j_2869_, v___x_2876_);
lean_dec(v_j_2869_);
v_j_2869_ = v___x_2877_;
goto _start;
}
else
{
lean_object* v___x_2879_; 
lean_dec_ref(v_p_2867_);
v___x_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2879_, 0, v_j_2869_);
return v___x_2879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___redArg___boxed(lean_object* v_p_2880_, lean_object* v_as_2881_, lean_object* v_j_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Array_findIdx_x3f_loop___redArg(v_p_2880_, v_as_2881_, v_j_2882_);
lean_dec_ref(v_as_2881_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop(lean_object* v_00_u03b1_2884_, lean_object* v_p_2885_, lean_object* v_as_2886_, lean_object* v_j_2887_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Array_findIdx_x3f_loop___redArg(v_p_2885_, v_as_2886_, v_j_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___boxed(lean_object* v_00_u03b1_2889_, lean_object* v_p_2890_, lean_object* v_as_2891_, lean_object* v_j_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Array_findIdx_x3f_loop(v_00_u03b1_2889_, v_p_2890_, v_as_2891_, v_j_2892_);
lean_dec_ref(v_as_2891_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg(lean_object* v_p_2894_, lean_object* v_as_2895_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_unsigned_to_nat(0u);
v___x_2897_ = l_Array_findIdx_x3f_loop___redArg(v_p_2894_, v_as_2895_, v___x_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___redArg___boxed(lean_object* v_p_2898_, lean_object* v_as_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Array_findIdx_x3f___redArg(v_p_2898_, v_as_2899_);
lean_dec_ref(v_as_2899_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f(lean_object* v_00_u03b1_2901_, lean_object* v_p_2902_, lean_object* v_as_2903_){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = lean_unsigned_to_nat(0u);
v___x_2905_ = l_Array_findIdx_x3f_loop___redArg(v_p_2902_, v_as_2903_, v___x_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___boxed(lean_object* v_00_u03b1_2906_, lean_object* v_p_2907_, lean_object* v_as_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Array_findIdx_x3f(v_00_u03b1_2906_, v_p_2907_, v_as_2908_);
lean_dec_ref(v_as_2908_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(lean_object* v_p_2910_, lean_object* v_as_2911_, lean_object* v_j_2912_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg___boxed(lean_object* v_p_2923_, lean_object* v_as_2924_, lean_object* v_j_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2923_, v_as_2924_, v_j_2925_);
lean_dec_ref(v_as_2924_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object* v_00_u03b1_2927_, lean_object* v_p_2928_, lean_object* v_as_2929_, lean_object* v_j_2930_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2928_, v_as_2929_, v_j_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___boxed(lean_object* v_00_u03b1_2932_, lean_object* v_p_2933_, lean_object* v_as_2934_, lean_object* v_j_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(v_00_u03b1_2932_, v_p_2933_, v_as_2934_, v_j_2935_);
lean_dec_ref(v_as_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg(lean_object* v_p_2937_, lean_object* v_as_2938_){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = lean_unsigned_to_nat(0u);
v___x_2940_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2937_, v_as_2938_, v___x_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___redArg___boxed(lean_object* v_p_2941_, lean_object* v_as_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Array_findFinIdx_x3f___redArg(v_p_2941_, v_as_2942_);
lean_dec_ref(v_as_2942_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f(lean_object* v_00_u03b1_2944_, lean_object* v_p_2945_, lean_object* v_as_2946_){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = lean_unsigned_to_nat(0u);
v___x_2948_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_2945_, v_as_2946_, v___x_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_2949_, lean_object* v_p_2950_, lean_object* v_as_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Array_findFinIdx_x3f(v_00_u03b1_2949_, v_p_2950_, v_as_2951_);
lean_dec_ref(v_as_2951_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg(lean_object* v_p_2953_, lean_object* v_as_2954_){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = lean_unsigned_to_nat(0u);
v___x_2956_ = l_Array_findIdx_x3f_loop___redArg(v_p_2953_, v_as_2954_, v___x_2955_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v___x_2957_; 
v___x_2957_ = lean_array_get_size(v_as_2954_);
return v___x_2957_;
}
else
{
lean_object* v_val_2958_; 
v_val_2958_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_val_2958_);
lean_dec_ref(v___x_2956_);
return v_val_2958_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___redArg___boxed(lean_object* v_p_2959_, lean_object* v_as_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Array_findIdx___redArg(v_p_2959_, v_as_2960_);
lean_dec_ref(v_as_2960_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx(lean_object* v_00_u03b1_2962_, lean_object* v_p_2963_, lean_object* v_as_2964_){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = lean_unsigned_to_nat(0u);
v___x_2966_ = l_Array_findIdx_x3f_loop___redArg(v_p_2963_, v_as_2964_, v___x_2965_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_array_get_size(v_as_2964_);
return v___x_2967_;
}
else
{
lean_object* v_val_2968_; 
v_val_2968_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_val_2968_);
lean_dec_ref(v___x_2966_);
return v_val_2968_;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___boxed(lean_object* v_00_u03b1_2969_, lean_object* v_p_2970_, lean_object* v_as_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Array_findIdx(v_00_u03b1_2969_, v_p_2970_, v_as_2971_);
lean_dec_ref(v_as_2971_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg(lean_object* v_inst_2973_, lean_object* v_xs_2974_, lean_object* v_v_2975_, lean_object* v_i_2976_){
_start:
{
lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2977_ = lean_array_get_size(v_xs_2974_);
v___x_2978_ = lean_nat_dec_lt(v_i_2976_, v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
lean_dec(v_i_2976_);
lean_dec(v_v_2975_);
lean_dec_ref(v_inst_2973_);
v___x_2979_ = lean_box(0);
return v___x_2979_;
}
else
{
lean_object* v___x_2980_; lean_object* v___x_2981_; uint8_t v___x_2982_; 
v___x_2980_ = lean_array_fget_borrowed(v_xs_2974_, v_i_2976_);
lean_inc_ref(v_inst_2973_);
lean_inc(v_v_2975_);
lean_inc(v___x_2980_);
v___x_2981_ = lean_apply_2(v_inst_2973_, v___x_2980_, v_v_2975_);
v___x_2982_ = lean_unbox(v___x_2981_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = lean_unsigned_to_nat(1u);
v___x_2984_ = lean_nat_add(v_i_2976_, v___x_2983_);
lean_dec(v_i_2976_);
v_i_2976_ = v___x_2984_;
goto _start;
}
else
{
lean_object* v___x_2986_; 
lean_dec(v_v_2975_);
lean_dec_ref(v_inst_2973_);
v___x_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_i_2976_);
return v___x_2986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___redArg___boxed(lean_object* v_inst_2987_, lean_object* v_xs_2988_, lean_object* v_v_2989_, lean_object* v_i_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Array_idxOfAux___redArg(v_inst_2987_, v_xs_2988_, v_v_2989_, v_i_2990_);
lean_dec_ref(v_xs_2988_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux(lean_object* v_00_u03b1_2992_, lean_object* v_inst_2993_, lean_object* v_xs_2994_, lean_object* v_v_2995_, lean_object* v_i_2996_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Array_idxOfAux___redArg(v_inst_2993_, v_xs_2994_, v_v_2995_, v_i_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___boxed(lean_object* v_00_u03b1_2998_, lean_object* v_inst_2999_, lean_object* v_xs_3000_, lean_object* v_v_3001_, lean_object* v_i_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Array_idxOfAux(v_00_u03b1_2998_, v_inst_2999_, v_xs_3000_, v_v_3001_, v_i_3002_);
lean_dec_ref(v_xs_3000_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg(lean_object* v_inst_3004_, lean_object* v_xs_3005_, lean_object* v_v_3006_){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = lean_unsigned_to_nat(0u);
v___x_3008_ = l_Array_idxOfAux___redArg(v_inst_3004_, v_xs_3005_, v_v_3006_, v___x_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_3009_, lean_object* v_xs_3010_, lean_object* v_v_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Array_finIdxOf_x3f___redArg(v_inst_3009_, v_xs_3010_, v_v_3011_);
lean_dec_ref(v_xs_3010_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f(lean_object* v_00_u03b1_3013_, lean_object* v_inst_3014_, lean_object* v_xs_3015_, lean_object* v_v_3016_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Array_finIdxOf_x3f___redArg(v_inst_3014_, v_xs_3015_, v_v_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_3018_, lean_object* v_inst_3019_, lean_object* v_xs_3020_, lean_object* v_v_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Array_finIdxOf_x3f(v_00_u03b1_3018_, v_inst_3019_, v_xs_3020_, v_v_3021_);
lean_dec_ref(v_xs_3020_);
return v_res_3022_;
}
}
LEAN_EXPORT uint8_t l_Array_idxOf___redArg___lam__0(lean_object* v_inst_3023_, lean_object* v_a_3024_, lean_object* v_x_3025_){
_start:
{
lean_object* v___x_3026_; uint8_t v___x_3027_; 
v___x_3026_ = lean_apply_2(v_inst_3023_, v_x_3025_, v_a_3024_);
v___x_3027_ = lean_unbox(v___x_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___lam__0___boxed(lean_object* v_inst_3028_, lean_object* v_a_3029_, lean_object* v_x_3030_){
_start:
{
uint8_t v_res_3031_; lean_object* v_r_3032_; 
v_res_3031_ = l_Array_idxOf___redArg___lam__0(v_inst_3028_, v_a_3029_, v_x_3030_);
v_r_3032_ = lean_box(v_res_3031_);
return v_r_3032_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg(lean_object* v_inst_3033_, lean_object* v_a_3034_, lean_object* v_as_3035_){
_start:
{
lean_object* v___f_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___f_3036_ = lean_alloc_closure((void*)(l_Array_idxOf___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3036_, 0, v_inst_3033_);
lean_closure_set(v___f_3036_, 1, v_a_3034_);
v___x_3037_ = lean_unsigned_to_nat(0u);
v___x_3038_ = l_Array_findIdx_x3f_loop___redArg(v___f_3036_, v_as_3035_, v___x_3037_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_array_get_size(v_as_3035_);
return v___x_3039_;
}
else
{
lean_object* v_val_3040_; 
v_val_3040_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_val_3040_);
lean_dec_ref(v___x_3038_);
return v_val_3040_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___redArg___boxed(lean_object* v_inst_3041_, lean_object* v_a_3042_, lean_object* v_as_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Array_idxOf___redArg(v_inst_3041_, v_a_3042_, v_as_3043_);
lean_dec_ref(v_as_3043_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf(lean_object* v_00_u03b1_3045_, lean_object* v_inst_3046_, lean_object* v_a_3047_, lean_object* v_as_3048_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Array_idxOf___redArg(v_inst_3046_, v_a_3047_, v_as_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___boxed(lean_object* v_00_u03b1_3050_, lean_object* v_inst_3051_, lean_object* v_a_3052_, lean_object* v_as_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Array_idxOf(v_00_u03b1_3050_, v_inst_3051_, v_a_3052_, v_as_3053_);
lean_dec_ref(v_as_3053_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg(lean_object* v_inst_3055_, lean_object* v_xs_3056_, lean_object* v_v_3057_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Array_finIdxOf_x3f___redArg(v_inst_3055_, v_xs_3056_, v_v_3057_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_box(0);
return v___x_3059_;
}
else
{
lean_object* v_val_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
v_val_3060_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3058_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_val_3060_);
lean_dec(v___x_3058_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_val_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___redArg___boxed(lean_object* v_inst_3068_, lean_object* v_xs_3069_, lean_object* v_v_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Array_idxOf_x3f___redArg(v_inst_3068_, v_xs_3069_, v_v_3070_);
lean_dec_ref(v_xs_3069_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f(lean_object* v_00_u03b1_3072_, lean_object* v_inst_3073_, lean_object* v_xs_3074_, lean_object* v_v_3075_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Array_idxOf_x3f___redArg(v_inst_3073_, v_xs_3074_, v_v_3075_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___boxed(lean_object* v_00_u03b1_3077_, lean_object* v_inst_3078_, lean_object* v_xs_3079_, lean_object* v_v_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Array_idxOf_x3f(v_00_u03b1_3077_, v_inst_3078_, v_xs_3079_, v_v_3080_);
lean_dec_ref(v_xs_3079_);
return v_res_3081_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg___lam__0(lean_object* v_p_3082_, lean_object* v_x_3083_){
_start:
{
lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3084_ = lean_apply_1(v_p_3082_, v_x_3083_);
v___x_3085_ = lean_unbox(v___x_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___lam__0___boxed(lean_object* v_p_3086_, lean_object* v_x_3087_){
_start:
{
uint8_t v_res_3088_; lean_object* v_r_3089_; 
v_res_3088_ = l_Array_any___redArg___lam__0(v_p_3086_, v_x_3087_);
v_r_3089_ = lean_box(v_res_3088_);
return v_r_3089_;
}
}
LEAN_EXPORT uint8_t l_Array_any___redArg(lean_object* v_as_3090_, lean_object* v_p_3091_, lean_object* v_start_3092_, lean_object* v_stop_3093_){
_start:
{
lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3094_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3095_ = lean_nat_dec_lt(v_start_3092_, v_stop_3093_);
if (v___x_3095_ == 0)
{
lean_dec(v_stop_3093_);
lean_dec_ref(v_p_3091_);
lean_dec_ref(v_as_3090_);
return v___x_3095_;
}
else
{
lean_object* v___f_3096_; lean_object* v___y_3098_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___f_3096_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3096_, 0, v_p_3091_);
v___x_3104_ = lean_array_get_size(v_as_3090_);
v___x_3105_ = lean_nat_dec_le(v_stop_3093_, v___x_3104_);
if (v___x_3105_ == 0)
{
lean_dec(v_stop_3093_);
v___y_3098_ = v___x_3104_;
goto v___jp_3097_;
}
else
{
v___y_3098_ = v_stop_3093_;
goto v___jp_3097_;
}
v___jp_3097_:
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_nat_dec_lt(v_start_3092_, v___y_3098_);
if (v___x_3099_ == 0)
{
lean_dec(v___y_3098_);
lean_dec_ref(v___f_3096_);
lean_dec_ref(v_as_3090_);
return v___x_3099_;
}
else
{
size_t v___x_3100_; size_t v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3100_ = lean_usize_of_nat(v_start_3092_);
v___x_3101_ = lean_usize_of_nat(v___y_3098_);
lean_dec(v___y_3098_);
v___x_3102_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3094_, v___f_3096_, v_as_3090_, v___x_3100_, v___x_3101_);
v___x_3103_ = lean_unbox(v___x_3102_);
lean_dec(v___x_3102_);
return v___x_3103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___redArg___boxed(lean_object* v_as_3106_, lean_object* v_p_3107_, lean_object* v_start_3108_, lean_object* v_stop_3109_){
_start:
{
uint8_t v_res_3110_; lean_object* v_r_3111_; 
v_res_3110_ = l_Array_any___redArg(v_as_3106_, v_p_3107_, v_start_3108_, v_stop_3109_);
lean_dec(v_start_3108_);
v_r_3111_ = lean_box(v_res_3110_);
return v_r_3111_;
}
}
LEAN_EXPORT uint8_t l_Array_any(lean_object* v_00_u03b1_3112_, lean_object* v_as_3113_, lean_object* v_p_3114_, lean_object* v_start_3115_, lean_object* v_stop_3116_){
_start:
{
lean_object* v___x_3117_; uint8_t v___x_3118_; 
v___x_3117_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3118_ = lean_nat_dec_lt(v_start_3115_, v_stop_3116_);
if (v___x_3118_ == 0)
{
lean_dec(v_stop_3116_);
lean_dec_ref(v_p_3114_);
lean_dec_ref(v_as_3113_);
return v___x_3118_;
}
else
{
lean_object* v___f_3119_; lean_object* v___y_3121_; lean_object* v___x_3127_; uint8_t v___x_3128_; 
v___f_3119_ = lean_alloc_closure((void*)(l_Array_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3119_, 0, v_p_3114_);
v___x_3127_ = lean_array_get_size(v_as_3113_);
v___x_3128_ = lean_nat_dec_le(v_stop_3116_, v___x_3127_);
if (v___x_3128_ == 0)
{
lean_dec(v_stop_3116_);
v___y_3121_ = v___x_3127_;
goto v___jp_3120_;
}
else
{
v___y_3121_ = v_stop_3116_;
goto v___jp_3120_;
}
v___jp_3120_:
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_nat_dec_lt(v_start_3115_, v___y_3121_);
if (v___x_3122_ == 0)
{
lean_dec(v___y_3121_);
lean_dec_ref(v___f_3119_);
lean_dec_ref(v_as_3113_);
return v___x_3122_;
}
else
{
size_t v___x_3123_; size_t v___x_3124_; lean_object* v___x_3125_; uint8_t v___x_3126_; 
v___x_3123_ = lean_usize_of_nat(v_start_3115_);
v___x_3124_ = lean_usize_of_nat(v___y_3121_);
lean_dec(v___y_3121_);
v___x_3125_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3117_, v___f_3119_, v_as_3113_, v___x_3123_, v___x_3124_);
v___x_3126_ = lean_unbox(v___x_3125_);
lean_dec(v___x_3125_);
return v___x_3126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any___boxed(lean_object* v_00_u03b1_3129_, lean_object* v_as_3130_, lean_object* v_p_3131_, lean_object* v_start_3132_, lean_object* v_stop_3133_){
_start:
{
uint8_t v_res_3134_; lean_object* v_r_3135_; 
v_res_3134_ = l_Array_any(v_00_u03b1_3129_, v_as_3130_, v_p_3131_, v_start_3132_, v_stop_3133_);
lean_dec(v_start_3132_);
v_r_3135_ = lean_box(v_res_3134_);
return v_r_3135_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg___lam__0(lean_object* v_p_3136_, uint8_t v___x_3137_, lean_object* v_v_3138_){
_start:
{
lean_object* v___x_3139_; uint8_t v___x_3140_; 
v___x_3139_ = lean_apply_1(v_p_3136_, v_v_3138_);
v___x_3140_ = lean_unbox(v___x_3139_);
if (v___x_3140_ == 0)
{
return v___x_3137_;
}
else
{
uint8_t v___x_3141_; 
v___x_3141_ = 0;
return v___x_3141_;
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___lam__0___boxed(lean_object* v_p_3142_, lean_object* v___x_3143_, lean_object* v_v_3144_){
_start:
{
uint8_t v___x_339__boxed_3145_; uint8_t v_res_3146_; lean_object* v_r_3147_; 
v___x_339__boxed_3145_ = lean_unbox(v___x_3143_);
v_res_3146_ = l_Array_all___redArg___lam__0(v_p_3142_, v___x_339__boxed_3145_, v_v_3144_);
v_r_3147_ = lean_box(v_res_3146_);
return v_r_3147_;
}
}
LEAN_EXPORT uint8_t l_Array_all___redArg(lean_object* v_as_3148_, lean_object* v_p_3149_, lean_object* v_start_3150_, lean_object* v_stop_3151_){
_start:
{
lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3152_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3153_ = lean_nat_dec_lt(v_start_3150_, v_stop_3151_);
if (v___x_3153_ == 0)
{
uint8_t v___x_3154_; 
lean_dec(v_stop_3151_);
lean_dec_ref(v_p_3149_);
lean_dec_ref(v_as_3148_);
v___x_3154_ = 1;
return v___x_3154_;
}
else
{
lean_object* v___x_3155_; lean_object* v___f_3156_; lean_object* v___y_3158_; lean_object* v___x_3165_; uint8_t v___x_3166_; 
v___x_3155_ = lean_box(v___x_3153_);
v___f_3156_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3156_, 0, v_p_3149_);
lean_closure_set(v___f_3156_, 1, v___x_3155_);
v___x_3165_ = lean_array_get_size(v_as_3148_);
v___x_3166_ = lean_nat_dec_le(v_stop_3151_, v___x_3165_);
if (v___x_3166_ == 0)
{
lean_dec(v_stop_3151_);
v___y_3158_ = v___x_3165_;
goto v___jp_3157_;
}
else
{
v___y_3158_ = v_stop_3151_;
goto v___jp_3157_;
}
v___jp_3157_:
{
uint8_t v___x_3159_; 
v___x_3159_ = lean_nat_dec_lt(v_start_3150_, v___y_3158_);
if (v___x_3159_ == 0)
{
lean_dec(v___y_3158_);
lean_dec_ref(v___f_3156_);
lean_dec_ref(v_as_3148_);
return v___x_3153_;
}
else
{
size_t v___x_3160_; size_t v___x_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; 
v___x_3160_ = lean_usize_of_nat(v_start_3150_);
v___x_3161_ = lean_usize_of_nat(v___y_3158_);
lean_dec(v___y_3158_);
v___x_3162_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3152_, v___f_3156_, v_as_3148_, v___x_3160_, v___x_3161_);
v___x_3163_ = lean_unbox(v___x_3162_);
lean_dec(v___x_3162_);
if (v___x_3163_ == 0)
{
return v___x_3159_;
}
else
{
uint8_t v___x_3164_; 
v___x_3164_ = 0;
return v___x_3164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___redArg___boxed(lean_object* v_as_3167_, lean_object* v_p_3168_, lean_object* v_start_3169_, lean_object* v_stop_3170_){
_start:
{
uint8_t v_res_3171_; lean_object* v_r_3172_; 
v_res_3171_ = l_Array_all___redArg(v_as_3167_, v_p_3168_, v_start_3169_, v_stop_3170_);
lean_dec(v_start_3169_);
v_r_3172_ = lean_box(v_res_3171_);
return v_r_3172_;
}
}
LEAN_EXPORT uint8_t l_Array_all(lean_object* v_00_u03b1_3173_, lean_object* v_as_3174_, lean_object* v_p_3175_, lean_object* v_start_3176_, lean_object* v_stop_3177_){
_start:
{
lean_object* v___x_3178_; uint8_t v___x_3179_; 
v___x_3178_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3179_ = lean_nat_dec_lt(v_start_3176_, v_stop_3177_);
if (v___x_3179_ == 0)
{
uint8_t v___x_3180_; 
lean_dec(v_stop_3177_);
lean_dec_ref(v_p_3175_);
lean_dec_ref(v_as_3174_);
v___x_3180_ = 1;
return v___x_3180_;
}
else
{
lean_object* v___x_3181_; lean_object* v___f_3182_; lean_object* v___y_3184_; lean_object* v___x_3191_; uint8_t v___x_3192_; 
v___x_3181_ = lean_box(v___x_3179_);
v___f_3182_ = lean_alloc_closure((void*)(l_Array_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3182_, 0, v_p_3175_);
lean_closure_set(v___f_3182_, 1, v___x_3181_);
v___x_3191_ = lean_array_get_size(v_as_3174_);
v___x_3192_ = lean_nat_dec_le(v_stop_3177_, v___x_3191_);
if (v___x_3192_ == 0)
{
lean_dec(v_stop_3177_);
v___y_3184_ = v___x_3191_;
goto v___jp_3183_;
}
else
{
v___y_3184_ = v_stop_3177_;
goto v___jp_3183_;
}
v___jp_3183_:
{
uint8_t v___x_3185_; 
v___x_3185_ = lean_nat_dec_lt(v_start_3176_, v___y_3184_);
if (v___x_3185_ == 0)
{
lean_dec(v___y_3184_);
lean_dec_ref(v___f_3182_);
lean_dec_ref(v_as_3174_);
return v___x_3179_;
}
else
{
size_t v___x_3186_; size_t v___x_3187_; lean_object* v___x_3188_; uint8_t v___x_3189_; 
v___x_3186_ = lean_usize_of_nat(v_start_3176_);
v___x_3187_ = lean_usize_of_nat(v___y_3184_);
lean_dec(v___y_3184_);
v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3178_, v___f_3182_, v_as_3174_, v___x_3186_, v___x_3187_);
v___x_3189_ = lean_unbox(v___x_3188_);
lean_dec(v___x_3188_);
if (v___x_3189_ == 0)
{
return v___x_3185_;
}
else
{
uint8_t v___x_3190_; 
v___x_3190_ = 0;
return v___x_3190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all___boxed(lean_object* v_00_u03b1_3193_, lean_object* v_as_3194_, lean_object* v_p_3195_, lean_object* v_start_3196_, lean_object* v_stop_3197_){
_start:
{
uint8_t v_res_3198_; lean_object* v_r_3199_; 
v_res_3198_ = l_Array_all(v_00_u03b1_3193_, v_as_3194_, v_p_3195_, v_start_3196_, v_stop_3197_);
lean_dec(v_start_3196_);
v_r_3199_ = lean_box(v_res_3198_);
return v_r_3199_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg___lam__0(lean_object* v_inst_3200_, lean_object* v_a_3201_, lean_object* v_x_3202_){
_start:
{
lean_object* v___x_3203_; uint8_t v___x_3204_; 
v___x_3203_ = lean_apply_2(v_inst_3200_, v_a_3201_, v_x_3202_);
v___x_3204_ = lean_unbox(v___x_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___lam__0___boxed(lean_object* v_inst_3205_, lean_object* v_a_3206_, lean_object* v_x_3207_){
_start:
{
uint8_t v_res_3208_; lean_object* v_r_3209_; 
v_res_3208_ = l_Array_contains___redArg___lam__0(v_inst_3205_, v_a_3206_, v_x_3207_);
v_r_3209_ = lean_box(v_res_3208_);
return v_r_3209_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___redArg(lean_object* v_inst_3210_, lean_object* v_as_3211_, lean_object* v_a_3212_){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; uint8_t v___x_3216_; 
v___x_3213_ = lean_unsigned_to_nat(0u);
v___x_3214_ = lean_array_get_size(v_as_3211_);
v___x_3215_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3216_ = lean_nat_dec_lt(v___x_3213_, v___x_3214_);
if (v___x_3216_ == 0)
{
lean_dec(v_a_3212_);
lean_dec_ref(v_as_3211_);
lean_dec_ref(v_inst_3210_);
return v___x_3216_;
}
else
{
if (v___x_3216_ == 0)
{
lean_dec(v_a_3212_);
lean_dec_ref(v_as_3211_);
lean_dec_ref(v_inst_3210_);
return v___x_3216_;
}
else
{
lean_object* v___f_3217_; size_t v___x_3218_; size_t v___x_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; 
v___f_3217_ = lean_alloc_closure((void*)(l_Array_contains___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3217_, 0, v_inst_3210_);
lean_closure_set(v___f_3217_, 1, v_a_3212_);
v___x_3218_ = ((size_t)0ULL);
v___x_3219_ = lean_usize_of_nat(v___x_3214_);
v___x_3220_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___redArg(v___x_3215_, v___f_3217_, v_as_3211_, v___x_3218_, v___x_3219_);
v___x_3221_ = lean_unbox(v___x_3220_);
lean_dec(v___x_3220_);
return v___x_3221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___redArg___boxed(lean_object* v_inst_3222_, lean_object* v_as_3223_, lean_object* v_a_3224_){
_start:
{
uint8_t v_res_3225_; lean_object* v_r_3226_; 
v_res_3225_ = l_Array_contains___redArg(v_inst_3222_, v_as_3223_, v_a_3224_);
v_r_3226_ = lean_box(v_res_3225_);
return v_r_3226_;
}
}
LEAN_EXPORT uint8_t l_Array_contains(lean_object* v_00_u03b1_3227_, lean_object* v_inst_3228_, lean_object* v_as_3229_, lean_object* v_a_3230_){
_start:
{
uint8_t v___x_3231_; 
v___x_3231_ = l_Array_contains___redArg(v_inst_3228_, v_as_3229_, v_a_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Array_contains___boxed(lean_object* v_00_u03b1_3232_, lean_object* v_inst_3233_, lean_object* v_as_3234_, lean_object* v_a_3235_){
_start:
{
uint8_t v_res_3236_; lean_object* v_r_3237_; 
v_res_3236_ = l_Array_contains(v_00_u03b1_3232_, v_inst_3233_, v_as_3234_, v_a_3235_);
v_r_3237_ = lean_box(v_res_3236_);
return v_r_3237_;
}
}
LEAN_EXPORT uint8_t l_Array_elem___redArg(lean_object* v_inst_3238_, lean_object* v_a_3239_, lean_object* v_as_3240_){
_start:
{
uint8_t v___x_3241_; 
v___x_3241_ = l_Array_contains___redArg(v_inst_3238_, v_as_3240_, v_a_3239_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___redArg___boxed(lean_object* v_inst_3242_, lean_object* v_a_3243_, lean_object* v_as_3244_){
_start:
{
uint8_t v_res_3245_; lean_object* v_r_3246_; 
v_res_3245_ = l_Array_elem___redArg(v_inst_3242_, v_a_3243_, v_as_3244_);
v_r_3246_ = lean_box(v_res_3245_);
return v_r_3246_;
}
}
LEAN_EXPORT uint8_t l_Array_elem(lean_object* v_00_u03b1_3247_, lean_object* v_inst_3248_, lean_object* v_a_3249_, lean_object* v_as_3250_){
_start:
{
uint8_t v___x_3251_; 
v___x_3251_ = l_Array_contains___redArg(v_inst_3248_, v_as_3250_, v_a_3249_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Array_elem___boxed(lean_object* v_00_u03b1_3252_, lean_object* v_inst_3253_, lean_object* v_a_3254_, lean_object* v_as_3255_){
_start:
{
uint8_t v_res_3256_; lean_object* v_r_3257_; 
v_res_3256_ = l_Array_elem(v_00_u03b1_3252_, v_inst_3253_, v_a_3254_, v_as_3255_);
v_r_3257_ = lean_box(v_res_3256_);
return v_r_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(lean_object* v_as_3258_, size_t v_i_3259_, size_t v_stop_3260_, lean_object* v_b_3261_){
_start:
{
uint8_t v___x_3262_; 
v___x_3262_ = lean_usize_dec_eq(v_i_3259_, v_stop_3260_);
if (v___x_3262_ == 0)
{
size_t v___x_3263_; size_t v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3263_ = ((size_t)1ULL);
v___x_3264_ = lean_usize_sub(v_i_3259_, v___x_3263_);
v___x_3265_ = lean_array_uget_borrowed(v_as_3258_, v___x_3264_);
lean_inc(v___x_3265_);
v___x_3266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3265_);
lean_ctor_set(v___x_3266_, 1, v_b_3261_);
v_i_3259_ = v___x_3264_;
v_b_3261_ = v___x_3266_;
goto _start;
}
else
{
return v_b_3261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg___boxed(lean_object* v_as_3268_, lean_object* v_i_3269_, lean_object* v_stop_3270_, lean_object* v_b_3271_){
_start:
{
size_t v_i_boxed_3272_; size_t v_stop_boxed_3273_; lean_object* v_res_3274_; 
v_i_boxed_3272_ = lean_unbox_usize(v_i_3269_);
lean_dec(v_i_3269_);
v_stop_boxed_3273_ = lean_unbox_usize(v_stop_3270_);
lean_dec(v_stop_3270_);
v_res_3274_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3268_, v_i_boxed_3272_, v_stop_boxed_3273_, v_b_3271_);
lean_dec_ref(v_as_3268_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg(lean_object* v_as_3275_){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; 
v___x_3276_ = lean_box(0);
v___x_3277_ = lean_array_get_size(v_as_3275_);
v___x_3278_ = lean_unsigned_to_nat(0u);
v___x_3279_ = lean_nat_dec_lt(v___x_3278_, v___x_3277_);
if (v___x_3279_ == 0)
{
return v___x_3276_;
}
else
{
size_t v___x_3280_; size_t v___x_3281_; lean_object* v___x_3282_; 
v___x_3280_ = lean_usize_of_nat(v___x_3277_);
v___x_3281_ = ((size_t)0ULL);
v___x_3282_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3275_, v___x_3280_, v___x_3281_, v___x_3276_);
return v___x_3282_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListImpl___redArg___boxed(lean_object* v_as_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Array_toListImpl___redArg(v_as_3283_);
lean_dec_ref(v_as_3283_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* lean_array_to_list_impl(lean_object* v_00_u03b1_3285_, lean_object* v_as_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Array_toListImpl___redArg(v_as_3286_);
lean_dec_ref(v_as_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(lean_object* v_00_u03b1_3288_, lean_object* v_as_3289_, size_t v_i_3290_, size_t v_stop_3291_, lean_object* v_b_3292_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___redArg(v_as_3289_, v_i_3290_, v_stop_3291_, v_b_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0___boxed(lean_object* v_00_u03b1_3294_, lean_object* v_as_3295_, lean_object* v_i_3296_, lean_object* v_stop_3297_, lean_object* v_b_3298_){
_start:
{
size_t v_i_boxed_3299_; size_t v_stop_boxed_3300_; lean_object* v_res_3301_; 
v_i_boxed_3299_ = lean_unbox_usize(v_i_3296_);
lean_dec(v_i_3296_);
v_stop_boxed_3300_ = lean_unbox_usize(v_stop_3297_);
lean_dec(v_stop_3297_);
v_res_3301_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Array_toListImpl_spec__0(v_00_u03b1_3294_, v_as_3295_, v_i_boxed_3299_, v_stop_boxed_3300_, v_b_3298_);
lean_dec_ref(v_as_3295_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg___lam__0(lean_object* v_x1_3302_, lean_object* v_x2_3303_){
_start:
{
lean_object* v___x_3304_; 
v___x_3304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3304_, 0, v_x1_3302_);
lean_ctor_set(v___x_3304_, 1, v_x2_3303_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___redArg(lean_object* v_as_3306_, lean_object* v_l_3307_){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; uint8_t v___x_3311_; 
v___x_3308_ = lean_array_get_size(v_as_3306_);
v___x_3309_ = lean_unsigned_to_nat(0u);
v___x_3310_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3311_ = lean_nat_dec_lt(v___x_3309_, v___x_3308_);
if (v___x_3311_ == 0)
{
lean_dec_ref(v_as_3306_);
return v_l_3307_;
}
else
{
lean_object* v___f_3312_; size_t v___x_3313_; size_t v___x_3314_; lean_object* v___x_3315_; 
v___f_3312_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3313_ = lean_usize_of_nat(v___x_3308_);
v___x_3314_ = ((size_t)0ULL);
v___x_3315_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3310_, v___f_3312_, v_as_3306_, v___x_3313_, v___x_3314_, v_l_3307_);
return v___x_3315_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend(lean_object* v_00_u03b1_3316_, lean_object* v_as_3317_, lean_object* v_l_3318_){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; uint8_t v___x_3322_; 
v___x_3319_ = lean_array_get_size(v_as_3317_);
v___x_3320_ = lean_unsigned_to_nat(0u);
v___x_3321_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3322_ = lean_nat_dec_lt(v___x_3320_, v___x_3319_);
if (v___x_3322_ == 0)
{
lean_dec_ref(v_as_3317_);
return v_l_3318_;
}
else
{
lean_object* v___f_3323_; size_t v___x_3324_; size_t v___x_3325_; lean_object* v___x_3326_; 
v___f_3323_ = ((lean_object*)(l_Array_toListAppend___redArg___closed__0));
v___x_3324_ = lean_usize_of_nat(v___x_3319_);
v___x_3325_ = ((size_t)0ULL);
v___x_3326_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v___x_3321_, v___f_3323_, v_as_3317_, v___x_3324_, v___x_3325_, v_l_3318_);
return v___x_3326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(lean_object* v_as_3327_, size_t v_i_3328_, size_t v_stop_3329_, lean_object* v_b_3330_){
_start:
{
uint8_t v___x_3331_; 
v___x_3331_ = lean_usize_dec_eq(v_i_3328_, v_stop_3329_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; lean_object* v___x_3333_; size_t v___x_3334_; size_t v___x_3335_; 
v___x_3332_ = lean_array_uget_borrowed(v_as_3327_, v_i_3328_);
lean_inc(v___x_3332_);
v___x_3333_ = lean_array_push(v_b_3330_, v___x_3332_);
v___x_3334_ = ((size_t)1ULL);
v___x_3335_ = lean_usize_add(v_i_3328_, v___x_3334_);
v_i_3328_ = v___x_3335_;
v_b_3330_ = v___x_3333_;
goto _start;
}
else
{
return v_b_3330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg___boxed(lean_object* v_as_3337_, lean_object* v_i_3338_, lean_object* v_stop_3339_, lean_object* v_b_3340_){
_start:
{
size_t v_i_boxed_3341_; size_t v_stop_boxed_3342_; lean_object* v_res_3343_; 
v_i_boxed_3341_ = lean_unbox_usize(v_i_3338_);
lean_dec(v_i_3338_);
v_stop_boxed_3342_ = lean_unbox_usize(v_stop_3339_);
lean_dec(v_stop_3339_);
v_res_3343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3337_, v_i_boxed_3341_, v_stop_boxed_3342_, v_b_3340_);
lean_dec_ref(v_as_3337_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg(lean_object* v_as_3344_, lean_object* v_bs_3345_){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; 
v___x_3346_ = lean_unsigned_to_nat(0u);
v___x_3347_ = lean_array_get_size(v_bs_3345_);
v___x_3348_ = lean_nat_dec_lt(v___x_3346_, v___x_3347_);
if (v___x_3348_ == 0)
{
return v_as_3344_;
}
else
{
uint8_t v___x_3349_; 
v___x_3349_ = lean_nat_dec_le(v___x_3347_, v___x_3347_);
if (v___x_3349_ == 0)
{
if (v___x_3348_ == 0)
{
return v_as_3344_;
}
else
{
size_t v___x_3350_; size_t v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = ((size_t)0ULL);
v___x_3351_ = lean_usize_of_nat(v___x_3347_);
v___x_3352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3345_, v___x_3350_, v___x_3351_, v_as_3344_);
return v___x_3352_;
}
}
else
{
size_t v___x_3353_; size_t v___x_3354_; lean_object* v___x_3355_; 
v___x_3353_ = ((size_t)0ULL);
v___x_3354_ = lean_usize_of_nat(v___x_3347_);
v___x_3355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_bs_3345_, v___x_3353_, v___x_3354_, v_as_3344_);
return v___x_3355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_append___redArg___boxed(lean_object* v_as_3356_, lean_object* v_bs_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Array_append___redArg(v_as_3356_, v_bs_3357_);
lean_dec_ref(v_bs_3357_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Array_append(lean_object* v_00_u03b1_3359_, lean_object* v_as_3360_, lean_object* v_bs_3361_){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = l_Array_append___redArg(v_as_3360_, v_bs_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Array_append___boxed(lean_object* v_00_u03b1_3363_, lean_object* v_as_3364_, lean_object* v_bs_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_Array_append(v_00_u03b1_3363_, v_as_3364_, v_bs_3365_);
lean_dec_ref(v_bs_3365_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(lean_object* v_00_u03b1_3367_, lean_object* v_as_3368_, size_t v_i_3369_, size_t v_stop_3370_, lean_object* v_b_3371_){
_start:
{
lean_object* v___x_3372_; 
v___x_3372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___redArg(v_as_3368_, v_i_3369_, v_stop_3370_, v_b_3371_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0___boxed(lean_object* v_00_u03b1_3373_, lean_object* v_as_3374_, lean_object* v_i_3375_, lean_object* v_stop_3376_, lean_object* v_b_3377_){
_start:
{
size_t v_i_boxed_3378_; size_t v_stop_boxed_3379_; lean_object* v_res_3380_; 
v_i_boxed_3378_ = lean_unbox_usize(v_i_3375_);
lean_dec(v_i_3375_);
v_stop_boxed_3379_ = lean_unbox_usize(v_stop_3376_);
lean_dec(v_stop_3376_);
v_res_3380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_append_spec__0(v_00_u03b1_3373_, v_as_3374_, v_i_boxed_3378_, v_stop_boxed_3379_, v_b_3377_);
lean_dec_ref(v_as_3374_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend(lean_object* v_00_u03b1_3382_){
_start:
{
lean_object* v___x_3383_; 
v___x_3383_ = ((lean_object*)(l_Array_instAppend___closed__0));
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object* v_x_3384_, lean_object* v_x_3385_){
_start:
{
if (lean_obj_tag(v_x_3385_) == 0)
{
return v_x_3384_;
}
else
{
lean_object* v_head_3386_; lean_object* v_tail_3387_; lean_object* v___x_3388_; 
v_head_3386_ = lean_ctor_get(v_x_3385_, 0);
lean_inc(v_head_3386_);
v_tail_3387_ = lean_ctor_get(v_x_3385_, 1);
lean_inc(v_tail_3387_);
lean_dec_ref(v_x_3385_);
v___x_3388_ = lean_array_push(v_x_3384_, v_head_3386_);
v_x_3384_ = v___x_3388_;
v_x_3385_ = v_tail_3387_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_appendList___redArg(lean_object* v_as_3390_, lean_object* v_bs_3391_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3390_, v_bs_3391_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Array_appendList(lean_object* v_00_u03b1_3393_, lean_object* v_as_3394_, lean_object* v_bs_3395_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_as_3394_, v_bs_3395_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Array_appendList_spec__0(lean_object* v_00_u03b1_3397_, lean_object* v_x_3398_, lean_object* v_x_3399_){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_3398_, v_x_3399_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList(lean_object* v_00_u03b1_3402_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = ((lean_object*)(l_Array_instHAppendList___closed__0));
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0(lean_object* v_bs_3404_, lean_object* v_toPure_3405_, lean_object* v_____do__lift_3406_){
_start:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3407_ = l_Array_append___redArg(v_bs_3404_, v_____do__lift_3406_);
v___x_3408_ = lean_apply_2(v_toPure_3405_, lean_box(0), v___x_3407_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__0___boxed(lean_object* v_bs_3409_, lean_object* v_toPure_3410_, lean_object* v_____do__lift_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_Array_flatMapM___redArg___lam__0(v_bs_3409_, v_toPure_3410_, v_____do__lift_3411_);
lean_dec_ref(v_____do__lift_3411_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg___lam__1(lean_object* v_toPure_3413_, lean_object* v_f_3414_, lean_object* v_toBind_3415_, lean_object* v_bs_3416_, lean_object* v_a_3417_){
_start:
{
lean_object* v___f_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___f_3418_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3418_, 0, v_bs_3416_);
lean_closure_set(v___f_3418_, 1, v_toPure_3413_);
v___x_3419_ = lean_apply_1(v_f_3414_, v_a_3417_);
v___x_3420_ = lean_apply_4(v_toBind_3415_, lean_box(0), lean_box(0), v___x_3419_, v___f_3418_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___redArg(lean_object* v_inst_3421_, lean_object* v_f_3422_, lean_object* v_as_3423_){
_start:
{
lean_object* v_toApplicative_3424_; lean_object* v_toBind_3425_; lean_object* v_toPure_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; 
v_toApplicative_3424_ = lean_ctor_get(v_inst_3421_, 0);
v_toBind_3425_ = lean_ctor_get(v_inst_3421_, 1);
v_toPure_3426_ = lean_ctor_get(v_toApplicative_3424_, 1);
v___x_3427_ = lean_unsigned_to_nat(0u);
v___x_3428_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3429_ = lean_array_get_size(v_as_3423_);
v___x_3430_ = lean_nat_dec_lt(v___x_3427_, v___x_3429_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; 
lean_inc(v_toPure_3426_);
lean_dec_ref(v_as_3423_);
lean_dec(v_f_3422_);
lean_dec_ref(v_inst_3421_);
v___x_3431_ = lean_apply_2(v_toPure_3426_, lean_box(0), v___x_3428_);
return v___x_3431_;
}
else
{
lean_object* v___f_3432_; uint8_t v___x_3433_; 
lean_inc(v_toBind_3425_);
lean_inc(v_toPure_3426_);
v___f_3432_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3432_, 0, v_toPure_3426_);
lean_closure_set(v___f_3432_, 1, v_f_3422_);
lean_closure_set(v___f_3432_, 2, v_toBind_3425_);
v___x_3433_ = lean_nat_dec_le(v___x_3429_, v___x_3429_);
if (v___x_3433_ == 0)
{
if (v___x_3430_ == 0)
{
lean_object* v___x_3434_; 
lean_inc(v_toPure_3426_);
lean_dec_ref(v___f_3432_);
lean_dec_ref(v_as_3423_);
lean_dec_ref(v_inst_3421_);
v___x_3434_ = lean_apply_2(v_toPure_3426_, lean_box(0), v___x_3428_);
return v___x_3434_;
}
else
{
size_t v___x_3435_; size_t v___x_3436_; lean_object* v___x_3437_; 
v___x_3435_ = ((size_t)0ULL);
v___x_3436_ = lean_usize_of_nat(v___x_3429_);
v___x_3437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3421_, v___f_3432_, v_as_3423_, v___x_3435_, v___x_3436_, v___x_3428_);
return v___x_3437_;
}
}
else
{
size_t v___x_3438_; size_t v___x_3439_; lean_object* v___x_3440_; 
v___x_3438_ = ((size_t)0ULL);
v___x_3439_ = lean_usize_of_nat(v___x_3429_);
v___x_3440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3421_, v___f_3432_, v_as_3423_, v___x_3438_, v___x_3439_, v___x_3428_);
return v___x_3440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM(lean_object* v_00_u03b1_3441_, lean_object* v_m_3442_, lean_object* v_00_u03b2_3443_, lean_object* v_inst_3444_, lean_object* v_f_3445_, lean_object* v_as_3446_){
_start:
{
lean_object* v_toApplicative_3447_; lean_object* v_toBind_3448_; lean_object* v_toPure_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; 
v_toApplicative_3447_ = lean_ctor_get(v_inst_3444_, 0);
v_toBind_3448_ = lean_ctor_get(v_inst_3444_, 1);
v_toPure_3449_ = lean_ctor_get(v_toApplicative_3447_, 1);
v___x_3450_ = lean_unsigned_to_nat(0u);
v___x_3451_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3452_ = lean_array_get_size(v_as_3446_);
v___x_3453_ = lean_nat_dec_lt(v___x_3450_, v___x_3452_);
if (v___x_3453_ == 0)
{
lean_object* v___x_3454_; 
lean_inc(v_toPure_3449_);
lean_dec_ref(v_as_3446_);
lean_dec(v_f_3445_);
lean_dec_ref(v_inst_3444_);
v___x_3454_ = lean_apply_2(v_toPure_3449_, lean_box(0), v___x_3451_);
return v___x_3454_;
}
else
{
lean_object* v___f_3455_; uint8_t v___x_3456_; 
lean_inc(v_toBind_3448_);
lean_inc(v_toPure_3449_);
v___f_3455_ = lean_alloc_closure((void*)(l_Array_flatMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3455_, 0, v_toPure_3449_);
lean_closure_set(v___f_3455_, 1, v_f_3445_);
lean_closure_set(v___f_3455_, 2, v_toBind_3448_);
v___x_3456_ = lean_nat_dec_le(v___x_3452_, v___x_3452_);
if (v___x_3456_ == 0)
{
if (v___x_3453_ == 0)
{
lean_object* v___x_3457_; 
lean_inc(v_toPure_3449_);
lean_dec_ref(v___f_3455_);
lean_dec_ref(v_as_3446_);
lean_dec_ref(v_inst_3444_);
v___x_3457_ = lean_apply_2(v_toPure_3449_, lean_box(0), v___x_3451_);
return v___x_3457_;
}
else
{
size_t v___x_3458_; size_t v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = ((size_t)0ULL);
v___x_3459_ = lean_usize_of_nat(v___x_3452_);
v___x_3460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3444_, v___f_3455_, v_as_3446_, v___x_3458_, v___x_3459_, v___x_3451_);
return v___x_3460_;
}
}
else
{
size_t v___x_3461_; size_t v___x_3462_; lean_object* v___x_3463_; 
v___x_3461_ = ((size_t)0ULL);
v___x_3462_ = lean_usize_of_nat(v___x_3452_);
v___x_3463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3444_, v___f_3455_, v_as_3446_, v___x_3461_, v___x_3462_, v___x_3451_);
return v___x_3463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg___lam__0(lean_object* v_f_3464_, lean_object* v_x1_3465_, lean_object* v_x2_3466_){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3467_ = lean_apply_1(v_f_3464_, v_x2_3466_);
v___x_3468_ = l_Array_append___redArg(v_x1_3465_, v___x_3467_);
lean_dec_ref(v___x_3467_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___redArg(lean_object* v_f_3469_, lean_object* v_as_3470_){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; 
v___x_3471_ = lean_unsigned_to_nat(0u);
v___x_3472_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3473_ = lean_array_get_size(v_as_3470_);
v___x_3474_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3475_ = lean_nat_dec_lt(v___x_3471_, v___x_3473_);
if (v___x_3475_ == 0)
{
lean_dec_ref(v_as_3470_);
lean_dec_ref(v_f_3469_);
return v___x_3472_;
}
else
{
lean_object* v___f_3476_; uint8_t v___x_3477_; 
v___f_3476_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3476_, 0, v_f_3469_);
v___x_3477_ = lean_nat_dec_le(v___x_3473_, v___x_3473_);
if (v___x_3477_ == 0)
{
if (v___x_3475_ == 0)
{
lean_dec_ref(v___f_3476_);
lean_dec_ref(v_as_3470_);
return v___x_3472_;
}
else
{
size_t v___x_3478_; size_t v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = ((size_t)0ULL);
v___x_3479_ = lean_usize_of_nat(v___x_3473_);
v___x_3480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3474_, v___f_3476_, v_as_3470_, v___x_3478_, v___x_3479_, v___x_3472_);
return v___x_3480_;
}
}
else
{
size_t v___x_3481_; size_t v___x_3482_; lean_object* v___x_3483_; 
v___x_3481_ = ((size_t)0ULL);
v___x_3482_ = lean_usize_of_nat(v___x_3473_);
v___x_3483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3474_, v___f_3476_, v_as_3470_, v___x_3481_, v___x_3482_, v___x_3472_);
return v___x_3483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap(lean_object* v_00_u03b1_3484_, lean_object* v_00_u03b2_3485_, lean_object* v_f_3486_, lean_object* v_as_3487_){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v___x_3488_ = lean_unsigned_to_nat(0u);
v___x_3489_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3490_ = lean_array_get_size(v_as_3487_);
v___x_3491_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3492_ = lean_nat_dec_lt(v___x_3488_, v___x_3490_);
if (v___x_3492_ == 0)
{
lean_dec_ref(v_as_3487_);
lean_dec_ref(v_f_3486_);
return v___x_3489_;
}
else
{
lean_object* v___f_3493_; uint8_t v___x_3494_; 
v___f_3493_ = lean_alloc_closure((void*)(l_Array_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3493_, 0, v_f_3486_);
v___x_3494_ = lean_nat_dec_le(v___x_3490_, v___x_3490_);
if (v___x_3494_ == 0)
{
if (v___x_3492_ == 0)
{
lean_dec_ref(v___f_3493_);
lean_dec_ref(v_as_3487_);
return v___x_3489_;
}
else
{
size_t v___x_3495_; size_t v___x_3496_; lean_object* v___x_3497_; 
v___x_3495_ = ((size_t)0ULL);
v___x_3496_ = lean_usize_of_nat(v___x_3490_);
v___x_3497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3491_, v___f_3493_, v_as_3487_, v___x_3495_, v___x_3496_, v___x_3489_);
return v___x_3497_;
}
}
else
{
size_t v___x_3498_; size_t v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = ((size_t)0ULL);
v___x_3499_ = lean_usize_of_nat(v___x_3490_);
v___x_3500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3491_, v___f_3493_, v_as_3487_, v___x_3498_, v___x_3499_, v___x_3489_);
return v___x_3500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten___redArg(lean_object* v_xss_3502_){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; uint8_t v___x_3507_; 
v___x_3503_ = lean_unsigned_to_nat(0u);
v___x_3504_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3505_ = lean_array_get_size(v_xss_3502_);
v___x_3506_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3507_ = lean_nat_dec_lt(v___x_3503_, v___x_3505_);
if (v___x_3507_ == 0)
{
lean_dec_ref(v_xss_3502_);
return v___x_3504_;
}
else
{
lean_object* v___f_3508_; uint8_t v___x_3509_; 
v___f_3508_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3509_ = lean_nat_dec_le(v___x_3505_, v___x_3505_);
if (v___x_3509_ == 0)
{
if (v___x_3507_ == 0)
{
lean_dec_ref(v_xss_3502_);
return v___x_3504_;
}
else
{
size_t v___x_3510_; size_t v___x_3511_; lean_object* v___x_3512_; 
v___x_3510_ = ((size_t)0ULL);
v___x_3511_ = lean_usize_of_nat(v___x_3505_);
v___x_3512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3506_, v___f_3508_, v_xss_3502_, v___x_3510_, v___x_3511_, v___x_3504_);
return v___x_3512_;
}
}
else
{
size_t v___x_3513_; size_t v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = ((size_t)0ULL);
v___x_3514_ = lean_usize_of_nat(v___x_3505_);
v___x_3515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3506_, v___f_3508_, v_xss_3502_, v___x_3513_, v___x_3514_, v___x_3504_);
return v___x_3515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten(lean_object* v_00_u03b1_3516_, lean_object* v_xss_3517_){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v___x_3518_ = lean_unsigned_to_nat(0u);
v___x_3519_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_3520_ = lean_array_get_size(v_xss_3517_);
v___x_3521_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3522_ = lean_nat_dec_lt(v___x_3518_, v___x_3520_);
if (v___x_3522_ == 0)
{
lean_dec_ref(v_xss_3517_);
return v___x_3519_;
}
else
{
lean_object* v___f_3523_; uint8_t v___x_3524_; 
v___f_3523_ = ((lean_object*)(l_Array_flatten___redArg___closed__0));
v___x_3524_ = lean_nat_dec_le(v___x_3520_, v___x_3520_);
if (v___x_3524_ == 0)
{
if (v___x_3522_ == 0)
{
lean_dec_ref(v_xss_3517_);
return v___x_3519_;
}
else
{
size_t v___x_3525_; size_t v___x_3526_; lean_object* v___x_3527_; 
v___x_3525_ = ((size_t)0ULL);
v___x_3526_ = lean_usize_of_nat(v___x_3520_);
v___x_3527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3521_, v___f_3523_, v_xss_3517_, v___x_3525_, v___x_3526_, v___x_3519_);
return v___x_3527_;
}
}
else
{
size_t v___x_3528_; size_t v___x_3529_; lean_object* v___x_3530_; 
v___x_3528_ = ((size_t)0ULL);
v___x_3529_ = lean_usize_of_nat(v___x_3520_);
v___x_3530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3521_, v___f_3523_, v_xss_3517_, v___x_3528_, v___x_3529_, v___x_3519_);
return v___x_3530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop___redArg(lean_object* v_as_3531_, lean_object* v_i_3532_, lean_object* v_j_3533_){
_start:
{
uint8_t v___x_3534_; 
v___x_3534_ = lean_nat_dec_lt(v_i_3532_, v_j_3533_);
if (v___x_3534_ == 0)
{
lean_dec(v_j_3533_);
lean_dec(v_i_3532_);
return v_as_3531_;
}
else
{
lean_object* v_as_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v_as_3535_ = lean_array_fswap(v_as_3531_, v_i_3532_, v_j_3533_);
v___x_3536_ = lean_unsigned_to_nat(1u);
v___x_3537_ = lean_nat_add(v_i_3532_, v___x_3536_);
lean_dec(v_i_3532_);
v___x_3538_ = lean_nat_sub(v_j_3533_, v___x_3536_);
lean_dec(v_j_3533_);
v_as_3531_ = v_as_3535_;
v_i_3532_ = v___x_3537_;
v_j_3533_ = v___x_3538_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop(lean_object* v_00_u03b1_3540_, lean_object* v_as_3541_, lean_object* v_i_3542_, lean_object* v_j_3543_){
_start:
{
lean_object* v___x_3544_; 
v___x_3544_ = l_Array_reverse_loop___redArg(v_as_3541_, v_i_3542_, v_j_3543_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Array_reverse___redArg(lean_object* v_as_3545_){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3546_ = lean_array_get_size(v_as_3545_);
v___x_3547_ = lean_unsigned_to_nat(1u);
v___x_3548_ = lean_nat_dec_le(v___x_3546_, v___x_3547_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = lean_unsigned_to_nat(0u);
v___x_3550_ = lean_nat_sub(v___x_3546_, v___x_3547_);
v___x_3551_ = l_Array_reverse_loop___redArg(v_as_3545_, v___x_3549_, v___x_3550_);
return v___x_3551_;
}
else
{
return v_as_3545_;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse(lean_object* v_00_u03b1_3552_, lean_object* v_as_3553_){
_start:
{
lean_object* v___x_3554_; 
v___x_3554_ = l_Array_reverse___redArg(v_as_3553_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___lam__0(lean_object* v_p_3555_, lean_object* v_x1_3556_, lean_object* v_x2_3557_){
_start:
{
lean_object* v___x_3558_; uint8_t v___x_3559_; 
lean_inc(v_x2_3557_);
v___x_3558_ = lean_apply_1(v_p_3555_, v_x2_3557_);
v___x_3559_ = lean_unbox(v___x_3558_);
if (v___x_3559_ == 0)
{
lean_dec(v_x2_3557_);
return v_x1_3556_;
}
else
{
lean_object* v___x_3560_; 
v___x_3560_ = lean_array_push(v_x1_3556_, v_x2_3557_);
return v___x_3560_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg(lean_object* v_p_3563_, lean_object* v_as_3564_, lean_object* v_start_3565_, lean_object* v_stop_3566_){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; uint8_t v___x_3569_; 
v___x_3567_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3568_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3569_ = lean_nat_dec_lt(v_start_3565_, v_stop_3566_);
if (v___x_3569_ == 0)
{
lean_dec_ref(v_as_3564_);
lean_dec_ref(v_p_3563_);
return v___x_3567_;
}
else
{
lean_object* v___f_3570_; lean_object* v___x_3571_; uint8_t v___x_3572_; 
v___f_3570_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3570_, 0, v_p_3563_);
v___x_3571_ = lean_array_get_size(v_as_3564_);
v___x_3572_ = lean_nat_dec_le(v_stop_3566_, v___x_3571_);
if (v___x_3572_ == 0)
{
uint8_t v___x_3573_; 
v___x_3573_ = lean_nat_dec_lt(v_start_3565_, v___x_3571_);
if (v___x_3573_ == 0)
{
lean_dec_ref(v___f_3570_);
lean_dec_ref(v_as_3564_);
return v___x_3567_;
}
else
{
size_t v___x_3574_; size_t v___x_3575_; lean_object* v___x_3576_; 
v___x_3574_ = lean_usize_of_nat(v_start_3565_);
v___x_3575_ = lean_usize_of_nat(v___x_3571_);
v___x_3576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3568_, v___f_3570_, v_as_3564_, v___x_3574_, v___x_3575_, v___x_3567_);
return v___x_3576_;
}
}
else
{
size_t v___x_3577_; size_t v___x_3578_; lean_object* v___x_3579_; 
v___x_3577_ = lean_usize_of_nat(v_start_3565_);
v___x_3578_ = lean_usize_of_nat(v_stop_3566_);
v___x_3579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3568_, v___f_3570_, v_as_3564_, v___x_3577_, v___x_3578_, v___x_3567_);
return v___x_3579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___redArg___boxed(lean_object* v_p_3580_, lean_object* v_as_3581_, lean_object* v_start_3582_, lean_object* v_stop_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_Array_filter___redArg(v_p_3580_, v_as_3581_, v_start_3582_, v_stop_3583_);
lean_dec(v_stop_3583_);
lean_dec(v_start_3582_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_Array_filter(lean_object* v_00_u03b1_3585_, lean_object* v_p_3586_, lean_object* v_as_3587_, lean_object* v_start_3588_, lean_object* v_stop_3589_){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; uint8_t v___x_3592_; 
v___x_3590_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3591_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3592_ = lean_nat_dec_lt(v_start_3588_, v_stop_3589_);
if (v___x_3592_ == 0)
{
lean_dec_ref(v_as_3587_);
lean_dec_ref(v_p_3586_);
return v___x_3590_;
}
else
{
lean_object* v___f_3593_; lean_object* v___x_3594_; uint8_t v___x_3595_; 
v___f_3593_ = lean_alloc_closure((void*)(l_Array_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3593_, 0, v_p_3586_);
v___x_3594_ = lean_array_get_size(v_as_3587_);
v___x_3595_ = lean_nat_dec_le(v_stop_3589_, v___x_3594_);
if (v___x_3595_ == 0)
{
uint8_t v___x_3596_; 
v___x_3596_ = lean_nat_dec_lt(v_start_3588_, v___x_3594_);
if (v___x_3596_ == 0)
{
lean_dec_ref(v___f_3593_);
lean_dec_ref(v_as_3587_);
return v___x_3590_;
}
else
{
size_t v___x_3597_; size_t v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = lean_usize_of_nat(v_start_3588_);
v___x_3598_ = lean_usize_of_nat(v___x_3594_);
v___x_3599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3591_, v___f_3593_, v_as_3587_, v___x_3597_, v___x_3598_, v___x_3590_);
return v___x_3599_;
}
}
else
{
size_t v___x_3600_; size_t v___x_3601_; lean_object* v___x_3602_; 
v___x_3600_ = lean_usize_of_nat(v_start_3588_);
v___x_3601_ = lean_usize_of_nat(v_stop_3589_);
v___x_3602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3591_, v___f_3593_, v_as_3587_, v___x_3600_, v___x_3601_, v___x_3590_);
return v___x_3602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter___boxed(lean_object* v_00_u03b1_3603_, lean_object* v_p_3604_, lean_object* v_as_3605_, lean_object* v_start_3606_, lean_object* v_stop_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Array_filter(v_00_u03b1_3603_, v_p_3604_, v_as_3605_, v_start_3606_, v_stop_3607_);
lean_dec(v_stop_3607_);
lean_dec(v_start_3606_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0(lean_object* v_toApplicative_3609_, lean_object* v_acc_3610_, lean_object* v_a_3611_, uint8_t v_____do__lift_3612_){
_start:
{
if (v_____do__lift_3612_ == 0)
{
lean_object* v_toPure_3613_; lean_object* v___x_3614_; 
lean_dec(v_a_3611_);
v_toPure_3613_ = lean_ctor_get(v_toApplicative_3609_, 1);
lean_inc(v_toPure_3613_);
lean_dec_ref(v_toApplicative_3609_);
v___x_3614_ = lean_apply_2(v_toPure_3613_, lean_box(0), v_acc_3610_);
return v___x_3614_;
}
else
{
lean_object* v_toPure_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v_toPure_3615_ = lean_ctor_get(v_toApplicative_3609_, 1);
lean_inc(v_toPure_3615_);
lean_dec_ref(v_toApplicative_3609_);
v___x_3616_ = lean_array_push(v_acc_3610_, v_a_3611_);
v___x_3617_ = lean_apply_2(v_toPure_3615_, lean_box(0), v___x_3616_);
return v___x_3617_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__0___boxed(lean_object* v_toApplicative_3618_, lean_object* v_acc_3619_, lean_object* v_a_3620_, lean_object* v_____do__lift_3621_){
_start:
{
uint8_t v_____do__lift_119__boxed_3622_; lean_object* v_res_3623_; 
v_____do__lift_119__boxed_3622_ = lean_unbox(v_____do__lift_3621_);
v_res_3623_ = l_Array_filterM___redArg___lam__0(v_toApplicative_3618_, v_acc_3619_, v_a_3620_, v_____do__lift_119__boxed_3622_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___lam__1(lean_object* v_toApplicative_3624_, lean_object* v_p_3625_, lean_object* v_toBind_3626_, lean_object* v_acc_3627_, lean_object* v_a_3628_){
_start:
{
lean_object* v___f_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
lean_inc(v_a_3628_);
v___f_3629_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3629_, 0, v_toApplicative_3624_);
lean_closure_set(v___f_3629_, 1, v_acc_3627_);
lean_closure_set(v___f_3629_, 2, v_a_3628_);
v___x_3630_ = lean_apply_1(v_p_3625_, v_a_3628_);
v___x_3631_ = lean_apply_4(v_toBind_3626_, lean_box(0), lean_box(0), v___x_3630_, v___f_3629_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg(lean_object* v_inst_3632_, lean_object* v_p_3633_, lean_object* v_as_3634_, lean_object* v_start_3635_, lean_object* v_stop_3636_){
_start:
{
lean_object* v_toApplicative_3637_; lean_object* v_toBind_3638_; lean_object* v___x_3639_; uint8_t v___x_3640_; 
v_toApplicative_3637_ = lean_ctor_get(v_inst_3632_, 0);
v_toBind_3638_ = lean_ctor_get(v_inst_3632_, 1);
v___x_3639_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3640_ = lean_nat_dec_lt(v_start_3635_, v_stop_3636_);
if (v___x_3640_ == 0)
{
lean_object* v_toPure_3641_; lean_object* v___x_3642_; 
lean_inc_ref(v_toApplicative_3637_);
lean_dec_ref(v_as_3634_);
lean_dec(v_p_3633_);
lean_dec_ref(v_inst_3632_);
v_toPure_3641_ = lean_ctor_get(v_toApplicative_3637_, 1);
lean_inc(v_toPure_3641_);
lean_dec_ref(v_toApplicative_3637_);
v___x_3642_ = lean_apply_2(v_toPure_3641_, lean_box(0), v___x_3639_);
return v___x_3642_;
}
else
{
lean_object* v___f_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
lean_inc(v_toBind_3638_);
lean_inc_ref(v_toApplicative_3637_);
v___f_3643_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3643_, 0, v_toApplicative_3637_);
lean_closure_set(v___f_3643_, 1, v_p_3633_);
lean_closure_set(v___f_3643_, 2, v_toBind_3638_);
v___x_3644_ = lean_array_get_size(v_as_3634_);
v___x_3645_ = lean_nat_dec_le(v_stop_3636_, v___x_3644_);
if (v___x_3645_ == 0)
{
uint8_t v___x_3646_; 
v___x_3646_ = lean_nat_dec_lt(v_start_3635_, v___x_3644_);
if (v___x_3646_ == 0)
{
lean_object* v_toPure_3647_; lean_object* v___x_3648_; 
lean_inc_ref(v_toApplicative_3637_);
lean_dec_ref(v___f_3643_);
lean_dec_ref(v_as_3634_);
lean_dec_ref(v_inst_3632_);
v_toPure_3647_ = lean_ctor_get(v_toApplicative_3637_, 1);
lean_inc(v_toPure_3647_);
lean_dec_ref(v_toApplicative_3637_);
v___x_3648_ = lean_apply_2(v_toPure_3647_, lean_box(0), v___x_3639_);
return v___x_3648_;
}
else
{
size_t v___x_3649_; size_t v___x_3650_; lean_object* v___x_3651_; 
v___x_3649_ = lean_usize_of_nat(v_start_3635_);
v___x_3650_ = lean_usize_of_nat(v___x_3644_);
v___x_3651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3632_, v___f_3643_, v_as_3634_, v___x_3649_, v___x_3650_, v___x_3639_);
return v___x_3651_;
}
}
else
{
size_t v___x_3652_; size_t v___x_3653_; lean_object* v___x_3654_; 
v___x_3652_ = lean_usize_of_nat(v_start_3635_);
v___x_3653_ = lean_usize_of_nat(v_stop_3636_);
v___x_3654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3632_, v___f_3643_, v_as_3634_, v___x_3652_, v___x_3653_, v___x_3639_);
return v___x_3654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___redArg___boxed(lean_object* v_inst_3655_, lean_object* v_p_3656_, lean_object* v_as_3657_, lean_object* v_start_3658_, lean_object* v_stop_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l_Array_filterM___redArg(v_inst_3655_, v_p_3656_, v_as_3657_, v_start_3658_, v_stop_3659_);
lean_dec(v_stop_3659_);
lean_dec(v_start_3658_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l_Array_filterM(lean_object* v_m_3661_, lean_object* v_00_u03b1_3662_, lean_object* v_inst_3663_, lean_object* v_p_3664_, lean_object* v_as_3665_, lean_object* v_start_3666_, lean_object* v_stop_3667_){
_start:
{
lean_object* v_toApplicative_3668_; lean_object* v_toBind_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; 
v_toApplicative_3668_ = lean_ctor_get(v_inst_3663_, 0);
v_toBind_3669_ = lean_ctor_get(v_inst_3663_, 1);
v___x_3670_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3671_ = lean_nat_dec_lt(v_start_3666_, v_stop_3667_);
if (v___x_3671_ == 0)
{
lean_object* v_toPure_3672_; lean_object* v___x_3673_; 
lean_inc_ref(v_toApplicative_3668_);
lean_dec_ref(v_as_3665_);
lean_dec(v_p_3664_);
lean_dec_ref(v_inst_3663_);
v_toPure_3672_ = lean_ctor_get(v_toApplicative_3668_, 1);
lean_inc(v_toPure_3672_);
lean_dec_ref(v_toApplicative_3668_);
v___x_3673_ = lean_apply_2(v_toPure_3672_, lean_box(0), v___x_3670_);
return v___x_3673_;
}
else
{
lean_object* v___f_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; 
lean_inc(v_toBind_3669_);
lean_inc_ref(v_toApplicative_3668_);
v___f_3674_ = lean_alloc_closure((void*)(l_Array_filterM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3674_, 0, v_toApplicative_3668_);
lean_closure_set(v___f_3674_, 1, v_p_3664_);
lean_closure_set(v___f_3674_, 2, v_toBind_3669_);
v___x_3675_ = lean_array_get_size(v_as_3665_);
v___x_3676_ = lean_nat_dec_le(v_stop_3667_, v___x_3675_);
if (v___x_3676_ == 0)
{
uint8_t v___x_3677_; 
v___x_3677_ = lean_nat_dec_lt(v_start_3666_, v___x_3675_);
if (v___x_3677_ == 0)
{
lean_object* v_toPure_3678_; lean_object* v___x_3679_; 
lean_inc_ref(v_toApplicative_3668_);
lean_dec_ref(v___f_3674_);
lean_dec_ref(v_as_3665_);
lean_dec_ref(v_inst_3663_);
v_toPure_3678_ = lean_ctor_get(v_toApplicative_3668_, 1);
lean_inc(v_toPure_3678_);
lean_dec_ref(v_toApplicative_3668_);
v___x_3679_ = lean_apply_2(v_toPure_3678_, lean_box(0), v___x_3670_);
return v___x_3679_;
}
else
{
size_t v___x_3680_; size_t v___x_3681_; lean_object* v___x_3682_; 
v___x_3680_ = lean_usize_of_nat(v_start_3666_);
v___x_3681_ = lean_usize_of_nat(v___x_3675_);
v___x_3682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3663_, v___f_3674_, v_as_3665_, v___x_3680_, v___x_3681_, v___x_3670_);
return v___x_3682_;
}
}
else
{
size_t v___x_3683_; size_t v___x_3684_; lean_object* v___x_3685_; 
v___x_3683_ = lean_usize_of_nat(v_start_3666_);
v___x_3684_ = lean_usize_of_nat(v_stop_3667_);
v___x_3685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3663_, v___f_3674_, v_as_3665_, v___x_3683_, v___x_3684_, v___x_3670_);
return v___x_3685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM___boxed(lean_object* v_m_3686_, lean_object* v_00_u03b1_3687_, lean_object* v_inst_3688_, lean_object* v_p_3689_, lean_object* v_as_3690_, lean_object* v_start_3691_, lean_object* v_stop_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Array_filterM(v_m_3686_, v_00_u03b1_3687_, v_inst_3688_, v_p_3689_, v_as_3690_, v_start_3691_, v_stop_3692_);
lean_dec(v_stop_3692_);
lean_dec(v_start_3691_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__0(lean_object* v_toPure_3694_, lean_object* v_acc_3695_, lean_object* v_a_3696_, uint8_t v_____do__lift_3697_){
_start:
{
if (v_____do__lift_3697_ == 0)
{
lean_object* v___x_3698_; 
lean_dec(v_a_3696_);
v___x_3698_ = lean_apply_2(v_toPure_3694_, lean_box(0), v_acc_3695_);
return v___x_3698_;
}
else
{
lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3699_ = lean_array_push(v_acc_3695_, v_a_3696_);
v___x_3700_ = lean_apply_2(v_toPure_3694_, lean_box(0), v___x_3699_);
return v___x_3700_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__0___boxed(lean_object* v_toPure_3701_, lean_object* v_acc_3702_, lean_object* v_a_3703_, lean_object* v_____do__lift_3704_){
_start:
{
uint8_t v_____do__lift_129__boxed_3705_; lean_object* v_res_3706_; 
v_____do__lift_129__boxed_3705_ = lean_unbox(v_____do__lift_3704_);
v_res_3706_ = l_Array_filterRevM___redArg___lam__0(v_toPure_3701_, v_acc_3702_, v_a_3703_, v_____do__lift_129__boxed_3705_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___lam__1(lean_object* v_toPure_3707_, lean_object* v_p_3708_, lean_object* v_toBind_3709_, lean_object* v_a_3710_, lean_object* v_acc_3711_){
_start:
{
lean_object* v___f_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
lean_inc(v_a_3710_);
v___f_3712_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3712_, 0, v_toPure_3707_);
lean_closure_set(v___f_3712_, 1, v_acc_3711_);
lean_closure_set(v___f_3712_, 2, v_a_3710_);
v___x_3713_ = lean_apply_1(v_p_3708_, v_a_3710_);
v___x_3714_ = lean_apply_4(v_toBind_3709_, lean_box(0), lean_box(0), v___x_3713_, v___f_3712_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg(lean_object* v_inst_3716_, lean_object* v_p_3717_, lean_object* v_as_3718_, lean_object* v_start_3719_, lean_object* v_stop_3720_){
_start:
{
lean_object* v_toApplicative_3721_; lean_object* v_toFunctor_3722_; lean_object* v_toBind_3723_; lean_object* v_toPure_3724_; lean_object* v_map_3725_; lean_object* v___f_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; uint8_t v___x_3730_; 
v_toApplicative_3721_ = lean_ctor_get(v_inst_3716_, 0);
v_toFunctor_3722_ = lean_ctor_get(v_toApplicative_3721_, 0);
v_toBind_3723_ = lean_ctor_get(v_inst_3716_, 1);
v_toPure_3724_ = lean_ctor_get(v_toApplicative_3721_, 1);
v_map_3725_ = lean_ctor_get(v_toFunctor_3722_, 0);
lean_inc(v_map_3725_);
lean_inc(v_toBind_3723_);
lean_inc(v_toPure_3724_);
v___f_3726_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3726_, 0, v_toPure_3724_);
lean_closure_set(v___f_3726_, 1, v_p_3717_);
lean_closure_set(v___f_3726_, 2, v_toBind_3723_);
v___x_3727_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3728_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3729_ = lean_array_get_size(v_as_3718_);
v___x_3730_ = lean_nat_dec_le(v_start_3719_, v___x_3729_);
if (v___x_3730_ == 0)
{
uint8_t v___x_3731_; 
v___x_3731_ = lean_nat_dec_lt(v_stop_3720_, v___x_3729_);
if (v___x_3731_ == 0)
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
lean_inc(v_toPure_3724_);
lean_dec_ref(v___f_3726_);
lean_dec_ref(v_as_3718_);
lean_dec_ref(v_inst_3716_);
v___x_3732_ = lean_apply_2(v_toPure_3724_, lean_box(0), v___x_3728_);
v___x_3733_ = lean_apply_4(v_map_3725_, lean_box(0), lean_box(0), v___x_3727_, v___x_3732_);
return v___x_3733_;
}
else
{
size_t v___x_3734_; size_t v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3734_ = lean_usize_of_nat(v___x_3729_);
v___x_3735_ = lean_usize_of_nat(v_stop_3720_);
v___x_3736_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3716_, v___f_3726_, v_as_3718_, v___x_3734_, v___x_3735_, v___x_3728_);
v___x_3737_ = lean_apply_4(v_map_3725_, lean_box(0), lean_box(0), v___x_3727_, v___x_3736_);
return v___x_3737_;
}
}
else
{
uint8_t v___x_3738_; 
v___x_3738_ = lean_nat_dec_lt(v_stop_3720_, v_start_3719_);
if (v___x_3738_ == 0)
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
lean_inc(v_toPure_3724_);
lean_dec_ref(v___f_3726_);
lean_dec_ref(v_as_3718_);
lean_dec_ref(v_inst_3716_);
v___x_3739_ = lean_apply_2(v_toPure_3724_, lean_box(0), v___x_3728_);
v___x_3740_ = lean_apply_4(v_map_3725_, lean_box(0), lean_box(0), v___x_3727_, v___x_3739_);
return v___x_3740_;
}
else
{
size_t v___x_3741_; size_t v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3741_ = lean_usize_of_nat(v_start_3719_);
v___x_3742_ = lean_usize_of_nat(v_stop_3720_);
v___x_3743_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3716_, v___f_3726_, v_as_3718_, v___x_3741_, v___x_3742_, v___x_3728_);
v___x_3744_ = lean_apply_4(v_map_3725_, lean_box(0), lean_box(0), v___x_3727_, v___x_3743_);
return v___x_3744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___redArg___boxed(lean_object* v_inst_3745_, lean_object* v_p_3746_, lean_object* v_as_3747_, lean_object* v_start_3748_, lean_object* v_stop_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l_Array_filterRevM___redArg(v_inst_3745_, v_p_3746_, v_as_3747_, v_start_3748_, v_stop_3749_);
lean_dec(v_stop_3749_);
lean_dec(v_start_3748_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM(lean_object* v_m_3751_, lean_object* v_00_u03b1_3752_, lean_object* v_inst_3753_, lean_object* v_p_3754_, lean_object* v_as_3755_, lean_object* v_start_3756_, lean_object* v_stop_3757_){
_start:
{
lean_object* v_toApplicative_3758_; lean_object* v_toFunctor_3759_; lean_object* v_toBind_3760_; lean_object* v_toPure_3761_; lean_object* v_map_3762_; lean_object* v___f_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; uint8_t v___x_3767_; 
v_toApplicative_3758_ = lean_ctor_get(v_inst_3753_, 0);
v_toFunctor_3759_ = lean_ctor_get(v_toApplicative_3758_, 0);
v_toBind_3760_ = lean_ctor_get(v_inst_3753_, 1);
v_toPure_3761_ = lean_ctor_get(v_toApplicative_3758_, 1);
v_map_3762_ = lean_ctor_get(v_toFunctor_3759_, 0);
lean_inc(v_map_3762_);
lean_inc(v_toBind_3760_);
lean_inc(v_toPure_3761_);
v___f_3763_ = lean_alloc_closure((void*)(l_Array_filterRevM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3763_, 0, v_toPure_3761_);
lean_closure_set(v___f_3763_, 1, v_p_3754_);
lean_closure_set(v___f_3763_, 2, v_toBind_3760_);
v___x_3764_ = ((lean_object*)(l_Array_filterRevM___redArg___closed__0));
v___x_3765_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3766_ = lean_array_get_size(v_as_3755_);
v___x_3767_ = lean_nat_dec_le(v_start_3756_, v___x_3766_);
if (v___x_3767_ == 0)
{
uint8_t v___x_3768_; 
v___x_3768_ = lean_nat_dec_lt(v_stop_3757_, v___x_3766_);
if (v___x_3768_ == 0)
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
lean_inc(v_toPure_3761_);
lean_dec_ref(v___f_3763_);
lean_dec_ref(v_as_3755_);
lean_dec_ref(v_inst_3753_);
v___x_3769_ = lean_apply_2(v_toPure_3761_, lean_box(0), v___x_3765_);
v___x_3770_ = lean_apply_4(v_map_3762_, lean_box(0), lean_box(0), v___x_3764_, v___x_3769_);
return v___x_3770_;
}
else
{
size_t v___x_3771_; size_t v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3771_ = lean_usize_of_nat(v___x_3766_);
v___x_3772_ = lean_usize_of_nat(v_stop_3757_);
v___x_3773_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3753_, v___f_3763_, v_as_3755_, v___x_3771_, v___x_3772_, v___x_3765_);
v___x_3774_ = lean_apply_4(v_map_3762_, lean_box(0), lean_box(0), v___x_3764_, v___x_3773_);
return v___x_3774_;
}
}
else
{
uint8_t v___x_3775_; 
v___x_3775_ = lean_nat_dec_lt(v_stop_3757_, v_start_3756_);
if (v___x_3775_ == 0)
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
lean_inc(v_toPure_3761_);
lean_dec_ref(v___f_3763_);
lean_dec_ref(v_as_3755_);
lean_dec_ref(v_inst_3753_);
v___x_3776_ = lean_apply_2(v_toPure_3761_, lean_box(0), v___x_3765_);
v___x_3777_ = lean_apply_4(v_map_3762_, lean_box(0), lean_box(0), v___x_3764_, v___x_3776_);
return v___x_3777_;
}
else
{
size_t v___x_3778_; size_t v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3778_ = lean_usize_of_nat(v_start_3756_);
v___x_3779_ = lean_usize_of_nat(v_stop_3757_);
v___x_3780_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___redArg(v_inst_3753_, v___f_3763_, v_as_3755_, v___x_3778_, v___x_3779_, v___x_3765_);
v___x_3781_ = lean_apply_4(v_map_3762_, lean_box(0), lean_box(0), v___x_3764_, v___x_3780_);
return v___x_3781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___boxed(lean_object* v_m_3782_, lean_object* v_00_u03b1_3783_, lean_object* v_inst_3784_, lean_object* v_p_3785_, lean_object* v_as_3786_, lean_object* v_start_3787_, lean_object* v_stop_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l_Array_filterRevM(v_m_3782_, v_00_u03b1_3783_, v_inst_3784_, v_p_3785_, v_as_3786_, v_start_3787_, v_stop_3788_);
lean_dec(v_stop_3788_);
lean_dec(v_start_3787_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__0(lean_object* v_toPure_3790_, lean_object* v_bs_3791_, lean_object* v_____do__lift_3792_){
_start:
{
if (lean_obj_tag(v_____do__lift_3792_) == 0)
{
lean_object* v___x_3793_; 
v___x_3793_ = lean_apply_2(v_toPure_3790_, lean_box(0), v_bs_3791_);
return v___x_3793_;
}
else
{
lean_object* v_val_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v_val_3794_ = lean_ctor_get(v_____do__lift_3792_, 0);
lean_inc(v_val_3794_);
lean_dec_ref(v_____do__lift_3792_);
v___x_3795_ = lean_array_push(v_bs_3791_, v_val_3794_);
v___x_3796_ = lean_apply_2(v_toPure_3790_, lean_box(0), v___x_3795_);
return v___x_3796_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___lam__1(lean_object* v_toPure_3797_, lean_object* v_f_3798_, lean_object* v_toBind_3799_, lean_object* v_bs_3800_, lean_object* v_a_3801_){
_start:
{
lean_object* v___f_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___f_3802_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3802_, 0, v_toPure_3797_);
lean_closure_set(v___f_3802_, 1, v_bs_3800_);
v___x_3803_ = lean_apply_1(v_f_3798_, v_a_3801_);
v___x_3804_ = lean_apply_4(v_toBind_3799_, lean_box(0), lean_box(0), v___x_3803_, v___f_3802_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg(lean_object* v_inst_3805_, lean_object* v_f_3806_, lean_object* v_as_3807_, lean_object* v_start_3808_, lean_object* v_stop_3809_){
_start:
{
lean_object* v_toApplicative_3810_; lean_object* v_toBind_3811_; lean_object* v_toPure_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v_toApplicative_3810_ = lean_ctor_get(v_inst_3805_, 0);
v_toBind_3811_ = lean_ctor_get(v_inst_3805_, 1);
v_toPure_3812_ = lean_ctor_get(v_toApplicative_3810_, 1);
v___x_3813_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3814_ = lean_nat_dec_lt(v_start_3808_, v_stop_3809_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; 
lean_inc(v_toPure_3812_);
lean_dec_ref(v_as_3807_);
lean_dec(v_f_3806_);
lean_dec_ref(v_inst_3805_);
v___x_3815_ = lean_apply_2(v_toPure_3812_, lean_box(0), v___x_3813_);
return v___x_3815_;
}
else
{
lean_object* v___f_3816_; lean_object* v___x_3817_; uint8_t v___x_3818_; 
lean_inc(v_toBind_3811_);
lean_inc(v_toPure_3812_);
v___f_3816_ = lean_alloc_closure((void*)(l_Array_filterMapM___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3816_, 0, v_toPure_3812_);
lean_closure_set(v___f_3816_, 1, v_f_3806_);
lean_closure_set(v___f_3816_, 2, v_toBind_3811_);
v___x_3817_ = lean_array_get_size(v_as_3807_);
v___x_3818_ = lean_nat_dec_le(v_stop_3809_, v___x_3817_);
if (v___x_3818_ == 0)
{
uint8_t v___x_3819_; 
v___x_3819_ = lean_nat_dec_lt(v_start_3808_, v___x_3817_);
if (v___x_3819_ == 0)
{
lean_object* v___x_3820_; 
lean_inc(v_toPure_3812_);
lean_dec_ref(v___f_3816_);
lean_dec_ref(v_as_3807_);
lean_dec_ref(v_inst_3805_);
v___x_3820_ = lean_apply_2(v_toPure_3812_, lean_box(0), v___x_3813_);
return v___x_3820_;
}
else
{
size_t v___x_3821_; size_t v___x_3822_; lean_object* v___x_3823_; 
v___x_3821_ = lean_usize_of_nat(v_start_3808_);
v___x_3822_ = lean_usize_of_nat(v___x_3817_);
v___x_3823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3805_, v___f_3816_, v_as_3807_, v___x_3821_, v___x_3822_, v___x_3813_);
return v___x_3823_;
}
}
else
{
size_t v___x_3824_; size_t v___x_3825_; lean_object* v___x_3826_; 
v___x_3824_ = lean_usize_of_nat(v_start_3808_);
v___x_3825_ = lean_usize_of_nat(v_stop_3809_);
v___x_3826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_3805_, v___f_3816_, v_as_3807_, v___x_3824_, v___x_3825_, v___x_3813_);
return v___x_3826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___redArg___boxed(lean_object* v_inst_3827_, lean_object* v_f_3828_, lean_object* v_as_3829_, lean_object* v_start_3830_, lean_object* v_stop_3831_){
_start:
{
lean_object* v_res_3832_; 
v_res_3832_ = l_Array_filterMapM___redArg(v_inst_3827_, v_f_3828_, v_as_3829_, v_start_3830_, v_stop_3831_);
lean_dec(v_stop_3831_);
lean_dec(v_start_3830_);
return v_res_3832_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM(lean_object* v_00_u03b1_3833_, lean_object* v_m_3834_, lean_object* v_00_u03b2_3835_, lean_object* v_inst_3836_, lean_object* v_f_3837_, lean_object* v_as_3838_, lean_object* v_start_3839_, lean_object* v_stop_3840_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = l_Array_filterMapM___redArg(v_inst_3836_, v_f_3837_, v_as_3838_, v_start_3839_, v_stop_3840_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___boxed(lean_object* v_00_u03b1_3842_, lean_object* v_m_3843_, lean_object* v_00_u03b2_3844_, lean_object* v_inst_3845_, lean_object* v_f_3846_, lean_object* v_as_3847_, lean_object* v_start_3848_, lean_object* v_stop_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Array_filterMapM(v_00_u03b1_3842_, v_m_3843_, v_00_u03b2_3844_, v_inst_3845_, v_f_3846_, v_as_3847_, v_start_3848_, v_stop_3849_);
lean_dec(v_stop_3849_);
lean_dec(v_start_3848_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg(lean_object* v_f_3851_, lean_object* v_as_3852_, lean_object* v_start_3853_, lean_object* v_stop_3854_){
_start:
{
lean_object* v___f_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___f_3855_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3855_, 0, v_f_3851_);
v___x_3856_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3857_ = l_Array_filterMapM___redArg(v___x_3856_, v___f_3855_, v_as_3852_, v_start_3853_, v_stop_3854_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___redArg___boxed(lean_object* v_f_3858_, lean_object* v_as_3859_, lean_object* v_start_3860_, lean_object* v_stop_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Array_filterMap___redArg(v_f_3858_, v_as_3859_, v_start_3860_, v_stop_3861_);
lean_dec(v_stop_3861_);
lean_dec(v_start_3860_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap(lean_object* v_00_u03b1_3863_, lean_object* v_00_u03b2_3864_, lean_object* v_f_3865_, lean_object* v_as_3866_, lean_object* v_start_3867_, lean_object* v_stop_3868_){
_start:
{
lean_object* v___f_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___f_3869_ = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3869_, 0, v_f_3865_);
v___x_3870_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3871_ = l_Array_filterMapM___redArg(v___x_3870_, v___f_3869_, v_as_3866_, v_start_3867_, v_stop_3868_);
return v___x_3871_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___boxed(lean_object* v_00_u03b1_3872_, lean_object* v_00_u03b2_3873_, lean_object* v_f_3874_, lean_object* v_as_3875_, lean_object* v_start_3876_, lean_object* v_stop_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Array_filterMap(v_00_u03b1_3872_, v_00_u03b2_3873_, v_f_3874_, v_as_3875_, v_start_3876_, v_stop_3877_);
lean_dec(v_stop_3877_);
lean_dec(v_start_3876_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg___lam__0(lean_object* v_lt_3879_, lean_object* v_x1_3880_, lean_object* v_x2_3881_){
_start:
{
lean_object* v___x_3882_; uint8_t v___x_3883_; 
lean_inc(v_x2_3881_);
lean_inc(v_x1_3880_);
v___x_3882_ = lean_apply_2(v_lt_3879_, v_x1_3880_, v_x2_3881_);
v___x_3883_ = lean_unbox(v___x_3882_);
if (v___x_3883_ == 0)
{
lean_dec(v_x2_3881_);
return v_x1_3880_;
}
else
{
lean_dec(v_x1_3880_);
return v_x2_3881_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___redArg(lean_object* v_as_3884_, lean_object* v_lt_3885_){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; uint8_t v___x_3888_; 
v___x_3886_ = lean_unsigned_to_nat(0u);
v___x_3887_ = lean_array_get_size(v_as_3884_);
v___x_3888_ = lean_nat_dec_lt(v___x_3886_, v___x_3887_);
if (v___x_3888_ == 0)
{
lean_object* v___x_3889_; 
lean_dec_ref(v_lt_3885_);
lean_dec_ref(v_as_3884_);
v___x_3889_ = lean_box(0);
return v___x_3889_;
}
else
{
lean_object* v_a0_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; uint8_t v___x_3893_; 
v_a0_3890_ = lean_array_fget(v_as_3884_, v___x_3886_);
v___x_3891_ = lean_unsigned_to_nat(1u);
v___x_3892_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3893_ = lean_nat_dec_lt(v___x_3891_, v___x_3887_);
if (v___x_3893_ == 0)
{
lean_object* v___x_3894_; 
lean_dec_ref(v_lt_3885_);
lean_dec_ref(v_as_3884_);
v___x_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3894_, 0, v_a0_3890_);
return v___x_3894_;
}
else
{
lean_object* v___f_3895_; uint8_t v___x_3896_; 
v___f_3895_ = lean_alloc_closure((void*)(l_Array_getMax_x3f___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3895_, 0, v_lt_3885_);
v___x_3896_ = lean_nat_dec_le(v___x_3887_, v___x_3887_);
if (v___x_3896_ == 0)
{
if (v___x_3893_ == 0)
{
lean_object* v___x_3897_; 
lean_dec_ref(v___f_3895_);
lean_dec_ref(v_as_3884_);
v___x_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3897_, 0, v_a0_3890_);
return v___x_3897_;
}
else
{
size_t v___x_3898_; size_t v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3898_ = ((size_t)1ULL);
v___x_3899_ = lean_usize_of_nat(v___x_3887_);
v___x_3900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3892_, v___f_3895_, v_as_3884_, v___x_3898_, v___x_3899_, v_a0_3890_);
v___x_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3900_);
return v___x_3901_;
}
}
else
{
size_t v___x_3902_; size_t v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3902_ = ((size_t)1ULL);
v___x_3903_ = lean_usize_of_nat(v___x_3887_);
v___x_3904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_3892_, v___f_3895_, v_as_3884_, v___x_3902_, v___x_3903_, v_a0_3890_);
v___x_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
return v___x_3905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f(lean_object* v_00_u03b1_3906_, lean_object* v_as_3907_, lean_object* v_lt_3908_){
_start:
{
lean_object* v___x_3909_; 
v___x_3909_ = l_Array_getMax_x3f___redArg(v_as_3907_, v_lt_3908_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg___lam__0(lean_object* v_p_3910_, lean_object* v_a_3911_, lean_object* v_x_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v_fst_3914_; lean_object* v_snd_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3931_; 
v_fst_3914_ = lean_ctor_get(v___y_3913_, 0);
v_snd_3915_ = lean_ctor_get(v___y_3913_, 1);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___y_3913_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3917_ = v___y_3913_;
v_isShared_3918_ = v_isSharedCheck_3931_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_snd_3915_);
lean_inc(v_fst_3914_);
lean_dec(v___y_3913_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3931_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3919_; uint8_t v___x_3920_; 
lean_inc(v_a_3911_);
v___x_3919_ = lean_apply_1(v_p_3910_, v_a_3911_);
v___x_3920_ = lean_unbox(v___x_3919_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; lean_object* v___x_3923_; 
v___x_3921_ = lean_array_push(v_snd_3915_, v_a_3911_);
if (v_isShared_3918_ == 0)
{
lean_ctor_set(v___x_3917_, 1, v___x_3921_);
v___x_3923_ = v___x_3917_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_fst_3914_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v___x_3921_);
v___x_3923_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
lean_object* v___x_3924_; 
v___x_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
return v___x_3924_;
}
}
else
{
lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3926_ = lean_array_push(v_fst_3914_, v_a_3911_);
if (v_isShared_3918_ == 0)
{
lean_ctor_set(v___x_3917_, 0, v___x_3926_);
v___x_3928_ = v___x_3917_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3930_, 1, v_snd_3915_);
v___x_3928_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3929_; 
v___x_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
return v___x_3929_;
}
}
}
}
}
static lean_object* _init_l_Array_partition___redArg___closed__0(void){
_start:
{
lean_object* v_bs_3932_; lean_object* v___x_3933_; 
v_bs_3932_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_3933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3933_, 0, v_bs_3932_);
lean_ctor_set(v___x_3933_, 1, v_bs_3932_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_Array_partition___redArg(lean_object* v_p_3934_, lean_object* v_as_3935_){
_start:
{
lean_object* v___f_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; size_t v_sz_3939_; size_t v___x_3940_; lean_object* v___x_3941_; lean_object* v_fst_3942_; lean_object* v_snd_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
v___f_3936_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3936_, 0, v_p_3934_);
v___x_3937_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3938_ = lean_obj_once(&l_Array_partition___redArg___closed__0, &l_Array_partition___redArg___closed__0_once, _init_l_Array_partition___redArg___closed__0);
v_sz_3939_ = lean_array_size(v_as_3935_);
v___x_3940_ = ((size_t)0ULL);
v___x_3941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_3937_, v_as_3935_, v___f_3936_, v_sz_3939_, v___x_3940_, v___x_3938_);
v_fst_3942_ = lean_ctor_get(v___x_3941_, 0);
v_snd_3943_ = lean_ctor_get(v___x_3941_, 1);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3941_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_snd_3943_);
lean_inc(v_fst_3942_);
lean_dec(v___x_3941_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_fst_3942_);
lean_ctor_set(v_reuseFailAlloc_3949_, 1, v_snd_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_partition(lean_object* v_00_u03b1_3951_, lean_object* v_p_3952_, lean_object* v_as_3953_){
_start:
{
lean_object* v___f_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; size_t v_sz_3957_; size_t v___x_3958_; lean_object* v___x_3959_; lean_object* v_fst_3960_; lean_object* v_snd_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3968_; 
v___f_3954_ = lean_alloc_closure((void*)(l_Array_partition___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3954_, 0, v_p_3952_);
v___x_3955_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_3956_ = lean_obj_once(&l_Array_partition___redArg___closed__0, &l_Array_partition___redArg___closed__0_once, _init_l_Array_partition___redArg___closed__0);
v_sz_3957_ = lean_array_size(v_as_3953_);
v___x_3958_ = ((size_t)0ULL);
v___x_3959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_3955_, v_as_3953_, v___f_3954_, v_sz_3957_, v___x_3958_, v___x_3956_);
v_fst_3960_ = lean_ctor_get(v___x_3959_, 0);
v_snd_3961_ = lean_ctor_get(v___x_3959_, 1);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3963_ = v___x_3959_;
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_snd_3961_);
lean_inc(v_fst_3960_);
lean_dec(v___x_3959_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3966_; 
if (v_isShared_3964_ == 0)
{
v___x_3966_ = v___x_3963_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_fst_3960_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_snd_3961_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile___redArg(lean_object* v_p_3969_, lean_object* v_as_3970_){
_start:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
v___x_3971_ = lean_unsigned_to_nat(0u);
v___x_3972_ = lean_array_get_size(v_as_3970_);
v___x_3973_ = lean_nat_dec_lt(v___x_3971_, v___x_3972_);
if (v___x_3973_ == 0)
{
lean_dec_ref(v_p_3969_);
return v_as_3970_;
}
else
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; 
v___x_3974_ = lean_unsigned_to_nat(1u);
v___x_3975_ = lean_nat_sub(v___x_3972_, v___x_3974_);
v___x_3976_ = lean_array_fget_borrowed(v_as_3970_, v___x_3975_);
lean_dec(v___x_3975_);
lean_inc_ref(v_p_3969_);
lean_inc(v___x_3976_);
v___x_3977_ = lean_apply_1(v_p_3969_, v___x_3976_);
v___x_3978_ = lean_unbox(v___x_3977_);
if (v___x_3978_ == 0)
{
lean_dec_ref(v_p_3969_);
return v_as_3970_;
}
else
{
lean_object* v___x_3979_; 
v___x_3979_ = lean_array_pop(v_as_3970_);
v_as_3970_ = v___x_3979_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile(lean_object* v_00_u03b1_3981_, lean_object* v_p_3982_, lean_object* v_as_3983_){
_start:
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Array_popWhile___redArg(v_p_3982_, v_as_3983_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(lean_object* v_p_3985_, lean_object* v_as_3986_, lean_object* v_i_3987_, lean_object* v_acc_3988_){
_start:
{
lean_object* v___x_3989_; uint8_t v___x_3990_; 
v___x_3989_ = lean_array_get_size(v_as_3986_);
v___x_3990_ = lean_nat_dec_lt(v_i_3987_, v___x_3989_);
if (v___x_3990_ == 0)
{
lean_dec(v_i_3987_);
lean_dec_ref(v_p_3985_);
return v_acc_3988_;
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3992_; uint8_t v___x_3993_; 
v_a_3991_ = lean_array_fget_borrowed(v_as_3986_, v_i_3987_);
lean_inc_ref(v_p_3985_);
lean_inc(v_a_3991_);
v___x_3992_ = lean_apply_1(v_p_3985_, v_a_3991_);
v___x_3993_ = lean_unbox(v___x_3992_);
if (v___x_3993_ == 0)
{
lean_dec(v_i_3987_);
lean_dec_ref(v_p_3985_);
return v_acc_3988_;
}
else
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3994_ = lean_unsigned_to_nat(1u);
v___x_3995_ = lean_nat_add(v_i_3987_, v___x_3994_);
lean_dec(v_i_3987_);
lean_inc(v_a_3991_);
v___x_3996_ = lean_array_push(v_acc_3988_, v_a_3991_);
v_i_3987_ = v___x_3995_;
v_acc_3988_ = v___x_3996_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg___boxed(lean_object* v_p_3998_, lean_object* v_as_3999_, lean_object* v_i_4000_, lean_object* v_acc_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_3998_, v_as_3999_, v_i_4000_, v_acc_4001_);
lean_dec_ref(v_as_3999_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(lean_object* v_00_u03b1_4003_, lean_object* v_p_4004_, lean_object* v_as_4005_, lean_object* v_i_4006_, lean_object* v_acc_4007_){
_start:
{
lean_object* v___x_4008_; 
v___x_4008_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4004_, v_as_4005_, v_i_4006_, v_acc_4007_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___boxed(lean_object* v_00_u03b1_4009_, lean_object* v_p_4010_, lean_object* v_as_4011_, lean_object* v_i_4012_, lean_object* v_acc_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go(v_00_u03b1_4009_, v_p_4010_, v_as_4011_, v_i_4012_, v_acc_4013_);
lean_dec_ref(v_as_4011_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg(lean_object* v_p_4015_, lean_object* v_as_4016_){
_start:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4017_ = lean_unsigned_to_nat(0u);
v___x_4018_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4019_ = l___private_Init_Data_Array_Basic_0__Array_takeWhile_go___redArg(v_p_4015_, v_as_4016_, v___x_4017_, v___x_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___redArg___boxed(lean_object* v_p_4020_, lean_object* v_as_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Array_takeWhile___redArg(v_p_4020_, v_as_4021_);
lean_dec_ref(v_as_4021_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile(lean_object* v_00_u03b1_4023_, lean_object* v_p_4024_, lean_object* v_as_4025_){
_start:
{
lean_object* v___x_4026_; 
v___x_4026_ = l_Array_takeWhile___redArg(v_p_4024_, v_as_4025_);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___boxed(lean_object* v_00_u03b1_4027_, lean_object* v_p_4028_, lean_object* v_as_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_Array_takeWhile(v_00_u03b1_4027_, v_p_4028_, v_as_4029_);
lean_dec_ref(v_as_4029_);
return v_res_4030_;
}
}
static lean_object* _init_l_Array_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_4031_; 
v___x_4031_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4031_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx___redArg(lean_object* v_xs_4032_, lean_object* v_i_4033_){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; uint8_t v___x_4037_; 
v___x_4034_ = lean_unsigned_to_nat(1u);
v___x_4035_ = lean_nat_add(v_i_4033_, v___x_4034_);
v___x_4036_ = lean_array_get_size(v_xs_4032_);
v___x_4037_ = lean_nat_dec_lt(v___x_4035_, v___x_4036_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4038_; 
lean_dec(v___x_4035_);
lean_dec(v_i_4033_);
v___x_4038_ = lean_array_pop(v_xs_4032_);
return v___x_4038_;
}
else
{
lean_object* v_xs_x27_4039_; 
v_xs_x27_4039_ = lean_array_fswap(v_xs_4032_, v___x_4035_, v_i_4033_);
lean_dec(v_i_4033_);
v_xs_4032_ = v_xs_x27_4039_;
v_i_4033_ = v___x_4035_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx(lean_object* v_00_u03b1_4041_, lean_object* v_xs_4042_, lean_object* v_i_4043_, lean_object* v_h_4044_){
_start:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Array_eraseIdx___redArg(v_xs_4042_, v_i_4043_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds___redArg(lean_object* v_xs_4046_, lean_object* v_i_4047_){
_start:
{
lean_object* v___x_4048_; uint8_t v___x_4049_; 
v___x_4048_ = lean_array_get_size(v_xs_4046_);
v___x_4049_ = lean_nat_dec_lt(v_i_4047_, v___x_4048_);
if (v___x_4049_ == 0)
{
lean_dec(v_i_4047_);
return v_xs_4046_;
}
else
{
lean_object* v___x_4050_; 
v___x_4050_ = l_Array_eraseIdx___redArg(v_xs_4046_, v_i_4047_);
return v___x_4050_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds(lean_object* v_00_u03b1_4051_, lean_object* v_xs_4052_, lean_object* v_i_4053_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Array_eraseIdxIfInBounds___redArg(v_xs_4052_, v_i_4053_);
return v___x_4054_;
}
}
static lean_object* _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = l_Array_instInhabited(lean_box(0));
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(lean_object* v_msg_4056_){
_start:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4057_ = lean_obj_once(&l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0, &l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0_once, _init_l_panic___at___00Array_eraseIdx_x21_spec__0___redArg___closed__0);
v___x_4058_ = lean_panic_fn(v___x_4057_, v_msg_4056_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Array_eraseIdx_x21_spec__0(lean_object* v_00_u03b1_4059_, lean_object* v_msg_4060_){
_start:
{
lean_object* v___x_4061_; 
v___x_4061_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v_msg_4060_);
return v___x_4061_;
}
}
static lean_object* _init_l_Array_eraseIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4064_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4065_ = lean_unsigned_to_nat(47u);
v___x_4066_ = lean_unsigned_to_nat(1808u);
v___x_4067_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__0));
v___x_4068_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4069_ = l_mkPanicMessageWithDecl(v___x_4068_, v___x_4067_, v___x_4066_, v___x_4065_, v___x_4064_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21___redArg(lean_object* v_xs_4070_, lean_object* v_i_4071_){
_start:
{
lean_object* v___x_4072_; uint8_t v___x_4073_; 
v___x_4072_ = lean_array_get_size(v_xs_4070_);
v___x_4073_ = lean_nat_dec_lt(v_i_4071_, v___x_4072_);
if (v___x_4073_ == 0)
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
lean_dec(v_i_4071_);
lean_dec_ref(v_xs_4070_);
v___x_4074_ = lean_obj_once(&l_Array_eraseIdx_x21___redArg___closed__2, &l_Array_eraseIdx_x21___redArg___closed__2_once, _init_l_Array_eraseIdx_x21___redArg___closed__2);
v___x_4075_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4074_);
return v___x_4075_;
}
else
{
lean_object* v___x_4076_; 
v___x_4076_ = l_Array_eraseIdx___redArg(v_xs_4070_, v_i_4071_);
return v___x_4076_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21(lean_object* v_00_u03b1_4077_, lean_object* v_xs_4078_, lean_object* v_i_4079_){
_start:
{
lean_object* v___x_4080_; 
v___x_4080_ = l_Array_eraseIdx_x21___redArg(v_xs_4078_, v_i_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Array_erase___redArg(lean_object* v_inst_4081_, lean_object* v_as_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Array_finIdxOf_x3f___redArg(v_inst_4081_, v_as_4082_, v_a_4083_);
if (lean_obj_tag(v___x_4084_) == 0)
{
return v_as_4082_;
}
else
{
lean_object* v_val_4085_; lean_object* v___x_4086_; 
v_val_4085_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_val_4085_);
lean_dec_ref(v___x_4084_);
v___x_4086_ = l_Array_eraseIdx___redArg(v_as_4082_, v_val_4085_);
return v___x_4086_;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase(lean_object* v_00_u03b1_4087_, lean_object* v_inst_4088_, lean_object* v_as_4089_, lean_object* v_a_4090_){
_start:
{
lean_object* v___x_4091_; 
v___x_4091_ = l_Array_erase___redArg(v_inst_4088_, v_as_4089_, v_a_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseP___redArg(lean_object* v_as_4092_, lean_object* v_p_4093_){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = lean_unsigned_to_nat(0u);
v___x_4095_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop___redArg(v_p_4093_, v_as_4092_, v___x_4094_);
if (lean_obj_tag(v___x_4095_) == 0)
{
return v_as_4092_;
}
else
{
lean_object* v_val_4096_; lean_object* v___x_4097_; 
v_val_4096_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_val_4096_);
lean_dec_ref(v___x_4095_);
v___x_4097_ = l_Array_eraseIdx___redArg(v_as_4092_, v_val_4096_);
return v___x_4097_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseP(lean_object* v_00_u03b1_4098_, lean_object* v_as_4099_, lean_object* v_p_4100_){
_start:
{
lean_object* v___x_4101_; 
v___x_4101_ = l_Array_eraseP___redArg(v_as_4099_, v_p_4100_);
return v___x_4101_;
}
}
static lean_object* _init_l_Array_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = lean_obj_once(&l_Array_swap___auto__1___closed__17, &l_Array_swap___auto__1___closed__17_once, _init_l_Array_swap___auto__1___closed__17);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(lean_object* v_i_4103_, lean_object* v_as_4104_, lean_object* v_j_4105_){
_start:
{
uint8_t v___x_4106_; 
v___x_4106_ = lean_nat_dec_lt(v_i_4103_, v_j_4105_);
if (v___x_4106_ == 0)
{
lean_dec(v_j_4105_);
return v_as_4104_;
}
else
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v_as_4109_; 
v___x_4107_ = lean_unsigned_to_nat(1u);
v___x_4108_ = lean_nat_sub(v_j_4105_, v___x_4107_);
v_as_4109_ = lean_array_fswap(v_as_4104_, v___x_4108_, v_j_4105_);
lean_dec(v_j_4105_);
v_as_4104_ = v_as_4109_;
v_j_4105_ = v___x_4108_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg___boxed(lean_object* v_i_4111_, lean_object* v_as_4112_, lean_object* v_j_4113_){
_start:
{
lean_object* v_res_4114_; 
v_res_4114_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4111_, v_as_4112_, v_j_4113_);
lean_dec(v_i_4111_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object* v_00_u03b1_4115_, lean_object* v_i_4116_, lean_object* v_as_4117_, lean_object* v_j_4118_){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4116_, v_as_4117_, v_j_4118_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___boxed(lean_object* v_00_u03b1_4120_, lean_object* v_i_4121_, lean_object* v_as_4122_, lean_object* v_j_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(v_00_u03b1_4120_, v_i_4121_, v_as_4122_, v_j_4123_);
lean_dec(v_i_4121_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg(lean_object* v_as_4125_, lean_object* v_i_4126_, lean_object* v_a_4127_){
_start:
{
lean_object* v_j_4128_; lean_object* v_as_4129_; lean_object* v___x_4130_; 
v_j_4128_ = lean_array_get_size(v_as_4125_);
v_as_4129_ = lean_array_push(v_as_4125_, v_a_4127_);
v___x_4130_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4126_, v_as_4129_, v_j_4128_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___redArg___boxed(lean_object* v_as_4131_, lean_object* v_i_4132_, lean_object* v_a_4133_){
_start:
{
lean_object* v_res_4134_; 
v_res_4134_ = l_Array_insertIdx___redArg(v_as_4131_, v_i_4132_, v_a_4133_);
lean_dec(v_i_4132_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx(lean_object* v_00_u03b1_4135_, lean_object* v_as_4136_, lean_object* v_i_4137_, lean_object* v_a_4138_, lean_object* v_x_4139_){
_start:
{
lean_object* v_j_4140_; lean_object* v_as_4141_; lean_object* v___x_4142_; 
v_j_4140_ = lean_array_get_size(v_as_4136_);
v_as_4141_ = lean_array_push(v_as_4136_, v_a_4138_);
v___x_4142_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4137_, v_as_4141_, v_j_4140_);
return v___x_4142_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___boxed(lean_object* v_00_u03b1_4143_, lean_object* v_as_4144_, lean_object* v_i_4145_, lean_object* v_a_4146_, lean_object* v_x_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Array_insertIdx(v_00_u03b1_4143_, v_as_4144_, v_i_4145_, v_a_4146_, v_x_4147_);
lean_dec(v_i_4145_);
return v_res_4148_;
}
}
static lean_object* _init_l_Array_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4150_ = ((lean_object*)(l_Array_eraseIdx_x21___redArg___closed__1));
v___x_4151_ = lean_unsigned_to_nat(7u);
v___x_4152_ = lean_unsigned_to_nat(1890u);
v___x_4153_ = ((lean_object*)(l_Array_insertIdx_x21___redArg___closed__0));
v___x_4154_ = ((lean_object*)(l_Array_swapAt_x21___redArg___closed__0));
v___x_4155_ = l_mkPanicMessageWithDecl(v___x_4154_, v___x_4153_, v___x_4152_, v___x_4151_, v___x_4150_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg(lean_object* v_as_4156_, lean_object* v_i_4157_, lean_object* v_a_4158_){
_start:
{
lean_object* v___x_4159_; uint8_t v___x_4160_; 
v___x_4159_ = lean_array_get_size(v_as_4156_);
v___x_4160_ = lean_nat_dec_le(v_i_4157_, v___x_4159_);
if (v___x_4160_ == 0)
{
lean_object* v___x_4161_; lean_object* v___x_4162_; 
lean_dec(v_a_4158_);
lean_dec_ref(v_as_4156_);
v___x_4161_ = lean_obj_once(&l_Array_insertIdx_x21___redArg___closed__1, &l_Array_insertIdx_x21___redArg___closed__1_once, _init_l_Array_insertIdx_x21___redArg___closed__1);
v___x_4162_ = l_panic___at___00Array_eraseIdx_x21_spec__0___redArg(v___x_4161_);
return v___x_4162_;
}
else
{
lean_object* v_as_4163_; lean_object* v___x_4164_; 
v_as_4163_ = lean_array_push(v_as_4156_, v_a_4158_);
v___x_4164_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4157_, v_as_4163_, v___x_4159_);
return v___x_4164_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___redArg___boxed(lean_object* v_as_4165_, lean_object* v_i_4166_, lean_object* v_a_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Array_insertIdx_x21___redArg(v_as_4165_, v_i_4166_, v_a_4167_);
lean_dec(v_i_4166_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21(lean_object* v_00_u03b1_4169_, lean_object* v_as_4170_, lean_object* v_i_4171_, lean_object* v_a_4172_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l_Array_insertIdx_x21___redArg(v_as_4170_, v_i_4171_, v_a_4172_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___boxed(lean_object* v_00_u03b1_4174_, lean_object* v_as_4175_, lean_object* v_i_4176_, lean_object* v_a_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Array_insertIdx_x21(v_00_u03b1_4174_, v_as_4175_, v_i_4176_, v_a_4177_);
lean_dec(v_i_4176_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg(lean_object* v_as_4179_, lean_object* v_i_4180_, lean_object* v_a_4181_){
_start:
{
lean_object* v___x_4182_; uint8_t v___x_4183_; 
v___x_4182_ = lean_array_get_size(v_as_4179_);
v___x_4183_ = lean_nat_dec_le(v_i_4180_, v___x_4182_);
if (v___x_4183_ == 0)
{
lean_dec(v_a_4181_);
return v_as_4179_;
}
else
{
lean_object* v_as_4184_; lean_object* v___x_4185_; 
v_as_4184_ = lean_array_push(v_as_4179_, v_a_4181_);
v___x_4185_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop___redArg(v_i_4180_, v_as_4184_, v___x_4182_);
return v___x_4185_;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___redArg___boxed(lean_object* v_as_4186_, lean_object* v_i_4187_, lean_object* v_a_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Array_insertIdxIfInBounds___redArg(v_as_4186_, v_i_4187_, v_a_4188_);
lean_dec(v_i_4187_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds(lean_object* v_00_u03b1_4190_, lean_object* v_as_4191_, lean_object* v_i_4192_, lean_object* v_a_4193_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l_Array_insertIdxIfInBounds___redArg(v_as_4191_, v_i_4192_, v_a_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___boxed(lean_object* v_00_u03b1_4195_, lean_object* v_as_4196_, lean_object* v_i_4197_, lean_object* v_a_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l_Array_insertIdxIfInBounds(v_00_u03b1_4195_, v_as_4196_, v_i_4197_, v_a_4198_);
lean_dec(v_i_4197_);
return v_res_4199_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux___redArg(lean_object* v_inst_4200_, lean_object* v_as_4201_, lean_object* v_bs_4202_, lean_object* v_i_4203_){
_start:
{
lean_object* v___x_4204_; uint8_t v___x_4205_; 
v___x_4204_ = lean_array_get_size(v_as_4201_);
v___x_4205_ = lean_nat_dec_lt(v_i_4203_, v___x_4204_);
if (v___x_4205_ == 0)
{
uint8_t v___x_4206_; 
lean_dec(v_i_4203_);
lean_dec_ref(v_inst_4200_);
v___x_4206_ = 1;
return v___x_4206_;
}
else
{
lean_object* v_a_4207_; lean_object* v_b_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; 
v_a_4207_ = lean_array_fget_borrowed(v_as_4201_, v_i_4203_);
v_b_4208_ = lean_array_fget_borrowed(v_bs_4202_, v_i_4203_);
lean_inc_ref(v_inst_4200_);
lean_inc(v_b_4208_);
lean_inc(v_a_4207_);
v___x_4209_ = lean_apply_2(v_inst_4200_, v_a_4207_, v_b_4208_);
v___x_4210_ = lean_unbox(v___x_4209_);
if (v___x_4210_ == 0)
{
uint8_t v___x_4211_; 
lean_dec(v_i_4203_);
lean_dec_ref(v_inst_4200_);
v___x_4211_ = lean_unbox(v___x_4209_);
return v___x_4211_;
}
else
{
lean_object* v___x_4212_; lean_object* v___x_4213_; 
v___x_4212_ = lean_unsigned_to_nat(1u);
v___x_4213_ = lean_nat_add(v_i_4203_, v___x_4212_);
lean_dec(v_i_4203_);
v_i_4203_ = v___x_4213_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___redArg___boxed(lean_object* v_inst_4215_, lean_object* v_as_4216_, lean_object* v_bs_4217_, lean_object* v_i_4218_){
_start:
{
uint8_t v_res_4219_; lean_object* v_r_4220_; 
v_res_4219_ = l_Array_isPrefixOfAux___redArg(v_inst_4215_, v_as_4216_, v_bs_4217_, v_i_4218_);
lean_dec_ref(v_bs_4217_);
lean_dec_ref(v_as_4216_);
v_r_4220_ = lean_box(v_res_4219_);
return v_r_4220_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux(lean_object* v_00_u03b1_4221_, lean_object* v_inst_4222_, lean_object* v_as_4223_, lean_object* v_bs_4224_, lean_object* v_hle_4225_, lean_object* v_i_4226_){
_start:
{
uint8_t v___x_4227_; 
v___x_4227_ = l_Array_isPrefixOfAux___redArg(v_inst_4222_, v_as_4223_, v_bs_4224_, v_i_4226_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___boxed(lean_object* v_00_u03b1_4228_, lean_object* v_inst_4229_, lean_object* v_as_4230_, lean_object* v_bs_4231_, lean_object* v_hle_4232_, lean_object* v_i_4233_){
_start:
{
uint8_t v_res_4234_; lean_object* v_r_4235_; 
v_res_4234_ = l_Array_isPrefixOfAux(v_00_u03b1_4228_, v_inst_4229_, v_as_4230_, v_bs_4231_, v_hle_4232_, v_i_4233_);
lean_dec_ref(v_bs_4231_);
lean_dec_ref(v_as_4230_);
v_r_4235_ = lean_box(v_res_4234_);
return v_r_4235_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf___redArg(lean_object* v_inst_4236_, lean_object* v_as_4237_, lean_object* v_bs_4238_){
_start:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; uint8_t v___x_4241_; 
v___x_4239_ = lean_array_get_size(v_as_4237_);
v___x_4240_ = lean_array_get_size(v_bs_4238_);
v___x_4241_ = lean_nat_dec_le(v___x_4239_, v___x_4240_);
if (v___x_4241_ == 0)
{
lean_dec_ref(v_inst_4236_);
return v___x_4241_;
}
else
{
lean_object* v___x_4242_; uint8_t v___x_4243_; 
v___x_4242_ = lean_unsigned_to_nat(0u);
v___x_4243_ = l_Array_isPrefixOfAux___redArg(v_inst_4236_, v_as_4237_, v_bs_4238_, v___x_4242_);
return v___x_4243_;
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___redArg___boxed(lean_object* v_inst_4244_, lean_object* v_as_4245_, lean_object* v_bs_4246_){
_start:
{
uint8_t v_res_4247_; lean_object* v_r_4248_; 
v_res_4247_ = l_Array_isPrefixOf___redArg(v_inst_4244_, v_as_4245_, v_bs_4246_);
lean_dec_ref(v_bs_4246_);
lean_dec_ref(v_as_4245_);
v_r_4248_ = lean_box(v_res_4247_);
return v_r_4248_;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf(lean_object* v_00_u03b1_4249_, lean_object* v_inst_4250_, lean_object* v_as_4251_, lean_object* v_bs_4252_){
_start:
{
uint8_t v___x_4253_; 
v___x_4253_ = l_Array_isPrefixOf___redArg(v_inst_4250_, v_as_4251_, v_bs_4252_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___boxed(lean_object* v_00_u03b1_4254_, lean_object* v_inst_4255_, lean_object* v_as_4256_, lean_object* v_bs_4257_){
_start:
{
uint8_t v_res_4258_; lean_object* v_r_4259_; 
v_res_4258_ = l_Array_isPrefixOf(v_00_u03b1_4254_, v_inst_4255_, v_as_4256_, v_bs_4257_);
lean_dec_ref(v_bs_4257_);
lean_dec_ref(v_as_4256_);
v_r_4259_ = lean_box(v_res_4258_);
return v_r_4259_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0___boxed(lean_object* v_i_4260_, lean_object* v_cs_4261_, lean_object* v_inst_4262_, lean_object* v_as_4263_, lean_object* v_bs_4264_, lean_object* v_f_4265_, lean_object* v_____do__lift_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l_Array_zipWithMAux___redArg___lam__0(v_i_4260_, v_cs_4261_, v_inst_4262_, v_as_4263_, v_bs_4264_, v_f_4265_, v_____do__lift_4266_);
lean_dec(v_i_4260_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg(lean_object* v_inst_4268_, lean_object* v_as_4269_, lean_object* v_bs_4270_, lean_object* v_f_4271_, lean_object* v_i_4272_, lean_object* v_cs_4273_){
_start:
{
lean_object* v___x_4274_; uint8_t v___x_4275_; 
v___x_4274_ = lean_array_get_size(v_as_4269_);
v___x_4275_ = lean_nat_dec_lt(v_i_4272_, v___x_4274_);
if (v___x_4275_ == 0)
{
lean_object* v_toApplicative_4276_; lean_object* v_toPure_4277_; lean_object* v___x_4278_; 
lean_dec(v_i_4272_);
lean_dec(v_f_4271_);
lean_dec_ref(v_bs_4270_);
lean_dec_ref(v_as_4269_);
v_toApplicative_4276_ = lean_ctor_get(v_inst_4268_, 0);
lean_inc_ref(v_toApplicative_4276_);
lean_dec_ref(v_inst_4268_);
v_toPure_4277_ = lean_ctor_get(v_toApplicative_4276_, 1);
lean_inc(v_toPure_4277_);
lean_dec_ref(v_toApplicative_4276_);
v___x_4278_ = lean_apply_2(v_toPure_4277_, lean_box(0), v_cs_4273_);
return v___x_4278_;
}
else
{
lean_object* v___x_4279_; uint8_t v___x_4280_; 
v___x_4279_ = lean_array_get_size(v_bs_4270_);
v___x_4280_ = lean_nat_dec_lt(v_i_4272_, v___x_4279_);
if (v___x_4280_ == 0)
{
lean_object* v_toApplicative_4281_; lean_object* v_toPure_4282_; lean_object* v___x_4283_; 
lean_dec(v_i_4272_);
lean_dec(v_f_4271_);
lean_dec_ref(v_bs_4270_);
lean_dec_ref(v_as_4269_);
v_toApplicative_4281_ = lean_ctor_get(v_inst_4268_, 0);
lean_inc_ref(v_toApplicative_4281_);
lean_dec_ref(v_inst_4268_);
v_toPure_4282_ = lean_ctor_get(v_toApplicative_4281_, 1);
lean_inc(v_toPure_4282_);
lean_dec_ref(v_toApplicative_4281_);
v___x_4283_ = lean_apply_2(v_toPure_4282_, lean_box(0), v_cs_4273_);
return v___x_4283_;
}
else
{
lean_object* v_toBind_4284_; lean_object* v___f_4285_; lean_object* v_a_4286_; lean_object* v_b_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v_toBind_4284_ = lean_ctor_get(v_inst_4268_, 1);
lean_inc(v_toBind_4284_);
lean_inc(v_f_4271_);
lean_inc_ref(v_bs_4270_);
lean_inc_ref(v_as_4269_);
lean_inc(v_i_4272_);
v___f_4285_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4285_, 0, v_i_4272_);
lean_closure_set(v___f_4285_, 1, v_cs_4273_);
lean_closure_set(v___f_4285_, 2, v_inst_4268_);
lean_closure_set(v___f_4285_, 3, v_as_4269_);
lean_closure_set(v___f_4285_, 4, v_bs_4270_);
lean_closure_set(v___f_4285_, 5, v_f_4271_);
v_a_4286_ = lean_array_fget(v_as_4269_, v_i_4272_);
lean_dec_ref(v_as_4269_);
v_b_4287_ = lean_array_fget(v_bs_4270_, v_i_4272_);
lean_dec(v_i_4272_);
lean_dec_ref(v_bs_4270_);
v___x_4288_ = lean_apply_2(v_f_4271_, v_a_4286_, v_b_4287_);
v___x_4289_ = lean_apply_4(v_toBind_4284_, lean_box(0), lean_box(0), v___x_4288_, v___f_4285_);
return v___x_4289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___redArg___lam__0(lean_object* v_i_4290_, lean_object* v_cs_4291_, lean_object* v_inst_4292_, lean_object* v_as_4293_, lean_object* v_bs_4294_, lean_object* v_f_4295_, lean_object* v_____do__lift_4296_){
_start:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4297_ = lean_unsigned_to_nat(1u);
v___x_4298_ = lean_nat_add(v_i_4290_, v___x_4297_);
v___x_4299_ = lean_array_push(v_cs_4291_, v_____do__lift_4296_);
v___x_4300_ = l_Array_zipWithMAux___redArg(v_inst_4292_, v_as_4293_, v_bs_4294_, v_f_4295_, v___x_4298_, v___x_4299_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux(lean_object* v_00_u03b1_4301_, lean_object* v_00_u03b2_4302_, lean_object* v_00_u03b3_4303_, lean_object* v_m_4304_, lean_object* v_inst_4305_, lean_object* v_as_4306_, lean_object* v_bs_4307_, lean_object* v_f_4308_, lean_object* v_i_4309_, lean_object* v_cs_4310_){
_start:
{
lean_object* v___x_4311_; 
v___x_4311_ = l_Array_zipWithMAux___redArg(v_inst_4305_, v_as_4306_, v_bs_4307_, v_f_4308_, v_i_4309_, v_cs_4310_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith___redArg(lean_object* v_f_4312_, lean_object* v_as_4313_, lean_object* v_bs_4314_){
_start:
{
lean_object* v___f_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___f_4315_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4315_, 0, v_f_4312_);
v___x_4316_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4317_ = lean_unsigned_to_nat(0u);
v___x_4318_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4319_ = l_Array_zipWithMAux___redArg(v___x_4316_, v_as_4313_, v_bs_4314_, v___f_4315_, v___x_4317_, v___x_4318_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith(lean_object* v_00_u03b1_4320_, lean_object* v_00_u03b2_4321_, lean_object* v_00_u03b3_4322_, lean_object* v_f_4323_, lean_object* v_as_4324_, lean_object* v_bs_4325_){
_start:
{
lean_object* v___f_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___f_4326_ = lean_alloc_closure((void*)(l_Array_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4326_, 0, v_f_4323_);
v___x_4327_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4328_ = lean_unsigned_to_nat(0u);
v___x_4329_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4330_ = l_Array_zipWithMAux___redArg(v___x_4327_, v_as_4324_, v_bs_4325_, v___f_4326_, v___x_4328_, v___x_4329_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(lean_object* v_as_4331_, lean_object* v_bs_4332_, lean_object* v_i_4333_, lean_object* v_cs_4334_){
_start:
{
lean_object* v___x_4335_; uint8_t v___x_4336_; 
v___x_4335_ = lean_array_get_size(v_as_4331_);
v___x_4336_ = lean_nat_dec_lt(v_i_4333_, v___x_4335_);
if (v___x_4336_ == 0)
{
lean_dec(v_i_4333_);
return v_cs_4334_;
}
else
{
lean_object* v___x_4337_; uint8_t v___x_4338_; 
v___x_4337_ = lean_array_get_size(v_bs_4332_);
v___x_4338_ = lean_nat_dec_lt(v_i_4333_, v___x_4337_);
if (v___x_4338_ == 0)
{
lean_dec(v_i_4333_);
return v_cs_4334_;
}
else
{
lean_object* v_a_4339_; lean_object* v_b_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v_a_4339_ = lean_array_fget_borrowed(v_as_4331_, v_i_4333_);
v_b_4340_ = lean_array_fget_borrowed(v_bs_4332_, v_i_4333_);
lean_inc(v_b_4340_);
lean_inc(v_a_4339_);
v___x_4341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4341_, 0, v_a_4339_);
lean_ctor_set(v___x_4341_, 1, v_b_4340_);
v___x_4342_ = lean_unsigned_to_nat(1u);
v___x_4343_ = lean_nat_add(v_i_4333_, v___x_4342_);
lean_dec(v_i_4333_);
v___x_4344_ = lean_array_push(v_cs_4334_, v___x_4341_);
v_i_4333_ = v___x_4343_;
v_cs_4334_ = v___x_4344_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg___boxed(lean_object* v_as_4346_, lean_object* v_bs_4347_, lean_object* v_i_4348_, lean_object* v_cs_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4346_, v_bs_4347_, v_i_4348_, v_cs_4349_);
lean_dec_ref(v_bs_4347_);
lean_dec_ref(v_as_4346_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg(lean_object* v_as_4353_, lean_object* v_bs_4354_){
_start:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4355_ = lean_unsigned_to_nat(0u);
v___x_4356_ = ((lean_object*)(l_Array_zip___redArg___closed__0));
v___x_4357_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4353_, v_bs_4354_, v___x_4355_, v___x_4356_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___redArg___boxed(lean_object* v_as_4358_, lean_object* v_bs_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = l_Array_zip___redArg(v_as_4358_, v_bs_4359_);
lean_dec_ref(v_bs_4359_);
lean_dec_ref(v_as_4358_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l_Array_zip(lean_object* v_00_u03b1_4361_, lean_object* v_00_u03b2_4362_, lean_object* v_as_4363_, lean_object* v_bs_4364_){
_start:
{
lean_object* v___x_4365_; 
v___x_4365_ = l_Array_zip___redArg(v_as_4363_, v_bs_4364_);
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l_Array_zip___boxed(lean_object* v_00_u03b1_4366_, lean_object* v_00_u03b2_4367_, lean_object* v_as_4368_, lean_object* v_bs_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Array_zip(v_00_u03b1_4366_, v_00_u03b2_4367_, v_as_4368_, v_bs_4369_);
lean_dec_ref(v_bs_4369_);
lean_dec_ref(v_as_4368_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0(lean_object* v_00_u03b1_4371_, lean_object* v_00_u03b2_4372_, lean_object* v_as_4373_, lean_object* v_bs_4374_, lean_object* v_i_4375_, lean_object* v_cs_4376_){
_start:
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Array_zipWithMAux___at___00Array_zip_spec__0___redArg(v_as_4373_, v_bs_4374_, v_i_4375_, v_cs_4376_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Array_zip_spec__0___boxed(lean_object* v_00_u03b1_4378_, lean_object* v_00_u03b2_4379_, lean_object* v_as_4380_, lean_object* v_bs_4381_, lean_object* v_i_4382_, lean_object* v_cs_4383_){
_start:
{
lean_object* v_res_4384_; 
v_res_4384_ = l_Array_zipWithMAux___at___00Array_zip_spec__0(v_00_u03b1_4378_, v_00_u03b2_4379_, v_as_4380_, v_bs_4381_, v_i_4382_, v_cs_4383_);
lean_dec_ref(v_bs_4381_);
lean_dec_ref(v_as_4380_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(lean_object* v_f_4385_, lean_object* v_as_4386_, lean_object* v_bs_4387_, lean_object* v_i_4388_, lean_object* v_cs_4389_){
_start:
{
lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4399_; lean_object* v___y_4406_; lean_object* v___x_4413_; lean_object* v___x_4414_; uint8_t v___x_4415_; 
v___x_4413_ = lean_array_get_size(v_as_4386_);
v___x_4414_ = lean_array_get_size(v_bs_4387_);
v___x_4415_ = lean_nat_dec_le(v___x_4413_, v___x_4414_);
if (v___x_4415_ == 0)
{
v___y_4406_ = v___x_4413_;
goto v___jp_4405_;
}
else
{
v___y_4406_ = v___x_4414_;
goto v___jp_4405_;
}
v___jp_4390_:
{
lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4393_ = lean_unsigned_to_nat(1u);
v___x_4394_ = lean_nat_add(v_i_4388_, v___x_4393_);
lean_dec(v_i_4388_);
lean_inc(v_f_4385_);
v___x_4395_ = lean_apply_2(v_f_4385_, v___y_4391_, v___y_4392_);
v___x_4396_ = lean_array_push(v_cs_4389_, v___x_4395_);
v_i_4388_ = v___x_4394_;
v_cs_4389_ = v___x_4396_;
goto _start;
}
v___jp_4398_:
{
lean_object* v___x_4400_; uint8_t v___x_4401_; 
v___x_4400_ = lean_array_get_size(v_bs_4387_);
v___x_4401_ = lean_nat_dec_lt(v_i_4388_, v___x_4400_);
if (v___x_4401_ == 0)
{
lean_object* v___x_4402_; 
v___x_4402_ = lean_box(0);
v___y_4391_ = v___y_4399_;
v___y_4392_ = v___x_4402_;
goto v___jp_4390_;
}
else
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = lean_array_fget_borrowed(v_bs_4387_, v_i_4388_);
lean_inc(v___x_4403_);
v___x_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
v___y_4391_ = v___y_4399_;
v___y_4392_ = v___x_4404_;
goto v___jp_4390_;
}
}
v___jp_4405_:
{
uint8_t v___x_4407_; 
v___x_4407_ = lean_nat_dec_lt(v_i_4388_, v___y_4406_);
lean_dec(v___y_4406_);
if (v___x_4407_ == 0)
{
lean_dec(v_i_4388_);
lean_dec(v_f_4385_);
return v_cs_4389_;
}
else
{
lean_object* v___x_4408_; uint8_t v___x_4409_; 
v___x_4408_ = lean_array_get_size(v_as_4386_);
v___x_4409_ = lean_nat_dec_lt(v_i_4388_, v___x_4408_);
if (v___x_4409_ == 0)
{
lean_object* v___x_4410_; 
v___x_4410_ = lean_box(0);
v___y_4399_ = v___x_4410_;
goto v___jp_4398_;
}
else
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4411_ = lean_array_fget_borrowed(v_as_4386_, v_i_4388_);
lean_inc(v___x_4411_);
v___x_4412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4411_);
v___y_4399_ = v___x_4412_;
goto v___jp_4398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg___boxed(lean_object* v_f_4416_, lean_object* v_as_4417_, lean_object* v_bs_4418_, lean_object* v_i_4419_, lean_object* v_cs_4420_){
_start:
{
lean_object* v_res_4421_; 
v_res_4421_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4416_, v_as_4417_, v_bs_4418_, v_i_4419_, v_cs_4420_);
lean_dec_ref(v_bs_4418_);
lean_dec_ref(v_as_4417_);
return v_res_4421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(lean_object* v_00_u03b1_4422_, lean_object* v_00_u03b2_4423_, lean_object* v_00_u03b3_4424_, lean_object* v_f_4425_, lean_object* v_as_4426_, lean_object* v_bs_4427_, lean_object* v_i_4428_, lean_object* v_cs_4429_){
_start:
{
lean_object* v___x_4430_; 
v___x_4430_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4425_, v_as_4426_, v_bs_4427_, v_i_4428_, v_cs_4429_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___boxed(lean_object* v_00_u03b1_4431_, lean_object* v_00_u03b2_4432_, lean_object* v_00_u03b3_4433_, lean_object* v_f_4434_, lean_object* v_as_4435_, lean_object* v_bs_4436_, lean_object* v_i_4437_, lean_object* v_cs_4438_){
_start:
{
lean_object* v_res_4439_; 
v_res_4439_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go(v_00_u03b1_4431_, v_00_u03b2_4432_, v_00_u03b3_4433_, v_f_4434_, v_as_4435_, v_bs_4436_, v_i_4437_, v_cs_4438_);
lean_dec_ref(v_bs_4436_);
lean_dec_ref(v_as_4435_);
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg(lean_object* v_f_4440_, lean_object* v_as_4441_, lean_object* v_bs_4442_){
_start:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4443_ = lean_unsigned_to_nat(0u);
v___x_4444_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4445_ = l___private_Init_Data_Array_Basic_0__Array_zipWithAll_go___redArg(v_f_4440_, v_as_4441_, v_bs_4442_, v___x_4443_, v___x_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___redArg___boxed(lean_object* v_f_4446_, lean_object* v_as_4447_, lean_object* v_bs_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l_Array_zipWithAll___redArg(v_f_4446_, v_as_4447_, v_bs_4448_);
lean_dec_ref(v_bs_4448_);
lean_dec_ref(v_as_4447_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll(lean_object* v_00_u03b1_4450_, lean_object* v_00_u03b2_4451_, lean_object* v_00_u03b3_4452_, lean_object* v_f_4453_, lean_object* v_as_4454_, lean_object* v_bs_4455_){
_start:
{
lean_object* v___x_4456_; 
v___x_4456_ = l_Array_zipWithAll___redArg(v_f_4453_, v_as_4454_, v_bs_4455_);
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___boxed(lean_object* v_00_u03b1_4457_, lean_object* v_00_u03b2_4458_, lean_object* v_00_u03b3_4459_, lean_object* v_f_4460_, lean_object* v_as_4461_, lean_object* v_bs_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_Array_zipWithAll(v_00_u03b1_4457_, v_00_u03b2_4458_, v_00_u03b3_4459_, v_f_4460_, v_as_4461_, v_bs_4462_);
lean_dec_ref(v_bs_4462_);
lean_dec_ref(v_as_4461_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM___redArg(lean_object* v_inst_4464_, lean_object* v_f_4465_, lean_object* v_as_4466_, lean_object* v_bs_4467_){
_start:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4468_ = lean_unsigned_to_nat(0u);
v___x_4469_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4470_ = l_Array_zipWithMAux___redArg(v_inst_4464_, v_as_4466_, v_bs_4467_, v_f_4465_, v___x_4468_, v___x_4469_);
return v___x_4470_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithM(lean_object* v_00_u03b1_4471_, lean_object* v_00_u03b2_4472_, lean_object* v_00_u03b3_4473_, lean_object* v_m_4474_, lean_object* v_inst_4475_, lean_object* v_f_4476_, lean_object* v_as_4477_, lean_object* v_bs_4478_){
_start:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
v___x_4479_ = lean_unsigned_to_nat(0u);
v___x_4480_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4481_ = l_Array_zipWithMAux___redArg(v_inst_4475_, v_as_4477_, v_bs_4478_, v_f_4476_, v___x_4479_, v___x_4480_);
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(lean_object* v_as_4482_, size_t v_i_4483_, size_t v_stop_4484_, lean_object* v_b_4485_){
_start:
{
uint8_t v___x_4486_; 
v___x_4486_ = lean_usize_dec_eq(v_i_4483_, v_stop_4484_);
if (v___x_4486_ == 0)
{
lean_object* v_fst_4487_; lean_object* v_snd_4488_; lean_object* v___x_4489_; lean_object* v_fst_4490_; lean_object* v_snd_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4503_; 
v_fst_4487_ = lean_ctor_get(v_b_4485_, 0);
lean_inc(v_fst_4487_);
v_snd_4488_ = lean_ctor_get(v_b_4485_, 1);
lean_inc(v_snd_4488_);
lean_dec_ref(v_b_4485_);
v___x_4489_ = lean_array_uget(v_as_4482_, v_i_4483_);
v_fst_4490_ = lean_ctor_get(v___x_4489_, 0);
v_snd_4491_ = lean_ctor_get(v___x_4489_, 1);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4493_ = v___x_4489_;
v_isShared_4494_ = v_isSharedCheck_4503_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_snd_4491_);
lean_inc(v_fst_4490_);
lean_dec(v___x_4489_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4503_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4498_; 
v___x_4495_ = lean_array_push(v_fst_4487_, v_fst_4490_);
v___x_4496_ = lean_array_push(v_snd_4488_, v_snd_4491_);
if (v_isShared_4494_ == 0)
{
lean_ctor_set(v___x_4493_, 1, v___x_4496_);
lean_ctor_set(v___x_4493_, 0, v___x_4495_);
v___x_4498_ = v___x_4493_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v___x_4495_);
lean_ctor_set(v_reuseFailAlloc_4502_, 1, v___x_4496_);
v___x_4498_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
size_t v___x_4499_; size_t v___x_4500_; 
v___x_4499_ = ((size_t)1ULL);
v___x_4500_ = lean_usize_add(v_i_4483_, v___x_4499_);
v_i_4483_ = v___x_4500_;
v_b_4485_ = v___x_4498_;
goto _start;
}
}
}
else
{
return v_b_4485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg___boxed(lean_object* v_as_4504_, lean_object* v_i_4505_, lean_object* v_stop_4506_, lean_object* v_b_4507_){
_start:
{
size_t v_i_boxed_4508_; size_t v_stop_boxed_4509_; lean_object* v_res_4510_; 
v_i_boxed_4508_ = lean_unbox_usize(v_i_4505_);
lean_dec(v_i_4505_);
v_stop_boxed_4509_ = lean_unbox_usize(v_stop_4506_);
lean_dec(v_stop_4506_);
v_res_4510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4504_, v_i_boxed_4508_, v_stop_boxed_4509_, v_b_4507_);
lean_dec_ref(v_as_4504_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg(lean_object* v_as_4511_){
_start:
{
lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; uint8_t v___x_4515_; 
v___x_4512_ = lean_unsigned_to_nat(0u);
v___x_4513_ = lean_obj_once(&l_Array_partition___redArg___closed__0, &l_Array_partition___redArg___closed__0_once, _init_l_Array_partition___redArg___closed__0);
v___x_4514_ = lean_array_get_size(v_as_4511_);
v___x_4515_ = lean_nat_dec_lt(v___x_4512_, v___x_4514_);
if (v___x_4515_ == 0)
{
return v___x_4513_;
}
else
{
uint8_t v___x_4516_; 
v___x_4516_ = lean_nat_dec_le(v___x_4514_, v___x_4514_);
if (v___x_4516_ == 0)
{
if (v___x_4515_ == 0)
{
return v___x_4513_;
}
else
{
size_t v___x_4517_; size_t v___x_4518_; lean_object* v___x_4519_; 
v___x_4517_ = ((size_t)0ULL);
v___x_4518_ = lean_usize_of_nat(v___x_4514_);
v___x_4519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4511_, v___x_4517_, v___x_4518_, v___x_4513_);
return v___x_4519_;
}
}
else
{
size_t v___x_4520_; size_t v___x_4521_; lean_object* v___x_4522_; 
v___x_4520_ = ((size_t)0ULL);
v___x_4521_ = lean_usize_of_nat(v___x_4514_);
v___x_4522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4511_, v___x_4520_, v___x_4521_, v___x_4513_);
return v___x_4522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_unzip___redArg___boxed(lean_object* v_as_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Array_unzip___redArg(v_as_4523_);
lean_dec_ref(v_as_4523_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip(lean_object* v_00_u03b1_4525_, lean_object* v_00_u03b2_4526_, lean_object* v_as_4527_){
_start:
{
lean_object* v___x_4528_; 
v___x_4528_ = l_Array_unzip___redArg(v_as_4527_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___boxed(lean_object* v_00_u03b1_4529_, lean_object* v_00_u03b2_4530_, lean_object* v_as_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l_Array_unzip(v_00_u03b1_4529_, v_00_u03b2_4530_, v_as_4531_);
lean_dec_ref(v_as_4531_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(lean_object* v_00_u03b1_4533_, lean_object* v_00_u03b2_4534_, lean_object* v_as_4535_, size_t v_i_4536_, size_t v_stop_4537_, lean_object* v_b_4538_){
_start:
{
lean_object* v___x_4539_; 
v___x_4539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___redArg(v_as_4535_, v_i_4536_, v_stop_4537_, v_b_4538_);
return v___x_4539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0___boxed(lean_object* v_00_u03b1_4540_, lean_object* v_00_u03b2_4541_, lean_object* v_as_4542_, lean_object* v_i_4543_, lean_object* v_stop_4544_, lean_object* v_b_4545_){
_start:
{
size_t v_i_boxed_4546_; size_t v_stop_boxed_4547_; lean_object* v_res_4548_; 
v_i_boxed_4546_ = lean_unbox_usize(v_i_4543_);
lean_dec(v_i_4543_);
v_stop_boxed_4547_ = lean_unbox_usize(v_stop_4544_);
lean_dec(v_stop_4544_);
v_res_4548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_unzip_spec__0(v_00_u03b1_4540_, v_00_u03b2_4541_, v_as_4542_, v_i_boxed_4546_, v_stop_boxed_4547_, v_b_4545_);
lean_dec_ref(v_as_4542_);
return v_res_4548_;
}
}
LEAN_EXPORT lean_object* l_Array_replace___redArg(lean_object* v_inst_4549_, lean_object* v_xs_4550_, lean_object* v_a_4551_, lean_object* v_b_4552_){
_start:
{
lean_object* v___x_4553_; 
v___x_4553_ = l_Array_finIdxOf_x3f___redArg(v_inst_4549_, v_xs_4550_, v_a_4551_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_dec(v_b_4552_);
return v_xs_4550_;
}
else
{
lean_object* v_val_4554_; lean_object* v___x_4555_; 
v_val_4554_ = lean_ctor_get(v___x_4553_, 0);
lean_inc(v_val_4554_);
lean_dec_ref(v___x_4553_);
v___x_4555_ = lean_array_fset(v_xs_4550_, v_val_4554_, v_b_4552_);
lean_dec(v_val_4554_);
return v___x_4555_;
}
}
}
LEAN_EXPORT lean_object* l_Array_replace(lean_object* v_00_u03b1_4556_, lean_object* v_inst_4557_, lean_object* v_xs_4558_, lean_object* v_a_4559_, lean_object* v_b_4560_){
_start:
{
lean_object* v___x_4561_; 
v___x_4561_ = l_Array_replace___redArg(v_inst_4557_, v_xs_4558_, v_a_4559_, v_b_4560_);
return v___x_4561_;
}
}
LEAN_EXPORT lean_object* l_Array_instLT(lean_object* v_00_u03b1_4562_, lean_object* v_inst_4563_){
_start:
{
lean_object* v___x_4564_; 
v___x_4564_ = lean_box(0);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l_Array_instLE(lean_object* v_00_u03b1_4565_, lean_object* v_inst_4566_){
_start:
{
lean_object* v___x_4567_; 
v___x_4567_ = lean_box(0);
return v___x_4567_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg(lean_object* v_n_4568_, lean_object* v_a_4569_, lean_object* v_xs_4570_){
_start:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4571_ = lean_array_get_size(v_xs_4570_);
v___x_4572_ = lean_nat_sub(v_n_4568_, v___x_4571_);
v___x_4573_ = lean_mk_array(v___x_4572_, v_a_4569_);
v___x_4574_ = l_Array_append___redArg(v___x_4573_, v_xs_4570_);
return v___x_4574_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___redArg___boxed(lean_object* v_n_4575_, lean_object* v_a_4576_, lean_object* v_xs_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l_Array_leftpad___redArg(v_n_4575_, v_a_4576_, v_xs_4577_);
lean_dec_ref(v_xs_4577_);
lean_dec(v_n_4575_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad(lean_object* v_00_u03b1_4579_, lean_object* v_n_4580_, lean_object* v_a_4581_, lean_object* v_xs_4582_){
_start:
{
lean_object* v___x_4583_; 
v___x_4583_ = l_Array_leftpad___redArg(v_n_4580_, v_a_4581_, v_xs_4582_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___boxed(lean_object* v_00_u03b1_4584_, lean_object* v_n_4585_, lean_object* v_a_4586_, lean_object* v_xs_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l_Array_leftpad(v_00_u03b1_4584_, v_n_4585_, v_a_4586_, v_xs_4587_);
lean_dec_ref(v_xs_4587_);
lean_dec(v_n_4585_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg(lean_object* v_n_4589_, lean_object* v_a_4590_, lean_object* v_xs_4591_){
_start:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4592_ = lean_array_get_size(v_xs_4591_);
v___x_4593_ = lean_nat_sub(v_n_4589_, v___x_4592_);
v___x_4594_ = lean_mk_array(v___x_4593_, v_a_4590_);
v___x_4595_ = l_Array_append___redArg(v_xs_4591_, v___x_4594_);
lean_dec_ref(v___x_4594_);
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___redArg___boxed(lean_object* v_n_4596_, lean_object* v_a_4597_, lean_object* v_xs_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = l_Array_rightpad___redArg(v_n_4596_, v_a_4597_, v_xs_4598_);
lean_dec(v_n_4596_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad(lean_object* v_00_u03b1_4600_, lean_object* v_n_4601_, lean_object* v_a_4602_, lean_object* v_xs_4603_){
_start:
{
lean_object* v___x_4604_; 
v___x_4604_ = l_Array_rightpad___redArg(v_n_4601_, v_a_4602_, v_xs_4603_);
return v___x_4604_;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___boxed(lean_object* v_00_u03b1_4605_, lean_object* v_n_4606_, lean_object* v_a_4607_, lean_object* v_xs_4608_){
_start:
{
lean_object* v_res_4609_; 
v_res_4609_ = l_Array_rightpad(v_00_u03b1_4605_, v_n_4606_, v_a_4607_, v_xs_4608_);
lean_dec(v_n_4606_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0(lean_object* v_x_4610_){
_start:
{
lean_inc(v_x_4610_);
return v_x_4610_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg___lam__0___boxed(lean_object* v_x_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l_Array_reduceOption___redArg___lam__0(v_x_4611_);
lean_dec(v_x_4611_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___redArg(lean_object* v_as_4614_){
_start:
{
lean_object* v___f_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___f_4615_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4616_ = lean_unsigned_to_nat(0u);
v___x_4617_ = lean_array_get_size(v_as_4614_);
v___x_4618_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4619_ = l_Array_filterMapM___redArg(v___x_4618_, v___f_4615_, v_as_4614_, v___x_4616_, v___x_4617_);
return v___x_4619_;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption(lean_object* v_00_u03b1_4620_, lean_object* v_as_4621_){
_start:
{
lean_object* v___f_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___f_4622_ = ((lean_object*)(l_Array_reduceOption___redArg___closed__0));
v___x_4623_ = lean_unsigned_to_nat(0u);
v___x_4624_ = lean_array_get_size(v_as_4621_);
v___x_4625_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4626_ = l_Array_filterMapM___redArg(v___x_4625_, v___f_4622_, v_as_4621_, v___x_4623_, v___x_4624_);
return v___x_4626_;
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg___lam__0(lean_object* v_inst_4627_, lean_object* v_x1_4628_, lean_object* v_x2_4629_){
_start:
{
lean_object* v_fst_4630_; lean_object* v_snd_4631_; lean_object* v___x_4632_; uint8_t v___x_4633_; 
v_fst_4630_ = lean_ctor_get(v_x1_4628_, 0);
v_snd_4631_ = lean_ctor_get(v_x1_4628_, 1);
lean_inc(v_fst_4630_);
lean_inc(v_x2_4629_);
v___x_4632_ = lean_apply_2(v_inst_4627_, v_x2_4629_, v_fst_4630_);
v___x_4633_ = lean_unbox(v___x_4632_);
if (v___x_4633_ == 0)
{
lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4641_; 
lean_inc(v_snd_4631_);
lean_inc(v_fst_4630_);
v_isSharedCheck_4641_ = !lean_is_exclusive(v_x1_4628_);
if (v_isSharedCheck_4641_ == 0)
{
lean_object* v_unused_4642_; lean_object* v_unused_4643_; 
v_unused_4642_ = lean_ctor_get(v_x1_4628_, 1);
lean_dec(v_unused_4642_);
v_unused_4643_ = lean_ctor_get(v_x1_4628_, 0);
lean_dec(v_unused_4643_);
v___x_4635_ = v_x1_4628_;
v_isShared_4636_ = v_isSharedCheck_4641_;
goto v_resetjp_4634_;
}
else
{
lean_dec(v_x1_4628_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4641_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v___x_4637_; lean_object* v___x_4639_; 
v___x_4637_ = lean_array_push(v_snd_4631_, v_fst_4630_);
if (v_isShared_4636_ == 0)
{
lean_ctor_set(v___x_4635_, 1, v___x_4637_);
lean_ctor_set(v___x_4635_, 0, v_x2_4629_);
v___x_4639_ = v___x_4635_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_x2_4629_);
lean_ctor_set(v_reuseFailAlloc_4640_, 1, v___x_4637_);
v___x_4639_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
return v___x_4639_;
}
}
}
else
{
lean_dec(v_x2_4629_);
return v_x1_4628_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___redArg(lean_object* v_inst_4644_, lean_object* v_as_4645_){
_start:
{
lean_object* v___y_4647_; lean_object* v___x_4651_; lean_object* v___x_4652_; uint8_t v___x_4653_; 
v___x_4651_ = lean_unsigned_to_nat(0u);
v___x_4652_ = lean_array_get_size(v_as_4645_);
v___x_4653_ = lean_nat_dec_lt(v___x_4651_, v___x_4652_);
if (v___x_4653_ == 0)
{
lean_object* v___x_4654_; 
lean_dec_ref(v_as_4645_);
lean_dec_ref(v_inst_4644_);
v___x_4654_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
return v___x_4654_;
}
else
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4655_ = lean_array_fget_borrowed(v_as_4645_, v___x_4651_);
v___x_4656_ = ((lean_object*)(l_Array_filter___redArg___closed__0));
v___x_4657_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
if (v___x_4653_ == 0)
{
lean_object* v___x_4658_; 
lean_inc(v___x_4655_);
lean_dec_ref(v_as_4645_);
lean_dec_ref(v_inst_4644_);
v___x_4658_ = lean_array_push(v___x_4656_, v___x_4655_);
return v___x_4658_;
}
else
{
lean_object* v___f_4659_; lean_object* v___x_4660_; uint8_t v___x_4661_; 
v___f_4659_ = lean_alloc_closure((void*)(l_Array_eraseReps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4659_, 0, v_inst_4644_);
lean_inc(v___x_4655_);
v___x_4660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4655_);
lean_ctor_set(v___x_4660_, 1, v___x_4656_);
v___x_4661_ = lean_nat_dec_le(v___x_4652_, v___x_4652_);
if (v___x_4661_ == 0)
{
if (v___x_4653_ == 0)
{
lean_object* v___x_4662_; 
lean_inc(v___x_4655_);
lean_dec_ref(v___x_4660_);
lean_dec_ref(v___f_4659_);
lean_dec_ref(v_as_4645_);
v___x_4662_ = lean_array_push(v___x_4656_, v___x_4655_);
return v___x_4662_;
}
else
{
size_t v___x_4663_; size_t v___x_4664_; lean_object* v___x_4665_; 
v___x_4663_ = ((size_t)0ULL);
v___x_4664_ = lean_usize_of_nat(v___x_4652_);
v___x_4665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4657_, v___f_4659_, v_as_4645_, v___x_4663_, v___x_4664_, v___x_4660_);
v___y_4647_ = v___x_4665_;
goto v___jp_4646_;
}
}
else
{
size_t v___x_4666_; size_t v___x_4667_; lean_object* v___x_4668_; 
v___x_4666_ = ((size_t)0ULL);
v___x_4667_ = lean_usize_of_nat(v___x_4652_);
v___x_4668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4657_, v___f_4659_, v_as_4645_, v___x_4666_, v___x_4667_, v___x_4660_);
v___y_4647_ = v___x_4668_;
goto v___jp_4646_;
}
}
}
v___jp_4646_:
{
lean_object* v_fst_4648_; lean_object* v_snd_4649_; lean_object* v___x_4650_; 
v_fst_4648_ = lean_ctor_get(v___y_4647_, 0);
lean_inc(v_fst_4648_);
v_snd_4649_ = lean_ctor_get(v___y_4647_, 1);
lean_inc(v_snd_4649_);
lean_dec_ref(v___y_4647_);
v___x_4650_ = lean_array_push(v_snd_4649_, v_fst_4648_);
return v___x_4650_;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps(lean_object* v_00_u03b1_4669_, lean_object* v_inst_4670_, lean_object* v_as_4671_){
_start:
{
lean_object* v___x_4672_; 
v___x_4672_ = l_Array_eraseReps___redArg(v_inst_4670_, v_as_4671_);
return v___x_4672_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(lean_object* v_inst_4673_, lean_object* v_as_4674_, lean_object* v_a_4675_, lean_object* v_x_4676_){
_start:
{
lean_object* v_zero_4677_; uint8_t v_isZero_4678_; 
v_zero_4677_ = lean_unsigned_to_nat(0u);
v_isZero_4678_ = lean_nat_dec_eq(v_x_4676_, v_zero_4677_);
if (v_isZero_4678_ == 1)
{
lean_dec(v_x_4676_);
lean_dec(v_a_4675_);
lean_dec_ref(v_inst_4673_);
return v_isZero_4678_;
}
else
{
lean_object* v_one_4679_; lean_object* v_n_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; uint8_t v___x_4683_; 
v_one_4679_ = lean_unsigned_to_nat(1u);
v_n_4680_ = lean_nat_sub(v_x_4676_, v_one_4679_);
lean_dec(v_x_4676_);
v___x_4681_ = lean_array_fget_borrowed(v_as_4674_, v_n_4680_);
lean_inc_ref(v_inst_4673_);
lean_inc(v___x_4681_);
lean_inc(v_a_4675_);
v___x_4682_ = lean_apply_2(v_inst_4673_, v_a_4675_, v___x_4681_);
v___x_4683_ = lean_unbox(v___x_4682_);
if (v___x_4683_ == 0)
{
v_x_4676_ = v_n_4680_;
goto _start;
}
else
{
lean_dec(v_n_4680_);
lean_dec(v_a_4675_);
lean_dec_ref(v_inst_4673_);
return v_isZero_4678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg___boxed(lean_object* v_inst_4685_, lean_object* v_as_4686_, lean_object* v_a_4687_, lean_object* v_x_4688_){
_start:
{
uint8_t v_res_4689_; lean_object* v_r_4690_; 
v_res_4689_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4685_, v_as_4686_, v_a_4687_, v_x_4688_);
lean_dec_ref(v_as_4686_);
v_r_4690_ = lean_box(v_res_4689_);
return v_r_4690_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(lean_object* v_00_u03b1_4691_, lean_object* v_inst_4692_, lean_object* v_as_4693_, lean_object* v_a_4694_, lean_object* v_x_4695_, lean_object* v_x_4696_){
_start:
{
uint8_t v___x_4697_; 
v___x_4697_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4692_, v_as_4693_, v_a_4694_, v_x_4695_);
return v___x_4697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___boxed(lean_object* v_00_u03b1_4698_, lean_object* v_inst_4699_, lean_object* v_as_4700_, lean_object* v_a_4701_, lean_object* v_x_4702_, lean_object* v_x_4703_){
_start:
{
uint8_t v_res_4704_; lean_object* v_r_4705_; 
v_res_4704_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(v_00_u03b1_4698_, v_inst_4699_, v_as_4700_, v_a_4701_, v_x_4702_, v_x_4703_);
lean_dec_ref(v_as_4700_);
v_r_4705_ = lean_box(v_res_4704_);
return v_r_4705_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(lean_object* v_inst_4706_, lean_object* v_as_4707_, lean_object* v_i_4708_){
_start:
{
lean_object* v___x_4709_; uint8_t v___x_4710_; 
v___x_4709_ = lean_array_get_size(v_as_4707_);
v___x_4710_ = lean_nat_dec_lt(v_i_4708_, v___x_4709_);
if (v___x_4710_ == 0)
{
uint8_t v___x_4711_; 
lean_dec(v_i_4708_);
lean_dec_ref(v_inst_4706_);
v___x_4711_ = 1;
return v___x_4711_;
}
else
{
lean_object* v___x_4712_; uint8_t v___x_4713_; 
v___x_4712_ = lean_array_fget_borrowed(v_as_4707_, v_i_4708_);
lean_inc(v_i_4708_);
lean_inc(v___x_4712_);
lean_inc_ref(v_inst_4706_);
v___x_4713_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___redArg(v_inst_4706_, v_as_4707_, v___x_4712_, v_i_4708_);
if (v___x_4713_ == 0)
{
lean_dec(v_i_4708_);
lean_dec_ref(v_inst_4706_);
return v___x_4713_;
}
else
{
lean_object* v___x_4714_; lean_object* v___x_4715_; 
v___x_4714_ = lean_unsigned_to_nat(1u);
v___x_4715_ = lean_nat_add(v_i_4708_, v___x_4714_);
lean_dec(v_i_4708_);
v_i_4708_ = v___x_4715_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg___boxed(lean_object* v_inst_4717_, lean_object* v_as_4718_, lean_object* v_i_4719_){
_start:
{
uint8_t v_res_4720_; lean_object* v_r_4721_; 
v_res_4720_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4717_, v_as_4718_, v_i_4719_);
lean_dec_ref(v_as_4718_);
v_r_4721_ = lean_box(v_res_4720_);
return v_r_4721_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux(lean_object* v_00_u03b1_4722_, lean_object* v_inst_4723_, lean_object* v_as_4724_, lean_object* v_i_4725_){
_start:
{
uint8_t v___x_4726_; 
v___x_4726_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4723_, v_as_4724_, v_i_4725_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___boxed(lean_object* v_00_u03b1_4727_, lean_object* v_inst_4728_, lean_object* v_as_4729_, lean_object* v_i_4730_){
_start:
{
uint8_t v_res_4731_; lean_object* v_r_4732_; 
v_res_4731_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux(v_00_u03b1_4727_, v_inst_4728_, v_as_4729_, v_i_4730_);
lean_dec_ref(v_as_4729_);
v_r_4732_ = lean_box(v_res_4731_);
return v_r_4732_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___redArg(lean_object* v_inst_4733_, lean_object* v_as_4734_){
_start:
{
lean_object* v___x_4735_; uint8_t v___x_4736_; 
v___x_4735_ = lean_unsigned_to_nat(0u);
v___x_4736_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___redArg(v_inst_4733_, v_as_4734_, v___x_4735_);
return v___x_4736_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___redArg___boxed(lean_object* v_inst_4737_, lean_object* v_as_4738_){
_start:
{
uint8_t v_res_4739_; lean_object* v_r_4740_; 
v_res_4739_ = l_Array_allDiff___redArg(v_inst_4737_, v_as_4738_);
lean_dec_ref(v_as_4738_);
v_r_4740_ = lean_box(v_res_4739_);
return v_r_4740_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff(lean_object* v_00_u03b1_4741_, lean_object* v_inst_4742_, lean_object* v_as_4743_){
_start:
{
uint8_t v___x_4744_; 
v___x_4744_ = l_Array_allDiff___redArg(v_inst_4742_, v_as_4743_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___boxed(lean_object* v_00_u03b1_4745_, lean_object* v_inst_4746_, lean_object* v_as_4747_){
_start:
{
uint8_t v_res_4748_; lean_object* v_r_4749_; 
v_res_4748_ = l_Array_allDiff(v_00_u03b1_4745_, v_inst_4746_, v_as_4747_);
lean_dec_ref(v_as_4747_);
v_r_4749_ = lean_box(v_res_4748_);
return v_r_4749_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0(uint8_t v___x_4750_, lean_object* v_x1_4751_, lean_object* v_x2_4752_){
_start:
{
lean_object* v_fst_4753_; uint8_t v___x_4754_; 
v_fst_4753_ = lean_ctor_get(v_x1_4751_, 0);
v___x_4754_ = lean_unbox(v_fst_4753_);
if (v___x_4754_ == 0)
{
lean_object* v_snd_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4763_; 
lean_dec(v_x2_4752_);
v_snd_4755_ = lean_ctor_get(v_x1_4751_, 1);
v_isSharedCheck_4763_ = !lean_is_exclusive(v_x1_4751_);
if (v_isSharedCheck_4763_ == 0)
{
lean_object* v_unused_4764_; 
v_unused_4764_ = lean_ctor_get(v_x1_4751_, 0);
lean_dec(v_unused_4764_);
v___x_4757_ = v_x1_4751_;
v_isShared_4758_ = v_isSharedCheck_4763_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_snd_4755_);
lean_dec(v_x1_4751_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4763_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4759_; lean_object* v___x_4761_; 
v___x_4759_ = lean_box(v___x_4750_);
if (v_isShared_4758_ == 0)
{
lean_ctor_set(v___x_4757_, 0, v___x_4759_);
v___x_4761_ = v___x_4757_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v___x_4759_);
lean_ctor_set(v_reuseFailAlloc_4762_, 1, v_snd_4755_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
else
{
lean_object* v_snd_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4775_; 
v_snd_4765_ = lean_ctor_get(v_x1_4751_, 1);
v_isSharedCheck_4775_ = !lean_is_exclusive(v_x1_4751_);
if (v_isSharedCheck_4775_ == 0)
{
lean_object* v_unused_4776_; 
v_unused_4776_ = lean_ctor_get(v_x1_4751_, 0);
lean_dec(v_unused_4776_);
v___x_4767_ = v_x1_4751_;
v_isShared_4768_ = v_isSharedCheck_4775_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_snd_4765_);
lean_dec(v_x1_4751_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4775_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
uint8_t v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4773_; 
v___x_4769_ = 0;
v___x_4770_ = lean_array_push(v_snd_4765_, v_x2_4752_);
v___x_4771_ = lean_box(v___x_4769_);
if (v_isShared_4768_ == 0)
{
lean_ctor_set(v___x_4767_, 1, v___x_4770_);
lean_ctor_set(v___x_4767_, 0, v___x_4771_);
v___x_4773_ = v___x_4767_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4771_);
lean_ctor_set(v_reuseFailAlloc_4774_, 1, v___x_4770_);
v___x_4773_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
return v___x_4773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg___lam__0___boxed(lean_object* v___x_4777_, lean_object* v_x1_4778_, lean_object* v_x2_4779_){
_start:
{
uint8_t v___x_172__boxed_4780_; lean_object* v_res_4781_; 
v___x_172__boxed_4780_ = lean_unbox(v___x_4777_);
v_res_4781_ = l_Array_getEvenElems___redArg___lam__0(v___x_172__boxed_4780_, v_x1_4778_, v_x2_4779_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___redArg(lean_object* v_as_4782_){
_start:
{
lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; uint8_t v___x_4787_; 
v___x_4783_ = lean_unsigned_to_nat(0u);
v___x_4784_ = ((lean_object*)(l_Array_instEmptyCollection___closed__0));
v___x_4785_ = lean_array_get_size(v_as_4782_);
v___x_4786_ = ((lean_object*)(l_Array_foldl___redArg___closed__9));
v___x_4787_ = lean_nat_dec_lt(v___x_4783_, v___x_4785_);
if (v___x_4787_ == 0)
{
lean_dec_ref(v_as_4782_);
return v___x_4784_;
}
else
{
lean_object* v___x_4788_; lean_object* v___f_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; uint8_t v___x_4792_; 
v___x_4788_ = lean_box(v___x_4787_);
v___f_4789_ = lean_alloc_closure((void*)(l_Array_getEvenElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4789_, 0, v___x_4788_);
v___x_4790_ = lean_box(v___x_4787_);
v___x_4791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4790_);
lean_ctor_set(v___x_4791_, 1, v___x_4784_);
v___x_4792_ = lean_nat_dec_le(v___x_4785_, v___x_4785_);
if (v___x_4792_ == 0)
{
if (v___x_4787_ == 0)
{
lean_dec_ref(v___x_4791_);
lean_dec_ref(v___f_4789_);
lean_dec_ref(v_as_4782_);
return v___x_4784_;
}
else
{
size_t v___x_4793_; size_t v___x_4794_; lean_object* v___x_4795_; lean_object* v_snd_4796_; 
v___x_4793_ = ((size_t)0ULL);
v___x_4794_ = lean_usize_of_nat(v___x_4785_);
v___x_4795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4786_, v___f_4789_, v_as_4782_, v___x_4793_, v___x_4794_, v___x_4791_);
v_snd_4796_ = lean_ctor_get(v___x_4795_, 1);
lean_inc(v_snd_4796_);
lean_dec(v___x_4795_);
return v_snd_4796_;
}
}
else
{
size_t v___x_4797_; size_t v___x_4798_; lean_object* v___x_4799_; lean_object* v_snd_4800_; 
v___x_4797_ = ((size_t)0ULL);
v___x_4798_ = lean_usize_of_nat(v___x_4785_);
v___x_4799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_4786_, v___f_4789_, v_as_4782_, v___x_4797_, v___x_4798_, v___x_4791_);
v_snd_4800_ = lean_ctor_get(v___x_4799_, 1);
lean_inc(v_snd_4800_);
lean_dec(v___x_4799_);
return v_snd_4800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems(lean_object* v_00_u03b1_4801_, lean_object* v_as_4802_){
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
static lean_object* _init_l_Array_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4826_ = ((lean_object*)(l_term_x23_x5b___x2c_x5d___closed__4));
v___x_4827_ = lean_string_length(v___x_4826_);
return v___x_4827_;
}
}
static lean_object* _init_l_Array_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4828_ = lean_obj_once(&l_Array_repr___redArg___closed__2, &l_Array_repr___redArg___closed__2_once, _init_l_Array_repr___redArg___closed__2);
v___x_4829_ = lean_nat_to_int(v___x_4828_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___redArg(lean_object* v_inst_4837_, lean_object* v_xs_4838_){
_start:
{
lean_object* v___x_4839_; lean_object* v___x_4840_; uint8_t v___x_4841_; 
v___x_4839_ = lean_array_get_size(v_xs_4838_);
v___x_4840_ = lean_unsigned_to_nat(0u);
v___x_4841_ = lean_nat_dec_eq(v___x_4839_, v___x_4840_);
if (v___x_4841_ == 0)
{
lean_object* v_x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; 
v_x_4842_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_4842_, 0, lean_box(0));
lean_closure_set(v_x_4842_, 1, v_inst_4837_);
v___x_4843_ = lean_array_to_list(v_xs_4838_);
v___x_4844_ = ((lean_object*)(l_Array_repr___redArg___closed__1));
v___x_4845_ = l_Std_Format_joinSep___redArg(v_x_4842_, v___x_4843_, v___x_4844_);
v___x_4846_ = lean_obj_once(&l_Array_repr___redArg___closed__3, &l_Array_repr___redArg___closed__3_once, _init_l_Array_repr___redArg___closed__3);
v___x_4847_ = ((lean_object*)(l_Array_repr___redArg___closed__4));
v___x_4848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4847_);
lean_ctor_set(v___x_4848_, 1, v___x_4845_);
v___x_4849_ = ((lean_object*)(l_Array_repr___redArg___closed__5));
v___x_4850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4850_, 0, v___x_4848_);
lean_ctor_set(v___x_4850_, 1, v___x_4849_);
v___x_4851_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4851_, 0, v___x_4846_);
lean_ctor_set(v___x_4851_, 1, v___x_4850_);
v___x_4852_ = l_Std_Format_fill(v___x_4851_);
return v___x_4852_;
}
else
{
lean_object* v___x_4853_; 
lean_dec_ref(v_xs_4838_);
lean_dec_ref(v_inst_4837_);
v___x_4853_ = ((lean_object*)(l_Array_repr___redArg___closed__7));
return v___x_4853_;
}
}
}
LEAN_EXPORT lean_object* l_Array_repr(lean_object* v_00_u03b1_4854_, lean_object* v_inst_4855_, lean_object* v_xs_4856_){
_start:
{
lean_object* v___x_4857_; 
v___x_4857_ = l_Array_repr___redArg(v_inst_4855_, v_xs_4856_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0(lean_object* v_inst_4858_, lean_object* v_xs_4859_, lean_object* v_x_4860_){
_start:
{
lean_object* v___x_4861_; 
v___x_4861_ = l_Array_repr___redArg(v_inst_4858_, v_xs_4859_);
return v___x_4861_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object* v_inst_4862_, lean_object* v_xs_4863_, lean_object* v_x_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l_Array_instRepr___redArg___lam__0(v_inst_4862_, v_xs_4863_, v_x_4864_);
lean_dec(v_x_4864_);
return v_res_4865_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___redArg(lean_object* v_inst_4866_){
_start:
{
lean_object* v___f_4867_; 
v___f_4867_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4867_, 0, v_inst_4866_);
return v___f_4867_;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr(lean_object* v_00_u03b1_4868_, lean_object* v_inst_4869_){
_start:
{
lean_object* v___f_4870_; 
v___f_4870_ = lean_alloc_closure((void*)(l_Array_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4870_, 0, v_inst_4869_);
return v___f_4870_;
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
